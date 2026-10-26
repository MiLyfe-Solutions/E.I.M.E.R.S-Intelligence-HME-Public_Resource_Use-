import V185TrunkScan23Chunk0837

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4959352 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_4959352 : Nat := 118140960795 + 4959352 * 2 ^ 59
def prefixEnd_4959352 : Nat := 4983230072969 + 3 ^ 40 * 4959352 * 2
def baseEnd_4959352 : Nat := 2546531310836585746192361

theorem tailTrace_4959352 : CollatzResearch.WordTrace tailWord_4959352 prefixEnd_4959352 2546531310836585746192361 := by
  unfold tailWord_4959352
  simp only [CollatzResearch.WordTrace]
  refine ⟨90441213764561084367200155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120588285019414779156266873 90441213764561084367200155)
  ·
    refine ⟨135661820646841626550800233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90441213764561084367200155 135661820646841626550800233)
    ·
      refine ⟨101746365485131219913100175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135661820646841626550800233 101746365485131219913100175)
      ·
        refine ⟨152619548227696829869650263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101746365485131219913100175 152619548227696829869650263)
        ·
          refine ⟨228929322341545244804475395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152619548227696829869650263 228929322341545244804475395)
          ·
            refine ⟨343393983512317867206713093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228929322341545244804475395 343393983512317867206713093)
            ·
              refine ⟨64386371908559600101258705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 343393983512317867206713093 64386371908559600101258705)
              ·
                refine ⟨48289778931419700075944029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64386371908559600101258705 48289778931419700075944029)
                ·
                  refine ⟨18108667099282387528479011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48289778931419700075944029 18108667099282387528479011)
                  ·
                    refine ⟨27163000648923581292718517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18108667099282387528479011 27163000648923581292718517)
                    ·
                      refine ⟨2546531310836585746192361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27163000648923581292718517 2546531310836585746192361)
                      ·
                        rfl

theorem cell23_4959352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_4959352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959352 prefixEnd_4959352 := by exact prefixLift 4959352
  have htrace : WordTrace (prefixWord ++ tailWord_4959352) baseStart_4959352 baseEnd_4959352 := by
    simpa [prefixWord, tailWord_4959352, baseEnd_4959352] using wordTrace_append hprefix tailTrace_4959352
  have hstable : (prefixWord ++ tailWord_4959352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959352).length < 2 ^ (prefixWord ++ tailWord_4959352).sum := by decide
  have hdescent : baseEnd_4959352 < baseStart_4959352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959353 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 2, 3, 2]
def baseStart_4959353 : Nat := 118140960795 + 4959353 * 2 ^ 59
def prefixEnd_4959353 : Nat := 4983230072969 + 3 ^ 40 * 4959353 * 2
def baseEnd_4959353 : Nat := 2546531824317240242279857

theorem tailTrace_4959353 : CollatzResearch.WordTrace tailWord_4959353 prefixEnd_4959353 2546531824317240242279857 := by
  unfold tailWord_4959353
  simp only [CollatzResearch.WordTrace]
  refine ⟨180882464002118545905186713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120588309334745697270124475 180882464002118545905186713)
  ·
    refine ⟨135661848001588909428890035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180882464002118545905186713 135661848001588909428890035)
    ·
      refine ⟨203492772002383364143335053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135661848001588909428890035 203492772002383364143335053)
      ·
        refine ⟨76309789500893761553750645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203492772002383364143335053 76309789500893761553750645)
        ·
          refine ⟨7154042765708790145664123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76309789500893761553750645 7154042765708790145664123)
          ·
            refine ⟨10731064148563185218496185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154042765708790145664123 10731064148563185218496185)
            ·
              refine ⟨8048298111422388913872139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10731064148563185218496185 8048298111422388913872139)
              ·
                refine ⟨12072447167133583370808209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048298111422388913872139 12072447167133583370808209)
                ·
                  refine ⟨9054335375350187528106157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12072447167133583370808209 9054335375350187528106157)
                  ·
                    refine ⟨3395375765756320323039809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9054335375350187528106157 3395375765756320323039809)
                    ·
                      refine ⟨2546531824317240242279857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395375765756320323039809 2546531824317240242279857)
                      ·
                        rfl

theorem cell23_4959353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_4959353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959353 prefixEnd_4959353 := by exact prefixLift 4959353
  have htrace : WordTrace (prefixWord ++ tailWord_4959353) baseStart_4959353 baseEnd_4959353 := by
    simpa [prefixWord, tailWord_4959353, baseEnd_4959353] using wordTrace_append hprefix tailTrace_4959353
  have hstable : (prefixWord ++ tailWord_4959353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959353).length < 2 ^ (prefixWord ++ tailWord_4959353).sum := by decide
  have hdescent : baseEnd_4959353 < baseStart_4959353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959369 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 5]
def baseStart_4959369 : Nat := 118140960795 + 4959369 * 2 ^ 59
def prefixEnd_4959369 : Nat := 4983230072969 + 3 ^ 40 * 4959369 * 2
def baseEnd_4959369 : Nat := 2546540040007712179679783

theorem tailTrace_4959369 : CollatzResearch.WordTrace tailWord_4959369 prefixEnd_4959369 2546540040007712179679783 := by
  unfold tailWord_4959369
  simp only [CollatzResearch.WordTrace]
  refine ⟨180883047570060580637769161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120588698380040387091846107 180883047570060580637769161)
  ·
    refine ⟨135662285677545435478326871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180883047570060580637769161 135662285677545435478326871)
    ·
      refine ⟨203493428516318153217490307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135662285677545435478326871 203493428516318153217490307)
      ·
        refine ⟨305240142774477229826235461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203493428516318153217490307 305240142774477229826235461)
        ·
          refine ⟨57232526770214480592419149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305240142774477229826235461 57232526770214480592419149)
          ·
            refine ⟨21462197538830430222157181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57232526770214480592419149 21462197538830430222157181)
            ·
              refine ⟨8048324077061411333308943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21462197538830430222157181 8048324077061411333308943)
              ·
                refine ⟨12072486115592116999963415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048324077061411333308943 12072486115592116999963415)
                ·
                  refine ⟨18108729173388175499945123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12072486115592116999963415 18108729173388175499945123)
                  ·
                    refine ⟨27163093760082263249917685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18108729173388175499945123 27163093760082263249917685)
                    ·
                      refine ⟨2546540040007712179679783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27163093760082263249917685 2546540040007712179679783)
                      ·
                        rfl

theorem cell23_4959369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_4959369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959369 prefixEnd_4959369 := by exact prefixLift 4959369
  have htrace : WordTrace (prefixWord ++ tailWord_4959369) baseStart_4959369 baseEnd_4959369 := by
    simpa [prefixWord, tailWord_4959369, baseEnd_4959369] using wordTrace_append hprefix tailTrace_4959369
  have hstable : (prefixWord ++ tailWord_4959369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959369).length < 2 ^ (prefixWord ++ tailWord_4959369).sum := by decide
  have hdescent : baseEnd_4959369 < baseStart_4959369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959386 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_4959386 : Nat := 118140960795 + 4959386 * 2 ^ 59
def prefixEnd_4959386 : Nat := 4983230072969 + 3 ^ 40 * 4959386 * 2
def baseEnd_4959386 : Nat := 2546548769178838613167205

theorem tailTrace_4959386 : CollatzResearch.WordTrace tailWord_4959386 prefixEnd_4959386 2546548769178838613167205 := by
  unfold tailWord_4959386
  simp only [CollatzResearch.WordTrace]
  refine ⟨45220916902749748135284503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120589111740665995027425341 45220916902749748135284503)
  ·
    refine ⟨67831375354124622202926755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45220916902749748135284503 67831375354124622202926755)
    ·
      refine ⟨101747063031186933304390133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67831375354124622202926755 101747063031186933304390133)
      ·
        refine ⟨9538787159173774997286575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101747063031186933304390133 9538787159173774997286575)
        ·
          refine ⟨14308180738760662495929863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9538787159173774997286575 14308180738760662495929863)
          ·
            refine ⟨21462271108140993743894795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14308180738760662495929863 21462271108140993743894795)
            ·
              refine ⟨32193406662211490615842193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21462271108140993743894795 32193406662211490615842193)
              ·
                refine ⟨24145054996658617961881645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32193406662211490615842193 24145054996658617961881645)
                ·
                  refine ⟨9054395623746981735705617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24145054996658617961881645 9054395623746981735705617)
                  ·
                    refine ⟨6790796717810236301779213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9054395623746981735705617 6790796717810236301779213)
                    ·
                      refine ⟨2546548769178838613167205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6790796717810236301779213 2546548769178838613167205)
                      ·
                        rfl

theorem cell23_4959386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_4959386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959386 prefixEnd_4959386 := by exact prefixLift 4959386
  have htrace : WordTrace (prefixWord ++ tailWord_4959386) baseStart_4959386 baseEnd_4959386 := by
    simpa [prefixWord, tailWord_4959386, baseEnd_4959386] using wordTrace_append hprefix tailTrace_4959386
  have hstable : (prefixWord ++ tailWord_4959386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959386).length < 2 ^ (prefixWord ++ tailWord_4959386).sum := by decide
  have hdescent : baseEnd_4959386 < baseStart_4959386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959396 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_4959396 : Nat := 118140960795 + 4959396 * 2 ^ 59
def prefixEnd_4959396 : Nat := 4983230072969 + 3 ^ 40 * 4959396 * 2
def baseEnd_4959396 : Nat := 2546553903985383574042159

theorem tailTrace_4959396 : CollatzResearch.WordTrace tailWord_4959396 prefixEnd_4959396 2546553903985383574042159 := by
  unfold tailWord_4959396
  simp only [CollatzResearch.WordTrace]
  refine ⟨90442016170481382124501021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120589354893975176166001361 90442016170481382124501021)
  ·
    refine ⟨33915756063930518296687883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90442016170481382124501021 33915756063930518296687883)
    ·
      refine ⟨50873634095895777445031825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33915756063930518296687883 50873634095895777445031825)
      ·
        refine ⟨38155225571921833083773869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50873634095895777445031825 38155225571921833083773869)
        ·
          refine ⟨14308209589470687406415201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38155225571921833083773869 14308209589470687406415201)
          ·
            refine ⟨10731157192103015554811401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14308209589470687406415201 10731157192103015554811401)
            ·
              refine ⟨8048367894077261666108551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10731157192103015554811401 8048367894077261666108551)
              ·
                refine ⟨12072551841115892499162827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048367894077261666108551 12072551841115892499162827)
                ·
                  refine ⟨18108827761673838748744241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12072551841115892499162827 18108827761673838748744241)
                  ·
                    refine ⟨13581620821255379061558181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18108827761673838748744241 13581620821255379061558181)
                    ·
                      refine ⟨2546553903985383574042159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13581620821255379061558181 2546553903985383574042159)
                      ·
                        rfl

theorem cell23_4959396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_4959396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959396 prefixEnd_4959396 := by exact prefixLift 4959396
  have htrace : WordTrace (prefixWord ++ tailWord_4959396) baseStart_4959396 baseEnd_4959396 := by
    simpa [prefixWord, tailWord_4959396, baseEnd_4959396] using wordTrace_append hprefix tailTrace_4959396
  have hstable : (prefixWord ++ tailWord_4959396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959396).length < 2 ^ (prefixWord ++ tailWord_4959396).sum := by decide
  have hdescent : baseEnd_4959396 < baseStart_4959396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959414 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4959414 : Nat := 118140960795 + 4959414 * 2 ^ 59
def prefixEnd_4959414 : Nat := 4983230072969 + 3 ^ 40 * 4959414 * 2
def baseEnd_4959414 : Nat := 848854382212388167872359

theorem tailTrace_4959414 : CollatzResearch.WordTrace tailWord_4959414 prefixEnd_4959414 848854382212388167872359 := by
  unfold tailWord_4959414
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305293053431097082697331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120589792569931702215438197 11305293053431097082697331)
  ·
    refine ⟨16957939580146645624045997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11305293053431097082697331 16957939580146645624045997)
    ·
      refine ⟨6359227342554992109017249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16957939580146645624045997 6359227342554992109017249)
      ·
        refine ⟨4769420506916244081762937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6359227342554992109017249 4769420506916244081762937)
        ·
          refine ⟨3577065380187183061322203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4769420506916244081762937 3577065380187183061322203)
          ·
            refine ⟨5365598070280774591983305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577065380187183061322203 5365598070280774591983305)
            ·
              refine ⟨4024198552710580943987479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5365598070280774591983305 4024198552710580943987479)
              ·
                refine ⟨6036297829065871415981219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024198552710580943987479 6036297829065871415981219)
                ·
                  refine ⟨9054446743598807123971829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6036297829065871415981219 9054446743598807123971829)
                  ·
                    refine ⟨848854382212388167872359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9054446743598807123971829 848854382212388167872359)
                    ·
                      rfl

theorem cell23_4959414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4959414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959414 prefixEnd_4959414 := by exact prefixLift 4959414
  have htrace : WordTrace (prefixWord ++ tailWord_4959414) baseStart_4959414 baseEnd_4959414 := by
    simpa [prefixWord, tailWord_4959414, baseEnd_4959414] using wordTrace_append hprefix tailTrace_4959414
  have hstable : (prefixWord ++ tailWord_4959414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959414).length < 2 ^ (prefixWord ++ tailWord_4959414).sum := by decide
  have hdescent : baseEnd_4959414 < baseStart_4959414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959420 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4959420 : Nat := 118140960795 + 4959420 * 2 ^ 59
def prefixEnd_4959420 : Nat := 4983230072969 + 3 ^ 40 * 4959420 * 2
def baseEnd_4959420 : Nat := 2546566227521091480142049

theorem tailTrace_4959420 : CollatzResearch.WordTrace tailWord_4959420 prefixEnd_4959420 2546566227521091480142049 := by
  unfold tailWord_4959420
  simp only [CollatzResearch.WordTrace]
  refine ⟨90442453846437908173937857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120589938461917210898583809 90442453846437908173937857)
  ·
    refine ⟨67831840384828431130453393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90442453846437908173937857 67831840384828431130453393)
    ·
      refine ⟨50873880288621323347840045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67831840384828431130453393 50873880288621323347840045)
      ·
        refine ⟨19077705108232996255440017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50873880288621323347840045 19077705108232996255440017)
        ·
          refine ⟨14308278831174747191580013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19077705108232996255440017 14308278831174747191580013)
          ·
            refine ⟨5365604561690530196842505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14308278831174747191580013 5365604561690530196842505)
            ·
              refine ⟨4024203421267897647631879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5365604561690530196842505 4024203421267897647631879)
              ·
                refine ⟨6036305131901846471447819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024203421267897647631879 6036305131901846471447819)
                ·
                  refine ⟨9054457697852769707171729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6036305131901846471447819 9054457697852769707171729)
                  ·
                    refine ⟨6790843273389577280378797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9054457697852769707171729 6790843273389577280378797)
                    ·
                      refine ⟨2546566227521091480142049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6790843273389577280378797 2546566227521091480142049)
                      ·
                        rfl

theorem cell23_4959420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4959420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959420 prefixEnd_4959420 := by exact prefixLift 4959420
  have htrace : WordTrace (prefixWord ++ tailWord_4959420) baseStart_4959420 baseEnd_4959420 := by
    simpa [prefixWord, tailWord_4959420, baseEnd_4959420] using wordTrace_append hprefix tailTrace_4959420
  have hstable : (prefixWord ++ tailWord_4959420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959420).length < 2 ^ (prefixWord ++ tailWord_4959420).sum := by decide
  have hdescent : baseEnd_4959420 < baseStart_4959420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959509 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_4959509 : Nat := 118140960795 + 4959509 * 2 ^ 59
def prefixEnd_4959509 : Nat := 4983230072969 + 3 ^ 40 * 4959509 * 2
def baseEnd_4959509 : Nat := 848870642433113877309713

theorem tailTrace_4959509 : CollatzResearch.WordTrace tailWord_4959509 prefixEnd_4959509 848870642433113877309713 := by
  unfold tailWord_4959509
  simp only [CollatzResearch.WordTrace]
  refine ⟨180888153789553384547865581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120592102526368923031910387 180888153789553384547865581)
  ·
    refine ⟨67833057671082519205449593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180888153789553384547865581 67833057671082519205449593)
    ·
      refine ⟨50874793253311889404087195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67833057671082519205449593 50874793253311889404087195)
      ·
        refine ⟨76312189879967834106130793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50874793253311889404087195 76312189879967834106130793)
        ·
          refine ⟨57234142409975875579598095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76312189879967834106130793 57234142409975875579598095)
          ·
            refine ⟨85851213614963813369397143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57234142409975875579598095 85851213614963813369397143)
            ·
              refine ⟨128776820422445720054095715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85851213614963813369397143 128776820422445720054095715)
              ·
                refine ⟨193165230633668580081143573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128776820422445720054095715 193165230633668580081143573)
                ·
                  refine ⟨9054620185953214691303605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 193165230633668580081143573 9054620185953214691303605)
                  ·
                    refine ⟨848870642433113877309713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9054620185953214691303605 848870642433113877309713)
                    ·
                      rfl

theorem cell23_4959509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_4959509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959509 prefixEnd_4959509 := by exact prefixLift 4959509
  have htrace : WordTrace (prefixWord ++ tailWord_4959509) baseStart_4959509 baseEnd_4959509 := by
    simpa [prefixWord, tailWord_4959509, baseEnd_4959509] using wordTrace_append hprefix tailTrace_4959509
  have hstable : (prefixWord ++ tailWord_4959509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959509).length < 2 ^ (prefixWord ++ tailWord_4959509).sum := by decide
  have hdescent : baseEnd_4959509 < baseStart_4959509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959546 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_4959546 : Nat := 118140960795 + 4959546 * 2 ^ 59
def prefixEnd_4959546 : Nat := 4983230072969 + 3 ^ 40 * 4959546 * 2
def baseEnd_4959546 : Nat := 2546630926083557987166469

theorem tailTrace_4959546 : CollatzResearch.WordTrace tailWord_4959546 prefixEnd_4959546 2546630926083557987166469 := by
  unfold tailWord_4959546
  simp only [CollatzResearch.WordTrace]
  refine ⟨45222375822604834966740623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120593002193612893244641661 45222375822604834966740623)
  ·
    refine ⟨67833563733907252450110935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45222375822604834966740623 67833563733907252450110935)
    ·
      refine ⟨101750345600860878675166403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67833563733907252450110935 101750345600860878675166403)
      ·
        refine ⟨152625518401291318012749605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101750345600860878675166403 152625518401291318012749605)
        ·
          refine ⟨28617284700242122127390551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152625518401291318012749605 28617284700242122127390551)
          ·
            refine ⟨42925927050363183191085827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28617284700242122127390551 42925927050363183191085827)
            ·
              refine ⟨64388890575544774786628741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42925927050363183191085827 64388890575544774786628741)
              ·
                refine ⟨12072916982914645272492889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64388890575544774786628741 12072916982914645272492889)
                ·
                  refine ⟨9054687737185983954369667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12072916982914645272492889 9054687737185983954369667)
                  ·
                    refine ⟨13582031605778975931554501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9054687737185983954369667 13582031605778975931554501)
                    ·
                      refine ⟨2546630926083557987166469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13582031605778975931554501 2546630926083557987166469)
                      ·
                        rfl

theorem cell23_4959546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_4959546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959546 prefixEnd_4959546 := by exact prefixLift 4959546
  have htrace : WordTrace (prefixWord ++ tailWord_4959546) baseStart_4959546 baseEnd_4959546 := by
    simpa [prefixWord, tailWord_4959546, baseEnd_4959546] using wordTrace_append hprefix tailTrace_4959546
  have hstable : (prefixWord ++ tailWord_4959546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959546).length < 2 ^ (prefixWord ++ tailWord_4959546).sum := by decide
  have hdescent : baseEnd_4959546 < baseStart_4959546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959566 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_4959566 : Nat := 118140960795 + 4959566 * 2 ^ 59
def prefixEnd_4959566 : Nat := 4983230072969 + 3 ^ 40 * 4959566 * 2
def baseEnd_4959566 : Nat := 2546641195696647908916377

theorem tailTrace_4959566 : CollatzResearch.WordTrace tailWord_4959566 prefixEnd_4959566 2546641195696647908916377 := by
  unfold tailWord_4959566
  simp only [CollatzResearch.WordTrace]
  refine ⟨22611279093793360410336319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120593488500231255521793701 22611279093793360410336319)
  ·
    refine ⟨33916918640690040615504479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22611279093793360410336319 33916918640690040615504479)
    ·
      refine ⟨50875377961035060923256719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33916918640690040615504479 50875377961035060923256719)
      ·
        refine ⟨76313066941552591384885079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50875377961035060923256719 76313066941552591384885079)
        ·
          refine ⟨114469600412328887077327619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76313066941552591384885079 114469600412328887077327619)
          ·
            refine ⟨171704400618493330615991429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114469600412328887077327619 171704400618493330615991429)
            ·
              refine ⟨32194575115967499490498393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171704400618493330615991429 32194575115967499490498393)
              ·
                refine ⟨24145931336975624617873795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32194575115967499490498393 24145931336975624617873795)
                ·
                  refine ⟨36218897005463436926810693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24145931336975624617873795 36218897005463436926810693)
                  ·
                    refine ⟨6791043188524394423777005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36218897005463436926810693 6791043188524394423777005)
                    ·
                      refine ⟨2546641195696647908916377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6791043188524394423777005 2546641195696647908916377)
                      ·
                        rfl

theorem cell23_4959566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_4959566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959566 prefixEnd_4959566 := by exact prefixLift 4959566
  have htrace : WordTrace (prefixWord ++ tailWord_4959566) baseStart_4959566 baseEnd_4959566 := by
    simpa [prefixWord, tailWord_4959566, baseEnd_4959566] using wordTrace_append hprefix tailTrace_4959566
  have hstable : (prefixWord ++ tailWord_4959566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959566).length < 2 ^ (prefixWord ++ tailWord_4959566).sum := by decide
  have hdescent : baseEnd_4959566 < baseStart_4959566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959573 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_4959573 : Nat := 118140960795 + 4959573 * 2 ^ 59
def prefixEnd_4959573 : Nat := 4983230072969 + 3 ^ 40 * 4959573 * 2
def baseEnd_4959573 : Nat := 848881596687076460509615

theorem tailTrace_4959573 : CollatzResearch.WordTrace tailWord_4959573 prefixEnd_4959573 848881596687076460509615 := by
  unfold tailWord_4959573
  simp only [CollatzResearch.WordTrace]
  refine ⟨180890488061321523478195373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120593658707547682318796915 180890488061321523478195373)
  ·
    refine ⟨67833933022995571304323265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180890488061321523478195373 67833933022995571304323265)
    ·
      refine ⟨50875449767246678478242449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67833933022995571304323265 50875449767246678478242449)
      ·
        refine ⟨38156587325435008858681837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50875449767246678478242449 38156587325435008858681837)
        ·
          refine ⟨14308720247038128322005689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38156587325435008858681837 14308720247038128322005689)
          ·
            refine ⟨10731540185278596241504267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14308720247038128322005689 10731540185278596241504267)
            ·
              refine ⟨16097310277917894362256401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10731540185278596241504267 16097310277917894362256401)
              ·
                refine ⟨12072982708438420771692301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16097310277917894362256401 12072982708438420771692301)
                ·
                  refine ⟨4527368515664407789384613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12072982708438420771692301 4527368515664407789384613)
                  ·
                    refine ⟨848881596687076460509615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527368515664407789384613 848881596687076460509615)
                    ·
                      rfl

theorem cell23_4959573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_4959573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959573 prefixEnd_4959573 := by exact prefixLift 4959573
  have htrace : WordTrace (prefixWord ++ tailWord_4959573) baseStart_4959573 baseEnd_4959573 := by
    simpa [prefixWord, tailWord_4959573, baseEnd_4959573] using wordTrace_append hprefix tailTrace_4959573
  have hstable : (prefixWord ++ tailWord_4959573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959573).length < 2 ^ (prefixWord ++ tailWord_4959573).sum := by decide
  have hdescent : baseEnd_4959573 < baseStart_4959573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959586 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 8]
def baseStart_4959586 : Nat := 118140960795 + 4959586 * 2 ^ 59
def prefixEnd_4959586 : Nat := 4983230072969 + 3 ^ 40 * 4959586 * 2
def baseEnd_4959586 : Nat := 282961273923304203407365

theorem tailTrace_4959586 : CollatzResearch.WordTrace tailWord_4959586 prefixEnd_4959586 282961273923304203407365 := by
  unfold tailWord_4959586
  simp only [CollatzResearch.WordTrace]
  refine ⟨45222740552568606674604653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120593974806849617798945741 45222740552568606674604653)
  ·
    refine ⟨16958527707213227502976745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45222740552568606674604653 16958527707213227502976745)
    ·
      refine ⟨12718895780409920627232559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16958527707213227502976745 12718895780409920627232559)
      ·
        refine ⟨19078343670614880940848839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12718895780409920627232559 19078343670614880940848839)
        ·
          refine ⟨28617515505922321411273259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19078343670614880940848839 28617515505922321411273259)
          ·
            refine ⟨42926273258883482116909889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28617515505922321411273259 42926273258883482116909889)
            ·
              refine ⟨32194704944162611587682417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42926273258883482116909889 32194704944162611587682417)
              ·
                refine ⟨24146028708121958690761813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32194704944162611587682417 24146028708121958690761813)
                ·
                  refine ⟨282961273923304203407365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24146028708121958690761813 282961273923304203407365)
                  ·
                    rfl

theorem cell23_4959586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_4959586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959586 prefixEnd_4959586 := by exact prefixLift 4959586
  have htrace : WordTrace (prefixWord ++ tailWord_4959586) baseStart_4959586 baseEnd_4959586 := by
    simpa [prefixWord, tailWord_4959586, baseEnd_4959586] using wordTrace_append hprefix tailTrace_4959586
  have hstable : (prefixWord ++ tailWord_4959586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959586).length < 2 ^ (prefixWord ++ tailWord_4959586).sum := by decide
  have hdescent : baseEnd_4959586 < baseStart_4959586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959623 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_4959623 : Nat := 118140960795 + 4959623 * 2 ^ 59
def prefixEnd_4959623 : Nat := 4983230072969 + 3 ^ 40 * 4959623 * 2
def baseEnd_4959623 : Nat := 2546670464093954185903615

theorem tailTrace_4959623 : CollatzResearch.WordTrace tailWord_4959623 prefixEnd_4959623 2546670464093954185903615 := by
  unfold tailWord_4959623
  simp only [CollatzResearch.WordTrace]
  refine ⟨180892311711140382017515523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120594874474093588011677015 180892311711140382017515523)
  ·
    refine ⟨271338467566710573026273285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180892311711140382017515523 271338467566710573026273285)
    ·
      refine ⟨50875962668758232442426241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271338467566710573026273285 50875962668758232442426241)
      ·
        refine ⟨38156972001568674331819681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50875962668758232442426241 38156972001568674331819681)
        ·
          refine ⟨28617729001176505748864761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38156972001568674331819681 28617729001176505748864761)
          ·
            refine ⟨21463296750882379311648571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28617729001176505748864761 21463296750882379311648571)
            ·
              refine ⟨32194945126323568967472857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21463296750882379311648571 32194945126323568967472857)
              ·
                refine ⟨24146208844742676725604643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32194945126323568967472857 24146208844742676725604643)
                ·
                  refine ⟨36219313267114015088406965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24146208844742676725604643 36219313267114015088406965)
                  ·
                    refine ⟨3395560618791938914538153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36219313267114015088406965 3395560618791938914538153)
                    ·
                      refine ⟨2546670464093954185903615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395560618791938914538153 2546670464093954185903615)
                      ·
                        rfl

theorem cell23_4959623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_4959623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959623 prefixEnd_4959623 := by exact prefixLift 4959623
  have htrace : WordTrace (prefixWord ++ tailWord_4959623) baseStart_4959623 baseEnd_4959623 := by
    simpa [prefixWord, tailWord_4959623, baseEnd_4959623] using wordTrace_append hprefix tailTrace_4959623
  have hstable : (prefixWord ++ tailWord_4959623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959623).length < 2 ^ (prefixWord ++ tailWord_4959623).sum := by decide
  have hdescent : baseEnd_4959623 < baseStart_4959623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959647 : List Nat := [1, 1, 2, 5, 1, 2, 3, 3, 1, 1, 3]
def baseStart_4959647 : Nat := 118140960795 + 4959647 * 2 ^ 59
def prefixEnd_4959647 : Nat := 4983230072969 + 3 ^ 40 * 4959647 * 2
def baseEnd_4959647 : Nat := 2546682787629662092003505

theorem tailTrace_4959647 : CollatzResearch.WordTrace tailWord_4959647 prefixEnd_4959647 2546682787629662092003505 := by
  unfold tailWord_4959647
  simp only [CollatzResearch.WordTrace]
  refine ⟨180893187063053434116389195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120595458042035622744259463 180893187063053434116389195)
  ·
    refine ⟨271339780594580151174583793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180893187063053434116389195 271339780594580151174583793)
    ·
      refine ⟨203504835445935113380937845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271339780594580151174583793 203504835445935113380937845)
      ·
        refine ⟨19078578323056416879462923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203504835445935113380937845 19078578323056416879462923)
        ·
          refine ⟨28617867484584625319194385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19078578323056416879462923 28617867484584625319194385)
          ·
            refine ⟨21463400613438468989395789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28617867484584625319194385 21463400613438468989395789)
            ·
              refine ⟨8048775230039425871023421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21463400613438468989395789 8048775230039425871023421)
              ·
                refine ⟨3018290711264784701633783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8048775230039425871023421 3018290711264784701633783)
                ·
                  refine ⟨4527436066897177052450675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3018290711264784701633783 4527436066897177052450675)
                  ·
                    refine ⟨6791154100345765578676013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4527436066897177052450675 6791154100345765578676013)
                    ·
                      refine ⟨2546682787629662092003505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6791154100345765578676013 2546682787629662092003505)
                      ·
                        rfl

theorem cell23_4959647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_4959647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959647 prefixEnd_4959647 := by exact prefixLift 4959647
  have htrace : WordTrace (prefixWord ++ tailWord_4959647) baseStart_4959647 baseEnd_4959647 := by
    simpa [prefixWord, tailWord_4959647, baseEnd_4959647] using wordTrace_append hprefix tailTrace_4959647
  have hstable : (prefixWord ++ tailWord_4959647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959647).length < 2 ^ (prefixWord ++ tailWord_4959647).sum := by decide
  have hdescent : baseEnd_4959647 < baseStart_4959647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959666 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_4959666 : Nat := 118140960795 + 4959666 * 2 ^ 59
def prefixEnd_4959666 : Nat := 4983230072969 + 3 ^ 40 * 4959666 * 2
def baseEnd_4959666 : Nat := 2546692543762097517665917

theorem tailTrace_4959666 : CollatzResearch.WordTrace tailWord_4959666 prefixEnd_4959666 2546692543762097517665917 := by
  unfold tailWord_4959666
  simp only [CollatzResearch.WordTrace]
  refine ⟨45223470012496150090332713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120595920033323066907553901 45223470012496150090332713)
  ·
    refine ⟨33917602509372112567749535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45223470012496150090332713 33917602509372112567749535)
    ·
      refine ⟨50876403764058168851624303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33917602509372112567749535 50876403764058168851624303)
      ·
        refine ⟨76314605646087253277436455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50876403764058168851624303 76314605646087253277436455)
        ·
          refine ⟨114471908469130879916154683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76314605646087253277436455 114471908469130879916154683)
          ·
            refine ⟨171707862703696319874232025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114471908469130879916154683 171707862703696319874232025)
            ·
              refine ⟨128780897027772239905674019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171707862703696319874232025 128780897027772239905674019)
              ·
                refine ⟨193171345541658359858511029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128780897027772239905674019 193171345541658359858511029)
                ·
                  refine ⟨18109813644530471236735409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193171345541658359858511029 18109813644530471236735409)
                  ·
                    refine ⟨13582360233397853427551557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18109813644530471236735409 13582360233397853427551557)
                    ·
                      refine ⟨2546692543762097517665917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13582360233397853427551557 2546692543762097517665917)
                      ·
                        rfl

theorem cell23_4959666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_4959666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959666 prefixEnd_4959666 := by exact prefixLift 4959666
  have htrace : WordTrace (prefixWord ++ tailWord_4959666) baseStart_4959666 baseEnd_4959666 := by
    simpa [prefixWord, tailWord_4959666, baseEnd_4959666] using wordTrace_append hprefix tailTrace_4959666
  have hstable : (prefixWord ++ tailWord_4959666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959666).length < 2 ^ (prefixWord ++ tailWord_4959666).sum := by decide
  have hdescent : baseEnd_4959666 < baseStart_4959666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959680 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 2, 4]
def baseStart_4959680 : Nat := 118140960795 + 4959680 * 2 ^ 59
def prefixEnd_4959680 : Nat := 4983230072969 + 3 ^ 40 * 4959680 * 2
def baseEnd_4959680 : Nat := 848899910830420154296951

theorem tailTrace_4959680 : CollatzResearch.WordTrace tailWord_4959680 prefixEnd_4959680 848899910830420154296951 := by
  unfold tailWord_4959680
  simp only [CollatzResearch.WordTrace]
  refine ⟨90447195335966940376170247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120596260447955920501560329 90447195335966940376170247)
  ·
    refine ⟨135670793003950410564255371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90447195335966940376170247 135670793003950410564255371)
    ·
      refine ⟨203506189505925615846383057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135670793003950410564255371 203506189505925615846383057)
      ·
        refine ⟨152629642129444211884787293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203506189505925615846383057 152629642129444211884787293)
        ·
          refine ⟨57236115798541579456795235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152629642129444211884787293 57236115798541579456795235)
          ·
            refine ⟨85854173697812369185192853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57236115798541579456795235 85854173697812369185192853)
            ·
              refine ⟨4024414392084954805555915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85854173697812369185192853 4024414392084954805555915)
              ·
                refine ⟨6036621588127432208333873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024414392084954805555915 6036621588127432208333873)
                ·
                  refine ⟨4527466191095574156250405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6036621588127432208333873 4527466191095574156250405)
                  ·
                    refine ⟨848899910830420154296951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527466191095574156250405 848899910830420154296951)
                    ·
                      rfl

theorem cell23_4959680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 2, 4].length) (baseStart_4959680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959680 prefixEnd_4959680 := by exact prefixLift 4959680
  have htrace : WordTrace (prefixWord ++ tailWord_4959680) baseStart_4959680 baseEnd_4959680 := by
    simpa [prefixWord, tailWord_4959680, baseEnd_4959680] using wordTrace_append hprefix tailTrace_4959680
  have hstable : (prefixWord ++ tailWord_4959680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959680).length < 2 ^ (prefixWord ++ tailWord_4959680).sum := by decide
  have hdescent : baseEnd_4959680 < baseStart_4959680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959690 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_4959690 : Nat := 118140960795 + 4959690 * 2 ^ 59
def prefixEnd_4959690 : Nat := 4983230072969 + 3 ^ 40 * 4959690 * 2
def baseEnd_4959690 : Nat := 2546704867297805423765807

theorem tailTrace_4959690 : CollatzResearch.WordTrace tailWord_4959690 prefixEnd_4959690 2546704867297805423765807 := by
  unfold tailWord_4959690
  simp only [CollatzResearch.WordTrace]
  refine ⟨45223688850474413115051131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120596503601265101640136349 45223688850474413115051131)
  ·
    refine ⟨67835533275711619672576697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45223688850474413115051131 67835533275711619672576697)
    ·
      refine ⟨50876649956783714754432523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67835533275711619672576697 50876649956783714754432523)
      ·
        refine ⟨76314974935175572131648785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50876649956783714754432523 76314974935175572131648785)
        ·
          refine ⟨57236231201381679098736589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76314974935175572131648785 57236231201381679098736589)
          ·
            refine ⟨21463586700518129662026221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57236231201381679098736589 21463586700518129662026221)
            ·
              refine ⟨8048845012694298623259833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21463586700518129662026221 8048845012694298623259833)
              ·
                refine ⟨6036633759520723967444875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8048845012694298623259833 6036633759520723967444875)
                ·
                  refine ⟨9054950639281085951167313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6036633759520723967444875 9054950639281085951167313)
                  ·
                    refine ⟨6791212979460814463375485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9054950639281085951167313 6791212979460814463375485)
                    ·
                      refine ⟨2546704867297805423765807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6791212979460814463375485 2546704867297805423765807)
                      ·
                        rfl

theorem cell23_4959690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_4959690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959690 prefixEnd_4959690 := by exact prefixLift 4959690
  have htrace : WordTrace (prefixWord ++ tailWord_4959690) baseStart_4959690 baseEnd_4959690 := by
    simpa [prefixWord, tailWord_4959690, baseEnd_4959690] using wordTrace_append hprefix tailTrace_4959690
  have hstable : (prefixWord ++ tailWord_4959690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959690).length < 2 ^ (prefixWord ++ tailWord_4959690).sum := by decide
  have hdescent : baseEnd_4959690 < baseStart_4959690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959700 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_4959700 : Nat := 118140960795 + 4959700 * 2 ^ 59
def prefixEnd_4959700 : Nat := 4983230072969 + 3 ^ 40 * 4959700 * 2
def baseEnd_4959700 : Nat := 2546710002104350384640761

theorem tailTrace_4959700 : CollatzResearch.WordTrace tailWord_4959700 prefixEnd_4959700 2546710002104350384640761 := by
  unfold tailWord_4959700
  simp only [CollatzResearch.WordTrace]
  refine ⟨90447560065930712084034277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120596746754574282778712369 90447560065930712084034277)
  ·
    refine ⟨16958917512362008515756427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90447560065930712084034277 16958917512362008515756427)
    ·
      refine ⟨25438376268543012773634641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16958917512362008515756427 25438376268543012773634641)
      ·
        refine ⟨19078782201407259580225981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25438376268543012773634641 19078782201407259580225981)
        ·
          refine ⟨7154543325527722342584743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19078782201407259580225981 7154543325527722342584743)
          ·
            refine ⟨10731814988291583513877115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154543325527722342584743 10731814988291583513877115)
            ·
              refine ⟨16097722482437375270815673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10731814988291583513877115 16097722482437375270815673)
              ·
                refine ⟨12073291861828031453111755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16097722482437375270815673 12073291861828031453111755)
                ·
                  refine ⟨18109937792742047179667633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12073291861828031453111755 18109937792742047179667633)
                  ·
                    refine ⟨13582453344556535384750725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18109937792742047179667633 13582453344556535384750725)
                    ·
                      refine ⟨2546710002104350384640761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13582453344556535384750725 2546710002104350384640761)
                      ·
                        rfl

theorem cell23_4959700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_4959700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959700 prefixEnd_4959700 := by exact prefixLift 4959700
  have htrace : WordTrace (prefixWord ++ tailWord_4959700) baseStart_4959700 baseEnd_4959700 := by
    simpa [prefixWord, tailWord_4959700, baseEnd_4959700] using wordTrace_append hprefix tailTrace_4959700
  have hstable : (prefixWord ++ tailWord_4959700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959700).length < 2 ^ (prefixWord ++ tailWord_4959700).sum := by decide
  have hdescent : baseEnd_4959700 < baseStart_4959700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959703 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_4959703 : Nat := 118140960795 + 4959703 * 2 ^ 59
def prefixEnd_4959703 : Nat := 4983230072969 + 3 ^ 40 * 4959703 * 2
def baseEnd_4959703 : Nat := 2546711542546313872903247

theorem tailTrace_4959703 : CollatzResearch.WordTrace tailWord_4959703 prefixEnd_4959703 2546711542546313872903247 := by
  unfold tailWord_4959703
  simp only [CollatzResearch.WordTrace]
  refine ⟨180895229550850555680427763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120596819700567037120285175 180895229550850555680427763)
  ·
    refine ⟨271342844326275833520641645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180895229550850555680427763 271342844326275833520641645)
    ·
      refine ⟨101753566622353437570240617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271342844326275833520641645 101753566622353437570240617)
      ·
        refine ⟨76315174966765078177680463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101753566622353437570240617 76315174966765078177680463)
        ·
          refine ⟨114472762450147617266520695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76315174966765078177680463 114472762450147617266520695)
          ·
            refine ⟨171709143675221425899781043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114472762450147617266520695 171709143675221425899781043)
            ·
              refine ⟨257563715512832138849671565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171709143675221425899781043 257563715512832138849671565)
              ·
                refine ⟨96586393317312052068626837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257563715512832138849671565 96586393317312052068626837)
                ·
                  refine ⟨4527487186749002440716883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96586393317312052068626837 4527487186749002440716883)
                  ·
                    refine ⟨6791230780123503661075325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4527487186749002440716883 6791230780123503661075325)
                    ·
                      refine ⟨2546711542546313872903247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6791230780123503661075325 2546711542546313872903247)
                      ·
                        rfl

theorem cell23_4959703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_4959703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959703 prefixEnd_4959703 := by exact prefixLift 4959703
  have htrace : WordTrace (prefixWord ++ tailWord_4959703) baseStart_4959703 baseEnd_4959703 := by
    simpa [prefixWord, tailWord_4959703, baseEnd_4959703] using wordTrace_append hprefix tailTrace_4959703
  have hstable : (prefixWord ++ tailWord_4959703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959703).length < 2 ^ (prefixWord ++ tailWord_4959703).sum := by decide
  have hdescent : baseEnd_4959703 < baseStart_4959703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959716 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_4959716 : Nat := 118140960795 + 4959716 * 2 ^ 59
def prefixEnd_4959716 : Nat := 4983230072969 + 3 ^ 40 * 4959716 * 2
def baseEnd_4959716 : Nat := 2546718217794822322040687

theorem tailTrace_4959716 : CollatzResearch.WordTrace tailWord_4959716 prefixEnd_4959716 2546718217794822322040687 := by
  unfold tailWord_4959716
  simp only [CollatzResearch.WordTrace]
  refine ⟨90447851849901729450325501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120597135799868972600434001 90447851849901729450325501)
  ·
    refine ⟨33917944443713148543872063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90447851849901729450325501 33917944443713148543872063)
    ·
      refine ⟨50876916665569722815808095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33917944443713148543872063 50876916665569722815808095)
      ·
        refine ⟨76315374998354584223712143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50876916665569722815808095 76315374998354584223712143)
        ·
          refine ⟨114473062497531876335568215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76315374998354584223712143 114473062497531876335568215)
          ·
            refine ⟨171709593746297814503352323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114473062497531876335568215 171709593746297814503352323)
            ·
              refine ⟨257564390619446721755028485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171709593746297814503352323 257564390619446721755028485)
              ·
                refine ⟨48293323241146260329067841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257564390619446721755028485 48293323241146260329067841)
                ·
                  refine ⟨36219992430859695246800881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48293323241146260329067841 36219992430859695246800881)
                  ·
                    refine ⟨27164994323144771435100661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36219992430859695246800881 27164994323144771435100661)
                    ·
                      refine ⟨2546718217794822322040687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27164994323144771435100661 2546718217794822322040687)
                      ·
                        rfl

theorem cell23_4959716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_4959716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959716 prefixEnd_4959716 := by exact prefixLift 4959716
  have htrace : WordTrace (prefixWord ++ tailWord_4959716) baseStart_4959716 baseEnd_4959716 := by
    simpa [prefixWord, tailWord_4959716, baseEnd_4959716] using wordTrace_append hprefix tailTrace_4959716
  have hstable : (prefixWord ++ tailWord_4959716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959716).length < 2 ^ (prefixWord ++ tailWord_4959716).sum := by decide
  have hdescent : baseEnd_4959716 < baseStart_4959716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959736 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 1, 8]
def baseStart_4959736 : Nat := 118140960795 + 4959736 * 2 ^ 59
def prefixEnd_4959736 : Nat := 4983230072969 + 3 ^ 40 * 4959736 * 2
def baseEnd_4959736 : Nat := 848909495802637414596865

theorem tailTrace_4959736 : CollatzResearch.WordTrace tailWord_4959736 prefixEnd_4959736 848909495802637414596865 := by
  unfold tailWord_4959736
  simp only [CollatzResearch.WordTrace]
  refine ⟨90448216579865501158189531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120597622106487334877586041 90448216579865501158189531)
  ·
    refine ⟨135672324869798251737284297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90448216579865501158189531 135672324869798251737284297)
    ·
      refine ⟨101754243652348688802963223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135672324869798251737284297 101754243652348688802963223)
      ·
        refine ⟨152631365478523033204444835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101754243652348688802963223 152631365478523033204444835)
        ·
          refine ⟨228947048217784549806667253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152631365478523033204444835 228947048217784549806667253)
          ·
            refine ⟨21463785770417301544375055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228947048217784549806667253 21463785770417301544375055)
            ·
              refine ⟨32195678655625952316562583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21463785770417301544375055 32195678655625952316562583)
              ·
                refine ⟨48293517983438928474843875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32195678655625952316562583 48293517983438928474843875)
                ·
                  refine ⟨72440276975158392712265813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48293517983438928474843875 72440276975158392712265813)
                  ·
                    refine ⟨848909495802637414596865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72440276975158392712265813 848909495802637414596865)
                    ·
                      rfl

theorem cell23_4959736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_4959736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959736 prefixEnd_4959736 := by exact prefixLift 4959736
  have htrace : WordTrace (prefixWord ++ tailWord_4959736) baseStart_4959736 baseEnd_4959736 := by
    simpa [prefixWord, tailWord_4959736, baseEnd_4959736] using wordTrace_append hprefix tailTrace_4959736
  have hstable : (prefixWord ++ tailWord_4959736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959736).length < 2 ^ (prefixWord ++ tailWord_4959736).sum := by decide
  have hdescent : baseEnd_4959736 < baseStart_4959736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959773 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4959773 : Nat := 118140960795 + 4959773 * 2 ^ 59
def prefixEnd_4959773 : Nat := 4983230072969 + 3 ^ 40 * 4959773 * 2
def baseEnd_4959773 : Nat := 2546747486192128599027925

theorem tailTrace_4959773 : CollatzResearch.WordTrace tailWord_4959773 prefixEnd_4959773 2546747486192128599027925 := by
  unfold tailWord_4959773
  simp only [CollatzResearch.WordTrace]
  refine ⟨180897782660596957635475973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120598521773731305090317315 180897782660596957635475973)
  ·
    refine ⟨33918334248861929556651745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180897782660596957635475973 33918334248861929556651745)
    ·
      refine ⟨25438750686646447167488809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33918334248861929556651745 25438750686646447167488809)
      ·
        refine ⟨19079063014984835375616607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25438750686646447167488809 19079063014984835375616607)
        ·
          refine ⟨28618594522477253063424911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19079063014984835375616607 28618594522477253063424911)
          ·
            refine ⟨42927891783715879595137367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28618594522477253063424911 42927891783715879595137367)
            ·
              refine ⟨64391837675573819392706051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42927891783715879595137367 64391837675573819392706051)
              ·
                refine ⟨96587756513360729089059077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64391837675573819392706051 96587756513360729089059077)
                ·
                  refine ⟨18110204346255136704198577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96587756513360729089059077 18110204346255136704198577)
                  ·
                    refine ⟨13582653259691352528148933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18110204346255136704198577 13582653259691352528148933)
                    ·
                      refine ⟨2546747486192128599027925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13582653259691352528148933 2546747486192128599027925)
                      ·
                        rfl

theorem cell23_4959773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4959773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959773 prefixEnd_4959773 := by exact prefixLift 4959773
  have htrace : WordTrace (prefixWord ++ tailWord_4959773) baseStart_4959773 baseEnd_4959773 := by
    simpa [prefixWord, tailWord_4959773, baseEnd_4959773] using wordTrace_append hprefix tailTrace_4959773
  have hstable : (prefixWord ++ tailWord_4959773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959773).length < 2 ^ (prefixWord ++ tailWord_4959773).sum := by decide
  have hdescent : baseEnd_4959773 < baseStart_4959773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959777 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_4959777 : Nat := 118140960795 + 4959777 * 2 ^ 59
def prefixEnd_4959777 : Nat := 4983230072969 + 3 ^ 40 * 4959777 * 2
def baseEnd_4959777 : Nat := 2546749540114746583377907

theorem tailTrace_4959777 : CollatzResearch.WordTrace tailWord_4959777 prefixEnd_4959777 2546749540114746583377907 := by
  unfold tailWord_4959777
  simp only [CollatzResearch.WordTrace]
  refine ⟨180897928552582466318621585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120598619035054977545747723 180897928552582466318621585)
  ·
    refine ⟨135673446414436849738966189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180897928552582466318621585 135673446414436849738966189)
    ·
      refine ⟨50877542405413818652112321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135673446414436849738966189 50877542405413818652112321)
      ·
        refine ⟨38158156804060363989084241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50877542405413818652112321 38158156804060363989084241)
        ·
          refine ⟨28618617603045272991813181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38158156804060363989084241 28618617603045272991813181)
          ·
            refine ⟨10731981601141977371929943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28618617603045272991813181 10731981601141977371929943)
            ·
              refine ⟨16097972401712966057894915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10731981601141977371929943 16097972401712966057894915)
              ·
                refine ⟨24146958602569449086842373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16097972401712966057894915 24146958602569449086842373)
                ·
                  refine ⟨4527554737981771703782945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24146958602569449086842373 4527554737981771703782945)
                  ·
                    refine ⟨3395666053486328777837209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4527554737981771703782945 3395666053486328777837209)
                    ·
                      refine ⟨2546749540114746583377907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395666053486328777837209 2546749540114746583377907)
                      ·
                        rfl

theorem cell23_4959777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_4959777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959777 prefixEnd_4959777 := by exact prefixLift 4959777
  have htrace : WordTrace (prefixWord ++ tailWord_4959777) baseStart_4959777 baseEnd_4959777 := by
    simpa [prefixWord, tailWord_4959777, baseEnd_4959777] using wordTrace_append hprefix tailTrace_4959777
  have hstable : (prefixWord ++ tailWord_4959777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959777).length < 2 ^ (prefixWord ++ tailWord_4959777).sum := by decide
  have hdescent : baseEnd_4959777 < baseStart_4959777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959790 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_4959790 : Nat := 118140960795 + 4959790 * 2 ^ 59
def prefixEnd_4959790 : Nat := 4983230072969 + 3 ^ 40 * 4959790 * 2
def baseEnd_4959790 : Nat := 2546756215363255032515347

theorem tailTrace_4959790 : CollatzResearch.WordTrace tailWord_4959790 prefixEnd_4959790 2546756215363255032515347 := by
  unfold tailWord_4959790
  simp only [CollatzResearch.WordTrace]
  refine ⟨22612300337691921192355603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120598935134356913025896549 22612300337691921192355603)
  ·
    refine ⟨33918450506537881788533405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22612300337691921192355603 33918450506537881788533405)
    ·
      refine ⟨12719418939951705670700027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33918450506537881788533405 12719418939951705670700027)
      ·
        refine ⟨19079128409927558506050041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12719418939951705670700027 19079128409927558506050041)
        ·
          refine ⟨14309346307445668879537531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19079128409927558506050041 14309346307445668879537531)
          ·
            refine ⟨21464019461168503319306297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14309346307445668879537531 21464019461168503319306297)
            ·
              refine ⟨16098014595876377489479723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21464019461168503319306297 16098014595876377489479723)
              ·
                refine ⟨24147021893814566234219585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16098014595876377489479723 24147021893814566234219585)
                ·
                  refine ⟨18110266420360924675664689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24147021893814566234219585 18110266420360924675664689)
                  ·
                    refine ⟨13582699815270693506748517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18110266420360924675664689 13582699815270693506748517)
                    ·
                      refine ⟨2546756215363255032515347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13582699815270693506748517 2546756215363255032515347)
                      ·
                        rfl

theorem cell23_4959790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_4959790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959790 prefixEnd_4959790 := by exact prefixLift 4959790
  have htrace : WordTrace (prefixWord ++ tailWord_4959790) baseStart_4959790 baseEnd_4959790 := by
    simpa [prefixWord, tailWord_4959790, baseEnd_4959790] using wordTrace_append hprefix tailTrace_4959790
  have hstable : (prefixWord ++ tailWord_4959790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959790).length < 2 ^ (prefixWord ++ tailWord_4959790).sum := by decide
  have hdescent : baseEnd_4959790 < baseStart_4959790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959813 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_4959813 : Nat := 118140960795 + 4959813 * 2 ^ 59
def prefixEnd_4959813 : Nat := 4983230072969 + 3 ^ 40 * 4959813 * 2
def baseEnd_4959813 : Nat := 848922675139436147509247

theorem tailTrace_4959813 : CollatzResearch.WordTrace tailWord_4959813 prefixEnd_4959813 848922675139436147509247 := by
  unfold tailWord_4959813
  simp only [CollatzResearch.WordTrace]
  refine ⟨180899241580452044466932093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120599494386968029644621395 180899241580452044466932093)
  ·
    refine ⟨67837215592669516675099535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180899241580452044466932093 67837215592669516675099535)
    ·
      refine ⟨101755823389004275012649303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67837215592669516675099535 101755823389004275012649303)
      ·
        refine ⟨152633735083506412518973955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101755823389004275012649303 152633735083506412518973955)
        ·
          refine ⟨228950602625259618778460933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152633735083506412518973955 228950602625259618778460933)
          ·
            refine ⟨42928237992236178520961425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228950602625259618778460933 42928237992236178520961425)
            ·
              refine ⟨32196178494177133890721069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42928237992236178520961425 32196178494177133890721069)
              ·
                refine ⟨12073566935316425209020401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32196178494177133890721069 12073566935316425209020401)
                ·
                  refine ⟨9055175201487318906765301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12073566935316425209020401 9055175201487318906765301)
                  ·
                    refine ⟨848922675139436147509247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9055175201487318906765301 848922675139436147509247)
                    ·
                      rfl

theorem cell23_4959813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_4959813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959813 prefixEnd_4959813 := by exact prefixLift 4959813
  have htrace : WordTrace (prefixWord ++ tailWord_4959813) baseStart_4959813 baseEnd_4959813 := by
    simpa [prefixWord, tailWord_4959813, baseEnd_4959813] using wordTrace_append hprefix tailTrace_4959813
  have hstable : (prefixWord ++ tailWord_4959813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959813).length < 2 ^ (prefixWord ++ tailWord_4959813).sum := by decide
  have hdescent : baseEnd_4959813 < baseStart_4959813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959877 : List Nat := [1, 3, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_4959877 : Nat := 118140960795 + 4959877 * 2 ^ 59
def prefixEnd_4959877 : Nat := 4983230072969 + 3 ^ 40 * 4959877 * 2
def baseEnd_4959877 : Nat := 848933629393398730709149

theorem tailTrace_4959877 : CollatzResearch.WordTrace tailWord_4959877 prefixEnd_4959877 848933629393398730709149 := by
  unfold tailWord_4959877
  simp only [CollatzResearch.WordTrace]
  refine ⟨180901575852220183397261885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120601050568146788931507923 180901575852220183397261885)
  ·
    refine ⟨67838090944582568773973207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180901575852220183397261885 67838090944582568773973207)
    ·
      refine ⟨101757136416873853160959811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67838090944582568773973207 101757136416873853160959811)
      ·
        refine ⟨152635704625310779741439717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101757136416873853160959811 152635704625310779741439717)
        ·
          refine ⟨28619194617245771201519947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152635704625310779741439717 28619194617245771201519947)
          ·
            refine ⟨42928791925868656802279921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28619194617245771201519947 42928791925868656802279921)
            ·
              refine ⟨32196593944401492601709941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42928791925868656802279921 32196593944401492601709941)
              ·
                refine ⟨3018430682287639931410307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32196593944401492601709941 3018430682287639931410307)
                ·
                  refine ⟨4527646023431459897115461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3018430682287639931410307 4527646023431459897115461)
                  ·
                    refine ⟨848933629393398730709149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527646023431459897115461 848933629393398730709149)
                    ·
                      rfl

theorem cell23_4959877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_4959877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959877 prefixEnd_4959877 := by exact prefixLift 4959877
  have htrace : WordTrace (prefixWord ++ tailWord_4959877) baseStart_4959877 baseEnd_4959877 := by
    simpa [prefixWord, tailWord_4959877, baseEnd_4959877] using wordTrace_append hprefix tailTrace_4959877
  have hstable : (prefixWord ++ tailWord_4959877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959877).length < 2 ^ (prefixWord ++ tailWord_4959877).sum := by decide
  have hdescent : baseEnd_4959877 < baseStart_4959877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959927 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 1, 5, 2]
def baseStart_4959927 : Nat := 118140960795 + 4959927 * 2 ^ 59
def prefixEnd_4959927 : Nat := 4983230072969 + 3 ^ 40 * 4959927 * 2
def baseEnd_4959927 : Nat := 2546826562212920996502217

theorem tailTrace_4959927 : CollatzResearch.WordTrace tailWord_4959927 prefixEnd_4959927 2546826562212920996502217 := by
  unfold tailWord_4959927
  simp only [CollatzResearch.WordTrace]
  refine ⟨180903399502039041936582035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120602266334692694624388023 180903399502039041936582035)
  ·
    refine ⟨271355099253058562904873053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180903399502039041936582035 271355099253058562904873053)
    ·
      refine ⟨101758162219896961089327395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271355099253058562904873053 101758162219896961089327395)
      ·
        refine ⟨152637243329845441633991093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101758162219896961089327395 152637243329845441633991093)
        ·
          refine ⟨14309741562173010153186665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152637243329845441633991093 14309741562173010153186665)
          ·
            refine ⟨10732306171629757614889999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14309741562173010153186665 10732306171629757614889999)
            ·
              refine ⟨16098459257444636422334999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10732306171629757614889999 16098459257444636422334999)
              ·
                refine ⟨24147688886166954633502499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16098459257444636422334999 24147688886166954633502499)
                ·
                  refine ⟨36221533329250431950253749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24147688886166954633502499 36221533329250431950253749)
                  ·
                    refine ⟨3395768749617227995336289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36221533329250431950253749 3395768749617227995336289)
                    ·
                      refine ⟨2546826562212920996502217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395768749617227995336289 2546826562212920996502217)
                      ·
                        rfl

theorem cell23_4959927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_4959927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959927 prefixEnd_4959927 := by exact prefixLift 4959927
  have htrace : WordTrace (prefixWord ++ tailWord_4959927) baseStart_4959927 baseEnd_4959927 := by
    simpa [prefixWord, tailWord_4959927, baseEnd_4959927] using wordTrace_append hprefix tailTrace_4959927
  have hstable : (prefixWord ++ tailWord_4959927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959927).length < 2 ^ (prefixWord ++ tailWord_4959927).sum := by decide
  have hdescent : baseEnd_4959927 < baseStart_4959927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959960 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_4959960 : Nat := 118140960795 + 4959960 * 2 ^ 59
def prefixEnd_4959960 : Nat := 4983230072969 + 3 ^ 40 * 4959960 * 2
def baseEnd_4959960 : Nat := 2546843507074519367389565

theorem tailTrace_4959960 : CollatzResearch.WordTrace tailWord_4959960 prefixEnd_4959960 2546843507074519367389565 := by
  unfold tailWord_4959960
  simp only [CollatzResearch.WordTrace]
  refine ⟨90452301555459744286266667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120603068740612992381688889 90452301555459744286266667)
  ·
    refine ⟨135678452333189616429400001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90452301555459744286266667 135678452333189616429400001)
    ·
      refine ⟨101758839249892212322050001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135678452333189616429400001 101758839249892212322050001)
      ·
        refine ⟨76319129437419159241537501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101758839249892212322050001 76319129437419159241537501)
        ·
          refine ⟨28619673539032184715576563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76319129437419159241537501 28619673539032184715576563)
          ·
            refine ⟨42929510308548277073364845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28619673539032184715576563 42929510308548277073364845)
            ·
              refine ⟨16098566365705603902511817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42929510308548277073364845 16098566365705603902511817)
              ·
                refine ⟨12073924774279202926883863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16098566365705603902511817 12073924774279202926883863)
                ·
                  refine ⟨18110887161418804390325795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12073924774279202926883863 18110887161418804390325795)
                  ·
                    refine ⟨27166330742128206585488693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18110887161418804390325795 27166330742128206585488693)
                    ·
                      refine ⟨2546843507074519367389565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27166330742128206585488693 2546843507074519367389565)
                      ·
                        rfl

theorem cell23_4959960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_4959960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959960 prefixEnd_4959960 := by exact prefixLift 4959960
  have htrace : WordTrace (prefixWord ++ tailWord_4959960) baseStart_4959960 baseEnd_4959960 := by
    simpa [prefixWord, tailWord_4959960, baseEnd_4959960] using wordTrace_append hprefix tailTrace_4959960
  have hstable : (prefixWord ++ tailWord_4959960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959960).length < 2 ^ (prefixWord ++ tailWord_4959960).sum := by decide
  have hdescent : baseEnd_4959960 < baseStart_4959960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959980 : List Nat := [2, 2, 1, 1, 2, 2, 6, 7]
def baseStart_4959980 : Nat := 118140960795 + 4959980 * 2 ^ 59
def prefixEnd_4959980 : Nat := 4983230072969 + 3 ^ 40 * 4959980 * 2
def baseEnd_4959980 : Nat := 94327917655096640338499

theorem tailTrace_4959980 : CollatzResearch.WordTrace tailWord_4959980 prefixEnd_4959980 94327917655096640338499 := by
  unfold tailWord_4959980
  simp only [CollatzResearch.WordTrace]
  refine ⟨90452666285423515994130697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120603555047231354658840929 90452666285423515994130697)
  ·
    refine ⟨67839499714067636995598023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90452666285423515994130697 67839499714067636995598023)
    ·
      refine ⟨101759249571101455493397035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67839499714067636995598023 101759249571101455493397035)
      ·
        refine ⟨152638874356652183240095553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101759249571101455493397035 152638874356652183240095553)
        ·
          refine ⟨114479155767489137430071665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152638874356652183240095553 114479155767489137430071665)
          ·
            refine ⟨85859366825616853072553749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114479155767489137430071665 85859366825616853072553749)
            ·
              refine ⟨4024657819950789987775957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85859366825616853072553749 4024657819950789987775957)
              ·
                refine ⟨94327917655096640338499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4024657819950789987775957 94327917655096640338499)
                ·
                  rfl

theorem cell23_4959980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 7].length) (baseStart_4959980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959980 prefixEnd_4959980 := by exact prefixLift 4959980
  have htrace : WordTrace (prefixWord ++ tailWord_4959980) baseStart_4959980 baseEnd_4959980 := by
    simpa [prefixWord, tailWord_4959980, baseEnd_4959980] using wordTrace_append hprefix tailTrace_4959980
  have hstable : (prefixWord ++ tailWord_4959980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959980).length < 2 ^ (prefixWord ++ tailWord_4959980).sum := by decide
  have hdescent : baseEnd_4959980 < baseStart_4959980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959991 : List Nat := [1, 1, 3, 1, 1, 1, 7, 3, 1, 2, 2]
def baseStart_4959991 : Nat := 118140960795 + 4959991 * 2 ^ 59
def prefixEnd_4959991 : Nat := 4983230072969 + 3 ^ 40 * 4959991 * 2
def baseEnd_4959991 : Nat := 2546859424974808746101923

theorem tailTrace_4959991 : CollatzResearch.WordTrace tailWord_4959991 prefixEnd_4959991 2546859424974808746101923 := by
  unfold tailWord_4959991
  simp only [CollatzResearch.WordTrace]
  refine ⟨180905733773807180866911827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120603822515871453911274551 180905733773807180866911827)
  ·
    refine ⟨271358600660710771300367741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180905733773807180866911827 271358600660710771300367741)
    ·
      refine ⟨101759475247766539237637903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271358600660710771300367741 101759475247766539237637903)
      ·
        refine ⟨152639212871649808856456855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101759475247766539237637903 152639212871649808856456855)
        ·
          refine ⟨228958819307474713284685283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152639212871649808856456855 228958819307474713284685283)
          ·
            refine ⟨343438228961212069927027925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228958819307474713284685283 343438228961212069927027925)
            ·
              refine ⟨8049333491278407888914717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 343438228961212069927027925 8049333491278407888914717)
              ·
                refine ⟨3018500059229402958343019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8049333491278407888914717 3018500059229402958343019)
                ·
                  refine ⟨4527750088844104437514529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3018500059229402958343019 4527750088844104437514529)
                  ·
                    refine ⟨3395812566633078328135897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4527750088844104437514529 3395812566633078328135897)
                    ·
                      refine ⟨2546859424974808746101923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395812566633078328135897 2546859424974808746101923)
                      ·
                        rfl

theorem cell23_4959991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_4959991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959991 prefixEnd_4959991 := by exact prefixLift 4959991
  have htrace : WordTrace (prefixWord ++ tailWord_4959991) baseStart_4959991 baseEnd_4959991 := by
    simpa [prefixWord, tailWord_4959991, baseEnd_4959991] using wordTrace_append hprefix tailTrace_4959991
  have hstable : (prefixWord ++ tailWord_4959991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959991).length < 2 ^ (prefixWord ++ tailWord_4959991).sum := by decide
  have hdescent : baseEnd_4959991 < baseStart_4959991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4959993 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 3, 9]
def baseStart_4959993 : Nat := 118140960795 + 4959993 * 2 ^ 59
def prefixEnd_4959993 : Nat := 4983230072969 + 3 ^ 40 * 4959993 * 2
def baseEnd_4959993 : Nat := 848953483978705912758971

theorem tailTrace_4959993 : CollatzResearch.WordTrace tailWord_4959993 prefixEnd_4959993 848953483978705912758971 := by
  unfold tailWord_4959993
  simp only [CollatzResearch.WordTrace]
  refine ⟨180905806719799935208484633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120603871146533290138989755 180905806719799935208484633)
  ·
    refine ⟨135679355039849951406363475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180905806719799935208484633 135679355039849951406363475)
    ·
      refine ⟨203519032559774927109545213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135679355039849951406363475 203519032559774927109545213)
      ·
        refine ⟨76319637209915597666079455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203519032559774927109545213 76319637209915597666079455)
        ·
          refine ⟨114479455814873396499119183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76319637209915597666079455 114479455814873396499119183)
          ·
            refine ⟨171719183722310094748678775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114479455814873396499119183 171719183722310094748678775)
            ·
              refine ⟨257578775583465142123018163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171719183722310094748678775 257578775583465142123018163)
              ·
                refine ⟨386368163375197713184527245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257578775583465142123018163 386368163375197713184527245)
                ·
                  refine ⟨144888061265699142444197717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386368163375197713184527245 144888061265699142444197717)
                  ·
                    refine ⟨848953483978705912758971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 144888061265699142444197717 848953483978705912758971)
                    ·
                      rfl

theorem cell23_4959993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_4959993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4959993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4959993 prefixEnd_4959993 := by exact prefixLift 4959993
  have htrace : WordTrace (prefixWord ++ tailWord_4959993) baseStart_4959993 baseEnd_4959993 := by
    simpa [prefixWord, tailWord_4959993, baseEnd_4959993] using wordTrace_append hprefix tailTrace_4959993
  have hstable : (prefixWord ++ tailWord_4959993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4959993).length < 2 ^ (prefixWord ++ tailWord_4959993).sum := by decide
  have hdescent : baseEnd_4959993 < baseStart_4959993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4959993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960008 : List Nat := [2, 1, 3, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_4960008 : Nat := 118140960795 + 4960008 * 2 ^ 59
def prefixEnd_4960008 : Nat := 4983230072969 + 3 ^ 40 * 4960008 * 2
def baseEnd_4960008 : Nat := 2546868154145935179589345

theorem tailTrace_4960008 : CollatzResearch.WordTrace tailWord_4960008 prefixEnd_4960008 2546868154145935179589345 := by
  unfold tailWord_4960008
  simp only [CollatzResearch.WordTrace]
  refine ⟨90453176907372796385140339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120604235876497061846853785 90453176907372796385140339)
  ·
    refine ⟨135679765361059194577710509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90453176907372796385140339 135679765361059194577710509)
    ·
      refine ⟨50879912010397197966641441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135679765361059194577710509 50879912010397197966641441)
      ·
        refine ⟨38159934007797898474981081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50879912010397197966641441 38159934007797898474981081)
        ·
          refine ⟨28619950505848423856235811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38159934007797898474981081 28619950505848423856235811)
          ·
            refine ⟨42929925758772635784353717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28619950505848423856235811 42929925758772635784353717)
            ·
              refine ⟨4024680539884934604783161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42929925758772635784353717 4024680539884934604783161)
              ·
                refine ⟨3018510404913700953587371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4024680539884934604783161 3018510404913700953587371)
                ·
                  refine ⟨4527765607370551430381057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3018510404913700953587371 4527765607370551430381057)
                  ·
                    refine ⟨3395824205527913572785793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4527765607370551430381057 3395824205527913572785793)
                    ·
                      refine ⟨2546868154145935179589345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395824205527913572785793 2546868154145935179589345)
                      ·
                        rfl

theorem cell23_4960008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_4960008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960008 prefixEnd_4960008 := by exact prefixLift 4960008
  have htrace : WordTrace (prefixWord ++ tailWord_4960008) baseStart_4960008 baseEnd_4960008 := by
    simpa [prefixWord, tailWord_4960008, baseEnd_4960008] using wordTrace_append hprefix tailTrace_4960008
  have hstable : (prefixWord ++ tailWord_4960008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960008).length < 2 ^ (prefixWord ++ tailWord_4960008).sum := by decide
  have hdescent : baseEnd_4960008 < baseStart_4960008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960017 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 3, 3, 2]
def baseStart_4960017 : Nat := 118140960795 + 4960017 * 2 ^ 59
def prefixEnd_4960017 : Nat := 4983230072969 + 3 ^ 40 * 4960017 * 2
def baseEnd_4960017 : Nat := 2546872775471825644376803

theorem tailTrace_4960017 : CollatzResearch.WordTrace tailWord_4960017 prefixEnd_4960017 2546872775471825644376803 := by
  unfold tailWord_4960017
  simp only [CollatzResearch.WordTrace]
  refine ⟨180906682071712987307358305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120604454714475324871572203 180906682071712987307358305)
  ·
    refine ⟨135680011553784740480518729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180906682071712987307358305 135680011553784740480518729)
    ·
      refine ⟨101760008665338555360389047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135680011553784740480518729 101760008665338555360389047)
      ·
        refine ⟨152640012998007833040583571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101760008665338555360389047 152640012998007833040583571)
        ·
          refine ⟨228960019497011749560875357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152640012998007833040583571 228960019497011749560875357)
          ·
            refine ⟨85860007311379406085328259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228960019497011749560875357 85860007311379406085328259)
            ·
              refine ⟨128790010967069109127992389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85860007311379406085328259 128790010967069109127992389)
              ·
                refine ⟨24148127056325457961498573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128790010967069109127992389 24148127056325457961498573)
                ·
                  refine ⟨9055547646122046735561965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24148127056325457961498573 9055547646122046735561965)
                  ·
                    refine ⟨3395830367295767525835737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9055547646122046735561965 3395830367295767525835737)
                    ·
                      refine ⟨2546872775471825644376803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395830367295767525835737 2546872775471825644376803)
                      ·
                        rfl

theorem cell23_4960017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_4960017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960017 prefixEnd_4960017 := by exact prefixLift 4960017
  have htrace : WordTrace (prefixWord ++ tailWord_4960017) baseStart_4960017 baseEnd_4960017 := by
    simpa [prefixWord, tailWord_4960017, baseEnd_4960017] using wordTrace_append hprefix tailTrace_4960017
  have hstable : (prefixWord ++ tailWord_4960017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960017).length < 2 ^ (prefixWord ++ tailWord_4960017).sum := by decide
  have hdescent : baseEnd_4960017 < baseStart_4960017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960018 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4960018 : Nat := 118140960795 + 4960018 * 2 ^ 59
def prefixEnd_4960018 : Nat := 4983230072969 + 3 ^ 40 * 4960018 * 2
def baseEnd_4960018 : Nat := 848957762984160046821433

theorem tailTrace_4960018 : CollatzResearch.WordTrace tailWord_4960018 prefixEnd_4960018 848957762984160046821433 := by
  unfold tailWord_4960018
  simp only [CollatzResearch.WordTrace]
  refine ⟨45226679636177341119536177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120604479029806242985429805 45226679636177341119536177)
  ·
    refine ⟨33920009727133005839652133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45226679636177341119536177 33920009727133005839652133)
    ·
      refine ⟨6360001823837438594934775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33920009727133005839652133 6360001823837438594934775)
      ·
        refine ⟨9540002735756157892402163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6360001823837438594934775 9540002735756157892402163)
        ·
          refine ⟨14310004103634236838603245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9540002735756157892402163 14310004103634236838603245)
          ·
            refine ⟨5366251538862838814476217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14310004103634236838603245 5366251538862838814476217)
            ·
              refine ⟨4024688654147129110857163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5366251538862838814476217 4024688654147129110857163)
              ·
                refine ⟨6037032981220693666285745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024688654147129110857163 6037032981220693666285745)
                ·
                  refine ⟨4527774735915520249714309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037032981220693666285745 4527774735915520249714309)
                  ·
                    refine ⟨848957762984160046821433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527774735915520249714309 848957762984160046821433)
                    ·
                      rfl

theorem cell23_4960018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4960018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960018 prefixEnd_4960018 := by exact prefixLift 4960018
  have htrace : WordTrace (prefixWord ++ tailWord_4960018) baseStart_4960018 baseEnd_4960018 := by
    simpa [prefixWord, tailWord_4960018, baseEnd_4960018] using wordTrace_append hprefix tailTrace_4960018
  have hstable : (prefixWord ++ tailWord_4960018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960018).length < 2 ^ (prefixWord ++ tailWord_4960018).sum := by decide
  have hdescent : baseEnd_4960018 < baseStart_4960018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960034 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_4960034 : Nat := 118140960795 + 4960034 * 2 ^ 59
def prefixEnd_4960034 : Nat := 4983230072969 + 3 ^ 40 * 4960034 * 2
def baseEnd_4960034 : Nat := 2546881504642952077864225

theorem tailTrace_4960034 : CollatzResearch.WordTrace tailWord_4960034 prefixEnd_4960034 2546881504642952077864225 := by
  unfold tailWord_4960034
  simp only [CollatzResearch.WordTrace]
  refine ⟨45226825528162849802681789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120604868075100932807151437 45226825528162849802681789)
  ·
    refine ⟨16960059573061068676005671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45226825528162849802681789 16960059573061068676005671)
    ·
      refine ⟨25440089359591603014008507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16960059573061068676005671 25440089359591603014008507)
      ·
        refine ⟨38160134039387404521012761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25440089359591603014008507 38160134039387404521012761)
        ·
          refine ⟨28620100529540553390759571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38160134039387404521012761 28620100529540553390759571)
          ·
            refine ⟨42930150794310830086139357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28620100529540553390759571 42930150794310830086139357)
            ·
              refine ⟨16098806547866561282302259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42930150794310830086139357 16098806547866561282302259)
              ·
                refine ⟨24148209821799841923453389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16098806547866561282302259 24148209821799841923453389)
                ·
                  refine ⟨9055578683174940721295021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24148209821799841923453389 9055578683174940721295021)
                  ·
                    refine ⟨3395842006190602770485633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9055578683174940721295021 3395842006190602770485633)
                    ·
                      refine ⟨2546881504642952077864225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395842006190602770485633 2546881504642952077864225)
                      ·
                        rfl

theorem cell23_4960034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_4960034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960034 prefixEnd_4960034 := by exact prefixLift 4960034
  have htrace : WordTrace (prefixWord ++ tailWord_4960034) baseStart_4960034 baseEnd_4960034 := by
    simpa [prefixWord, tailWord_4960034, baseEnd_4960034] using wordTrace_append hprefix tailTrace_4960034
  have hstable : (prefixWord ++ tailWord_4960034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960034).length < 2 ^ (prefixWord ++ tailWord_4960034).sum := by decide
  have hdescent : baseEnd_4960034 < baseStart_4960034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960047 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 1, 4, 2]
def baseStart_4960047 : Nat := 118140960795 + 4960047 * 2 ^ 59
def prefixEnd_4960047 : Nat := 4983230072969 + 3 ^ 40 * 4960047 * 2
def baseEnd_4960047 : Nat := 2546888179891460527001665

theorem tailTrace_4960047 : CollatzResearch.WordTrace tailWord_4960047 prefixEnd_4960047 2546888179891460527001665 := by
  unfold tailWord_4960047
  simp only [CollatzResearch.WordTrace]
  refine ⟨180907776261604302430950395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120605184174402868287300263 180907776261604302430950395)
  ·
    refine ⟨271361664392406453646425593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180907776261604302430950395 271361664392406453646425593)
    ·
      refine ⟨203521248294304840234819195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271361664392406453646425593 203521248294304840234819195)
      ·
        refine ⟨305281872441457260352228793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203521248294304840234819195 305281872441457260352228793)
        ·
          refine ⟨228961404331092945264171595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305281872441457260352228793 228961404331092945264171595)
          ·
            refine ⟨343442106496639417896257393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228961404331092945264171595 343442106496639417896257393)
            ·
              refine ⟨257581579872479563422193045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343442106496639417896257393 257581579872479563422193045)
              ·
                refine ⟨12074136556522479535415299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 257581579872479563422193045 12074136556522479535415299)
                ·
                  refine ⟨18111204834783719303122949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12074136556522479535415299 18111204834783719303122949)
                  ·
                    refine ⟨3395850906521947369335553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18111204834783719303122949 3395850906521947369335553)
                    ·
                      refine ⟨2546888179891460527001665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395850906521947369335553 2546888179891460527001665)
                      ·
                        rfl

theorem cell23_4960047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 4, 2].length) (baseStart_4960047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960047 prefixEnd_4960047 := by exact prefixLift 4960047
  have htrace : WordTrace (prefixWord ++ tailWord_4960047) baseStart_4960047 baseEnd_4960047 := by
    simpa [prefixWord, tailWord_4960047, baseEnd_4960047] using wordTrace_append hprefix tailTrace_4960047
  have hstable : (prefixWord ++ tailWord_4960047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960047).length < 2 ^ (prefixWord ++ tailWord_4960047).sum := by decide
  have hdescent : baseEnd_4960047 < baseStart_4960047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960081 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 2, 2, 2]
def baseStart_4960081 : Nat := 118140960795 + 4960081 * 2 ^ 59
def prefixEnd_4960081 : Nat := 4983230072969 + 3 ^ 40 * 4960081 * 2
def baseEnd_4960081 : Nat := 2546905638233713393976509

theorem tailTrace_4960081 : CollatzResearch.WordTrace tailWord_4960081 prefixEnd_4960081 2546905638233713393976509 := by
  unfold tailWord_4960081
  simp only [CollatzResearch.WordTrace]
  refine ⟨180909016343481126237688097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120606010895654084158458731 180909016343481126237688097)
  ·
    refine ⟨135681762257610844678266073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180909016343481126237688097 135681762257610844678266073)
    ·
      refine ⟨101761321693208133508699555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135681762257610844678266073 101761321693208133508699555)
      ·
        refine ⟨152641982539812200263049333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101761321693208133508699555 152641982539812200263049333)
        ·
          refine ⟨14310185863107393774660875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152641982539812200263049333 14310185863107393774660875)
          ·
            refine ⟨21465278794661090661991313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14310185863107393774660875 21465278794661090661991313)
            ·
              refine ⟨16098959095995817996493485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21465278794661090661991313 16098959095995817996493485)
              ·
                refine ⟨6037109660998431748685057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16098959095995817996493485 6037109660998431748685057)
                ·
                  refine ⟨4527832245748823811513793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037109660998431748685057 4527832245748823811513793)
                  ·
                    refine ⟨3395874184311617858635345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4527832245748823811513793 3395874184311617858635345)
                    ·
                      refine ⟨2546905638233713393976509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395874184311617858635345 2546905638233713393976509)
                      ·
                        rfl

theorem cell23_4960081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_4960081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960081 prefixEnd_4960081 := by exact prefixLift 4960081
  have htrace : WordTrace (prefixWord ++ tailWord_4960081) baseStart_4960081 baseEnd_4960081 := by
    simpa [prefixWord, tailWord_4960081, baseEnd_4960081] using wordTrace_append hprefix tailTrace_4960081
  have hstable : (prefixWord ++ tailWord_4960081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960081).length < 2 ^ (prefixWord ++ tailWord_4960081).sum := by decide
  have hdescent : baseEnd_4960081 < baseStart_4960081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960087 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 7]
def baseStart_4960087 : Nat := 118140960795 + 4960087 * 2 ^ 59
def prefixEnd_4960087 : Nat := 4983230072969 + 3 ^ 40 * 4960087 * 2
def baseEnd_4960087 : Nat := 282989857679737818944609

theorem tailTrace_4960087 : CollatzResearch.WordTrace tailWord_4960087 prefixEnd_4960087 282989857679737818944609 := by
  unfold tailWord_4960087
  simp only [CollatzResearch.WordTrace]
  refine ⟨180909235181459389262406515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120606156787639592841604343 180909235181459389262406515)
  ·
    refine ⟨271363852772189083893609773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180909235181459389262406515 271363852772189083893609773)
    ·
      refine ⟨101761444789570906460103665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271363852772189083893609773 101761444789570906460103665)
      ·
        refine ⟨76321083592178179845077749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101761444789570906460103665 76321083592178179845077749)
        ·
          refine ⟨7155101586766704360476039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76321083592178179845077749 7155101586766704360476039)
          ·
            refine ⟨10732652380150056540714059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7155101586766704360476039 10732652380150056540714059)
            ·
              refine ⟨16098978570225084811071089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10732652380150056540714059 16098978570225084811071089)
              ·
                refine ⟨12074233927668813608303317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16098978570225084811071089 12074233927668813608303317)
                ·
                  refine ⟨282989857679737818944609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12074233927668813608303317 282989857679737818944609)
                  ·
                    rfl

theorem cell23_4960087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 7].length) (baseStart_4960087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960087 prefixEnd_4960087 := by exact prefixLift 4960087
  have htrace : WordTrace (prefixWord ++ tailWord_4960087) baseStart_4960087 baseEnd_4960087 := by
    simpa [prefixWord, tailWord_4960087, baseEnd_4960087] using wordTrace_append hprefix tailTrace_4960087
  have hstable : (prefixWord ++ tailWord_4960087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960087).length < 2 ^ (prefixWord ++ tailWord_4960087).sum := by decide
  have hdescent : baseEnd_4960087 < baseStart_4960087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960104 : List Nat := [2, 1, 4, 2, 1, 1, 4, 3, 5]
def baseStart_4960104 : Nat := 118140960795 + 4960104 * 2 ^ 59
def prefixEnd_4960104 : Nat := 4983230072969 + 3 ^ 40 * 4960104 * 2
def baseEnd_4960104 : Nat := 282990827587640755998767

theorem tailTrace_4960104 : CollatzResearch.WordTrace tailWord_4960104 prefixEnd_4960104 282990827587640755998767 := by
  unfold tailWord_4960104
  simp only [CollatzResearch.WordTrace]
  refine ⟨90454927611198900582887683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120606570148265200777183577 90454927611198900582887683)
  ·
    refine ⟨135682391416798350874331525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90454927611198900582887683 135682391416798350874331525)
    ·
      refine ⟨25440448390649690788937161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135682391416798350874331525 25440448390649690788937161)
      ·
        refine ⟨19080336292987268091702871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25440448390649690788937161 19080336292987268091702871)
        ·
          refine ⟨28620504439480902137554307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19080336292987268091702871 28620504439480902137554307)
          ·
            refine ⟨42930756659221353206331461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28620504439480902137554307 42930756659221353206331461)
            ·
              refine ⟨8049516873604003726187149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42930756659221353206331461 8049516873604003726187149)
              ·
                refine ⟨3018568827601501397320181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8049516873604003726187149 3018568827601501397320181)
                ·
                  refine ⟨282990827587640755998767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3018568827601501397320181 282990827587640755998767)
                  ·
                    rfl

theorem cell23_4960104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 5].length) (baseStart_4960104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960104 prefixEnd_4960104 := by exact prefixLift 4960104
  have htrace : WordTrace (prefixWord ++ tailWord_4960104) baseStart_4960104 baseEnd_4960104 := by
    simpa [prefixWord, tailWord_4960104, baseEnd_4960104] using wordTrace_append hprefix tailTrace_4960104
  have hstable : (prefixWord ++ tailWord_4960104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960104).length < 2 ^ (prefixWord ++ tailWord_4960104).sum := by decide
  have hdescent : baseEnd_4960104 < baseStart_4960104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960117 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_4960117 : Nat := 118140960795 + 4960117 * 2 ^ 59
def prefixEnd_4960117 : Nat := 4983230072969 + 3 ^ 40 * 4960117 * 2
def baseEnd_4960117 : Nat := 848974707845758417708781

theorem tailTrace_4960117 : CollatzResearch.WordTrace tailWord_4960117 prefixEnd_4960117 848974707845758417708781 := by
  unfold tailWord_4960117
  simp only [CollatzResearch.WordTrace]
  refine ⟨180910329371350704385998605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120606886247567136257332403 180910329371350704385998605)
  ·
    refine ⟨67841373514256514144749477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180910329371350704385998605 67841373514256514144749477)
    ·
      refine ⟨12720257533923096402140527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67841373514256514144749477 12720257533923096402140527)
      ·
        refine ⟨19080386300884644603210791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12720257533923096402140527 19080386300884644603210791)
        ·
          refine ⟨28620579451326966904816187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19080386300884644603210791 28620579451326966904816187)
          ·
            refine ⟨42930869176990450357224281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28620579451326966904816187 42930869176990450357224281)
            ·
              refine ⟨32198151882742837767918211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42930869176990450357224281 32198151882742837767918211)
              ·
                refine ⟨48297227824114256651877317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32198151882742837767918211 48297227824114256651877317)
                ·
                  refine ⟨9055730217021423122226997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48297227824114256651877317 9055730217021423122226997)
                  ·
                    refine ⟨848974707845758417708781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9055730217021423122226997 848974707845758417708781)
                    ·
                      rfl

theorem cell23_4960117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_4960117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960117 prefixEnd_4960117 := by exact prefixLift 4960117
  have htrace : WordTrace (prefixWord ++ tailWord_4960117) baseStart_4960117 baseEnd_4960117 := by
    simpa [prefixWord, tailWord_4960117, baseEnd_4960117] using wordTrace_append hprefix tailTrace_4960117
  have hstable : (prefixWord ++ tailWord_4960117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960117).length < 2 ^ (prefixWord ++ tailWord_4960117).sum := by decide
  have hdescent : baseEnd_4960117 < baseStart_4960117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960177 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 8]
def baseStart_4960177 : Nat := 118140960795 + 4960177 * 2 ^ 59
def prefixEnd_4960177 : Nat := 4983230072969 + 3 ^ 40 * 4960177 * 2
def baseEnd_4960177 : Nat := 282994992486282779819563

theorem tailTrace_4960177 : CollatzResearch.WordTrace tailWord_4960177 prefixEnd_4960177 282994992486282779819563 := by
  unfold tailWord_4960177
  simp only [CollatzResearch.WordTrace]
  refine ⟨180912517751133334633182785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120608345167422223088788523 180912517751133334633182785)
  ·
    refine ⟨135684388313350000974887089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180912517751133334633182785 135684388313350000974887089)
    ·
      refine ⟨101763291235012500731165317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135684388313350000974887089 101763291235012500731165317)
      ·
        refine ⟨19080617106564843887093497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101763291235012500731165317 19080617106564843887093497)
        ·
          refine ⟨14310462829923632915320123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19080617106564843887093497 14310462829923632915320123)
          ·
            refine ⟨21465694244885449372980185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14310462829923632915320123 21465694244885449372980185)
            ·
              refine ⟨16099270683664087029735139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21465694244885449372980185 16099270683664087029735139)
              ·
                refine ⟨24148906025496130544602709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16099270683664087029735139 24148906025496130544602709)
                ·
                  refine ⟨282994992486282779819563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24148906025496130544602709 282994992486282779819563)
                  ·
                    rfl

theorem cell23_4960177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 8].length) (baseStart_4960177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960177 prefixEnd_4960177 := by exact prefixLift 4960177
  have htrace : WordTrace (prefixWord ++ tailWord_4960177) baseStart_4960177 baseEnd_4960177 := by
    simpa [prefixWord, tailWord_4960177, baseEnd_4960177] using wordTrace_append hprefix tailTrace_4960177
  have hstable : (prefixWord ++ tailWord_4960177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960177).length < 2 ^ (prefixWord ++ tailWord_4960177).sum := by decide
  have hdescent : baseEnd_4960177 < baseStart_4960177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960181 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_4960181 : Nat := 118140960795 + 4960181 * 2 ^ 59
def prefixEnd_4960181 : Nat := 4983230072969 + 3 ^ 40 * 4960181 * 2
def baseEnd_4960181 : Nat := 848985662099721000908683

theorem tailTrace_4960181 : CollatzResearch.WordTrace tailWord_4960181 prefixEnd_4960181 848985662099721000908683 := by
  unfold tailWord_4960181
  simp only [CollatzResearch.WordTrace]
  refine ⟨180912663643118843316328397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120608442428745895544218931 180912663643118843316328397)
  ·
    refine ⟨67842248866169566243623149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180912663643118843316328397 67842248866169566243623149)
    ·
      refine ⟨25440843324813587341358681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67842248866169566243623149 25440843324813587341358681)
      ·
        refine ⟨19080632493610190506019011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25440843324813587341358681 19080632493610190506019011)
        ·
          refine ⟨28620948740415285759028517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19080632493610190506019011 28620948740415285759028517)
          ·
            refine ⟨5366427888827866079817847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28620948740415285759028517 5366427888827866079817847)
            ·
              refine ⟨8049641833241799119726771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5366427888827866079817847 8049641833241799119726771)
              ·
                refine ⟨12074462749862698679590157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8049641833241799119726771 12074462749862698679590157)
                ·
                  refine ⟨4527923531198512004846309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12074462749862698679590157 4527923531198512004846309)
                  ·
                    refine ⟨848985662099721000908683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4527923531198512004846309 848985662099721000908683)
                    ·
                      rfl

theorem cell23_4960181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_4960181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960181 prefixEnd_4960181 := by exact prefixLift 4960181
  have htrace : WordTrace (prefixWord ++ tailWord_4960181) baseStart_4960181 baseEnd_4960181 := by
    simpa [prefixWord, tailWord_4960181, baseEnd_4960181] using wordTrace_append hprefix tailTrace_4960181
  have hstable : (prefixWord ++ tailWord_4960181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960181).length < 2 ^ (prefixWord ++ tailWord_4960181).sum := by decide
  have hdescent : baseEnd_4960181 < baseStart_4960181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960207 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 3, 5]
def baseStart_4960207 : Nat := 118140960795 + 4960207 * 2 ^ 59
def prefixEnd_4960207 : Nat := 4983230072969 + 3 ^ 40 * 4960207 * 2
def baseEnd_4960207 : Nat := 848990112265393300333643

theorem tailTrace_4960207 : CollatzResearch.WordTrace tailWord_4960207 prefixEnd_4960207 848990112265393300333643 := by
  unfold tailWord_4960207
  simp only [CollatzResearch.WordTrace]
  refine ⟨180913611941024649756774875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120609074627349766504516583 180913611941024649756774875)
  ·
    refine ⟨271370417911536974635162313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180913611941024649756774875 271370417911536974635162313)
    ·
      refine ⟨203527813433652730976371735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271370417911536974635162313 203527813433652730976371735)
      ·
        refine ⟨305291720150479096464557603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203527813433652730976371735 305291720150479096464557603)
        ·
          refine ⟨457937580225718644696836405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305291720150479096464557603 457937580225718644696836405)
          ·
            refine ⟨42931648146161122940328413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 457937580225718644696836405 42931648146161122940328413)
            ·
              refine ⟨16099368054810421102623155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42931648146161122940328413 16099368054810421102623155)
              ·
                refine ⟨24149052082215631653934733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16099368054810421102623155 24149052082215631653934733)
                ·
                  refine ⟨9055894530830861870225525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24149052082215631653934733 9055894530830861870225525)
                  ·
                    refine ⟨848990112265393300333643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9055894530830861870225525 848990112265393300333643)
                    ·
                      rfl

theorem cell23_4960207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_4960207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960207 prefixEnd_4960207 := by exact prefixLift 4960207
  have htrace : WordTrace (prefixWord ++ tailWord_4960207) baseStart_4960207 baseEnd_4960207 := by
    simpa [prefixWord, tailWord_4960207, baseEnd_4960207] using wordTrace_append hprefix tailTrace_4960207
  have hstable : (prefixWord ++ tailWord_4960207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960207).length < 2 ^ (prefixWord ++ tailWord_4960207).sum := by decide
  have hdescent : baseEnd_4960207 < baseStart_4960207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960261 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 5, 2, 2]
def baseStart_4960261 : Nat := 118140960795 + 4960261 * 2 ^ 59
def prefixEnd_4960261 : Nat := 4983230072969 + 3 ^ 40 * 4960261 * 2
def baseEnd_4960261 : Nat := 2546998064751522689725681

theorem tailTrace_4960261 : CollatzResearch.WordTrace tailWord_4960261 prefixEnd_4960261 2546998064751522689725681 := by
  unfold tailWord_4960261
  simp only [CollatzResearch.WordTrace]
  refine ⟨180915581482829016979240637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120610387655219344652827091 180915581482829016979240637)
  ·
    refine ⟨67843343056060881367215239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180915581482829016979240637 67843343056060881367215239)
    ·
      refine ⟨101765014584091322050822859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67843343056060881367215239 101765014584091322050822859)
      ·
        refine ⟨152647521876136983076234289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101765014584091322050822859 152647521876136983076234289)
        ·
          refine ⟨114485641407102737307175717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152647521876136983076234289 114485641407102737307175717)
          ·
            refine ⟨21466057763831763245095447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114485641407102737307175717 21466057763831763245095447)
            ·
              refine ⟨32199086645747644867643171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21466057763831763245095447 32199086645747644867643171)
              ·
                refine ⟨48298629968621467301464757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32199086645747644867643171 48298629968621467301464757)
                ·
                  refine ⟨4527996559558262559512321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48298629968621467301464757 4527996559558262559512321)
                  ·
                    refine ⟨3395997419668696919634241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4527996559558262559512321 3395997419668696919634241)
                    ·
                      refine ⟨2546998064751522689725681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3395997419668696919634241 2546998064751522689725681)
                      ·
                        rfl

theorem cell23_4960261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_4960261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960261 prefixEnd_4960261 := by exact prefixLift 4960261
  have htrace : WordTrace (prefixWord ++ tailWord_4960261) baseStart_4960261 baseEnd_4960261 := by
    simpa [prefixWord, tailWord_4960261, baseEnd_4960261] using wordTrace_append hprefix tailTrace_4960261
  have hstable : (prefixWord ++ tailWord_4960261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960261).length < 2 ^ (prefixWord ++ tailWord_4960261).sum := by decide
  have hdescent : baseEnd_4960261 < baseStart_4960261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960264 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_4960264 : Nat := 118140960795 + 4960264 * 2 ^ 59
def prefixEnd_4960264 : Nat := 4983230072969 + 3 ^ 40 * 4960264 * 2
def baseEnd_4960264 : Nat := 2546999605193486177988167

theorem tailTrace_4960264 : CollatzResearch.WordTrace tailWord_4960264 prefixEnd_4960264 2546999605193486177988167 := by
  unfold tailWord_4960264
  simp only [CollatzResearch.WordTrace]
  refine ⟨90457845450909074245799923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120610460601212098994399897 90457845450909074245799923)
  ·
    refine ⟨135686768176363611368699885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90457845450909074245799923 135686768176363611368699885)
    ·
      refine ⟨50882538066136354263262457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135686768176363611368699885 50882538066136354263262457)
      ·
        refine ⟨38161903549602265697446843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50882538066136354263262457 38161903549602265697446843)
        ·
          refine ⟨57242855324403398546170265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38161903549602265697446843 57242855324403398546170265)
          ·
            refine ⟨42932141493302548909627699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57242855324403398546170265 42932141493302548909627699)
            ·
              refine ⟨64398212239953823364441549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42932141493302548909627699 64398212239953823364441549)
              ·
                refine ⟨24149329589982683761665581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64398212239953823364441549 24149329589982683761665581)
                ·
                  refine ⟨9055998596243506410624593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24149329589982683761665581 9055998596243506410624593)
                  ·
                    refine ⟨6791998947182629807968445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9055998596243506410624593 6791998947182629807968445)
                    ·
                      refine ⟨2546999605193486177988167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6791998947182629807968445 2546999605193486177988167)
                      ·
                        rfl

theorem cell23_4960264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_4960264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960264 prefixEnd_4960264 := by exact prefixLift 4960264
  have htrace : WordTrace (prefixWord ++ tailWord_4960264) baseStart_4960264 baseEnd_4960264 := by
    simpa [prefixWord, tailWord_4960264, baseEnd_4960264] using wordTrace_append hprefix tailTrace_4960264
  have hstable : (prefixWord ++ tailWord_4960264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960264).length < 2 ^ (prefixWord ++ tailWord_4960264).sum := by decide
  have hdescent : baseEnd_4960264 < baseStart_4960264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960311 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_4960311 : Nat := 118140960795 + 4960311 * 2 ^ 59
def prefixEnd_4960311 : Nat := 4983230072969 + 3 ^ 40 * 4960311 * 2
def baseEnd_4960311 : Nat := 2547023738784247494100451

theorem tailTrace_4960311 : CollatzResearch.WordTrace tailWord_4960311 prefixEnd_4960311 2547023738784247494100451 := by
  unfold tailWord_4960311
  simp only [CollatzResearch.WordTrace]
  refine ⟨180917405132647875518560787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120611603421765250345707191 180917405132647875518560787)
  ·
    refine ⟨271376107698971813277841181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180917405132647875518560787 271376107698971813277841181)
    ·
      refine ⟨101766040387114429979190443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271376107698971813277841181 101766040387114429979190443)
      ·
        refine ⟨152649060580671644968785665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101766040387114429979190443 152649060580671644968785665)
        ·
          refine ⟨114486795435503733726589249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152649060580671644968785665 114486795435503733726589249)
          ·
            refine ⟨85865096576627800294941937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114486795435503733726589249 85865096576627800294941937)
            ·
              refine ⟨64398822432470850221206453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85865096576627800294941937 64398822432470850221206453)
              ·
                refine ⟨6037389603044142208238105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64398822432470850221206453 6037389603044142208238105)
                ·
                  refine ⟨4528042202283106656178579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037389603044142208238105 4528042202283106656178579)
                  ·
                    refine ⟨6792063303424659984267869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4528042202283106656178579 6792063303424659984267869)
                    ·
                      refine ⟨2547023738784247494100451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6792063303424659984267869 2547023738784247494100451)
                      ·
                        rfl

theorem cell23_4960311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_4960311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960311 prefixEnd_4960311 := by exact prefixLift 4960311
  have htrace : WordTrace (prefixWord ++ tailWord_4960311) baseStart_4960311 baseEnd_4960311 := by
    simpa [prefixWord, tailWord_4960311, baseEnd_4960311] using wordTrace_append hprefix tailTrace_4960311
  have hstable : (prefixWord ++ tailWord_4960311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960311).length < 2 ^ (prefixWord ++ tailWord_4960311).sum := by decide
  have hdescent : baseEnd_4960311 < baseStart_4960311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960318 : List Nat := [4, 2, 1, 3, 2, 2, 2, 7]
def baseStart_4960318 : Nat := 118140960795 + 4960318 * 2 ^ 59
def prefixEnd_4960318 : Nat := 4983230072969 + 3 ^ 40 * 4960318 * 2
def baseEnd_4960318 : Nat := 94334345672178850618997

theorem tailTrace_4960318 : CollatzResearch.WordTrace tailWord_4960318 prefixEnd_4960318 94334345672178850618997 := by
  unfold tailWord_4960318
  simp only [CollatzResearch.WordTrace]
  refine ⟨22614707555452814464258201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120611773629081677142710405 22614707555452814464258201)
  ·
    refine ⟨16961030666589610848193651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22614707555452814464258201 16961030666589610848193651)
    ·
      refine ⟨25441545999884416272290477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16961030666589610848193651 25441545999884416272290477)
      ·
        refine ⟨9540579749956656102108929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25441545999884416272290477 9540579749956656102108929)
        ·
          refine ⟨7155434812467492076581697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9540579749956656102108929 7155434812467492076581697)
          ·
            refine ⟨5366576109350619057436273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7155434812467492076581697 5366576109350619057436273)
            ·
              refine ⟨4024932082012964293077205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5366576109350619057436273 4024932082012964293077205)
              ·
                refine ⟨94334345672178850618997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4024932082012964293077205 94334345672178850618997)
                ·
                  rfl

theorem cell23_4960318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_4960318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960318 prefixEnd_4960318 := by exact prefixLift 4960318
  have htrace : WordTrace (prefixWord ++ tailWord_4960318) baseStart_4960318 baseEnd_4960318 := by
    simpa [prefixWord, tailWord_4960318, baseEnd_4960318] using wordTrace_append hprefix tailTrace_4960318
  have hstable : (prefixWord ++ tailWord_4960318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960318).length < 2 ^ (prefixWord ++ tailWord_4960318).sum := by decide
  have hdescent : baseEnd_4960318 < baseStart_4960318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960362 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_4960362 : Nat := 118140960795 + 4960362 * 2 ^ 59
def prefixEnd_4960362 : Nat := 4983230072969 + 3 ^ 40 * 4960362 * 2
def baseEnd_4960362 : Nat := 2547049926297626794562717

theorem tailTrace_4960362 : CollatzResearch.WordTrace tailWord_4960362 prefixEnd_4960362 2547049926297626794562717 := by
  unfold tailWord_4960362
  simp only [CollatzResearch.WordTrace]
  refine ⟨45229816313865777807166835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120612843503642074152444893 45229816313865777807166835)
  ·
    refine ⟨67844724470798666710750253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45229816313865777807166835 67844724470798666710750253)
    ·
      refine ⟨25441771676549500016531345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67844724470798666710750253 25441771676549500016531345)
      ·
        refine ⟨19081328757412125012398509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25441771676549500016531345 19081328757412125012398509)
        ·
          refine ⟨7155498284029546879649441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19081328757412125012398509 7155498284029546879649441)
          ·
            refine ⟨5366623713022160159737081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7155498284029546879649441 5366623713022160159737081)
            ·
              refine ⟨4024967784766620119802811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5366623713022160159737081 4024967784766620119802811)
              ·
                refine ⟨6037451677149930179704217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024967784766620119802811 6037451677149930179704217)
                ·
                  refine ⟨4528088757862447634778163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6037451677149930179704217 4528088757862447634778163)
                  ·
                    refine ⟨6792133136793671452167245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4528088757862447634778163 6792133136793671452167245)
                    ·
                      refine ⟨2547049926297626794562717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6792133136793671452167245 2547049926297626794562717)
                      ·
                        rfl

theorem cell23_4960362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_4960362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960362 prefixEnd_4960362 := by exact prefixLift 4960362
  have htrace : WordTrace (prefixWord ++ tailWord_4960362) baseStart_4960362 baseEnd_4960362 := by
    simpa [prefixWord, tailWord_4960362, baseEnd_4960362] using wordTrace_append hprefix tailTrace_4960362
  have hstable : (prefixWord ++ tailWord_4960362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960362).length < 2 ^ (prefixWord ++ tailWord_4960362).sum := by decide
  have hdescent : baseEnd_4960362 < baseStart_4960362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960384 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 3]
def baseStart_4960384 : Nat := 118140960795 + 4960384 * 2 ^ 59
def prefixEnd_4960384 : Nat := 4983230072969 + 3 ^ 40 * 4960384 * 2
def baseEnd_4960384 : Nat := 2547061222872025708487615

theorem tailTrace_4960384 : CollatzResearch.WordTrace tailWord_4960384 prefixEnd_4960384 2547061222872025708487615 := by
  unfold tailWord_4960384
  simp only [CollatzResearch.WordTrace]
  refine ⟨90460033830691704492984103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120613378440922272657312137 90460033830691704492984103)
  ·
    refine ⟨135690050746037556739476155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90460033830691704492984103 135690050746037556739476155)
    ·
      refine ⟨203535076119056335109214233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135690050746037556739476155 203535076119056335109214233)
      ·
        refine ⟨152651307089292251331910675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203535076119056335109214233 152651307089292251331910675)
        ·
          refine ⟨228976960633938376997866013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152651307089292251331910675 228976960633938376997866013)
          ·
            refine ⟨85866360237726891374199755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228976960633938376997866013 85866360237726891374199755)
            ·
              refine ⟨128799540356590337061299633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85866360237726891374199755 128799540356590337061299633)
              ·
                refine ⟨96599655267442752795974725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128799540356590337061299633 96599655267442752795974725)
                ·
                  refine ⟨18112435362645516149245261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96599655267442752795974725 18112435362645516149245261)
                  ·
                    refine ⟨6792163260992068555966973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18112435362645516149245261 6792163260992068555966973)
                    ·
                      refine ⟨2547061222872025708487615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6792163260992068555966973 2547061222872025708487615)
                      ·
                        rfl

theorem cell23_4960384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_4960384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960384 prefixEnd_4960384 := by exact prefixLift 4960384
  have htrace : WordTrace (prefixWord ++ tailWord_4960384) baseStart_4960384 baseEnd_4960384 := by
    simpa [prefixWord, tailWord_4960384, baseEnd_4960384] using wordTrace_append hprefix tailTrace_4960384
  have hstable : (prefixWord ++ tailWord_4960384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960384).length < 2 ^ (prefixWord ++ tailWord_4960384).sum := by decide
  have hdescent : baseEnd_4960384 < baseStart_4960384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960408 : List Nat := [2, 1, 2, 4, 3, 1, 1, 4, 5]
def baseStart_4960408 : Nat := 118140960795 + 4960408 * 2 ^ 59
def prefixEnd_4960408 : Nat := 4983230072969 + 3 ^ 40 * 4960408 * 2
def baseEnd_4960408 : Nat := 283008171823081512731945

theorem tailTrace_4960408 : CollatzResearch.WordTrace tailWord_4960408 prefixEnd_4960408 283008171823081512731945 := by
  unfold tailWord_4960408
  simp only [CollatzResearch.WordTrace]
  refine ⟨90460471506648230542420939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120613962008864307389894585 90460471506648230542420939)
  ·
    refine ⟨135690707259972345813631409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90460471506648230542420939 135690707259972345813631409)
    ·
      refine ⟨101768030444979259360223557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135690707259972345813631409 101768030444979259360223557)
      ·
        refine ⟨19081505708433611130041917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101768030444979259360223557 19081505708433611130041917)
        ·
          refine ⟨7155564640662604173765719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19081505708433611130041917 7155564640662604173765719)
          ·
            refine ⟨10733346960993906260648579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7155564640662604173765719 10733346960993906260648579)
            ·
              refine ⟨16100020441490859390972869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10733346960993906260648579 16100020441490859390972869)
              ·
                refine ⟨3018753832779536135807413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16100020441490859390972869 3018753832779536135807413)
                ·
                  refine ⟨283008171823081512731945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3018753832779536135807413 283008171823081512731945)
                  ·
                    rfl

theorem cell23_4960408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 5].length) (baseStart_4960408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960408 prefixEnd_4960408 := by exact prefixLift 4960408
  have htrace : WordTrace (prefixWord ++ tailWord_4960408) baseStart_4960408 baseEnd_4960408 := by
    simpa [prefixWord, tailWord_4960408, baseEnd_4960408] using wordTrace_append hprefix tailTrace_4960408
  have hstable : (prefixWord ++ tailWord_4960408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960408).length < 2 ^ (prefixWord ++ tailWord_4960408).sum := by decide
  have hdescent : baseEnd_4960408 < baseStart_4960408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960418 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4960418 : Nat := 118140960795 + 4960418 * 2 ^ 59
def prefixEnd_4960418 : Nat := 4983230072969 + 3 ^ 40 * 4960418 * 2
def baseEnd_4960418 : Nat := 2547078681214278575462459

theorem tailTrace_4960418 : CollatzResearch.WordTrace tailWord_4960418 prefixEnd_4960418 2547078681214278575462459 := by
  unfold tailWord_4960418
  simp only [CollatzResearch.WordTrace]
  refine ⟨45230326935815058198176477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120614205162173488528470605 45230326935815058198176477)
  ·
    refine ⟨16961372600930646824316179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45230326935815058198176477 16961372600930646824316179)
    ·
      refine ⟨25442058901395970236474269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16961372600930646824316179 25442058901395970236474269)
      ·
        refine ⟨9540772088023488838677851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25442058901395970236474269 9540772088023488838677851)
        ·
          refine ⟨14311158132035233258016777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9540772088023488838677851 14311158132035233258016777)
          ·
            refine ⟨10733368599026424943512583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14311158132035233258016777 10733368599026424943512583)
            ·
              refine ⟨16100052898539637415268875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10733368599026424943512583 16100052898539637415268875)
              ·
                refine ⟨24150079347809456122903313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16100052898539637415268875 24150079347809456122903313)
                ·
                  refine ⟨18112559510857092092177485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24150079347809456122903313 18112559510857092092177485)
                  ·
                    refine ⟨6792209816571409534566557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18112559510857092092177485 6792209816571409534566557)
                    ·
                      refine ⟨2547078681214278575462459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6792209816571409534566557 2547078681214278575462459)
                      ·
                        rfl

theorem cell23_4960418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4960418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960418 prefixEnd_4960418 := by exact prefixLift 4960418
  have htrace : WordTrace (prefixWord ++ tailWord_4960418) baseStart_4960418 baseEnd_4960418 := by
    simpa [prefixWord, tailWord_4960418, baseEnd_4960418] using wordTrace_append hprefix tailTrace_4960418
  have hstable : (prefixWord ++ tailWord_4960418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960418).length < 2 ^ (prefixWord ++ tailWord_4960418).sum := by decide
  have hdescent : baseEnd_4960418 < baseStart_4960418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960441 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 1, 6, 2]
def baseStart_4960441 : Nat := 118140960795 + 4960441 * 2 ^ 59
def prefixEnd_4960441 : Nat := 4983230072969 + 3 ^ 40 * 4960441 * 2
def baseEnd_4960441 : Nat := 2547090491269331985474853

theorem tailTrace_4960441 : CollatzResearch.WordTrace tailWord_4960441 prefixEnd_4960441 2547090491269331985474853 := by
  unfold tailWord_4960441
  simp only [CollatzResearch.WordTrace]
  refine ⟨180922146622176907720793177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120614764414784605147195451 180922146622176907720793177)
  ·
    refine ⟨135691609966632680790594883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180922146622176907720793177 135691609966632680790594883)
    ·
      refine ⟨203537414949949021185892325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135691609966632680790594883 203537414949949021185892325)
      ·
        refine ⟨38163265303115441472354811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203537414949949021185892325 38163265303115441472354811)
        ·
          refine ⟨57244897954673162208532217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38163265303115441472354811 57244897954673162208532217)
          ·
            refine ⟨42933673466004871656399163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57244897954673162208532217 42933673466004871656399163)
            ·
              refine ⟨64400510199007307484598745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42933673466004871656399163 64400510199007307484598745)
              ·
                refine ⟨48300382649255480613449059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64400510199007307484598745 48300382649255480613449059)
                ·
                  refine ⟨72450573973883220920173589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48300382649255480613449059 72450573973883220920173589)
                  ·
                    refine ⟨3396120655025775980633137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72450573973883220920173589 3396120655025775980633137)
                    ·
                      refine ⟨2547090491269331985474853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3396120655025775980633137 2547090491269331985474853)
                      ·
                        rfl

theorem cell23_4960441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_4960441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960441 prefixEnd_4960441 := by exact prefixLift 4960441
  have htrace : WordTrace (prefixWord ++ tailWord_4960441) baseStart_4960441 baseEnd_4960441 := by
    simpa [prefixWord, tailWord_4960441, baseEnd_4960441] using wordTrace_append hprefix tailTrace_4960441
  have hstable : (prefixWord ++ tailWord_4960441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960441).length < 2 ^ (prefixWord ++ tailWord_4960441).sum := by decide
  have hdescent : baseEnd_4960441 < baseStart_4960441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960484 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_4960484 : Nat := 118140960795 + 4960484 * 2 ^ 59
def prefixEnd_4960484 : Nat := 4983230072969 + 3 ^ 40 * 4960484 * 2
def baseEnd_4960484 : Nat := 2547112570937475317237155

theorem tailTrace_4960484 : CollatzResearch.WordTrace tailWord_4960484 prefixEnd_4960484 2547112570937475317237155 := by
  unfold tailWord_4960484
  simp only [CollatzResearch.WordTrace]
  refine ⟨90461857480510563032304253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120615809974014084043072337 90461857480510563032304253)
  ·
    refine ⟨33923196555191461137114095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90461857480510563032304253 33923196555191461137114095)
    ·
      refine ⟨50884794832787191705671143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33923196555191461137114095 50884794832787191705671143)
      ·
        refine ⟨76327192249180787558506715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50884794832787191705671143 76327192249180787558506715)
        ·
          refine ⟨114490788373771181337760073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76327192249180787558506715 114490788373771181337760073)
          ·
            refine ⟨85868091280328386003320055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114490788373771181337760073 85868091280328386003320055)
            ·
              refine ⟨128802136920492579004980083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85868091280328386003320055 128802136920492579004980083)
              ·
                refine ⟨193203205380738868507470125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128802136920492579004980083 193203205380738868507470125)
                ·
                  refine ⟨72451202017777075690301297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193203205380738868507470125 72451202017777075690301297)
                  ·
                    refine ⟨54338401513332806767725973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72451202017777075690301297 54338401513332806767725973)
                    ·
                      refine ⟨2547112570937475317237155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54338401513332806767725973 2547112570937475317237155)
                      ·
                        rfl

theorem cell23_4960484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_4960484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960484 prefixEnd_4960484 := by exact prefixLift 4960484
  have htrace : WordTrace (prefixWord ++ tailWord_4960484) baseStart_4960484 baseEnd_4960484 := by
    simpa [prefixWord, tailWord_4960484, baseEnd_4960484] using wordTrace_append hprefix tailTrace_4960484
  have hstable : (prefixWord ++ tailWord_4960484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960484).length < 2 ^ (prefixWord ++ tailWord_4960484).sum := by decide
  have hdescent : baseEnd_4960484 < baseStart_4960484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960511 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 1, 5]
def baseStart_4960511 : Nat := 118140960795 + 4960511 * 2 ^ 59
def prefixEnd_4960511 : Nat := 4983230072969 + 3 ^ 40 * 4960511 * 2
def baseEnd_4960511 : Nat := 849042144971715570533177

theorem tailTrace_4960511 : CollatzResearch.WordTrace tailWord_4960511 prefixEnd_4960511 849042144971715570533177 := by
  unfold tailWord_4960511
  simp only [CollatzResearch.WordTrace]
  refine ⟨180924699731923309675841387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120616466487948873117227591 180924699731923309675841387)
  ·
    refine ⟨271387049597884964513762081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180924699731923309675841387 271387049597884964513762081)
    ·
      refine ⟨203540287198413723385321561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271387049597884964513762081 203540287198413723385321561)
      ·
        refine ⟨152655215398810292538991171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203540287198413723385321561 152655215398810292538991171)
        ·
          refine ⟨228982823098215438808486757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152655215398810292538991171 228982823098215438808486757)
          ·
            refine ⟨42934279330915394776591267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 228982823098215438808486757 42934279330915394776591267)
            ·
              refine ⟨64401418996373092164886901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42934279330915394776591267 64401418996373092164886901)
              ·
                refine ⟨6037633030909977390458147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64401418996373092164886901 6037633030909977390458147)
                ·
                  refine ⟨9056449546364966085687221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6037633030909977390458147 9056449546364966085687221)
                  ·
                    refine ⟨849042144971715570533177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9056449546364966085687221 849042144971715570533177)
                    ·
                      rfl

theorem cell23_4960511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_4960511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960511 prefixEnd_4960511 := by exact prefixLift 4960511
  have htrace : WordTrace (prefixWord ++ tailWord_4960511) baseStart_4960511 baseEnd_4960511 := by
    simpa [prefixWord, tailWord_4960511, baseEnd_4960511] using wordTrace_append hprefix tailTrace_4960511
  have hstable : (prefixWord ++ tailWord_4960511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960511).length < 2 ^ (prefixWord ++ tailWord_4960511).sum := by decide
  have hdescent : baseEnd_4960511 < baseStart_4960511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960519 : List Nat := [1, 1, 4, 5, 1, 1, 3, 2, 1, 4]
def baseStart_4960519 : Nat := 118140960795 + 4960519 * 2 ^ 59
def prefixEnd_4960519 : Nat := 4983230072969 + 3 ^ 40 * 4960519 * 2
def baseEnd_4960519 : Nat := 849043514253460893433165

theorem tailTrace_4960519 : CollatzResearch.WordTrace tailWord_4960519 prefixEnd_4960519 849043514253460893433165 := by
  unfold tailWord_4960519
  simp only [CollatzResearch.WordTrace]
  refine ⟨180924991515894327042132611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120616661010596218028088407 180924991515894327042132611)
  ·
    refine ⟨271387487273841490563198917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180924991515894327042132611 271387487273841490563198917)
    ·
      refine ⟨50885153863845279480599797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271387487273841490563198917 50885153863845279480599797)
      ·
        refine ⟨4770483174735494951306231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50885153863845279480599797 4770483174735494951306231)
        ·
          refine ⟨7155724762103242426959347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4770483174735494951306231 7155724762103242426959347)
          ·
            refine ⟨10733587143154863640439021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7155724762103242426959347 10733587143154863640439021)
            ·
              refine ⟨4025095178683073865164633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10733587143154863640439021 4025095178683073865164633)
              ·
                refine ⟨3018821384012305398873475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4025095178683073865164633 3018821384012305398873475)
                ·
                  refine ⟨4528232076018458098310213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3018821384012305398873475 4528232076018458098310213)
                  ·
                    refine ⟨849043514253460893433165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4528232076018458098310213 849043514253460893433165)
                    ·
                      rfl

theorem cell23_4960519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_4960519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960519 prefixEnd_4960519 := by exact prefixLift 4960519
  have htrace : WordTrace (prefixWord ++ tailWord_4960519) baseStart_4960519 baseEnd_4960519 := by
    simpa [prefixWord, tailWord_4960519, baseEnd_4960519] using wordTrace_append hprefix tailTrace_4960519
  have hstable : (prefixWord ++ tailWord_4960519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960519).length < 2 ^ (prefixWord ++ tailWord_4960519).sum := by decide
  have hdescent : baseEnd_4960519 < baseStart_4960519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960548 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_4960548 : Nat := 118140960795 + 4960548 * 2 ^ 59
def prefixEnd_4960548 : Nat := 4983230072969 + 3 ^ 40 * 4960548 * 2
def baseEnd_4960548 : Nat := 2547145433699363066836861

theorem tailTrace_4960548 : CollatzResearch.WordTrace tailWord_4960548 prefixEnd_4960548 2547145433699363066836861 := by
  unfold tailWord_4960548
  simp only [CollatzResearch.WordTrace]
  refine ⟨90463024616394632497469149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120617366155192843329958865 90463024616394632497469149)
  ·
    refine ⟨33923634231147987186550931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90463024616394632497469149 33923634231147987186550931)
    ·
      refine ⟨50885451346721980779826397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33923634231147987186550931 50885451346721980779826397)
      ·
        refine ⟨19082044255020742792434899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50885451346721980779826397 19082044255020742792434899)
        ·
          refine ⟨28623066382531114188652349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19082044255020742792434899 28623066382531114188652349)
          ·
            refine ⟨10733649893449167820744631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28623066382531114188652349 10733649893449167820744631)
            ·
              refine ⟨16100474840173751731116947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10733649893449167820744631 16100474840173751731116947)
              ·
                refine ⟨24150712260260627596675421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16100474840173751731116947 24150712260260627596675421)
                ·
                  refine ⟨9056517097597735348753283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24150712260260627596675421 9056517097597735348753283)
                  ·
                    refine ⟨13584775646396603023129925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9056517097597735348753283 13584775646396603023129925)
                    ·
                      refine ⟨2547145433699363066836861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13584775646396603023129925 2547145433699363066836861)
                      ·
                        rfl

theorem cell23_4960548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_4960548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960548 prefixEnd_4960548 := by exact prefixLift 4960548
  have htrace : WordTrace (prefixWord ++ tailWord_4960548) baseStart_4960548 baseEnd_4960548 := by
    simpa [prefixWord, tailWord_4960548, baseEnd_4960548] using wordTrace_append hprefix tailTrace_4960548
  have hstable : (prefixWord ++ tailWord_4960548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960548).length < 2 ^ (prefixWord ++ tailWord_4960548).sum := by decide
  have hdescent : baseEnd_4960548 < baseStart_4960548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960552 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_4960552 : Nat := 118140960795 + 4960552 * 2 ^ 59
def prefixEnd_4960552 : Nat := 4983230072969 + 3 ^ 40 * 4960552 * 2
def baseEnd_4960552 : Nat := 2547147487621981051186843

theorem tailTrace_4960552 : CollatzResearch.WordTrace tailWord_4960552 prefixEnd_4960552 2547147487621981051186843 := by
  unfold tailWord_4960552
  simp only [CollatzResearch.WordTrace]
  refine ⟨90463097562387386839041955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120617463416516515785389273 90463097562387386839041955)
  ·
    refine ⟨135694646343581080258562933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90463097562387386839041955 135694646343581080258562933)
    ·
      refine ⟨12721373094710726274240275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135694646343581080258562933 12721373094710726274240275)
      ·
        refine ⟨19082059642066089411360413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12721373094710726274240275 19082059642066089411360413)
        ·
          refine ⟨7155772365774783529260155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19082059642066089411360413 7155772365774783529260155)
          ·
            refine ⟨10733658548662175293890233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7155772365774783529260155 10733658548662175293890233)
            ·
              refine ⟨8050243911496631470417675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10733658548662175293890233 8050243911496631470417675)
              ·
                refine ⟨12075365867244947205626513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8050243911496631470417675 12075365867244947205626513)
                ·
                  refine ⟨9056524400433710404219885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12075365867244947205626513 9056524400433710404219885)
                  ·
                    refine ⟨3396196650162641401582457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9056524400433710404219885 3396196650162641401582457)
                    ·
                      refine ⟨2547147487621981051186843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3396196650162641401582457 2547147487621981051186843)
                      ·
                        rfl

theorem cell23_4960552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_4960552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960552 prefixEnd_4960552 := by exact prefixLift 4960552
  have htrace : WordTrace (prefixWord ++ tailWord_4960552) baseStart_4960552 baseEnd_4960552 := by
    simpa [prefixWord, tailWord_4960552, baseEnd_4960552] using wordTrace_append hprefix tailTrace_4960552
  have hstable : (prefixWord ++ tailWord_4960552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960552).length < 2 ^ (prefixWord ++ tailWord_4960552).sum := by decide
  have hdescent : baseEnd_4960552 < baseStart_4960552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960565 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_4960565 : Nat := 118140960795 + 4960565 * 2 ^ 59
def prefixEnd_4960565 : Nat := 4983230072969 + 3 ^ 40 * 4960565 * 2
def baseEnd_4960565 : Nat := 2547154162870489500324283

theorem tailTrace_4960565 : CollatzResearch.WordTrace tailWord_4960565 prefixEnd_4960565 2547154162870489500324283 := by
  unfold tailWord_4960565
  simp only [CollatzResearch.WordTrace]
  refine ⟨180926669273727676898307149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120617779515818451265538099 180926669273727676898307149)
  ·
    refine ⟨67847500977647878836865181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180926669273727676898307149 67847500977647878836865181)
    ·
      refine ⟨25442812866617954563824443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67847500977647878836865181 25442812866617954563824443)
      ·
        refine ⟨38164219299926931845736665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25442812866617954563824443 38164219299926931845736665)
        ·
          refine ⟨28623164474945198884302499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38164219299926931845736665 28623164474945198884302499)
          ·
            refine ⟨42934746712417798326453749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28623164474945198884302499 42934746712417798326453749)
            ·
              refine ⟨4025132504289168593105039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42934746712417798326453749 4025132504289168593105039)
              ·
                refine ⟨6037698756433752889657559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025132504289168593105039 6037698756433752889657559)
                ·
                  refine ⟨9056548134650629334486339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6037698756433752889657559 9056548134650629334486339)
                  ·
                    refine ⟨13584822201975944001729509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9056548134650629334486339 13584822201975944001729509)
                    ·
                      refine ⟨2547154162870489500324283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13584822201975944001729509 2547154162870489500324283)
                      ·
                        rfl

theorem cell23_4960565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_4960565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960565 prefixEnd_4960565 := by exact prefixLift 4960565
  have htrace : WordTrace (prefixWord ++ tailWord_4960565) baseStart_4960565 baseEnd_4960565 := by
    simpa [prefixWord, tailWord_4960565, baseEnd_4960565] using wordTrace_append hprefix tailTrace_4960565
  have hstable : (prefixWord ++ tailWord_4960565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960565).length < 2 ^ (prefixWord ++ tailWord_4960565).sum := by decide
  have hdescent : baseEnd_4960565 < baseStart_4960565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960568 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_4960568 : Nat := 118140960795 + 4960568 * 2 ^ 59
def prefixEnd_4960568 : Nat := 4983230072969 + 3 ^ 40 * 4960568 * 2
def baseEnd_4960568 : Nat := 2547155703312452988586769

theorem tailTrace_4960568 : CollatzResearch.WordTrace tailWord_4960568 prefixEnd_4960568 2547155703312452988586769 := by
  unfold tailWord_4960568
  simp only [CollatzResearch.WordTrace]
  refine ⟨90463389346358404205333179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120617852461811205607110905 90463389346358404205333179)
  ·
    refine ⟨135695084019537606307999769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90463389346358404205333179 135695084019537606307999769)
    ·
      refine ⟨101771313014653204730999827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135695084019537606307999769 101771313014653204730999827)
      ·
        refine ⟨152656969521979807096499741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101771313014653204730999827 152656969521979807096499741)
        ·
          refine ⟨57246363570742427661187403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152656969521979807096499741 57246363570742427661187403)
          ·
            refine ⟨85869545356113641491781105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57246363570742427661187403 85869545356113641491781105)
            ·
              refine ⟨64402159017085231118835829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85869545356113641491781105 64402159017085231118835829)
              ·
                refine ⟨6037702407851740417390859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64402159017085231118835829 6037702407851740417390859)
                ·
                  refine ⟨9056553611777610626086289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6037702407851740417390859 9056553611777610626086289)
                  ·
                    refine ⟨6792415208833207969564717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9056553611777610626086289 6792415208833207969564717)
                    ·
                      refine ⟨2547155703312452988586769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6792415208833207969564717 2547155703312452988586769)
                      ·
                        rfl

theorem cell23_4960568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_4960568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960568 prefixEnd_4960568 := by exact prefixLift 4960568
  have htrace : WordTrace (prefixWord ++ tailWord_4960568) baseStart_4960568 baseEnd_4960568 := by
    simpa [prefixWord, tailWord_4960568, baseEnd_4960568] using wordTrace_append hprefix tailTrace_4960568
  have hstable : (prefixWord ++ tailWord_4960568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960568).length < 2 ^ (prefixWord ++ tailWord_4960568).sum := by decide
  have hdescent : baseEnd_4960568 < baseStart_4960568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960611 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4960611 : Nat := 118140960795 + 4960611 * 2 ^ 59
def prefixEnd_4960611 : Nat := 4983230072969 + 3 ^ 40 * 4960611 * 2
def baseEnd_4960611 : Nat := 2547177782980596320349071

theorem tailTrace_4960611 : CollatzResearch.WordTrace tailWord_4960611 prefixEnd_4960611 2547177782980596320349071 := by
  unfold tailWord_4960611
  simp only [CollatzResearch.WordTrace]
  refine ⟨180928347031561026754481687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120618898021040684502987791 180928347031561026754481687)
  ·
    refine ⟨271392520547341540131722531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180928347031561026754481687 271392520547341540131722531)
    ·
      refine ⟨407088780821012310197583797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271392520547341540131722531 407088780821012310197583797)
      ·
        refine ⟨38164573201969904081023481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 407088780821012310197583797 38164573201969904081023481)
        ·
          refine ⟨28623429901477428060767611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38164573201969904081023481 28623429901477428060767611)
          ·
            refine ⟨42935144852216142091151417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28623429901477428060767611 42935144852216142091151417)
            ·
              refine ⟨32201358639162106568363563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42935144852216142091151417 32201358639162106568363563)
              ·
                refine ⟨48302037958743159852545345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32201358639162106568363563 48302037958743159852545345)
                ·
                  refine ⟨36226528469057369889409009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48302037958743159852545345 36226528469057369889409009)
                  ·
                    refine ⟨27169896351793027417056757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36226528469057369889409009 27169896351793027417056757)
                    ·
                      refine ⟨2547177782980596320349071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27169896351793027417056757 2547177782980596320349071)
                      ·
                        rfl

theorem cell23_4960611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4960611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960611 prefixEnd_4960611 := by exact prefixLift 4960611
  have htrace : WordTrace (prefixWord ++ tailWord_4960611) baseStart_4960611 baseEnd_4960611 := by
    simpa [prefixWord, tailWord_4960611, baseEnd_4960611] using wordTrace_append hprefix tailTrace_4960611
  have hstable : (prefixWord ++ tailWord_4960611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960611).length < 2 ^ (prefixWord ++ tailWord_4960611).sum := by decide
  have hdescent : baseEnd_4960611 < baseStart_4960611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960721 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 2, 8]
def baseStart_4960721 : Nat := 118140960795 + 4960721 * 2 ^ 59
def prefixEnd_4960721 : Nat := 4983230072969 + 3 ^ 40 * 4960721 * 2
def baseEnd_4960721 : Nat := 849078088617530296657855

theorem tailTrace_4960721 : CollatzResearch.WordTrace tailWord_4960721 prefixEnd_4960721 849078088617530296657855 := by
  unfold tailWord_4960721
  simp only [CollatzResearch.WordTrace]
  refine ⟨180932359061162515540986017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120621572707441677027324011 180932359061162515540986017)
  ·
    refine ⟨135699269295871886655739513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180932359061162515540986017 135699269295871886655739513)
    ·
      refine ⟨101774451971903914991804635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135699269295871886655739513 101774451971903914991804635)
      ·
        refine ⟨152661677957855872487706953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101774451971903914991804635 152661677957855872487706953)
        ·
          refine ⟨114496258468391904365780215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152661677957855872487706953 114496258468391904365780215)
          ·
            refine ⟨171744387702587856548670323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114496258468391904365780215 171744387702587856548670323)
            ·
              refine ⟨257616581553881784823005485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171744387702587856548670323 257616581553881784823005485)
              ·
                refine ⟨96606218082705669308627057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257616581553881784823005485 96606218082705669308627057)
                ·
                  refine ⟨72454663562029251981470293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96606218082705669308627057 72454663562029251981470293)
                  ·
                    refine ⟨849078088617530296657855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72454663562029251981470293 849078088617530296657855)
                    ·
                      rfl

theorem cell23_4960721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_4960721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960721 prefixEnd_4960721 := by exact prefixLift 4960721
  have htrace : WordTrace (prefixWord ++ tailWord_4960721) baseStart_4960721 baseEnd_4960721 := by
    simpa [prefixWord, tailWord_4960721, baseEnd_4960721] using wordTrace_append hprefix tailTrace_4960721
  have hstable : (prefixWord ++ tailWord_4960721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960721).length < 2 ^ (prefixWord ++ tailWord_4960721).sum := by decide
  have hdescent : baseEnd_4960721 < baseStart_4960721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960725 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_4960725 : Nat := 118140960795 + 4960725 * 2 ^ 59
def prefixEnd_4960725 : Nat := 4983230072969 + 3 ^ 40 * 4960725 * 2
def baseEnd_4960725 : Nat := 849078773258402958107849

theorem tailTrace_4960725 : CollatzResearch.WordTrace tailWord_4960725 prefixEnd_4960725 849078773258402958107849 := by
  unfold tailWord_4960725
  simp only [CollatzResearch.WordTrace]
  refine ⟨180932504953148024224131629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120621669968765349482754419 180932504953148024224131629)
  ·
    refine ⟨67849689357430509084049361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180932504953148024224131629 67849689357430509084049361)
    ·
      refine ⟨50887267018072881813037021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67849689357430509084049361 50887267018072881813037021)
      ·
        refine ⟨19082725131777330679888883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50887267018072881813037021 19082725131777330679888883)
        ·
          refine ⟨28624087697665996019833325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19082725131777330679888883 28624087697665996019833325)
          ·
            refine ⟨10734032886624748507437497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28624087697665996019833325 10734032886624748507437497)
            ·
              refine ⟨8050524664968561380578123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10734032886624748507437497 8050524664968561380578123)
              ·
                refine ⟨12075786997452842070867185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8050524664968561380578123 12075786997452842070867185)
                ·
                  refine ⟨9056840248089631553150389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12075786997452842070867185 9056840248089631553150389)
                  ·
                    refine ⟨849078773258402958107849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9056840248089631553150389 849078773258402958107849)
                    ·
                      rfl

theorem cell23_4960725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_4960725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960725 prefixEnd_4960725 := by exact prefixLift 4960725
  have htrace : WordTrace (prefixWord ++ tailWord_4960725) baseStart_4960725 baseEnd_4960725 := by
    simpa [prefixWord, tailWord_4960725, baseEnd_4960725] using wordTrace_append hprefix tailTrace_4960725
  have hstable : (prefixWord ++ tailWord_4960725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960725).length < 2 ^ (prefixWord ++ tailWord_4960725).sum := by decide
  have hdescent : baseEnd_4960725 < baseStart_4960725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960772 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_4960772 : Nat := 118140960795 + 4960772 * 2 ^ 59
def prefixEnd_4960772 : Nat := 4983230072969 + 3 ^ 40 * 4960772 * 2
def baseEnd_4960772 : Nat := 849086817788656730145277

theorem tailTrace_4960772 : CollatzResearch.WordTrace tailWord_4960772 prefixEnd_4960772 849086817788656730145277 := by
  unfold tailWord_4960772
  simp only [CollatzResearch.WordTrace]
  refine ⟨90467109591988875625546285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120622812789318500834061713 90467109591988875625546285)
  ·
    refine ⟨33925166096995828359579857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90467109591988875625546285 33925166096995828359579857)
    ·
      refine ⟨25443874572746871269684893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33925166096995828359579857 25443874572746871269684893)
      ·
        refine ⟨9541452964780076726131835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25443874572746871269684893 9541452964780076726131835)
        ·
          refine ⟨14312179447170115089197753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9541452964780076726131835 14312179447170115089197753)
          ·
            refine ⟨10734134585377586316898315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14312179447170115089197753 10734134585377586316898315)
            ·
              refine ⟨16101201878066379475347473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10734134585377586316898315 16101201878066379475347473)
              ·
                refine ⟨12075901408549784606510605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16101201878066379475347473 12075901408549784606510605)
                ·
                  refine ⟨4528463028206169227441477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12075901408549784606510605 4528463028206169227441477)
                  ·
                    refine ⟨849086817788656730145277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4528463028206169227441477 849086817788656730145277)
                    ·
                      rfl

theorem cell23_4960772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_4960772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960772 prefixEnd_4960772 := by exact prefixLift 4960772
  have htrace : WordTrace (prefixWord ++ tailWord_4960772) baseStart_4960772 baseEnd_4960772 := by
    simpa [prefixWord, tailWord_4960772, baseEnd_4960772] using wordTrace_append hprefix tailTrace_4960772
  have hstable : (prefixWord ++ tailWord_4960772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960772).length < 2 ^ (prefixWord ++ tailWord_4960772).sum := by decide
  have hdescent : baseEnd_4960772 < baseStart_4960772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960782 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_4960782 : Nat := 118140960795 + 4960782 * 2 ^ 59
def prefixEnd_4960782 : Nat := 4983230072969 + 3 ^ 40 * 4960782 * 2
def baseEnd_4960782 : Nat := 2547265588172515151310785

theorem tailTrace_4960782 : CollatzResearch.WordTrace tailWord_4960782 prefixEnd_4960782 2547265588172515151310785 := by
  unfold tailWord_4960782
  simp only [CollatzResearch.WordTrace]
  refine ⟨22616822989242690369869575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120623055942627681972637733 22616822989242690369869575)
  ·
    refine ⟨33925234483864035554804363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22616822989242690369869575 33925234483864035554804363)
    ·
      refine ⟨50887851725796053332206545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33925234483864035554804363 50887851725796053332206545)
      ·
        refine ⟨38165888794347039999154909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50887851725796053332206545 38165888794347039999154909)
        ·
          refine ⟨14312208297880139999683091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38165888794347039999154909 14312208297880139999683091)
          ·
            refine ⟨21468312446820209999524637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14312208297880139999683091 21468312446820209999524637)
            ·
              refine ⟨8050617167557578749821739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21468312446820209999524637 8050617167557578749821739)
              ·
                refine ⟨12075925751336368124732609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8050617167557578749821739 12075925751336368124732609)
                ·
                  refine ⟨9056944313502276093549457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12075925751336368124732609 9056944313502276093549457)
                  ·
                    refine ⟨6792708235126707070162093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9056944313502276093549457 6792708235126707070162093)
                    ·
                      refine ⟨2547265588172515151310785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6792708235126707070162093 2547265588172515151310785)
                      ·
                        rfl

theorem cell23_4960782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_4960782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960782 prefixEnd_4960782 := by exact prefixLift 4960782
  have htrace : WordTrace (prefixWord ++ tailWord_4960782) baseStart_4960782 baseEnd_4960782 := by
    simpa [prefixWord, tailWord_4960782, baseEnd_4960782] using wordTrace_append hprefix tailTrace_4960782
  have hstable : (prefixWord ++ tailWord_4960782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960782).length < 2 ^ (prefixWord ++ tailWord_4960782).sum := by decide
  have hdescent : baseEnd_4960782 < baseStart_4960782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960852 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_4960852 : Nat := 118140960795 + 4960852 * 2 ^ 59
def prefixEnd_4960852 : Nat := 4983230072969 + 3 ^ 40 * 4960852 * 2
def baseEnd_4960852 : Nat := 2547301531818329877435463

theorem tailTrace_4960852 : CollatzResearch.WordTrace tailWord_4960852 prefixEnd_4960852 2547301531818329877435463 := by
  unfold tailWord_4960852
  simp only [CollatzResearch.WordTrace]
  refine ⟨90468568511843962457002405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120624758015791949942669873 90468568511843962457002405)
  ·
    refine ⟨16962856595970742960687951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90468568511843962457002405 16962856595970742960687951)
    ·
      refine ⟨25444284893956114441031927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16962856595970742960687951 25444284893956114441031927)
      ·
        refine ⟨38166427340934171661547891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25444284893956114441031927 38166427340934171661547891)
        ·
          refine ⟨57249641011401257492321837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38166427340934171661547891 57249641011401257492321837)
          ·
            refine ⟨21468615379275471559620689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57249641011401257492321837 21468615379275471559620689)
            ·
              refine ⟨16101461534456603669715517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21468615379275471559620689 16101461534456603669715517)
              ·
                refine ⟨6038048075421226376143319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16101461534456603669715517 6038048075421226376143319)
                ·
                  refine ⟨9057072113131839564214979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6038048075421226376143319 9057072113131839564214979)
                  ·
                    refine ⟨13585608169697759346322469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9057072113131839564214979 13585608169697759346322469)
                    ·
                      refine ⟨2547301531818329877435463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13585608169697759346322469 2547301531818329877435463)
                      ·
                        rfl

theorem cell23_4960852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_4960852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960852 prefixEnd_4960852 := by exact prefixLift 4960852
  have htrace : WordTrace (prefixWord ++ tailWord_4960852) baseStart_4960852 baseEnd_4960852 := by
    simpa [prefixWord, tailWord_4960852, baseEnd_4960852] using wordTrace_append hprefix tailTrace_4960852
  have hstable : (prefixWord ++ tailWord_4960852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960852).length < 2 ^ (prefixWord ++ tailWord_4960852).sum := by decide
  have hdescent : baseEnd_4960852 < baseStart_4960852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960855 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_4960855 : Nat := 118140960795 + 4960855 * 2 ^ 59
def prefixEnd_4960855 : Nat := 4983230072969 + 3 ^ 40 * 4960855 * 2
def baseEnd_4960855 : Nat := 2547303072260293365697949

theorem tailTrace_4960855 : CollatzResearch.WordTrace tailWord_4960855 prefixEnd_4960855 2547303072260293365697949 := by
  unfold tailWord_4960855
  simp only [CollatzResearch.WordTrace]
  refine ⟨180937246442677056426364019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120624830961784704284242679 180937246442677056426364019)
  ·
    refine ⟨271405869664015584639546029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180937246442677056426364019 271405869664015584639546029)
    ·
      refine ⟨101777201124005844239829761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271405869664015584639546029 101777201124005844239829761)
      ·
        refine ⟨76332900843004383179872321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101777201124005844239829761 76332900843004383179872321)
        ·
          refine ⟨57249675632253287384904241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76332900843004383179872321 57249675632253287384904241)
          ·
            refine ⟨42937256724189965538678181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57249675632253287384904241 42937256724189965538678181)
            ·
              refine ⟨8050735635785618538502159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42937256724189965538678181 8050735635785618538502159)
              ·
                refine ⟨12076103453678427807753239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8050735635785618538502159 12076103453678427807753239)
                ·
                  refine ⟨18114155180517641711629859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12076103453678427807753239 18114155180517641711629859)
                  ·
                    refine ⟨27171232770776462567444789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18114155180517641711629859 27171232770776462567444789)
                    ·
                      refine ⟨2547303072260293365697949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27171232770776462567444789 2547303072260293365697949)
                      ·
                        rfl

theorem cell23_4960855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_4960855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960855 prefixEnd_4960855 := by exact prefixLift 4960855
  have htrace : WordTrace (prefixWord ++ tailWord_4960855) baseStart_4960855 baseEnd_4960855 := by
    simpa [prefixWord, tailWord_4960855, baseEnd_4960855] using wordTrace_append hprefix tailTrace_4960855
  have hstable : (prefixWord ++ tailWord_4960855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960855).length < 2 ^ (prefixWord ++ tailWord_4960855).sum := by decide
  have hdescent : baseEnd_4960855 < baseStart_4960855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960886 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_4960886 : Nat := 118140960795 + 4960886 * 2 ^ 59
def prefixEnd_4960886 : Nat := 4983230072969 + 3 ^ 40 * 4960886 * 2
def baseEnd_4960886 : Nat := 2547318990160582744410307

theorem tailTrace_4960886 : CollatzResearch.WordTrace tailWord_4960886 prefixEnd_4960886 2547318990160582744410307 := by
  unfold tailWord_4960886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11308648569097796795046407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120625584737043165813828341 11308648569097796795046407)
  ·
    refine ⟨16962972853646695192569611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11308648569097796795046407 16962972853646695192569611)
    ·
      refine ⟨25444459280470042788854417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16962972853646695192569611 25444459280470042788854417)
      ·
        refine ⟨19083344460352532091640813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25444459280470042788854417 19083344460352532091640813)
        ·
          refine ⟨7156254172632199534365305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19083344460352532091640813 7156254172632199534365305)
          ·
            refine ⟨5367190629474149650773979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7156254172632199534365305 5367190629474149650773979)
            ·
              refine ⟨8050785944211224476160969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5367190629474149650773979 8050785944211224476160969)
              ·
                refine ⟨6038089458158418357120727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8050785944211224476160969 6038089458158418357120727)
                ·
                  refine ⟨9057134187237627535681091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6038089458158418357120727 9057134187237627535681091)
                  ·
                    refine ⟨13585701280856441303521637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9057134187237627535681091 13585701280856441303521637)
                    ·
                      refine ⟨2547318990160582744410307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13585701280856441303521637 2547318990160582744410307)
                      ·
                        rfl

theorem cell23_4960886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_4960886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960886 prefixEnd_4960886 := by exact prefixLift 4960886
  have htrace : WordTrace (prefixWord ++ tailWord_4960886) baseStart_4960886 baseEnd_4960886 := by
    simpa [prefixWord, tailWord_4960886, baseEnd_4960886] using wordTrace_append hprefix tailTrace_4960886
  have hstable : (prefixWord ++ tailWord_4960886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960886).length < 2 ^ (prefixWord ++ tailWord_4960886).sum := by decide
  have hdescent : baseEnd_4960886 < baseStart_4960886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960888 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 2, 7]
def baseStart_4960888 : Nat := 118140960795 + 4960888 * 2 ^ 59
def prefixEnd_4960888 : Nat := 4983230072969 + 3 ^ 40 * 4960888 * 2
def baseEnd_4960888 : Nat := 849106672373963912195099

theorem tailTrace_4960888 : CollatzResearch.WordTrace tailWord_4960888 prefixEnd_4960888 849106672373963912195099 := by
  unfold tailWord_4960888
  simp only [CollatzResearch.WordTrace]
  refine ⟨90469225025778751531157659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120625633367705002041543545 90469225025778751531157659)
  ·
    refine ⟨135703837538668127296736489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90469225025778751531157659 135703837538668127296736489)
    ·
      refine ⟨101777878154001095472552367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135703837538668127296736489 101777878154001095472552367)
      ·
        refine ⟨152666817231001643208828551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101777878154001095472552367 152666817231001643208828551)
        ·
          refine ⟨229000225846502464813242827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152666817231001643208828551 229000225846502464813242827)
          ·
            refine ⟨343500338769753697219864241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229000225846502464813242827 343500338769753697219864241)
            ·
              refine ⟨257625254077315272914898181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343500338769753697219864241 257625254077315272914898181)
              ·
                refine ⟨48304735139496613671543409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257625254077315272914898181 48304735139496613671543409)
                ·
                  refine ⟨36228551354622460253657557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48304735139496613671543409 36228551354622460253657557)
                  ·
                    refine ⟨849106672373963912195099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36228551354622460253657557 849106672373963912195099)
                    ·
                      rfl

theorem cell23_4960888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_4960888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960888 prefixEnd_4960888 := by exact prefixLift 4960888
  have htrace : WordTrace (prefixWord ++ tailWord_4960888) baseStart_4960888 baseEnd_4960888 := by
    simpa [prefixWord, tailWord_4960888, baseEnd_4960888] using wordTrace_append hprefix tailTrace_4960888
  have hstable : (prefixWord ++ tailWord_4960888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960888).length < 2 ^ (prefixWord ++ tailWord_4960888).sum := by decide
  have hdescent : baseEnd_4960888 < baseStart_4960888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960889 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 3]
def baseStart_4960889 : Nat := 118140960795 + 4960889 * 2 ^ 59
def prefixEnd_4960889 : Nat := 4983230072969 + 3 ^ 40 * 4960889 * 2
def baseEnd_4960889 : Nat := 2547320530602546232672793

theorem tailTrace_4960889 : CollatzResearch.WordTrace tailWord_4960889 prefixEnd_4960889 2547320530602546232672793 := by
  unfold tailWord_4960889
  simp only [CollatzResearch.WordTrace]
  refine ⟨180938486524553880233101721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120625657683035920155401147 180938486524553880233101721)
  ·
    refine ⟨135703864893415410174826291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180938486524553880233101721 135703864893415410174826291)
    ·
      refine ⟨203555797340123115262239437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135703864893415410174826291 203555797340123115262239437)
      ·
        refine ⟨76333424002546168223339789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203555797340123115262239437 76333424002546168223339789)
        ·
          refine ⟨28625034000954813083752421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76333424002546168223339789 28625034000954813083752421)
          ·
            refine ⟨5367193875179027453203579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28625034000954813083752421 5367193875179027453203579)
            ·
              refine ⟨8050790812768541179805369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5367193875179027453203579 8050790812768541179805369)
              ·
                refine ⟨6038093109576405884854027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8050790812768541179805369 6038093109576405884854027)
                ·
                  refine ⟨9057139664364608827281041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6038093109576405884854027 9057139664364608827281041)
                  ·
                    refine ⟨6792854748273456620460781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9057139664364608827281041 6792854748273456620460781)
                    ·
                      refine ⟨2547320530602546232672793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6792854748273456620460781 2547320530602546232672793)
                      ·
                        rfl

theorem cell23_4960889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_4960889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960889 prefixEnd_4960889 := by exact prefixLift 4960889
  have htrace : WordTrace (prefixWord ++ tailWord_4960889) baseStart_4960889 baseEnd_4960889 := by
    simpa [prefixWord, tailWord_4960889, baseEnd_4960889] using wordTrace_append hprefix tailTrace_4960889
  have hstable : (prefixWord ++ tailWord_4960889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960889).length < 2 ^ (prefixWord ++ tailWord_4960889).sum := by decide
  have hdescent : baseEnd_4960889 < baseStart_4960889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960906 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_4960906 : Nat := 118140960795 + 4960906 * 2 ^ 59
def prefixEnd_4960906 : Nat := 4983230072969 + 3 ^ 40 * 4960906 * 2
def baseEnd_4960906 : Nat := 2547329259773672666160215

theorem tailTrace_4960906 : CollatzResearch.WordTrace tailWord_4960906 prefixEnd_4960906 2547329259773672666160215 := by
  unfold tailWord_4960906
  simp only [CollatzResearch.WordTrace]
  refine ⟨45234776641373073034117643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120626071043661528090980381 45234776641373073034117643)
  ·
    refine ⟨67852164962059609551176465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45234776641373073034117643 67852164962059609551176465)
    ·
      refine ⟨50889123721544707163382349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67852164962059609551176465 50889123721544707163382349)
      ·
        refine ⟨19083421395579265186268381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50889123721544707163382349 19083421395579265186268381)
        ·
          refine ⟨7156283023342224444850643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19083421395579265186268381 7156283023342224444850643)
          ·
            refine ⟨10734424535013336667275965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7156283023342224444850643 10734424535013336667275965)
            ·
              refine ⟨4025409200630001250228487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10734424535013336667275965 4025409200630001250228487)
              ·
                refine ⟨6038113800945001875342731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025409200630001250228487 6038113800945001875342731)
                ·
                  refine ⟨9057170701417502813014097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6038113800945001875342731 9057170701417502813014097)
                  ·
                    refine ⟨6792878026063127109760573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9057170701417502813014097 6792878026063127109760573)
                    ·
                      refine ⟨2547329259773672666160215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6792878026063127109760573 2547329259773672666160215)
                      ·
                        rfl

theorem cell23_4960906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_4960906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960906 prefixEnd_4960906 := by exact prefixLift 4960906
  have htrace : WordTrace (prefixWord ++ tailWord_4960906) baseStart_4960906 baseEnd_4960906 := by
    simpa [prefixWord, tailWord_4960906, baseEnd_4960906] using wordTrace_append hprefix tailTrace_4960906
  have hstable : (prefixWord ++ tailWord_4960906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960906).length < 2 ^ (prefixWord ++ tailWord_4960906).sum := by decide
  have hdescent : baseEnd_4960906 < baseStart_4960906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960919 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_4960919 : Nat := 118140960795 + 4960919 * 2 ^ 59
def prefixEnd_4960919 : Nat := 4983230072969 + 3 ^ 40 * 4960919 * 2
def baseEnd_4960919 : Nat := 2547335935022181115297655

theorem tailTrace_4960919 : CollatzResearch.WordTrace tailWord_4960919 prefixEnd_4960919 2547335935022181115297655 := by
  unfold tailWord_4960919
  simp only [CollatzResearch.WordTrace]
  refine ⟨180939580714445195356693811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120626387142963463571129207 180939580714445195356693811)
  ·
    refine ⟨271409371071667793035040717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180939580714445195356693811 271409371071667793035040717)
    ·
      refine ⟨101778514151875422388140269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271409371071667793035040717 101778514151875422388140269)
      ·
        refine ⟨38166942806953283395552601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101778514151875422388140269 38166942806953283395552601)
        ·
          refine ⟨28625207105214962546664451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38166942806953283395552601 28625207105214962546664451)
          ·
            refine ⟨42937810657822443819996677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28625207105214962546664451 42937810657822443819996677)
            ·
              refine ⟨8050839498341708216249377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42937810657822443819996677 8050839498341708216249377)
              ·
                refine ⟨6038129623756281162187033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8050839498341708216249377 6038129623756281162187033)
                ·
                  refine ⟨4528597217817210871640275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6038129623756281162187033 4528597217817210871640275)
                  ·
                    refine ⟨6792895826725816307460413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4528597217817210871640275 6792895826725816307460413)
                    ·
                      refine ⟨2547335935022181115297655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6792895826725816307460413 2547335935022181115297655)
                      ·
                        rfl

theorem cell23_4960919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_4960919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960919 prefixEnd_4960919 := by exact prefixLift 4960919
  have htrace : WordTrace (prefixWord ++ tailWord_4960919) baseStart_4960919 baseEnd_4960919 := by
    simpa [prefixWord, tailWord_4960919, baseEnd_4960919] using wordTrace_append hprefix tailTrace_4960919
  have hstable : (prefixWord ++ tailWord_4960919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960919).length < 2 ^ (prefixWord ++ tailWord_4960919).sum := by decide
  have hdescent : baseEnd_4960919 < baseStart_4960919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960925 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_4960925 : Nat := 118140960795 + 4960925 * 2 ^ 59
def prefixEnd_4960925 : Nat := 4983230072969 + 3 ^ 40 * 4960925 * 2
def baseEnd_4960925 : Nat := 2547339015906108091822627

theorem tailTrace_4960925 : CollatzResearch.WordTrace tailWord_4960925 prefixEnd_4960925 2547339015906108091822627 := by
  unfold tailWord_4960925
  simp only [CollatzResearch.WordTrace]
  refine ⟨180939799552423458381412229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120626533034948972254274819 180939799552423458381412229)
  ·
    refine ⟨33926212416079398446514793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180939799552423458381412229 33926212416079398446514793)
    ·
      refine ⟨25444659312059548834886095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33926212416079398446514793 25444659312059548834886095)
      ·
        refine ⟨38166988968089323252329143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25444659312059548834886095 38166988968089323252329143)
        ·
          refine ⟨57250483452133984878493715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38166988968089323252329143 57250483452133984878493715)
          ·
            refine ⟨85875725178200977317740573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57250483452133984878493715 85875725178200977317740573)
            ·
              refine ⟨32203396941825366494152715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85875725178200977317740573 32203396941825366494152715)
              ·
                refine ⟨48305095412738049741229073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32203396941825366494152715 48305095412738049741229073)
                ·
                  refine ⟨36228821559553537305921805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48305095412738049741229073 36228821559553537305921805)
                  ·
                    refine ⟨13585808084832576489720677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36228821559553537305921805 13585808084832576489720677)
                    ·
                      refine ⟨2547339015906108091822627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13585808084832576489720677 2547339015906108091822627)
                      ·
                        rfl

theorem cell23_4960925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_4960925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960925 prefixEnd_4960925 := by exact prefixLift 4960925
  have htrace : WordTrace (prefixWord ++ tailWord_4960925) baseStart_4960925 baseEnd_4960925 := by
    simpa [prefixWord, tailWord_4960925, baseEnd_4960925] using wordTrace_append hprefix tailTrace_4960925
  have hstable : (prefixWord ++ tailWord_4960925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960925).length < 2 ^ (prefixWord ++ tailWord_4960925).sum := by decide
  have hdescent : baseEnd_4960925 < baseStart_4960925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960972 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4960972 : Nat := 118140960795 + 4960972 * 2 ^ 59
def prefixEnd_4960972 : Nat := 4983230072969 + 3 ^ 40 * 4960972 * 2
def baseEnd_4960972 : Nat := 2547363149496869407934911

theorem tailTrace_4960972 : CollatzResearch.WordTrace tailWord_4960972 prefixEnd_4960972 2547363149496869407934911 := by
  unfold tailWord_4960972
  simp only [CollatzResearch.WordTrace]
  refine ⟨90470756891626592704186585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120627675855502123605582113 90470756891626592704186585)
  ·
    refine ⟨67853067668719944528139939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90470756891626592704186585 67853067668719944528139939)
    ·
      refine ⟨101779601503079916792209909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67853067668719944528139939 101779601503079916792209909)
      ·
        refine ⟨9541837640913742199269679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101779601503079916792209909 9541837640913742199269679)
        ·
          refine ⟨14312756461370613298904519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9541837640913742199269679 14312756461370613298904519)
          ·
            refine ⟨21469134692055919948356779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14312756461370613298904519 21469134692055919948356779)
            ·
              refine ⟨32203702038083879922535169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21469134692055919948356779 32203702038083879922535169)
              ·
                refine ⟨24152776528562909941901377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32203702038083879922535169 24152776528562909941901377)
                ·
                  refine ⟨18114582396422182456426033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24152776528562909941901377 18114582396422182456426033)
                  ·
                    refine ⟨13585936797316636842319525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18114582396422182456426033 13585936797316636842319525)
                    ·
                      refine ⟨2547363149496869407934911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13585936797316636842319525 2547363149496869407934911)
                      ·
                        rfl

theorem cell23_4960972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4960972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960972 prefixEnd_4960972 := by exact prefixLift 4960972
  have htrace : WordTrace (prefixWord ++ tailWord_4960972) baseStart_4960972 baseEnd_4960972 := by
    simpa [prefixWord, tailWord_4960972, baseEnd_4960972] using wordTrace_append hprefix tailTrace_4960972
  have hstable : (prefixWord ++ tailWord_4960972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960972).length < 2 ^ (prefixWord ++ tailWord_4960972).sum := by decide
  have hdescent : baseEnd_4960972 < baseStart_4960972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4960993 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_4960993 : Nat := 118140960795 + 4960993 * 2 ^ 59
def prefixEnd_4960993 : Nat := 4983230072969 + 3 ^ 40 * 4960993 * 2
def baseEnd_4960993 : Nat := 2547373932590613825772315

theorem tailTrace_4960993 : CollatzResearch.WordTrace tailWord_4960993 prefixEnd_4960993 2547373932590613825772315 := by
  unfold tailWord_4960993
  simp only [CollatzResearch.WordTrace]
  refine ⟨180942279716177105994887633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120628186477451403996591755 180942279716177105994887633)
  ·
    refine ⟨135706709787132829496165725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180942279716177105994887633 135706709787132829496165725)
    ·
      refine ⟨50890016170174811061062147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135706709787132829496165725 50890016170174811061062147)
      ·
        refine ⟨76335024255262216591593221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50890016170174811061062147 76335024255262216591593221)
        ·
          refine ⟨14312817047861665610923729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76335024255262216591593221 14312817047861665610923729)
          ·
            refine ⟨10734612785896249208192797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14312817047861665610923729 10734612785896249208192797)
            ·
              refine ⟨4025479794711093453072299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10734612785896249208192797 4025479794711093453072299)
              ·
                refine ⟨6038219692066640179608449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025479794711093453072299 6038219692066640179608449)
                ·
                  refine ⟨4528664769049980134706337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6038219692066640179608449 4528664769049980134706337)
                  ·
                    refine ⟨3396498576787485101029753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4528664769049980134706337 3396498576787485101029753)
                    ·
                      refine ⟨2547373932590613825772315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3396498576787485101029753 2547373932590613825772315)
                      ·
                        rfl

theorem cell23_4960993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_4960993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4960993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4960993 prefixEnd_4960993 := by exact prefixLift 4960993
  have htrace : WordTrace (prefixWord ++ tailWord_4960993) baseStart_4960993 baseEnd_4960993 := by
    simpa [prefixWord, tailWord_4960993, baseEnd_4960993] using wordTrace_append hprefix tailTrace_4960993
  have hstable : (prefixWord ++ tailWord_4960993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4960993).length < 2 ^ (prefixWord ++ tailWord_4960993).sum := by decide
  have hdescent : baseEnd_4960993 < baseStart_4960993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4960993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961032 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_4961032 : Nat := 118140960795 + 4961032 * 2 ^ 59
def prefixEnd_4961032 : Nat := 4983230072969 + 3 ^ 40 * 4961032 * 2
def baseEnd_4961032 : Nat := 2547393958336139173184635

theorem tailTrace_4961032 : CollatzResearch.WordTrace tailWord_4961032 prefixEnd_4961032 2547393958336139173184635 := by
  unfold tailWord_4961032
  simp only [CollatzResearch.WordTrace]
  refine ⟨90471851081517907827778675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120629134775357210437038233 90471851081517907827778675)
  ·
    refine ⟨135707776622276861741668013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90471851081517907827778675 135707776622276861741668013)
    ·
      refine ⟨50890416233353823153125505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135707776622276861741668013 50890416233353823153125505)
      ·
        refine ⟨38167812175015367364844129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50890416233353823153125505 38167812175015367364844129)
        ·
          refine ⟨28625859131261525523633097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38167812175015367364844129 28625859131261525523633097)
          ·
            refine ⟨21469394348446144142724823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28625859131261525523633097 21469394348446144142724823)
            ·
              refine ⟨32204091522669216214087235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21469394348446144142724823 32204091522669216214087235)
              ·
                refine ⟨48306137284003824321130853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32204091522669216214087235 48306137284003824321130853)
                ·
                  refine ⟨9057400740750717060212035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48306137284003824321130853 9057400740750717060212035)
                  ·
                    refine ⟨13586101111126075590318053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9057400740750717060212035 13586101111126075590318053)
                    ·
                      refine ⟨2547393958336139173184635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13586101111126075590318053 2547393958336139173184635)
                      ·
                        rfl

theorem cell23_4961032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_4961032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961032 prefixEnd_4961032 := by exact prefixLift 4961032
  have htrace : WordTrace (prefixWord ++ tailWord_4961032) baseStart_4961032 baseEnd_4961032 := by
    simpa [prefixWord, tailWord_4961032, baseEnd_4961032] using wordTrace_append hprefix tailTrace_4961032
  have hstable : (prefixWord ++ tailWord_4961032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961032).length < 2 ^ (prefixWord ++ tailWord_4961032).sum := by decide
  have hdescent : baseEnd_4961032 < baseStart_4961032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961109 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_4961109 : Nat := 118140960795 + 4961109 * 2 ^ 59
def prefixEnd_4961109 : Nat := 4983230072969 + 3 ^ 40 * 4961109 * 2
def baseEnd_4961109 : Nat := 2547433496346535371921781

theorem tailTrace_4961109 : CollatzResearch.WordTrace tailWord_4961109 prefixEnd_4961109 2547433496346535371921781 := by
  unfold tailWord_4961109
  simp only [CollatzResearch.WordTrace]
  refine ⟨180946510583756857806110381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120631007055837905204073587 180946510583756857806110381)
  ·
    refine ⟨67854941468908821677291393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180946510583756857806110381 67854941468908821677291393)
    ·
      refine ⟨50891206101681616257968545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67854941468908821677291393 50891206101681616257968545)
      ·
        refine ⟨38168404576261212193476409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50891206101681616257968545 38168404576261212193476409)
        ·
          refine ⟨28626303432195909145107307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38168404576261212193476409 28626303432195909145107307)
          ·
            refine ⟨42939455148293863717660961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28626303432195909145107307 42939455148293863717660961)
            ·
              refine ⟨32204591361220397788245721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42939455148293863717660961 32204591361220397788245721)
              ·
                refine ⟨24153443520915298341184291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32204591361220397788245721 24153443520915298341184291)
                ·
                  refine ⟨36230165281372947511776437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24153443520915298341184291 36230165281372947511776437)
                  ·
                    refine ⟨3396577995128713829229041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36230165281372947511776437 3396577995128713829229041)
                    ·
                      refine ⟨2547433496346535371921781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3396577995128713829229041 2547433496346535371921781)
                      ·
                        rfl

theorem cell23_4961109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_4961109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961109 prefixEnd_4961109 := by exact prefixLift 4961109
  have htrace : WordTrace (prefixWord ++ tailWord_4961109) baseStart_4961109 baseEnd_4961109 := by
    simpa [prefixWord, tailWord_4961109, baseEnd_4961109] using wordTrace_append hprefix tailTrace_4961109
  have hstable : (prefixWord ++ tailWord_4961109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961109).length < 2 ^ (prefixWord ++ tailWord_4961109).sum := by decide
  have hdescent : baseEnd_4961109 < baseStart_4961109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961116 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_4961116 : Nat := 118140960795 + 4961116 * 2 ^ 59
def prefixEnd_4961116 : Nat := 4983230072969 + 3 ^ 40 * 4961116 * 2
def baseEnd_4961116 : Nat := 2547437090711116844534249

theorem tailTrace_4961116 : CollatzResearch.WordTrace tailWord_4961116 prefixEnd_4961116 2547437090711116844534249 := by
  unfold tailWord_4961116
  simp only [CollatzResearch.WordTrace]
  refine ⟨90473382947365749000807601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120631177263154332001076801 90473382947365749000807601)
  ·
    refine ⟨67855037210524311750605701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90473382947365749000807601 67855037210524311750605701)
    ·
      refine ⟨12722819476973308453238569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67855037210524311750605701 12722819476973308453238569)
      ·
        refine ⟨9542114607729981339928927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12722819476973308453238569 9542114607729981339928927)
        ·
          refine ⟨14313171911594972009893391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9542114607729981339928927 14313171911594972009893391)
          ·
            refine ⟨21469757867392458014840087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14313171911594972009893391 21469757867392458014840087)
            ·
              refine ⟨32204636801088687022260131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21469757867392458014840087 32204636801088687022260131)
              ·
                refine ⟨48306955201633030533390197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32204636801088687022260131 48306955201633030533390197)
                ·
                  refine ⟨4528777050153096612505331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48306955201633030533390197 4528777050153096612505331)
                  ·
                    refine ⟨6793165575229644918757997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4528777050153096612505331 6793165575229644918757997)
                    ·
                      refine ⟨2547437090711116844534249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6793165575229644918757997 2547437090711116844534249)
                      ·
                        rfl

theorem cell23_4961116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_4961116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961116 prefixEnd_4961116 := by exact prefixLift 4961116
  have htrace : WordTrace (prefixWord ++ tailWord_4961116) baseStart_4961116 baseEnd_4961116 := by
    simpa [prefixWord, tailWord_4961116, baseEnd_4961116] using wordTrace_append hprefix tailTrace_4961116
  have hstable : (prefixWord ++ tailWord_4961116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961116).length < 2 ^ (prefixWord ++ tailWord_4961116).sum := by decide
  have hdescent : baseEnd_4961116 < baseStart_4961116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961132 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_4961132 : Nat := 118140960795 + 4961132 * 2 ^ 59
def prefixEnd_4961132 : Nat := 4983230072969 + 3 ^ 40 * 4961132 * 2
def baseEnd_4961132 : Nat := 849148435467196260644725

theorem tailTrace_4961132 : CollatzResearch.WordTrace tailWord_4961132 prefixEnd_4961132 849148435467196260644725 := by
  unfold tailWord_4961132
  simp only [CollatzResearch.WordTrace]
  refine ⟨90473674731336766367098825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120631566308449021822798433 90473674731336766367098825)
  ·
    refine ⟨67855256048502574775324119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90473674731336766367098825 67855256048502574775324119)
    ·
      refine ⟨101782884072753862162986179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67855256048502574775324119 101782884072753862162986179)
      ·
        refine ⟨152674326109130793244479269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101782884072753862162986179 152674326109130793244479269)
        ·
          refine ⟨28626436145462023733339863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152674326109130793244479269 28626436145462023733339863)
          ·
            refine ⟨42939654218193035600009795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28626436145462023733339863 42939654218193035600009795)
            ·
              refine ⟨64409481327289553400014693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42939654218193035600009795 64409481327289553400014693)
              ·
                refine ⟨12076777748866791262502755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64409481327289553400014693 12076777748866791262502755)
                ·
                  refine ⟨18115166623300186893754133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12076777748866791262502755 18115166623300186893754133)
                  ·
                    refine ⟨849148435467196260644725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18115166623300186893754133 849148435467196260644725)
                    ·
                      rfl

theorem cell23_4961132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_4961132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961132 prefixEnd_4961132 := by exact prefixLift 4961132
  have htrace : WordTrace (prefixWord ++ tailWord_4961132) baseStart_4961132 baseEnd_4961132 := by
    simpa [prefixWord, tailWord_4961132, baseEnd_4961132] using wordTrace_append hprefix tailTrace_4961132
  have hstable : (prefixWord ++ tailWord_4961132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961132).length < 2 ^ (prefixWord ++ tailWord_4961132).sum := by decide
  have hdescent : baseEnd_4961132 < baseStart_4961132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961150 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4961150 : Nat := 118140960795 + 4961150 * 2 ^ 59
def prefixEnd_4961150 : Nat := 4983230072969 + 3 ^ 40 * 4961150 * 2
def baseEnd_4961150 : Nat := 2547454549053369711509093

theorem tailTrace_4961150 : CollatzResearch.WordTrace tailWord_4961150 prefixEnd_4961150 2547454549053369711509093 := by
  unfold tailWord_4961150
  simp only [CollatzResearch.WordTrace]
  refine ⟨22618500747076040226044113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120632003984405547872235269 22618500747076040226044113)
  ·
    refine ⟨16963875560307030169533085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22618500747076040226044113 16963875560307030169533085)
    ·
      refine ⟨6361453335115136313574907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16963875560307030169533085 6361453335115136313574907)
      ·
        refine ⟨9542180002672704470362361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6361453335115136313574907 9542180002672704470362361)
        ·
          refine ⟨7156635002004528352771771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9542180002672704470362361 7156635002004528352771771)
          ·
            refine ⟨10734952503006792529157657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7156635002004528352771771 10734952503006792529157657)
            ·
              refine ⟨8051214377255094396868243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10734952503006792529157657 8051214377255094396868243)
              ·
                refine ⟨12076821565882641595302365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8051214377255094396868243 12076821565882641595302365)
                ·
                  refine ⟨4528808087205990598238387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12076821565882641595302365 4528808087205990598238387)
                  ·
                    refine ⟨6793212130808985897357581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4528808087205990598238387 6793212130808985897357581)
                    ·
                      refine ⟨2547454549053369711509093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6793212130808985897357581 2547454549053369711509093)
                      ·
                        rfl

theorem cell23_4961150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4961150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961150 prefixEnd_4961150 := by exact prefixLift 4961150
  have htrace : WordTrace (prefixWord ++ tailWord_4961150) baseStart_4961150 baseEnd_4961150 := by
    simpa [prefixWord, tailWord_4961150, baseEnd_4961150] using wordTrace_append hprefix tailTrace_4961150
  have hstable : (prefixWord ++ tailWord_4961150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961150).length < 2 ^ (prefixWord ++ tailWord_4961150).sum := by decide
  have hdescent : baseEnd_4961150 < baseStart_4961150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961159 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_4961159 : Nat := 118140960795 + 4961159 * 2 ^ 59
def prefixEnd_4961159 : Nat := 4983230072969 + 3 ^ 40 * 4961159 * 2
def baseEnd_4961159 : Nat := 2547459170379260176296551

theorem tailTrace_4961159 : CollatzResearch.WordTrace tailWord_4961159 prefixEnd_4961159 2547459170379260176296551 := by
  unfold tailWord_4961159
  simp only [CollatzResearch.WordTrace]
  refine ⟨180948334233575716345430531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120632222822383810896953687 180948334233575716345430531)
  ·
    refine ⟨271422501350363574518145797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180948334233575716345430531 271422501350363574518145797)
    ·
      refine ⟨50891719003193170222152337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271422501350363574518145797 50891719003193170222152337)
      ·
        refine ⟨38168789252394877666614253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50891719003193170222152337 38168789252394877666614253)
        ·
          refine ⟨14313295969648079124980345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38168789252394877666614253 14313295969648079124980345)
          ·
            refine ⟨10734971977236059343735259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14313295969648079124980345 10734971977236059343735259)
            ·
              refine ⟨16102457965854089015602889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10734971977236059343735259 16102457965854089015602889)
              ·
                refine ⟨12076843474390566761702167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16102457965854089015602889 12076843474390566761702167)
                ·
                  refine ⟨18115265211585850142553251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12076843474390566761702167 18115265211585850142553251)
                  ·
                    refine ⟨27172897817378775213829877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18115265211585850142553251 27172897817378775213829877)
                    ·
                      refine ⟨2547459170379260176296551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27172897817378775213829877 2547459170379260176296551)
                      ·
                        rfl

theorem cell23_4961159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_4961159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961159 prefixEnd_4961159 := by exact prefixLift 4961159
  have htrace : WordTrace (prefixWord ++ tailWord_4961159) baseStart_4961159 baseEnd_4961159 := by
    simpa [prefixWord, tailWord_4961159, baseEnd_4961159] using wordTrace_append hprefix tailTrace_4961159
  have hstable : (prefixWord ++ tailWord_4961159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961159).length < 2 ^ (prefixWord ++ tailWord_4961159).sum := by decide
  have hdescent : baseEnd_4961159 < baseStart_4961159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961223 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_4961223 : Nat := 118140960795 + 4961223 * 2 ^ 59
def prefixEnd_4961223 : Nat := 4983230072969 + 3 ^ 40 * 4961223 * 2
def baseEnd_4961223 : Nat := 2547492033141147925896257

theorem tailTrace_4961223 : CollatzResearch.WordTrace tailWord_4961223 prefixEnd_4961223 2547492033141147925896257 := by
  unfold tailWord_4961223
  simp only [CollatzResearch.WordTrace]
  refine ⟨180950668505343855275760323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120633779003562570183840215 180950668505343855275760323)
  ·
    refine ⟨271426002758015782913640485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180950668505343855275760323 271426002758015782913640485)
    ·
      refine ⟨50892375517127959296307591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271426002758015782913640485 50892375517127959296307591)
      ·
        refine ⟨76338563275691938944461387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50892375517127959296307591 76338563275691938944461387)
        ·
          refine ⟨114507844913537908416692081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76338563275691938944461387 114507844913537908416692081)
          ·
            refine ⟨85880883685153431312519061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114507844913537908416692081 85880883685153431312519061)
            ·
              refine ⟨4025666422741567092774331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85880883685153431312519061 4025666422741567092774331)
              ·
                refine ⟨6038499634112350639161497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025666422741567092774331 6038499634112350639161497)
                ·
                  refine ⟨4528874725584262979371123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6038499634112350639161497 4528874725584262979371123)
                  ·
                    refine ⟨6793312088376394469056685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4528874725584262979371123 6793312088376394469056685)
                    ·
                      refine ⟨2547492033141147925896257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6793312088376394469056685 2547492033141147925896257)
                      ·
                        rfl

theorem cell23_4961223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_4961223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961223 prefixEnd_4961223 := by exact prefixLift 4961223
  have htrace : WordTrace (prefixWord ++ tailWord_4961223) baseStart_4961223 baseEnd_4961223 := by
    simpa [prefixWord, tailWord_4961223, baseEnd_4961223] using wordTrace_append hprefix tailTrace_4961223
  have hstable : (prefixWord ++ tailWord_4961223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961223).length < 2 ^ (prefixWord ++ tailWord_4961223).sum := by decide
  have hdescent : baseEnd_4961223 < baseStart_4961223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961252 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 11]
def baseStart_4961252 : Nat := 118140960795 + 4961252 * 2 ^ 59
def prefixEnd_4961252 : Nat := 4983230072969 + 3 ^ 40 * 4961252 * 2
def baseEnd_4961252 : Nat := 283056324897792034714847

theorem tailTrace_4961252 : CollatzResearch.WordTrace tailWord_4961252 prefixEnd_4961252 283056324897792034714847 := by
  unfold tailWord_4961252
  simp only [CollatzResearch.WordTrace]
  refine ⟨90475863111119396614283005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120634484148159195485710673 90475863111119396614283005)
  ·
    refine ⟨33928448666669773730356127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90475863111119396614283005 33928448666669773730356127)
    ·
      refine ⟨50892673000004660595534191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33928448666669773730356127 50892673000004660595534191)
      ·
        refine ⟨76339009500006990893301287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50892673000004660595534191 76339009500006990893301287)
        ·
          refine ⟨114508514250010486339951931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76339009500006990893301287 114508514250010486339951931)
          ·
            refine ⟨171762771375015729509927897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114508514250010486339951931 171762771375015729509927897)
            ·
              refine ⟨128822078531261797132445923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171762771375015729509927897 128822078531261797132445923)
              ·
                refine ⟨193233117796892695698668885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128822078531261797132445923 193233117796892695698668885)
                ·
                  refine ⟨283056324897792034714847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 193233117796892695698668885 283056324897792034714847)
                  ·
                    rfl

theorem cell23_4961252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_4961252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961252 prefixEnd_4961252 := by exact prefixLift 4961252
  have htrace : WordTrace (prefixWord ++ tailWord_4961252) baseStart_4961252 baseEnd_4961252 := by
    simpa [prefixWord, tailWord_4961252, baseEnd_4961252] using wordTrace_append hprefix tailTrace_4961252
  have hstable : (prefixWord ++ tailWord_4961252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961252).length < 2 ^ (prefixWord ++ tailWord_4961252).sum := by decide
  have hdescent : baseEnd_4961252 < baseStart_4961252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961263 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 2, 2, 2]
def baseStart_4961263 : Nat := 118140960795 + 4961263 * 2 ^ 59
def prefixEnd_4961263 : Nat := 4983230072969 + 3 ^ 40 * 4961263 * 2
def baseEnd_4961263 : Nat := 2547512572367327769396073

theorem tailTrace_4961263 : CollatzResearch.WordTrace tailWord_4961263 prefixEnd_4961263 2547512572367327769396073 := by
  unfold tailWord_4961263
  simp only [CollatzResearch.WordTrace]
  refine ⟨180952127425198942107216443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120634751616799294738144295 180952127425198942107216443)
  ·
    refine ⟨271428191137798413160824665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180952127425198942107216443 271428191137798413160824665)
    ·
      refine ⟨203571143353348809870618499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271428191137798413160824665 203571143353348809870618499)
      ·
        refine ⟨305356715030023214805927749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203571143353348809870618499 305356715030023214805927749)
        ·
          refine ⟨57254384068129352776111453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305356715030023214805927749 57254384068129352776111453)
          ·
            refine ⟨21470394025548507291041795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57254384068129352776111453 21470394025548507291041795)
            ·
              refine ⟨32205591038322760936562693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21470394025548507291041795 32205591038322760936562693)
              ·
                refine ⟨6038548319685517675605505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32205591038322760936562693 6038548319685517675605505)
                ·
                  refine ⟨4528911239764138256704129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6038548319685517675605505 4528911239764138256704129)
                  ·
                    refine ⟨3396683429823103692528097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4528911239764138256704129 3396683429823103692528097)
                    ·
                      refine ⟨2547512572367327769396073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3396683429823103692528097 2547512572367327769396073)
                      ·
                        rfl

theorem cell23_4961263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 2, 2].length) (baseStart_4961263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961263 prefixEnd_4961263 := by exact prefixLift 4961263
  have htrace : WordTrace (prefixWord ++ tailWord_4961263) baseStart_4961263 baseEnd_4961263 := by
    simpa [prefixWord, tailWord_4961263, baseEnd_4961263] using wordTrace_append hprefix tailTrace_4961263
  have hstable : (prefixWord ++ tailWord_4961263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961263).length < 2 ^ (prefixWord ++ tailWord_4961263).sum := by decide
  have hdescent : baseEnd_4961263 < baseStart_4961263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961272 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_4961272 : Nat := 118140960795 + 4961272 * 2 ^ 59
def prefixEnd_4961272 : Nat := 4983230072969 + 3 ^ 40 * 4961272 * 2
def baseEnd_4961272 : Nat := 2547517193693218234183531

theorem tailTrace_4961272 : CollatzResearch.WordTrace tailWord_4961272 prefixEnd_4961272 2547517193693218234183531 := by
  unfold tailWord_4961272
  simp only [CollatzResearch.WordTrace]
  refine ⟨90476227841083168322147035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120634970454777557762862713 90476227841083168322147035)
  ·
    refine ⟨135714341761624752483220553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90476227841083168322147035 135714341761624752483220553)
    ·
      refine ⟨101785756321218564362415415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135714341761624752483220553 101785756321218564362415415)
      ·
        refine ⟨152678634481827846543623123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101785756321218564362415415 152678634481827846543623123)
        ·
          refine ⟨229017951722741769815434685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152678634481827846543623123 229017951722741769815434685)
          ·
            refine ⟨85881731896028163680788007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229017951722741769815434685 85881731896028163680788007)
            ·
              refine ⟨128822597844042245521182011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85881731896028163680788007 128822597844042245521182011)
              ·
                refine ⟨193233896766063368281773017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128822597844042245521182011 193233896766063368281773017)
                ·
                  refine ⟨144925422574547526211329763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193233896766063368281773017 144925422574547526211329763)
                  ·
                    refine ⟨217388133861821289316994645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 144925422574547526211329763 217388133861821289316994645)
                    ·
                      refine ⟨2547517193693218234183531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 217388133861821289316994645 2547517193693218234183531)
                      ·
                        rfl

theorem cell23_4961272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_4961272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961272 prefixEnd_4961272 := by exact prefixLift 4961272
  have htrace : WordTrace (prefixWord ++ tailWord_4961272) baseStart_4961272 baseEnd_4961272 := by
    simpa [prefixWord, tailWord_4961272, baseEnd_4961272] using wordTrace_append hprefix tailTrace_4961272
  have hstable : (prefixWord ++ tailWord_4961272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961272).length < 2 ^ (prefixWord ++ tailWord_4961272).sum := by decide
  have hdescent : baseEnd_4961272 < baseStart_4961272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961303 : List Nat := [1, 1, 3, 5, 1, 2, 2, 3, 5]
def baseStart_4961303 : Nat := 118140960795 + 4961303 * 2 ^ 59
def prefixEnd_4961303 : Nat := 4983230072969 + 3 ^ 40 * 4961303 * 2
def baseEnd_4961303 : Nat := 283059234621500845877321

theorem tailTrace_4961303 : CollatzResearch.WordTrace tailWord_4961303 prefixEnd_4961303 283059234621500845877321 := by
  unfold tailWord_4961303
  simp only [CollatzResearch.WordTrace]
  refine ⟨180953586345054028938672563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120635724230036019292448375 180953586345054028938672563)
  ·
    refine ⟨271430379517581043408008845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180953586345054028938672563 271430379517581043408008845)
    ·
      refine ⟨101786392319092891278003317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271430379517581043408008845 101786392319092891278003317)
      ·
        refine ⟨9542474279914958557312811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101786392319092891278003317 9542474279914958557312811)
        ·
          refine ⟨14313711419872437835969217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9542474279914958557312811 14313711419872437835969217)
          ·
            refine ⟨10735283564904328376976913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14313711419872437835969217 10735283564904328376976913)
            ·
              refine ⟨8051462673678246282732685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10735283564904328376976913 8051462673678246282732685)
              ·
                refine ⟨3019298502629342356024757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8051462673678246282732685 3019298502629342356024757)
                ·
                  refine ⟨283059234621500845877321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3019298502629342356024757 283059234621500845877321)
                  ·
                    rfl

theorem cell23_4961303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 5].length) (baseStart_4961303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961303 prefixEnd_4961303 := by exact prefixLift 4961303
  have htrace : WordTrace (prefixWord ++ tailWord_4961303) baseStart_4961303 baseEnd_4961303 := by
    simpa [prefixWord, tailWord_4961303, baseEnd_4961303] using wordTrace_append hprefix tailTrace_4961303
  have hstable : (prefixWord ++ tailWord_4961303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961303).length < 2 ^ (prefixWord ++ tailWord_4961303).sum := by decide
  have hdescent : baseEnd_4961303 < baseStart_4961303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961356 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_4961356 : Nat := 118140960795 + 4961356 * 2 ^ 59
def prefixEnd_4961356 : Nat := 4983230072969 + 3 ^ 40 * 4961356 * 2
def baseEnd_4961356 : Nat := 2547560326068195905533145

theorem tailTrace_4961356 : CollatzResearch.WordTrace tailWord_4961356 prefixEnd_4961356 2547560326068195905533145 := by
  unfold tailWord_4961356
  simp only [CollatzResearch.WordTrace]
  refine ⟨90477759706931009495175961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120637012942574679326901281 90477759706931009495175961)
  ·
    refine ⟨67858319780198257121381971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90477759706931009495175961 67858319780198257121381971)
    ·
      refine ⟨101787479670297385682072957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67858319780198257121381971 101787479670297385682072957)
      ·
        refine ⟨38170304876361519630777359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101787479670297385682072957 38170304876361519630777359)
        ·
          refine ⟨57255457314542279446166039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38170304876361519630777359 57255457314542279446166039)
          ·
            refine ⟨85883185971813419169249059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57255457314542279446166039 85883185971813419169249059)
            ·
              refine ⟨128824778957720128753873589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85883185971813419169249059 128824778957720128753873589)
              ·
                refine ⟨12077323027286262070675649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128824778957720128753873589 12077323027286262070675649)
                ·
                  refine ⟨9057992270464696553006737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12077323027286262070675649 9057992270464696553006737)
                  ·
                    refine ⟨6793494202848522414755053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9057992270464696553006737 6793494202848522414755053)
                    ·
                      refine ⟨2547560326068195905533145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6793494202848522414755053 2547560326068195905533145)
                      ·
                        rfl

theorem cell23_4961356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_4961356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961356 prefixEnd_4961356 := by exact prefixLift 4961356
  have htrace : WordTrace (prefixWord ++ tailWord_4961356) baseStart_4961356 baseEnd_4961356 := by
    simpa [prefixWord, tailWord_4961356, baseEnd_4961356] using wordTrace_append hprefix tailTrace_4961356
  have hstable : (prefixWord ++ tailWord_4961356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961356).length < 2 ^ (prefixWord ++ tailWord_4961356).sum := by decide
  have hdescent : baseEnd_4961356 < baseStart_4961356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961443 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 7, 2, 2]
def baseStart_4961443 : Nat := 118140960795 + 4961443 * 2 ^ 59
def prefixEnd_4961443 : Nat := 4983230072969 + 3 ^ 40 * 4961443 * 2
def baseEnd_4961443 : Nat := 2547604998885137065145245

theorem tailTrace_4961443 : CollatzResearch.WordTrace tailWord_4961443 prefixEnd_4961443 2547604998885137065145245 := by
  unfold tailWord_4961443
  simp only [CollatzResearch.WordTrace]
  refine ⟨180958692564546832848768983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120639128376364555232512655 180958692564546832848768983)
  ·
    refine ⟨271438038846820249273153475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180958692564546832848768983 271438038846820249273153475)
    ·
      refine ⟨407157058270230373909730213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271438038846820249273153475 407157058270230373909730213)
      ·
        refine ⟨76341948425668195108074415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407157058270230373909730213 76341948425668195108074415)
        ·
          refine ⟨114512922638502292662111623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76341948425668195108074415 114512922638502292662111623)
          ·
            refine ⟨171769383957753438993167435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114512922638502292662111623 171769383957753438993167435)
            ·
              refine ⟨257654075936630158489751153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171769383957753438993167435 257654075936630158489751153)
              ·
                refine ⟨193240556952472618867313365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257654075936630158489751153 193240556952472618867313365)
                ·
                  refine ⟨4529075553573577004702657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 193240556952472618867313365 4529075553573577004702657)
                  ·
                    refine ⟨3396806665180182753526993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4529075553573577004702657 3396806665180182753526993)
                    ·
                      refine ⟨2547604998885137065145245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3396806665180182753526993 2547604998885137065145245)
                      ·
                        rfl

theorem cell23_4961443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_4961443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961443 prefixEnd_4961443 := by exact prefixLift 4961443
  have htrace : WordTrace (prefixWord ++ tailWord_4961443) baseStart_4961443 baseEnd_4961443 := by
    simpa [prefixWord, tailWord_4961443, baseEnd_4961443] using wordTrace_append hprefix tailTrace_4961443
  have hstable : (prefixWord ++ tailWord_4961443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961443).length < 2 ^ (prefixWord ++ tailWord_4961443).sum := by decide
  have hdescent : baseEnd_4961443 < baseStart_4961443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961463 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_4961463 : Nat := 118140960795 + 4961463 * 2 ^ 59
def prefixEnd_4961463 : Nat := 4983230072969 + 3 ^ 40 * 4961463 * 2
def baseEnd_4961463 : Nat := 2547615268498226986895153

theorem tailTrace_4961463 : CollatzResearch.WordTrace tailWord_4961463 prefixEnd_4961463 2547615268498226986895153 := by
  unfold tailWord_4961463
  simp only [CollatzResearch.WordTrace]
  refine ⟨180959422024474376264497043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120639614682982917509664695 180959422024474376264497043)
  ·
    refine ⟨271439133036711564396745565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180959422024474376264497043 271439133036711564396745565)
    ·
      refine ⟨101789674888766836648779587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271439133036711564396745565 101789674888766836648779587)
      ·
        refine ⟨152684512333150254973169381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101789674888766836648779587 152684512333150254973169381)
        ·
          refine ⟨28628346062465672807469259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152684512333150254973169381 28628346062465672807469259)
          ·
            refine ⟨42942519093698509211203889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28628346062465672807469259 42942519093698509211203889)
            ·
              refine ⟨32206889320273881908402917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42942519093698509211203889 32206889320273881908402917)
              ·
                refine ⟨6038791747551352857825547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32206889320273881908402917 6038791747551352857825547)
                ·
                  refine ⟨9058187621327029286738321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6038791747551352857825547 9058187621327029286738321)
                  ·
                    refine ⟨6793640715995271965053741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9058187621327029286738321 6793640715995271965053741)
                    ·
                      refine ⟨2547615268498226986895153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6793640715995271965053741 2547615268498226986895153)
                      ·
                        rfl

theorem cell23_4961463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_4961463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961463 prefixEnd_4961463 := by exact prefixLift 4961463
  have htrace : WordTrace (prefixWord ++ tailWord_4961463) baseStart_4961463 baseEnd_4961463 := by
    simpa [prefixWord, tailWord_4961463, baseEnd_4961463] using wordTrace_append hprefix tailTrace_4961463
  have hstable : (prefixWord ++ tailWord_4961463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961463).length < 2 ^ (prefixWord ++ tailWord_4961463).sum := by decide
  have hdescent : baseEnd_4961463 < baseStart_4961463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961480 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_4961480 : Nat := 118140960795 + 4961480 * 2 ^ 59
def prefixEnd_4961480 : Nat := 4983230072969 + 3 ^ 40 * 4961480 * 2
def baseEnd_4961480 : Nat := 2547623997669353420382575

theorem tailTrace_4961480 : CollatzResearch.WordTrace tailWord_4961480 prefixEnd_4961480 2547623997669353420382575 := by
  unfold tailWord_4961480
  simp only [CollatzResearch.WordTrace]
  refine ⟨90480021032706394083932947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120640028043608525445243929 90480021032706394083932947)
  ·
    refine ⟨135720031549059591125899421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90480021032706394083932947 135720031549059591125899421)
    ·
      refine ⟨50895011830897346672212283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135720031549059591125899421 50895011830897346672212283)
      ·
        refine ⟨76342517746346020008318425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50895011830897346672212283 76342517746346020008318425)
        ·
          refine ⟨57256888309759515006238819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76342517746346020008318425 57256888309759515006238819)
          ·
            refine ⟨85885332464639272509358229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57256888309759515006238819 85885332464639272509358229)
            ·
              refine ⟨4025874959279965898876167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85885332464639272509358229 4025874959279965898876167)
              ·
                refine ⟨6038812438919948848314251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4025874959279965898876167 6038812438919948848314251)
                ·
                  refine ⟨9058218658379923272471377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6038812438919948848314251 9058218658379923272471377)
                  ·
                    refine ⟨6793663993784942454353533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9058218658379923272471377 6793663993784942454353533)
                    ·
                      refine ⟨2547623997669353420382575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6793663993784942454353533 2547623997669353420382575)
                      ·
                        rfl

theorem cell23_4961480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_4961480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961480 prefixEnd_4961480 := by exact prefixLift 4961480
  have htrace : WordTrace (prefixWord ++ tailWord_4961480) baseStart_4961480 baseEnd_4961480 := by
    simpa [prefixWord, tailWord_4961480, baseEnd_4961480] using wordTrace_append hprefix tailTrace_4961480
  have hstable : (prefixWord ++ tailWord_4961480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961480).length < 2 ^ (prefixWord ++ tailWord_4961480).sum := by decide
  have hdescent : baseEnd_4961480 < baseStart_4961480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961499 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 10]
def baseStart_4961499 : Nat := 118140960795 + 4961499 * 2 ^ 59
def prefixEnd_4961499 : Nat := 4983230072969 + 3 ^ 40 * 4961499 * 2
def baseEnd_4961499 : Nat := 2547633753801788846044987

theorem tailTrace_4961499 : CollatzResearch.WordTrace tailWord_4961499 prefixEnd_4961499 2547633753801788846044987 := by
  unfold tailWord_4961499
  simp only [CollatzResearch.WordTrace]
  refine ⟨180960735052343954412807551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120640490034895969608538367 180960735052343954412807551)
  ·
    refine ⟨271441102578515931619211327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180960735052343954412807551 271441102578515931619211327)
    ·
      refine ⟨407161653867773897428816991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271441102578515931619211327 407161653867773897428816991)
      ·
        refine ⟨610742480801660846143225487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407161653867773897428816991 610742480801660846143225487)
        ·
          refine ⟨916113721202491269214838231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610742480801660846143225487 916113721202491269214838231)
          ·
            refine ⟨1374170581803736903822257347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916113721202491269214838231 1374170581803736903822257347)
            ·
              refine ⟨2061255872705605355733386021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374170581803736903822257347 2061255872705605355733386021)
              ·
                refine ⟨386485476132301004200009879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2061255872705605355733386021 386485476132301004200009879)
                ·
                  refine ⟨579728214198451506300014819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386485476132301004200009879 579728214198451506300014819)
                  ·
                    refine ⟨869592321297677259450022229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579728214198451506300014819 869592321297677259450022229)
                    ·
                      refine ⟨2547633753801788846044987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 869592321297677259450022229 2547633753801788846044987)
                      ·
                        rfl

theorem cell23_4961499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_4961499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961499 prefixEnd_4961499 := by exact prefixLift 4961499
  have htrace : WordTrace (prefixWord ++ tailWord_4961499) baseStart_4961499 baseEnd_4961499 := by
    simpa [prefixWord, tailWord_4961499, baseEnd_4961499] using wordTrace_append hprefix tailTrace_4961499
  have hstable : (prefixWord ++ tailWord_4961499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961499).length < 2 ^ (prefixWord ++ tailWord_4961499).sum := by decide
  have hdescent : baseEnd_4961499 < baseStart_4961499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961503 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 5, 3, 2]
def baseStart_4961503 : Nat := 118140960795 + 4961503 * 2 ^ 59
def prefixEnd_4961503 : Nat := 4983230072969 + 3 ^ 40 * 4961503 * 2
def baseEnd_4961503 : Nat := 2547635807724406830394969

theorem tailTrace_4961503 : CollatzResearch.WordTrace tailWord_4961503 prefixEnd_4961503 2547635807724406830394969 := by
  unfold tailWord_4961503
  simp only [CollatzResearch.WordTrace]
  refine ⟨180960880944329463095953163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120640587296219642063968775 180960880944329463095953163)
  ·
    refine ⟨271441321416494194643929745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180960880944329463095953163 271441321416494194643929745)
    ·
      refine ⟨203580991062370645982947309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271441321416494194643929745 203580991062370645982947309)
      ·
        refine ⟨76342871648388992243605241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203580991062370645982947309 76342871648388992243605241)
        ·
          refine ⟨57257153736291744182703931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76342871648388992243605241 57257153736291744182703931)
          ·
            refine ⟨85885730604437616274055897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57257153736291744182703931 85885730604437616274055897)
            ·
              refine ⟨64414297953328212205541923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85885730604437616274055897 64414297953328212205541923)
              ·
                refine ⟨96621446929992318308312885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64414297953328212205541923 96621446929992318308312885)
                ·
                  refine ⟨9058260649686779841404333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96621446929992318308312885 9058260649686779841404333)
                  ·
                    refine ⟨3396847743632542440526625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9058260649686779841404333 3396847743632542440526625)
                    ·
                      refine ⟨2547635807724406830394969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3396847743632542440526625 2547635807724406830394969)
                      ·
                        rfl

theorem cell23_4961503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_4961503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961503 prefixEnd_4961503 := by exact prefixLift 4961503
  have htrace : WordTrace (prefixWord ++ tailWord_4961503) baseStart_4961503 baseEnd_4961503 := by
    simpa [prefixWord, tailWord_4961503, baseEnd_4961503] using wordTrace_append hprefix tailTrace_4961503
  have hstable : (prefixWord ++ tailWord_4961503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961503).length < 2 ^ (prefixWord ++ tailWord_4961503).sum := by decide
  have hdescent : baseEnd_4961503 < baseStart_4961503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961536 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 3]
def baseStart_4961536 : Nat := 118140960795 + 4961536 * 2 ^ 59
def prefixEnd_4961536 : Nat := 4983230072969 + 3 ^ 40 * 4961536 * 2
def baseEnd_4961536 : Nat := 2547652752586005201282317

theorem tailTrace_4961536 : CollatzResearch.WordTrace tailWord_4961536 prefixEnd_4961536 2547652752586005201282317 := by
  unfold tailWord_4961536
  simp only [CollatzResearch.WordTrace]
  refine ⟨90481042276604954865952231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120641389702139939821269641 90481042276604954865952231)
  ·
    refine ⟨135721563414907432298928347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90481042276604954865952231 135721563414907432298928347)
    ·
      refine ⟨203582345122361148448392521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135721563414907432298928347 203582345122361148448392521)
      ·
        refine ⟨152686758841770861336294391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203582345122361148448392521 152686758841770861336294391)
        ·
          refine ⟨229030138262656292004441587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152686758841770861336294391 229030138262656292004441587)
          ·
            refine ⟨343545207393984438006662381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229030138262656292004441587 343545207393984438006662381)
            ·
              refine ⟨128829452772744164252498393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343545207393984438006662381 128829452772744164252498393)
              ·
                refine ⟨96622089579558123189373795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128829452772744164252498393 96622089579558123189373795)
                ·
                  refine ⟨144933134369337184784060693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96622089579558123189373795 144933134369337184784060693)
                  ·
                    refine ⟨6793740673562680536752845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 144933134369337184784060693 6793740673562680536752845)
                    ·
                      refine ⟨2547652752586005201282317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6793740673562680536752845 2547652752586005201282317)
                      ·
                        rfl

theorem cell23_4961536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_4961536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961536 prefixEnd_4961536 := by exact prefixLift 4961536
  have htrace : WordTrace (prefixWord ++ tailWord_4961536) baseStart_4961536 baseEnd_4961536 := by
    simpa [prefixWord, tailWord_4961536, baseEnd_4961536] using wordTrace_append hprefix tailTrace_4961536
  have hstable : (prefixWord ++ tailWord_4961536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961536).length < 2 ^ (prefixWord ++ tailWord_4961536).sum := by decide
  have hdescent : baseEnd_4961536 < baseStart_4961536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961607 : List Nat := [1, 1, 4, 1, 2, 5, 2, 2, 5]
def baseStart_4961607 : Nat := 118140960795 + 4961607 * 2 ^ 59
def prefixEnd_4961607 : Nat := 4983230072969 + 3 ^ 40 * 4961607 * 2
def baseEnd_4961607 : Nat := 283076578856941602610499

theorem tailTrace_4961607 : CollatzResearch.WordTrace tailWord_4961607 prefixEnd_4961607 283076578856941602610499 := by
  unfold tailWord_4961607
  simp only [CollatzResearch.WordTrace]
  refine ⟨180964674135952688857739075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120643116090635125905159383 180964674135952688857739075)
  ·
    refine ⟨271447011203929033286608613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180964674135952688857739075 271447011203929033286608613)
    ·
      refine ⟨50896314600736693741239115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271447011203929033286608613 50896314600736693741239115)
      ·
        refine ⟨76344471901105040611858673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50896314600736693741239115 76344471901105040611858673)
        ·
          refine ⟨57258353925828780458894005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76344471901105040611858673 57258353925828780458894005)
          ·
            refine ⟨5367970680546448168021313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57258353925828780458894005 5367970680546448168021313)
            ·
              refine ⟨4025978010409836126015985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5367970680546448168021313 4025978010409836126015985)
              ·
                refine ⟨3019483507807377094511989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4025978010409836126015985 3019483507807377094511989)
                ·
                  refine ⟨283076578856941602610499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3019483507807377094511989 283076578856941602610499)
                  ·
                    rfl

theorem cell23_4961607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 5].length) (baseStart_4961607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961607 prefixEnd_4961607 := by exact prefixLift 4961607
  have htrace : WordTrace (prefixWord ++ tailWord_4961607) baseStart_4961607 baseEnd_4961607 := by
    simpa [prefixWord, tailWord_4961607, baseEnd_4961607] using wordTrace_append hprefix tailTrace_4961607
  have hstable : (prefixWord ++ tailWord_4961607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961607).length < 2 ^ (prefixWord ++ tailWord_4961607).sum := by decide
  have hdescent : baseEnd_4961607 < baseStart_4961607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961640 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4961640 : Nat := 118140960795 + 4961640 * 2 ^ 59
def prefixEnd_4961640 : Nat := 4983230072969 + 3 ^ 40 * 4961640 * 2
def baseEnd_4961640 : Nat := 2547706154574072794381839

theorem tailTrace_4961640 : CollatzResearch.WordTrace tailWord_4961640 prefixEnd_4961640 2547706154574072794381839 := by
  unfold tailWord_4961640
  simp only [CollatzResearch.WordTrace]
  refine ⟨90482938872416567746845187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120643918496555423662460249 90482938872416567746845187)
  ·
    refine ⟨135724408308624851620267781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90482938872416567746845187 135724408308624851620267781)
    ·
      refine ⟨25448326557867159678800209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135724408308624851620267781 25448326557867159678800209)
      ·
        refine ⟨19086244918400369759100157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25448326557867159678800209 19086244918400369759100157)
        ·
          refine ⟨7157341844400138659662559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19086244918400369759100157 7157341844400138659662559)
          ·
            refine ⟨10736012766600207989493839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7157341844400138659662559 10736012766600207989493839)
            ·
              refine ⟨16104019149900311984240759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10736012766600207989493839 16104019149900311984240759)
              ·
                refine ⟨24156028724850467976361139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16104019149900311984240759 24156028724850467976361139)
                ·
                  refine ⟨36234043087275701964541709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24156028724850467976361139 36234043087275701964541709)
                  ·
                    refine ⟨13587766157728388236703141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36234043087275701964541709 13587766157728388236703141)
                    ·
                      refine ⟨2547706154574072794381839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13587766157728388236703141 2547706154574072794381839)
                      ·
                        rfl

theorem cell23_4961640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4961640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961640 prefixEnd_4961640 := by exact prefixLift 4961640
  have htrace : WordTrace (prefixWord ++ tailWord_4961640) baseStart_4961640 baseEnd_4961640 := by
    simpa [prefixWord, tailWord_4961640, baseEnd_4961640] using wordTrace_append hprefix tailTrace_4961640
  have hstable : (prefixWord ++ tailWord_4961640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961640).length < 2 ^ (prefixWord ++ tailWord_4961640).sum := by decide
  have hdescent : baseEnd_4961640 < baseStart_4961640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961656 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_4961656 : Nat := 118140960795 + 4961656 * 2 ^ 59
def prefixEnd_4961656 : Nat := 4983230072969 + 3 ^ 40 * 4961656 * 2
def baseEnd_4961656 : Nat := 2547714370264544731781765

theorem tailTrace_4961656 : CollatzResearch.WordTrace tailWord_4961656 prefixEnd_4961656 2547714370264544731781765 := by
  unfold tailWord_4961656
  simp only [CollatzResearch.WordTrace]
  refine ⟨90483230656387585113136411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120644307541850113484181881 90483230656387585113136411)
  ·
    refine ⟨135724845984581377669704617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90483230656387585113136411 135724845984581377669704617)
    ·
      refine ⟨101793634488436033252278463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135724845984581377669704617 101793634488436033252278463)
      ·
        refine ⟨152690451732654049878417695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101793634488436033252278463 152690451732654049878417695)
        ·
          refine ⟨229035677598981074817626543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152690451732654049878417695 229035677598981074817626543)
          ·
            refine ⟨343553516398471612226439815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229035677598981074817626543 343553516398471612226439815)
            ·
              refine ⟨515330274597707418339659723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343553516398471612226439815 515330274597707418339659723)
              ·
                refine ⟨772995411896561127509489585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515330274597707418339659723 772995411896561127509489585)
                ·
                  refine ⟨579746558922420845632117189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772995411896561127509489585 579746558922420845632117189)
                  ·
                    refine ⟨108702479797953908556021973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 579746558922420845632117189 108702479797953908556021973)
                    ·
                      refine ⟨2547714370264544731781765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108702479797953908556021973 2547714370264544731781765)
                      ·
                        rfl

theorem cell23_4961656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_4961656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961656 prefixEnd_4961656 := by exact prefixLift 4961656
  have htrace : WordTrace (prefixWord ++ tailWord_4961656) baseStart_4961656 baseEnd_4961656 := by
    simpa [prefixWord, tailWord_4961656, baseEnd_4961656] using wordTrace_append hprefix tailTrace_4961656
  have hstable : (prefixWord ++ tailWord_4961656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961656).length < 2 ^ (prefixWord ++ tailWord_4961656).sum := by decide
  have hdescent : baseEnd_4961656 < baseStart_4961656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961667 : List Nat := [1, 1, 1, 3, 5, 1, 2, 4, 1, 4]
def baseStart_4961667 : Nat := 118140960795 + 4961667 * 2 ^ 59
def prefixEnd_4961667 : Nat := 4983230072969 + 3 ^ 40 * 4961667 * 2
def baseEnd_4961667 : Nat := 849240006183914729581405

theorem tailTrace_4961667 : CollatzResearch.WordTrace tailWord_4961667 prefixEnd_4961667 849240006183914729581405 := by
  unfold tailWord_4961667
  simp only [CollatzResearch.WordTrace]
  refine ⟨180966862515735319104923255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120644575010490212736615503 180966862515735319104923255)
  ·
    refine ⟨271450293773602978657384883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180966862515735319104923255 271450293773602978657384883)
    ·
      refine ⟨407175440660404467986077325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271450293773602978657384883 407175440660404467986077325)
      ·
        refine ⟨152690790247651675494778997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407175440660404467986077325 152690790247651675494778997)
        ·
          refine ⟨14314761585717344577635531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152690790247651675494778997 14314761585717344577635531)
          ·
            refine ⟨21472142378576016866453297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14314761585717344577635531 21472142378576016866453297)
            ·
              refine ⟨16104106783932012649839973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21472142378576016866453297 16104106783932012649839973)
              ·
                refine ⟨3019520021987252371844995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16104106783932012649839973 3019520021987252371844995)
                ·
                  refine ⟨4529280032980878557767493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019520021987252371844995 4529280032980878557767493)
                  ·
                    refine ⟨849240006183914729581405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4529280032980878557767493 849240006183914729581405)
                    ·
                      rfl

theorem cell23_4961667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 4].length) (baseStart_4961667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961667 prefixEnd_4961667 := by exact prefixLift 4961667
  have htrace : WordTrace (prefixWord ++ tailWord_4961667) baseStart_4961667 baseEnd_4961667 := by
    simpa [prefixWord, tailWord_4961667, baseEnd_4961667] using wordTrace_append hprefix tailTrace_4961667
  have hstable : (prefixWord ++ tailWord_4961667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961667).length < 2 ^ (prefixWord ++ tailWord_4961667).sum := by decide
  have hdescent : baseEnd_4961667 < baseStart_4961667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961717 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_4961717 : Nat := 118140960795 + 4961717 * 2 ^ 59
def prefixEnd_4961717 : Nat := 4983230072969 + 3 ^ 40 * 4961717 * 2
def baseEnd_4961717 : Nat := 2547745692584468993118985

theorem tailTrace_4961717 : CollatzResearch.WordTrace tailWord_4961717 prefixEnd_4961717 2547745692584468993118985 := by
  unfold tailWord_4961717
  simp only [CollatzResearch.WordTrace]
  refine ⟨180968686165554177644243405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120645790777036118429495603 180968686165554177644243405)
  ·
    refine ⟨67863257312082816616591277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180968686165554177644243405 67863257312082816616591277)
    ·
      refine ⟨25448721492031056231221729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67863257312082816616591277 25448721492031056231221729)
      ·
        refine ⟨19086541119023292173416297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25448721492031056231221729 19086541119023292173416297)
        ·
          refine ⟨14314905839267469130062223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19086541119023292173416297 14314905839267469130062223)
          ·
            refine ⟨21472358758901203695093335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14314905839267469130062223 21472358758901203695093335)
            ·
              refine ⟨32208538138351805542640003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21472358758901203695093335 32208538138351805542640003)
              ·
                refine ⟨48312807207527708313960005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32208538138351805542640003 48312807207527708313960005)
                ·
                  refine ⟨9058651351411445308867501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48312807207527708313960005 9058651351411445308867501)
                  ·
                    refine ⟨3396994256779291990825313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9058651351411445308867501 3396994256779291990825313)
                    ·
                      refine ⟨2547745692584468993118985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3396994256779291990825313 2547745692584468993118985)
                      ·
                        rfl

theorem cell23_4961717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_4961717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961717 prefixEnd_4961717 := by exact prefixLift 4961717
  have htrace : WordTrace (prefixWord ++ tailWord_4961717) baseStart_4961717 baseEnd_4961717 := by
    simpa [prefixWord, tailWord_4961717, baseEnd_4961717] using wordTrace_append hprefix tailTrace_4961717
  have hstable : (prefixWord ++ tailWord_4961717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961717).length < 2 ^ (prefixWord ++ tailWord_4961717).sum := by decide
  have hdescent : baseEnd_4961717 < baseStart_4961717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961743 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_4961743 : Nat := 118140960795 + 4961743 * 2 ^ 59
def prefixEnd_4961743 : Nat := 4983230072969 + 3 ^ 40 * 4961743 * 2
def baseEnd_4961743 : Nat := 2547759043081485891393865

theorem tailTrace_4961743 : CollatzResearch.WordTrace tailWord_4961743 prefixEnd_4961743 2547759043081485891393865 := by
  unfold tailWord_4961743
  simp only [CollatzResearch.WordTrace]
  refine ⟨180969634463459984084689883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120646422975639989389793255 180969634463459984084689883)
  ·
    refine ⟨271454451695189976127034825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180969634463459984084689883 271454451695189976127034825)
    ·
      refine ⟨203590838771392482095276119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271454451695189976127034825 203590838771392482095276119)
      ·
        refine ⟨305386258157088723142914179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203590838771392482095276119 305386258157088723142914179)
        ·
          refine ⟨458079387235633084714371269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305386258157088723142914179 458079387235633084714371269)
          ·
            refine ⟨85889885106681203383944613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 458079387235633084714371269 85889885106681203383944613)
            ·
              refine ⟨16104353457502725634489615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85889885106681203383944613 16104353457502725634489615)
              ·
                refine ⟨24156530186254088451734423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16104353457502725634489615 24156530186254088451734423)
                ·
                  refine ⟨36234795279381132677601635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24156530186254088451734423 36234795279381132677601635)
                  ·
                    refine ⟨54352192919071699016402453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36234795279381132677601635 54352192919071699016402453)
                    ·
                      refine ⟨2547759043081485891393865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54352192919071699016402453 2547759043081485891393865)
                      ·
                        rfl

theorem cell23_4961743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_4961743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961743 prefixEnd_4961743 := by exact prefixLift 4961743
  have htrace : WordTrace (prefixWord ++ tailWord_4961743) baseStart_4961743 baseEnd_4961743 := by
    simpa [prefixWord, tailWord_4961743, baseEnd_4961743] using wordTrace_append hprefix tailTrace_4961743
  have hstable : (prefixWord ++ tailWord_4961743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961743).length < 2 ^ (prefixWord ++ tailWord_4961743).sum := by decide
  have hdescent : baseEnd_4961743 < baseStart_4961743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961753 : List Nat := [1, 2, 1, 2, 4, 2, 2, 9]
def baseStart_4961753 : Nat := 118140960795 + 4961753 * 2 ^ 59
def prefixEnd_4961753 : Nat := 4983230072969 + 3 ^ 40 * 4961753 * 2
def baseEnd_4961753 : Nat := 94361636218075216750697

theorem tailTrace_4961753 : CollatzResearch.WordTrace tailWord_4961753 prefixEnd_4961753 94361636218075216750697 := by
  unfold tailWord_4961753
  simp only [CollatzResearch.WordTrace]
  refine ⟨180969999193423755792553913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120646666128949170528369275 180969999193423755792553913)
  ·
    refine ⟨135727499395067816844415435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180969999193423755792553913 135727499395067816844415435)
    ·
      refine ⟨203591249092601725266623153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135727499395067816844415435 203591249092601725266623153)
      ·
        refine ⟨152693436819451293949967365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203591249092601725266623153 152693436819451293949967365)
        ·
          refine ⟨28630019403647117615618881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152693436819451293949967365 28630019403647117615618881)
          ·
            refine ⟨21472514552735338211714161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28630019403647117615618881 21472514552735338211714161)
            ·
              refine ⟨16104385914551503658785621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21472514552735338211714161 16104385914551503658785621)
              ·
                refine ⟨94361636218075216750697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16104385914551503658785621 94361636218075216750697)
                ·
                  rfl

theorem cell23_4961753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 9].length) (baseStart_4961753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961753 prefixEnd_4961753 := by exact prefixLift 4961753
  have htrace : WordTrace (prefixWord ++ tailWord_4961753) baseStart_4961753 baseEnd_4961753 := by
    simpa [prefixWord, tailWord_4961753, baseEnd_4961753] using wordTrace_append hprefix tailTrace_4961753
  have hstable : (prefixWord ++ tailWord_4961753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961753).length < 2 ^ (prefixWord ++ tailWord_4961753).sum := by decide
  have hdescent : baseEnd_4961753 < baseStart_4961753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961767 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_4961767 : Nat := 118140960795 + 4961767 * 2 ^ 59
def prefixEnd_4961767 : Nat := 4983230072969 + 3 ^ 40 * 4961767 * 2
def baseEnd_4961767 : Nat := 2547771366617193797493755

theorem tailTrace_4961767 : CollatzResearch.WordTrace tailWord_4961767 prefixEnd_4961767 2547771366617193797493755 := by
  unfold tailWord_4961767
  simp only [CollatzResearch.WordTrace]
  refine ⟨180970509815373036183563555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120647006543582024122375703 180970509815373036183563555)
  ·
    refine ⟨271455764723059554275345333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180970509815373036183563555 271455764723059554275345333)
    ·
      refine ⟨25448977942786833213313625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 271455764723059554275345333 25448977942786833213313625)
      ·
        refine ⟨19086733457090124909985219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25448977942786833213313625 19086733457090124909985219)
        ·
          refine ⟨28630100185635187364977829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19086733457090124909985219 28630100185635187364977829)
          ·
            refine ⟨5368143784806597630933343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28630100185635187364977829 5368143784806597630933343)
            ·
              refine ⟨8052215677209896446400015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5368143784806597630933343 8052215677209896446400015)
              ·
                refine ⟨12078323515814844669600023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052215677209896446400015 12078323515814844669600023)
                ·
                  refine ⟨18117485273722267004400035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12078323515814844669600023 18117485273722267004400035)
                  ·
                    refine ⟨27176227910583400506600053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18117485273722267004400035 27176227910583400506600053)
                    ·
                      refine ⟨2547771366617193797493755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27176227910583400506600053 2547771366617193797493755)
                      ·
                        rfl

theorem cell23_4961767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_4961767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961767 prefixEnd_4961767 := by exact prefixLift 4961767
  have htrace : WordTrace (prefixWord ++ tailWord_4961767) baseStart_4961767 baseEnd_4961767 := by
    simpa [prefixWord, tailWord_4961767, baseEnd_4961767] using wordTrace_append hprefix tailTrace_4961767
  have hstable : (prefixWord ++ tailWord_4961767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961767).length < 2 ^ (prefixWord ++ tailWord_4961767).sum := by decide
  have hdescent : baseEnd_4961767 < baseStart_4961767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961770 : List Nat := [3, 1, 3, 1, 5, 10]
def baseStart_4961770 : Nat := 118140960795 + 4961770 * 2 ^ 59
def prefixEnd_4961770 : Nat := 4983230072969 + 3 ^ 40 * 4961770 * 2
def baseEnd_4961770 : Nat := 10484662168967725455787

theorem tailTrace_4961770 : CollatzResearch.WordTrace tailWord_4961770 prefixEnd_4961770 10484662168967725455787 := by
  unfold tailWord_4961770
  simp only [CollatzResearch.WordTrace]
  refine ⟨45242654808590541923980691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120647079489574778463948509 45242654808590541923980691)
  ·
    refine ⟨67863982212885812885971037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45242654808590541923980691 67863982212885812885971037)
    ·
      refine ⟨25448993329832179832239139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67863982212885812885971037 25448993329832179832239139)
      ·
        refine ⟨38173489994748269748358709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25448993329832179832239139 38173489994748269748358709)
        ·
          refine ⟨3578764687007650288908629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38173489994748269748358709 3578764687007650288908629)
          ·
            refine ⟨10484662168967725455787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3578764687007650288908629 10484662168967725455787)
            ·
              rfl

theorem cell23_4961770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 10].length) (baseStart_4961770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961770 prefixEnd_4961770 := by exact prefixLift 4961770
  have htrace : WordTrace (prefixWord ++ tailWord_4961770) baseStart_4961770 baseEnd_4961770 := by
    simpa [prefixWord, tailWord_4961770, baseEnd_4961770] using wordTrace_append hprefix tailTrace_4961770
  have hstable : (prefixWord ++ tailWord_4961770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961770).length < 2 ^ (prefixWord ++ tailWord_4961770).sum := by decide
  have hdescent : baseEnd_4961770 < baseStart_4961770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961794 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_4961794 : Nat := 118140960795 + 4961794 * 2 ^ 59
def prefixEnd_4961794 : Nat := 4983230072969 + 3 ^ 40 * 4961794 * 2
def baseEnd_4961794 : Nat := 2547785230594865191856131

theorem tailTrace_4961794 : CollatzResearch.WordTrace tailWord_4961794 prefixEnd_4961794 2547785230594865191856131 := by
  unfold tailWord_4961794
  simp only [CollatzResearch.WordTrace]
  refine ⟨45242873646568804948699109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120647663057516813196530957 45242873646568804948699109)
  ·
    refine ⟨8483038808731650927881083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45242873646568804948699109 8483038808731650927881083)
    ·
      refine ⟨12724558213097476391821625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8483038808731650927881083 12724558213097476391821625)
      ·
        refine ⟨9543418659823107293866219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12724558213097476391821625 9543418659823107293866219)
        ·
          refine ⟨14315127989734660940799329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9543418659823107293866219 14315127989734660940799329)
          ·
            refine ⟨10736345992300995705599497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14315127989734660940799329 10736345992300995705599497)
            ·
              refine ⟨8052259494225746779199623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10736345992300995705599497 8052259494225746779199623)
              ·
                refine ⟨12078389241338620168799435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052259494225746779199623 12078389241338620168799435)
                ·
                  refine ⟨18117583862007930253199153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12078389241338620168799435 18117583862007930253199153)
                  ·
                    refine ⟨13588187896505947689899365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18117583862007930253199153 13588187896505947689899365)
                    ·
                      refine ⟨2547785230594865191856131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13588187896505947689899365 2547785230594865191856131)
                      ·
                        rfl

theorem cell23_4961794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_4961794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961794 prefixEnd_4961794 := by exact prefixLift 4961794
  have htrace : WordTrace (prefixWord ++ tailWord_4961794) baseStart_4961794 baseEnd_4961794 := by
    simpa [prefixWord, tailWord_4961794, baseEnd_4961794] using wordTrace_append hprefix tailTrace_4961794
  have hstable : (prefixWord ++ tailWord_4961794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961794).length < 2 ^ (prefixWord ++ tailWord_4961794).sum := by decide
  have hdescent : baseEnd_4961794 < baseStart_4961794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961850 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_4961850 : Nat := 118140960795 + 4961850 * 2 ^ 59
def prefixEnd_4961850 : Nat := 4983230072969 + 3 ^ 40 * 4961850 * 2
def baseEnd_4961850 : Nat := 2547813985511516972755873

theorem tailTrace_4961850 : CollatzResearch.WordTrace tailWord_4961850 prefixEnd_4961850 2547813985511516972755873 := by
  unfold tailWord_4961850
  simp only [CollatzResearch.WordTrace]
  refine ⟨45243384268518085339708751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120649024716048227572556669 45243384268518085339708751)
  ·
    refine ⟨67865076402777128009563127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45243384268518085339708751 67865076402777128009563127)
    ·
      refine ⟨101797614604165692014344691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67865076402777128009563127 101797614604165692014344691)
      ·
        refine ⟨152696421906248538021517037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101797614604165692014344691 152696421906248538021517037)
        ·
          refine ⟨57261158214843201758068889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152696421906248538021517037 57261158214843201758068889)
          ·
            refine ⟨42945868661132401318551667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57261158214843201758068889 42945868661132401318551667)
            ·
              refine ⟨64418802991698601977827501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42945868661132401318551667 64418802991698601977827501)
              ·
                refine ⟨24157051121886975741685313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64418802991698601977827501 24157051121886975741685313)
                ·
                  refine ⟨18117788341415231806263985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24157051121886975741685313 18117788341415231806263985)
                  ·
                    refine ⟨13588341256061423854697989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18117788341415231806263985 13588341256061423854697989)
                    ·
                      refine ⟨2547813985511516972755873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13588341256061423854697989 2547813985511516972755873)
                      ·
                        rfl

theorem cell23_4961850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_4961850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961850 prefixEnd_4961850 := by exact prefixLift 4961850
  have htrace : WordTrace (prefixWord ++ tailWord_4961850) baseStart_4961850 baseEnd_4961850 := by
    simpa [prefixWord, tailWord_4961850, baseEnd_4961850] using wordTrace_append hprefix tailTrace_4961850
  have hstable : (prefixWord ++ tailWord_4961850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961850).length < 2 ^ (prefixWord ++ tailWord_4961850).sum := by decide
  have hdescent : baseEnd_4961850 < baseStart_4961850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961924 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_4961924 : Nat := 118140960795 + 4961924 * 2 ^ 59
def prefixEnd_4961924 : Nat := 4983230072969 + 3 ^ 40 * 4961924 * 2
def baseEnd_4961924 : Nat := 849283994359983227743511

theorem tailTrace_4961924 : CollatzResearch.WordTrace tailWord_4961924 prefixEnd_4961924 849283994359983227743511 := by
  unfold tailWord_4961924
  simp only [CollatzResearch.WordTrace]
  refine ⟨90488118037902125998514413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120650824050536167998019217 90488118037902125998514413)
  ·
    refine ⟨33933044264213297249442905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90488118037902125998514413 33933044264213297249442905)
    ·
      refine ⟨25449783198159972937082179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33933044264213297249442905 25449783198159972937082179)
      ·
        refine ⟨38174674797239959405623269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25449783198159972937082179 38174674797239959405623269)
        ·
          refine ⟨7157751524482492388554363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38174674797239959405623269 7157751524482492388554363)
          ·
            refine ⟨10736627286723738582831545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7157751524482492388554363 10736627286723738582831545)
            ·
              refine ⟨8052470465042803937123659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10736627286723738582831545 8052470465042803937123659)
              ·
                refine ⟨12078705697564205905685489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052470465042803937123659 12078705697564205905685489)
                ·
                  refine ⟨9059029273173154429264117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12078705697564205905685489 9059029273173154429264117)
                  ·
                    refine ⟨849283994359983227743511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9059029273173154429264117 849283994359983227743511)
                    ·
                      rfl

theorem cell23_4961924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_4961924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961924 prefixEnd_4961924 := by exact prefixLift 4961924
  have htrace : WordTrace (prefixWord ++ tailWord_4961924) baseStart_4961924 baseEnd_4961924 := by
    simpa [prefixWord, tailWord_4961924, baseEnd_4961924] using wordTrace_append hprefix tailTrace_4961924
  have hstable : (prefixWord ++ tailWord_4961924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961924).length < 2 ^ (prefixWord ++ tailWord_4961924).sum := by decide
  have hdescent : baseEnd_4961924 < baseStart_4961924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4961927 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_4961927 : Nat := 118140960795 + 4961927 * 2 ^ 59
def prefixEnd_4961927 : Nat := 4983230072969 + 3 ^ 40 * 4961927 * 2
def baseEnd_4961927 : Nat := 2547853523521913171493019

theorem tailTrace_4961927 : CollatzResearch.WordTrace tailWord_4961927 prefixEnd_4961927 2547853523521913171493019 := by
  unfold tailWord_4961927
  simp only [CollatzResearch.WordTrace]
  refine ⟨180976345494793383509388035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120650896996528922339592023 180976345494793383509388035)
  ·
    refine ⟨271464518242190075264082053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180976345494793383509388035 271464518242190075264082053)
    ·
      refine ⟨50899597170410639112015385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271464518242190075264082053 50899597170410639112015385)
      ·
        refine ⟨38174697877807979334011539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50899597170410639112015385 38174697877807979334011539)
        ·
          refine ⟨57262046816711969001017309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38174697877807979334011539 57262046816711969001017309)
          ·
            refine ⟨21473267556266988375381491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57262046816711969001017309 21473267556266988375381491)
            ·
              refine ⟨32209901334400482563072237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21473267556266988375381491 32209901334400482563072237)
              ·
                refine ⟨12078713000400180961152089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32209901334400482563072237 12078713000400180961152089)
                ·
                  refine ⟨9059034750300135720864067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12078713000400180961152089 9059034750300135720864067)
                  ·
                    refine ⟨13588552125450203581296101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9059034750300135720864067 13588552125450203581296101)
                    ·
                      refine ⟨2547853523521913171493019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13588552125450203581296101 2547853523521913171493019)
                      ·
                        rfl

theorem cell23_4961927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_4961927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4961927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4961927 prefixEnd_4961927 := by exact prefixLift 4961927
  have htrace : WordTrace (prefixWord ++ tailWord_4961927) baseStart_4961927 baseEnd_4961927 := by
    simpa [prefixWord, tailWord_4961927, baseEnd_4961927] using wordTrace_append hprefix tailTrace_4961927
  have hstable : (prefixWord ++ tailWord_4961927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4961927).length < 2 ^ (prefixWord ++ tailWord_4961927).sum := by decide
  have hdescent : baseEnd_4961927 < baseStart_4961927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4961927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962027 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 1, 6]
def baseStart_4962027 : Nat := 118140960795 + 4962027 * 2 ^ 59
def prefixEnd_4962027 : Nat := 4983230072969 + 3 ^ 40 * 4962027 * 2
def baseEnd_4962027 : Nat := 849301623862454260080853

theorem tailTrace_4962027 : CollatzResearch.WordTrace tailWord_4962027 prefixEnd_4962027 849301623862454260080853 := by
  unfold tailWord_4962027
  simp only [CollatzResearch.WordTrace]
  refine ⟨180979992794431100588028335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120653328529620733725352223 180979992794431100588028335)
  ·
    refine ⟨271469989191646650882042503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180979992794431100588028335 271469989191646650882042503)
    ·
      refine ⟨407204983787469976323063755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271469989191646650882042503 407204983787469976323063755)
      ·
        refine ⟨610807475681204964484595633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407204983787469976323063755 610807475681204964484595633)
        ·
          refine ⟨458105606760903723363446725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610807475681204964484595633 458105606760903723363446725)
          ·
            refine ⟨85894801267669448130646261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 458105606760903723363446725 85894801267669448130646261)
            ·
              refine ⟨8052637618844010762248087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85894801267669448130646261 8052637618844010762248087)
              ·
                refine ⟨12078956428266016143372131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052637618844010762248087 12078956428266016143372131)
                ·
                  refine ⟨18118434642399024215058197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12078956428266016143372131 18118434642399024215058197)
                  ·
                    refine ⟨849301623862454260080853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18118434642399024215058197 849301623862454260080853)
                    ·
                      rfl

theorem cell23_4962027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 6].length) (baseStart_4962027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962027 prefixEnd_4962027 := by exact prefixLift 4962027
  have htrace : WordTrace (prefixWord ++ tailWord_4962027) baseStart_4962027 baseEnd_4962027 := by
    simpa [prefixWord, tailWord_4962027, baseEnd_4962027] using wordTrace_append hprefix tailTrace_4962027
  have hstable : (prefixWord ++ tailWord_4962027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962027).length < 2 ^ (prefixWord ++ tailWord_4962027).sum := by decide
  have hdescent : baseEnd_4962027 < baseStart_4962027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962034 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_4962034 : Nat := 118140960795 + 4962034 * 2 ^ 59
def prefixEnd_4962034 : Nat := 4983230072969 + 3 ^ 40 * 4962034 * 2
def baseEnd_4962034 : Nat := 2547908465951944252855027

theorem tailTrace_4962034 : CollatzResearch.WordTrace tailWord_4962034 prefixEnd_4962034 2547908465951944252855027 := by
  unfold tailWord_4962034
  simp only [CollatzResearch.WordTrace]
  refine ⟨45245062026351435195883289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120653498736937160522355437 45245062026351435195883289)
  ·
    refine ⟨33933796519763576396912467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45245062026351435195883289 33933796519763576396912467)
    ·
      refine ⟨50900694779645364595368701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33933796519763576396912467 50900694779645364595368701)
      ·
        refine ⟨19087760542367011723263263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50900694779645364595368701 19087760542367011723263263)
        ·
          refine ⟨28631640813550517584894895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19087760542367011723263263 28631640813550517584894895)
          ·
            refine ⟨42947461220325776377342343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28631640813550517584894895 42947461220325776377342343)
            ·
              refine ⟨64421191830488664566013515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42947461220325776377342343 64421191830488664566013515)
              ·
                refine ⟨96631787745732996849020273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64421191830488664566013515 96631787745732996849020273)
                ·
                  refine ⟨72473840809299747636765205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96631787745732996849020273 72473840809299747636765205)
                  ·
                    refine ⟨3397211287935925670473369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72473840809299747636765205 3397211287935925670473369)
                    ·
                      refine ⟨2547908465951944252855027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397211287935925670473369 2547908465951944252855027)
                      ·
                        rfl

theorem cell23_4962034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_4962034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962034 prefixEnd_4962034 := by exact prefixLift 4962034
  have htrace : WordTrace (prefixWord ++ tailWord_4962034) baseStart_4962034 baseEnd_4962034 := by
    simpa [prefixWord, tailWord_4962034, baseEnd_4962034] using wordTrace_append hprefix tailTrace_4962034
  have hstable : (prefixWord ++ tailWord_4962034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962034).length < 2 ^ (prefixWord ++ tailWord_4962034).sum := by decide
  have hdescent : baseEnd_4962034 < baseStart_4962034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962047 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_4962047 : Nat := 118140960795 + 4962047 * 2 ^ 59
def prefixEnd_4962047 : Nat := 4983230072969 + 3 ^ 40 * 4962047 * 2
def baseEnd_4962047 : Nat := 2547915141200452701992467

theorem tailTrace_4962047 : CollatzResearch.WordTrace tailWord_4962047 prefixEnd_4962047 2547915141200452701992467 := by
  unfold tailWord_4962047
  simp only [CollatzResearch.WordTrace]
  refine ⟨180980722254358644003756395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120653814836239096002504263 180980722254358644003756395)
  ·
    refine ⟨271471083381537966005634593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180980722254358644003756395 271471083381537966005634593)
    ·
      refine ⟨203603312536153474504225945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271471083381537966005634593 203603312536153474504225945)
      ·
        refine ⟨152702484402115105878169459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203603312536153474504225945 152702484402115105878169459)
        ·
          refine ⟨229053726603172658817254189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152702484402115105878169459 229053726603172658817254189)
          ·
            refine ⟨85895147476189747056470321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229053726603172658817254189 85895147476189747056470321)
            ·
              refine ⟨64421360607142310292352741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85895147476189747056470321 64421360607142310292352741)
              ·
                refine ⟨12079005113839183179816139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64421360607142310292352741 12079005113839183179816139)
                ·
                  refine ⟨18118507670758774769724209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12079005113839183179816139 18118507670758774769724209)
                  ·
                    refine ⟨13588880753069081077293157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18118507670758774769724209 13588880753069081077293157)
                    ·
                      refine ⟨2547915141200452701992467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13588880753069081077293157 2547915141200452701992467)
                      ·
                        rfl

theorem cell23_4962047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_4962047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962047 prefixEnd_4962047 := by exact prefixLift 4962047
  have htrace : WordTrace (prefixWord ++ tailWord_4962047) baseStart_4962047 baseEnd_4962047 := by
    simpa [prefixWord, tailWord_4962047, baseEnd_4962047] using wordTrace_append hprefix tailTrace_4962047
  have hstable : (prefixWord ++ tailWord_4962047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962047).length < 2 ^ (prefixWord ++ tailWord_4962047).sum := by decide
  have hdescent : baseEnd_4962047 < baseStart_4962047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962067 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 3]
def baseStart_4962067 : Nat := 118140960795 + 4962067 * 2 ^ 59
def prefixEnd_4962067 : Nat := 4983230072969 + 3 ^ 40 * 4962067 * 2
def baseEnd_4962067 : Nat := 2547925410813542623742375

theorem tailTrace_4962067 : CollatzResearch.WordTrace tailWord_4962067 prefixEnd_4962067 2547925410813542623742375 := by
  unfold tailWord_4962067
  simp only [CollatzResearch.WordTrace]
  refine ⟨180981451714286187419484455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120654301142857458279656303 180981451714286187419484455)
  ·
    refine ⟨271472177571429281129226683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180981451714286187419484455 271472177571429281129226683)
    ·
      refine ⟨407208266357143921693840025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271472177571429281129226683 407208266357143921693840025)
      ·
        refine ⟨305406199767857941270380019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407208266357143921693840025 305406199767857941270380019)
        ·
          refine ⟨458109299651786911905570029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305406199767857941270380019 458109299651786911905570029)
          ·
            refine ⟨171790987369420091964588761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 458109299651786911905570029 171790987369420091964588761)
            ·
              refine ⟨128843240527065068973441571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171790987369420091964588761 128843240527065068973441571)
              ·
                refine ⟨193264860790597603460162357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128843240527065068973441571 193264860790597603460162357)
                ·
                  refine ⟨18118580699118525324390221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193264860790597603460162357 18118580699118525324390221)
                  ·
                    refine ⟨6794467762169446996646333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18118580699118525324390221 6794467762169446996646333)
                    ·
                      refine ⟨2547925410813542623742375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6794467762169446996646333 2547925410813542623742375)
                      ·
                        rfl

theorem cell23_4962067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_4962067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962067 prefixEnd_4962067 := by exact prefixLift 4962067
  have htrace : WordTrace (prefixWord ++ tailWord_4962067) baseStart_4962067 baseEnd_4962067 := by
    simpa [prefixWord, tailWord_4962067, baseEnd_4962067] using wordTrace_append hprefix tailTrace_4962067
  have hstable : (prefixWord ++ tailWord_4962067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962067).length < 2 ^ (prefixWord ++ tailWord_4962067).sum := by decide
  have hdescent : baseEnd_4962067 < baseStart_4962067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962088 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_4962088 : Nat := 118140960795 + 4962088 * 2 ^ 59
def prefixEnd_4962088 : Nat := 4983230072969 + 3 ^ 40 * 4962088 * 2
def baseEnd_4962088 : Nat := 2547936193907287041579779

theorem tailTrace_4962088 : CollatzResearch.WordTrace tailWord_4962088 prefixEnd_4962088 2547936193907287041579779 := by
  unfold tailWord_4962088
  simp only [CollatzResearch.WordTrace]
  refine ⟨90491108823605054002999459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120654811764806738670665945 90491108823605054002999459)
  ·
    refine ⟨135736663235407581004499189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90491108823605054002999459 135736663235407581004499189)
    ·
      refine ⟨12725312178319460719171799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135736663235407581004499189 12725312178319460719171799)
      ·
        refine ⟨19087968267479191078757699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12725312178319460719171799 19087968267479191078757699)
        ·
          refine ⟨28631952401218786618136549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19087968267479191078757699 28631952401218786618136549)
          ·
            refine ⟨5368491075228522490900603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28631952401218786618136549 5368491075228522490900603)
            ·
              refine ⟨8052736612842783736350905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5368491075228522490900603 8052736612842783736350905)
              ·
                refine ⟨6039552459632087802263179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8052736612842783736350905 6039552459632087802263179)
                ·
                  refine ⟨9059328689448131703394769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6039552459632087802263179 9059328689448131703394769)
                  ·
                    refine ⟨6794496517086098777546077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9059328689448131703394769 6794496517086098777546077)
                    ·
                      refine ⟨2547936193907287041579779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6794496517086098777546077 2547936193907287041579779)
                      ·
                        rfl

theorem cell23_4962088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_4962088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962088 prefixEnd_4962088 := by exact prefixLift 4962088
  have htrace : WordTrace (prefixWord ++ tailWord_4962088) baseStart_4962088 baseEnd_4962088 := by
    simpa [prefixWord, tailWord_4962088, baseEnd_4962088] using wordTrace_append hprefix tailTrace_4962088
  have hstable : (prefixWord ++ tailWord_4962088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962088).length < 2 ^ (prefixWord ++ tailWord_4962088).sum := by decide
  have hdescent : baseEnd_4962088 < baseStart_4962088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962101 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_4962101 : Nat := 118140960795 + 4962101 * 2 ^ 59
def prefixEnd_4962101 : Nat := 4983230072969 + 3 ^ 40 * 4962101 * 2
def baseEnd_4962101 : Nat := 2547942869155795490717219

theorem tailTrace_4962101 : CollatzResearch.WordTrace tailWord_4962101 prefixEnd_4962101 2547942869155795490717219 := by
  unfold tailWord_4962101
  simp only [CollatzResearch.WordTrace]
  refine ⟨180982691796163011226222157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120655127864108674150814771 180982691796163011226222157)
  ·
    refine ⟨67868509423561129209833309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180982691796163011226222157 67868509423561129209833309)
    ·
      refine ⟨25450691033835423453687491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67868509423561129209833309 25450691033835423453687491)
      ·
        refine ⟨38176036550753135180531237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25450691033835423453687491 38176036550753135180531237)
        ·
          refine ⟨7158006853266212846349607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38176036550753135180531237 7158006853266212846349607)
          ·
            refine ⟨10737010279899319269524411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158006853266212846349607 10737010279899319269524411)
            ·
              refine ⟨16105515419848978904286617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10737010279899319269524411 16105515419848978904286617)
              ·
                refine ⟨12079136564886734178214963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16105515419848978904286617 12079136564886734178214963)
                ·
                  refine ⟨18118704847330101267322445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12079136564886734178214963 18118704847330101267322445)
                  ·
                    refine ⟨6794514317748787975245917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18118704847330101267322445 6794514317748787975245917)
                    ·
                      refine ⟨2547942869155795490717219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6794514317748787975245917 2547942869155795490717219)
                      ·
                        rfl

theorem cell23_4962101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_4962101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962101 prefixEnd_4962101 := by exact prefixLift 4962101
  have htrace : WordTrace (prefixWord ++ tailWord_4962101) baseStart_4962101 baseEnd_4962101 := by
    simpa [prefixWord, tailWord_4962101, baseEnd_4962101] using wordTrace_append hprefix tailTrace_4962101
  have hstable : (prefixWord ++ tailWord_4962101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962101).length < 2 ^ (prefixWord ++ tailWord_4962101).sum := by decide
  have hdescent : baseEnd_4962101 < baseStart_4962101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962105 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4962105 : Nat := 118140960795 + 4962105 * 2 ^ 59
def prefixEnd_4962105 : Nat := 4983230072969 + 3 ^ 40 * 4962105 * 2
def baseEnd_4962105 : Nat := 2547944923078413475067201

theorem tailTrace_4962105 : CollatzResearch.WordTrace tailWord_4962105 prefixEnd_4962105 2547944923078413475067201 := by
  unfold tailWord_4962105
  simp only [CollatzResearch.WordTrace]
  refine ⟨180982837688148519909367769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120655225125432346606245179 180982837688148519909367769)
  ·
    refine ⟨135737128266111389932025827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180982837688148519909367769 135737128266111389932025827)
    ·
      refine ⟨203605692399167084898038741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135737128266111389932025827 203605692399167084898038741)
      ·
        refine ⟨4772008415605478552297783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 203605692399167084898038741 4772008415605478552297783)
        ·
          refine ⟨7158012623408217828446675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772008415605478552297783 7158012623408217828446675)
          ·
            refine ⟨10737018935112326742670013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158012623408217828446675 10737018935112326742670013)
            ·
              refine ⟨4026382100667122528501255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10737018935112326742670013 4026382100667122528501255)
              ·
                refine ⟨6039573151000683792751883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026382100667122528501255 6039573151000683792751883)
                ·
                  refine ⟨9059359726501025689127825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6039573151000683792751883 9059359726501025689127825)
                  ·
                    refine ⟨6794519794875769266845869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9059359726501025689127825 6794519794875769266845869)
                    ·
                      refine ⟨2547944923078413475067201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6794519794875769266845869 2547944923078413475067201)
                      ·
                        rfl

theorem cell23_4962105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4962105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962105 prefixEnd_4962105 := by exact prefixLift 4962105
  have htrace : WordTrace (prefixWord ++ tailWord_4962105) baseStart_4962105 baseEnd_4962105 := by
    simpa [prefixWord, tailWord_4962105, baseEnd_4962105] using wordTrace_append hprefix tailTrace_4962105
  have hstable : (prefixWord ++ tailWord_4962105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962105).length < 2 ^ (prefixWord ++ tailWord_4962105).sum := by decide
  have hdescent : baseEnd_4962105 < baseStart_4962105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962117 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_4962117 : Nat := 118140960795 + 4962117 * 2 ^ 59
def prefixEnd_4962117 : Nat := 4983230072969 + 3 ^ 40 * 4962117 * 2
def baseEnd_4962117 : Nat := 849317028282089142705715

theorem tailTrace_4962117 : CollatzResearch.WordTrace tailWord_4962117 prefixEnd_4962117 849317028282089142705715 := by
  unfold tailWord_4962117
  simp only [CollatzResearch.WordTrace]
  refine ⟨180983275364105045958804605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120655516909403363972536403 180983275364105045958804605)
  ·
    refine ⟨67868728261539392234551727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180983275364105045958804605 67868728261539392234551727)
    ·
      refine ⟨101803092392309088351827591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67868728261539392234551727 101803092392309088351827591)
      ·
        refine ⟨152704638588463632527741387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101803092392309088351827591 152704638588463632527741387)
        ·
          refine ⟨229056957882695448791612081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152704638588463632527741387 229056957882695448791612081)
          ·
            refine ⟨171792718412021586593709061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229056957882695448791612081 171792718412021586593709061)
            ·
              refine ⟨32211134702254047486320449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171792718412021586593709061 32211134702254047486320449)
              ·
                refine ⟨24158351026690535614740337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32211134702254047486320449 24158351026690535614740337)
                ·
                  refine ⟨18118763270017901711055253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24158351026690535614740337 18118763270017901711055253)
                  ·
                    refine ⟨849317028282089142705715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18118763270017901711055253 849317028282089142705715)
                    ·
                      rfl

theorem cell23_4962117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_4962117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962117 prefixEnd_4962117 := by exact prefixLift 4962117
  have htrace : WordTrace (prefixWord ++ tailWord_4962117) baseStart_4962117 baseEnd_4962117 := by
    simpa [prefixWord, tailWord_4962117, baseEnd_4962117] using wordTrace_append hprefix tailTrace_4962117
  have hstable : (prefixWord ++ tailWord_4962117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962117).length < 2 ^ (prefixWord ++ tailWord_4962117).sum := by decide
  have hdescent : baseEnd_4962117 < baseStart_4962117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962158 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4962158 : Nat := 118140960795 + 4962158 * 2 ^ 59
def prefixEnd_4962158 : Nat := 4983230072969 + 3 ^ 40 * 4962158 * 2
def baseEnd_4962158 : Nat := 2547972137553101767704457

theorem tailTrace_4962158 : CollatzResearch.WordTrace tailWord_4962158 prefixEnd_4962158 2547972137553101767704457 := by
  unfold tailWord_4962158
  simp only [CollatzResearch.WordTrace]
  refine ⟨22623096344619563745130891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120656513837971006640698085 22623096344619563745130891)
  ·
    refine ⟨33934644516929345617696337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22623096344619563745130891 33934644516929345617696337)
    ·
      refine ⟨25450983387697009213272253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33934644516929345617696337 25450983387697009213272253)
      ·
        refine ⟨9544118770386378454977095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25450983387697009213272253 9544118770386378454977095)
        ·
          refine ⟨14316178155579567682465643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9544118770386378454977095 14316178155579567682465643)
          ·
            refine ⟨21474267233369351523698465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14316178155579567682465643 21474267233369351523698465)
            ·
              refine ⟨16105700425027013642773849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21474267233369351523698465 16105700425027013642773849)
              ·
                refine ⟨12079275318770260232080387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16105700425027013642773849 12079275318770260232080387)
                ·
                  refine ⟨18118912978155390348120581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12079275318770260232080387 18118912978155390348120581)
                  ·
                    refine ⟨3397296183404135690272609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18118912978155390348120581 3397296183404135690272609)
                    ·
                      refine ⟨2547972137553101767704457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397296183404135690272609 2547972137553101767704457)
                      ·
                        rfl

theorem cell23_4962158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4962158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962158 prefixEnd_4962158 := by exact prefixLift 4962158
  have htrace : WordTrace (prefixWord ++ tailWord_4962158) baseStart_4962158 baseEnd_4962158 := by
    simpa [prefixWord, tailWord_4962158, baseEnd_4962158] using wordTrace_append hprefix tailTrace_4962158
  have hstable : (prefixWord ++ tailWord_4962158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962158).length < 2 ^ (prefixWord ++ tailWord_4962158).sum := by decide
  have hdescent : baseEnd_4962158 < baseStart_4962158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962187 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 7]
def baseStart_4962187 : Nat := 118140960795 + 4962187 * 2 ^ 59
def prefixEnd_4962187 : Nat := 4983230072969 + 3 ^ 40 * 4962187 * 2
def baseEnd_4962187 : Nat := 2547987028492082154241823

theorem tailTrace_4962187 : CollatzResearch.WordTrace tailWord_4962187 prefixEnd_4962187 2547987028492082154241823 := by
  unfold tailWord_4962187
  simp only [CollatzResearch.WordTrace]
  refine ⟨180985828473851447913852815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120657218982567631942568543 180985828473851447913852815)
  ·
    refine ⟨271478742710777171870779223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180985828473851447913852815 271478742710777171870779223)
    ·
      refine ⟨407218114066165757806168835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271478742710777171870779223 407218114066165757806168835)
      ·
        refine ⟨610827171099248636709253253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407218114066165757806168835 610827171099248636709253253)
        ·
          refine ⟨114530094581109119382984985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 610827171099248636709253253 114530094581109119382984985)
          ·
            refine ⟨85897570935831839537238739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114530094581109119382984985 85897570935831839537238739)
            ·
              refine ⟨128846356403747759305858109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85897570935831839537238739 128846356403747759305858109)
              ·
                refine ⟨48317383651405409739696791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128846356403747759305858109 48317383651405409739696791)
                ·
                  refine ⟨72476075477108114609545187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48317383651405409739696791 72476075477108114609545187)
                  ·
                    refine ⟨108714113215662171914317781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72476075477108114609545187 108714113215662171914317781)
                    ·
                      refine ⟨2547987028492082154241823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108714113215662171914317781 2547987028492082154241823)
                      ·
                        rfl

theorem cell23_4962187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_4962187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962187 prefixEnd_4962187 := by exact prefixLift 4962187
  have htrace : WordTrace (prefixWord ++ tailWord_4962187) baseStart_4962187 baseEnd_4962187 := by
    simpa [prefixWord, tailWord_4962187, baseEnd_4962187] using wordTrace_append hprefix tailTrace_4962187
  have hstable : (prefixWord ++ tailWord_4962187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962187).length < 2 ^ (prefixWord ++ tailWord_4962187).sum := by decide
  have hdescent : baseEnd_4962187 < baseStart_4962187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962234 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_4962234 : Nat := 118140960795 + 4962234 * 2 ^ 59
def prefixEnd_4962234 : Nat := 4983230072969 + 3 ^ 40 * 4962234 * 2
def baseEnd_4962234 : Nat := 2548011162082843470354107

theorem tailTrace_4962234 : CollatzResearch.WordTrace tailWord_4962234 prefixEnd_4962234 2548011162082843470354107 := by
  unfold tailWord_4962234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45246885676170293735203439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120658361803120783293875837 45246885676170293735203439)
  ·
    refine ⟨67870328514255440602805159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45246885676170293735203439 67870328514255440602805159)
    ·
      refine ⟨101805492771383160904207739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67870328514255440602805159 101805492771383160904207739)
      ·
        refine ⟨152708239157074741356311609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101805492771383160904207739 152708239157074741356311609)
        ·
          refine ⟨114531179367806056017233707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152708239157074741356311609 114531179367806056017233707)
          ·
            refine ⟨171796769051709084025850561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114531179367806056017233707 171796769051709084025850561)
            ·
              refine ⟨128847576788781813019387921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171796769051709084025850561 128847576788781813019387921)
              ·
                refine ⟨96635682591586359764540941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128847576788781813019387921 96635682591586359764540941)
                ·
                  refine ⟨36238380971844884911702853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96635682591586359764540941 36238380971844884911702853)
                  ·
                    refine ⟨6794696432220915920944285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36238380971844884911702853 6794696432220915920944285)
                    ·
                      refine ⟨2548011162082843470354107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6794696432220915920944285 2548011162082843470354107)
                      ·
                        rfl

theorem cell23_4962234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_4962234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962234 prefixEnd_4962234 := by exact prefixLift 4962234
  have htrace : WordTrace (prefixWord ++ tailWord_4962234) baseStart_4962234 baseEnd_4962234 := by
    simpa [prefixWord, tailWord_4962234, baseEnd_4962234] using wordTrace_append hprefix tailTrace_4962234
  have hstable : (prefixWord ++ tailWord_4962234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962234).length < 2 ^ (prefixWord ++ tailWord_4962234).sum := by decide
  have hdescent : baseEnd_4962234 < baseStart_4962234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962332 : List Nat := [2, 2, 3, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_4962332 : Nat := 118140960795 + 4962332 * 2 ^ 59
def prefixEnd_4962332 : Nat := 4983230072969 + 3 ^ 40 * 4962332 * 2
def baseEnd_4962332 : Nat := 2548061483186984086928657

theorem tailTrace_4962332 : CollatzResearch.WordTrace tailWord_4962332 prefixEnd_4962332 2548061483186984086928657 := by
  unfold tailWord_4962332
  simp only [CollatzResearch.WordTrace]
  refine ⟨90495558529163068838940625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120660744705550758451920833 90495558529163068838940625)
  ·
    refine ⟨67871668896872301629205469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90495558529163068838940625 67871668896872301629205469)
    ·
      refine ⟨25451875836327113110952051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67871668896872301629205469 25451875836327113110952051)
      ·
        refine ⟨38177813754490669666428077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25451875836327113110952051 38177813754490669666428077)
        ·
          refine ⟨14316680157934001124910529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38177813754490669666428077 14316680157934001124910529)
          ·
            refine ⟨10737510118450500843682897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14316680157934001124910529 10737510118450500843682897)
            ·
              refine ⟨8053132588837875632762173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10737510118450500843682897 8053132588837875632762173)
              ·
                refine ⟨3019924720814203362285815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8053132588837875632762173 3019924720814203362285815)
                ·
                  refine ⟨4529887081221305043428723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019924720814203362285815 4529887081221305043428723)
                  ·
                    refine ⟨6794830621831957565143085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4529887081221305043428723 6794830621831957565143085)
                    ·
                      refine ⟨2548061483186984086928657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6794830621831957565143085 2548061483186984086928657)
                      ·
                        rfl

theorem cell23_4962332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_4962332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962332 prefixEnd_4962332 := by exact prefixLift 4962332
  have htrace : WordTrace (prefixWord ++ tailWord_4962332) baseStart_4962332 baseEnd_4962332 := by
    simpa [prefixWord, tailWord_4962332, baseEnd_4962332] using wordTrace_append hprefix tailTrace_4962332
  have hstable : (prefixWord ++ tailWord_4962332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962332).length < 2 ^ (prefixWord ++ tailWord_4962332).sum := by decide
  have hdescent : baseEnd_4962332 < baseStart_4962332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962338 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_4962338 : Nat := 118140960795 + 4962338 * 2 ^ 59
def prefixEnd_4962338 : Nat := 4983230072969 + 3 ^ 40 * 4962338 * 2
def baseEnd_4962338 : Nat := 2548064564070911063453629

theorem tailTrace_4962338 : CollatzResearch.WordTrace tailWord_4962338 prefixEnd_4962338 2548064564070911063453629 := by
  unfold tailWord_4962338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45247833974076100175649917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120660890597536267135066445 45247833974076100175649917)
  ·
    refine ⟨16967937740278537565868719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45247833974076100175649917 16967937740278537565868719)
    ·
      refine ⟨25451906610417806348803079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16967937740278537565868719 25451906610417806348803079)
      ·
        refine ⟨38177859915626709523204619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25451906610417806348803079 38177859915626709523204619)
        ·
          refine ⟨57266789873440064284806929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38177859915626709523204619 57266789873440064284806929)
          ·
            refine ⟨42950092405080048213605197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57266789873440064284806929 42950092405080048213605197)
            ·
              refine ⟨16106284651905018080101949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42950092405080048213605197 16106284651905018080101949)
              ·
                refine ⟨6039856744464381780038231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16106284651905018080101949 6039856744464381780038231)
                ·
                  refine ⟨9059785116696572670057347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6039856744464381780038231 9059785116696572670057347)
                  ·
                    refine ⟨13589677675044859005086021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9059785116696572670057347 13589677675044859005086021)
                    ·
                      refine ⟨2548064564070911063453629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13589677675044859005086021 2548064564070911063453629)
                      ·
                        rfl

theorem cell23_4962338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_4962338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962338 prefixEnd_4962338 := by exact prefixLift 4962338
  have htrace : WordTrace (prefixWord ++ tailWord_4962338) baseStart_4962338 baseEnd_4962338 := by
    simpa [prefixWord, tailWord_4962338, baseEnd_4962338] using wordTrace_append hprefix tailTrace_4962338
  have hstable : (prefixWord ++ tailWord_4962338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962338).length < 2 ^ (prefixWord ++ tailWord_4962338).sum := by decide
  have hdescent : baseEnd_4962338 < baseStart_4962338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962358 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_4962358 : Nat := 118140960795 + 4962358 * 2 ^ 59
def prefixEnd_4962358 : Nat := 4983230072969 + 3 ^ 40 * 4962358 * 2
def baseEnd_4962358 : Nat := 2548074833684000985203537

theorem tailTrace_4962358 : CollatzResearch.WordTrace tailWord_4962358 prefixEnd_4962358 2548074833684000985203537 := by
  unfold tailWord_4962358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312004084764496507395483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120661376904154629412218485 11312004084764496507395483)
  ·
    refine ⟨16968006127146744761093225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11312004084764496507395483 16968006127146744761093225)
    ·
      refine ⟨12726004595360058570819919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16968006127146744761093225 12726004595360058570819919)
      ·
        refine ⟨19089006893040087856229879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12726004595360058570819919 19089006893040087856229879)
        ·
          refine ⟨28633510339560131784344819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19089006893040087856229879 28633510339560131784344819)
          ·
            refine ⟨42950265509340197676517229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28633510339560131784344819 42950265509340197676517229)
            ·
              refine ⟨16106349566002574128693961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42950265509340197676517229 16106349566002574128693961)
              ·
                refine ⟨12079762174501930596520471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16106349566002574128693961 12079762174501930596520471)
                ·
                  refine ⟨18119643261752895894780707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12079762174501930596520471 18119643261752895894780707)
                  ·
                    refine ⟨27179464892629343842171061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18119643261752895894780707 27179464892629343842171061)
                    ·
                      refine ⟨2548074833684000985203537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27179464892629343842171061 2548074833684000985203537)
                      ·
                        rfl

theorem cell23_4962358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_4962358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962358 prefixEnd_4962358 := by exact prefixLift 4962358
  have htrace : WordTrace (prefixWord ++ tailWord_4962358) baseStart_4962358 baseEnd_4962358 := by
    simpa [prefixWord, tailWord_4962358, baseEnd_4962358] using wordTrace_append hprefix tailTrace_4962358
  have hstable : (prefixWord ++ tailWord_4962358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962358).length < 2 ^ (prefixWord ++ tailWord_4962358).sum := by decide
  have hdescent : baseEnd_4962358 < baseStart_4962358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962365 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_4962365 : Nat := 118140960795 + 4962365 * 2 ^ 59
def prefixEnd_4962365 : Nat := 4983230072969 + 3 ^ 40 * 4962365 * 2
def baseEnd_4962365 : Nat := 849359476016194152605335

theorem tailTrace_4962365 : CollatzResearch.WordTrace tailWord_4962365 prefixEnd_4962365 849359476016194152605335 := by
  unfold tailWord_4962365
  simp only [CollatzResearch.WordTrace]
  refine ⟨180992320667206584313832549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120661547111471056209221699 180992320667206584313832549)
  ·
    refine ⟨33936060125101234558843603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 180992320667206584313832549 33936060125101234558843603)
    ·
      refine ⟨50904090187651851838265405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33936060125101234558843603 50904090187651851838265405)
      ·
        refine ⟨19089033820369444439349527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50904090187651851838265405 19089033820369444439349527)
        ·
          refine ⟨28633550730554166659024291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19089033820369444439349527 28633550730554166659024291)
          ·
            refine ⟨42950326095831249988536437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28633550730554166659024291 42950326095831249988536437)
            ·
              refine ⟨4026593071484179686425291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42950326095831249988536437 4026593071484179686425291)
              ·
                refine ⟨6039889607226269529637937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026593071484179686425291 6039889607226269529637937)
                ·
                  refine ⟨4529917205419702147228453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6039889607226269529637937 4529917205419702147228453)
                  ·
                    refine ⟨849359476016194152605335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4529917205419702147228453 849359476016194152605335)
                    ·
                      rfl

theorem cell23_4962365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_4962365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962365 prefixEnd_4962365 := by exact prefixLift 4962365
  have htrace : WordTrace (prefixWord ++ tailWord_4962365) baseStart_4962365 baseEnd_4962365 := by
    simpa [prefixWord, tailWord_4962365, baseEnd_4962365] using wordTrace_append hprefix tailTrace_4962365
  have hstable : (prefixWord ++ tailWord_4962365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962365).length < 2 ^ (prefixWord ++ tailWord_4962365).sum := by decide
  have hdescent : baseEnd_4962365 < baseStart_4962365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962368 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 4]
def baseStart_4962368 : Nat := 118140960795 + 4962368 * 2 ^ 59
def prefixEnd_4962368 : Nat := 4983230072969 + 3 ^ 40 * 4962368 * 2
def baseEnd_4962368 : Nat := 2548079968490545946078491

theorem tailTrace_4962368 : CollatzResearch.WordTrace tailWord_4962368 prefixEnd_4962368 2548079968490545946078491 := by
  unfold tailWord_4962368
  simp only [CollatzResearch.WordTrace]
  refine ⟨90496215043097857913095879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120661620057463810550794505 90496215043097857913095879)
  ·
    refine ⟨135744322564646786869643819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90496215043097857913095879 135744322564646786869643819)
    ·
      refine ⟨203616483846970180304465729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135744322564646786869643819 203616483846970180304465729)
      ·
        refine ⟨152712362885227635228349297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203616483846970180304465729 152712362885227635228349297)
        ·
          refine ⟨114534272163920726421261973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152712362885227635228349297 114534272163920726421261973)
          ·
            refine ⟨5368794007683784050996655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114534272163920726421261973 5368794007683784050996655)
            ·
              refine ⟨8053191011525676076494983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5368794007683784050996655 8053191011525676076494983)
              ·
                refine ⟨12079786517288514114742475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8053191011525676076494983 12079786517288514114742475)
                ·
                  refine ⟨18119679775932771172113713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12079786517288514114742475 18119679775932771172113713)
                  ·
                    refine ⟨13589759831949578379085285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18119679775932771172113713 13589759831949578379085285)
                    ·
                      refine ⟨2548079968490545946078491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13589759831949578379085285 2548079968490545946078491)
                      ·
                        rfl

theorem cell23_4962368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_4962368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962368 prefixEnd_4962368 := by exact prefixLift 4962368
  have htrace : WordTrace (prefixWord ++ tailWord_4962368) baseStart_4962368 baseEnd_4962368 := by
    simpa [prefixWord, tailWord_4962368, baseEnd_4962368] using wordTrace_append hprefix tailTrace_4962368
  have hstable : (prefixWord ++ tailWord_4962368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962368).length < 2 ^ (prefixWord ++ tailWord_4962368).sum := by decide
  have hdescent : baseEnd_4962368 < baseStart_4962368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962371 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 3]
def baseStart_4962371 : Nat := 118140960795 + 4962371 * 2 ^ 59
def prefixEnd_4962371 : Nat := 4983230072969 + 3 ^ 40 * 4962371 * 2
def baseEnd_4962371 : Nat := 2548081508932509434340977

theorem tailTrace_4962371 : CollatzResearch.WordTrace tailWord_4962371 prefixEnd_4962371 2548081508932509434340977 := by
  unfold tailWord_4962371
  simp only [CollatzResearch.WordTrace]
  refine ⟨180992539505184847338550967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120661693003456564892367311 180992539505184847338550967)
  ·
    refine ⟨271488809257777271007826451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180992539505184847338550967 271488809257777271007826451)
    ·
      refine ⟨407233213886665906511739677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271488809257777271007826451 407233213886665906511739677)
      ·
        refine ⟨152712455207499714941902379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407233213886665906511739677 152712455207499714941902379)
        ·
          refine ⟨229068682811249572412853569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152712455207499714941902379 229068682811249572412853569)
          ·
            refine ⟨171801512108437179309640177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229068682811249572412853569 171801512108437179309640177)
            ·
              refine ⟨128851134081327884482230133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171801512108437179309640177 128851134081327884482230133)
              ·
                refine ⟨12079793820124489170209075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128851134081327884482230133 12079793820124489170209075)
                ·
                  refine ⟨18119690730186733755313613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12079793820124489170209075 18119690730186733755313613)
                  ·
                    refine ⟨6794884023820025158242605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18119690730186733755313613 6794884023820025158242605)
                    ·
                      refine ⟨2548081508932509434340977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6794884023820025158242605 2548081508932509434340977)
                      ·
                        rfl

theorem cell23_4962371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_4962371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962371 prefixEnd_4962371 := by exact prefixLift 4962371
  have htrace : WordTrace (prefixWord ++ tailWord_4962371) baseStart_4962371 baseEnd_4962371 := by
    simpa [prefixWord, tailWord_4962371, baseEnd_4962371] using wordTrace_append hprefix tailTrace_4962371
  have hstable : (prefixWord ++ tailWord_4962371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962371).length < 2 ^ (prefixWord ++ tailWord_4962371).sum := by decide
  have hdescent : baseEnd_4962371 < baseStart_4962371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962389 : List Nat := [1, 3, 2, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_4962389 : Nat := 118140960795 + 4962389 * 2 ^ 59
def prefixEnd_4962389 : Nat := 4983230072969 + 3 ^ 40 * 4962389 * 2
def baseEnd_4962389 : Nat := 2548090751584290363915895

theorem tailTrace_4962389 : CollatzResearch.WordTrace tailWord_4962389 prefixEnd_4962389 2548090751584290363915895 := by
  unfold tailWord_4962389
  simp only [CollatzResearch.WordTrace]
  refine ⟨180993196019119636412706221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120662130679413090941804147 180993196019119636412706221)
  ·
    refine ⟨67872448507169863654764833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180993196019119636412706221 67872448507169863654764833)
    ·
      refine ⟨50904336380377397741073625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67872448507169863654764833 50904336380377397741073625)
      ·
        refine ⟨38178252285283048305805219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50904336380377397741073625 38178252285283048305805219)
        ·
          refine ⟨57267378427924572458707829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38178252285283048305805219 57267378427924572458707829)
          ·
            refine ⟨5368816727617928668003859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57267378427924572458707829 5368816727617928668003859)
            ·
              refine ⟨8053225091426893002005789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5368816727617928668003859 8053225091426893002005789)
              ·
                refine ⟨3019959409285084875752171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8053225091426893002005789 3019959409285084875752171)
                ·
                  refine ⟨4529939113927627313628257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019959409285084875752171 4529939113927627313628257)
                  ·
                    refine ⟨3397454335445720485221193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4529939113927627313628257 3397454335445720485221193)
                    ·
                      refine ⟨2548090751584290363915895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397454335445720485221193 2548090751584290363915895)
                      ·
                        rfl

theorem cell23_4962389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_4962389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962389 prefixEnd_4962389 := by exact prefixLift 4962389
  have htrace : WordTrace (prefixWord ++ tailWord_4962389) baseStart_4962389 baseEnd_4962389 := by
    simpa [prefixWord, tailWord_4962389, baseEnd_4962389] using wordTrace_append hprefix tailTrace_4962389
  have hstable : (prefixWord ++ tailWord_4962389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962389).length < 2 ^ (prefixWord ++ tailWord_4962389).sum := by decide
  have hdescent : baseEnd_4962389 < baseStart_4962389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962422 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_4962422 : Nat := 118140960795 + 4962422 * 2 ^ 59
def prefixEnd_4962422 : Nat := 4983230072969 + 3 ^ 40 * 4962422 * 2
def baseEnd_4962422 : Nat := 2548107696445888734803243

theorem tailTrace_4962422 : CollatzResearch.WordTrace tailWord_4962422 prefixEnd_4962422 2548107696445888734803243 := by
  unfold tailWord_4962422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312149976750005190541095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120662933085333388699105013 11312149976750005190541095)
  ·
    refine ⟨16968224965125007785811643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11312149976750005190541095 16968224965125007785811643)
    ·
      refine ⟨25452337447687511678717465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16968224965125007785811643 25452337447687511678717465)
      ·
        refine ⟨19089253085765633759038099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25452337447687511678717465 19089253085765633759038099)
        ·
          refine ⟨28633879628648450638557149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19089253085765633759038099 28633879628648450638557149)
          ·
            refine ⟨10737704860743168989458931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28633879628648450638557149 10737704860743168989458931)
            ·
              refine ⟨16106557291114753484188397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10737704860743168989458931 16106557291114753484188397)
              ·
                refine ⟨6039958984168032556570649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16106557291114753484188397 6039958984168032556570649)
                ·
                  refine ⟨4529969238126024417427987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6039958984168032556570649 4529969238126024417427987)
                  ·
                    refine ⟨6794953857189036626141981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4529969238126024417427987 6794953857189036626141981)
                    ·
                      refine ⟨2548107696445888734803243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6794953857189036626141981 2548107696445888734803243)
                      ·
                        rfl

theorem cell23_4962422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_4962422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962422 prefixEnd_4962422 := by exact prefixLift 4962422
  have htrace : WordTrace (prefixWord ++ tailWord_4962422) baseStart_4962422 baseEnd_4962422 := by
    simpa [prefixWord, tailWord_4962422, baseEnd_4962422] using wordTrace_append hprefix tailTrace_4962422
  have hstable : (prefixWord ++ tailWord_4962422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962422).length < 2 ^ (prefixWord ++ tailWord_4962422).sum := by decide
  have hdescent : baseEnd_4962422 < baseStart_4962422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962485 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 7]
def baseStart_4962485 : Nat := 118140960795 + 4962485 * 2 ^ 59
def prefixEnd_4962485 : Nat := 4983230072969 + 3 ^ 40 * 4962485 * 2
def baseEnd_4962485 : Nat := 283126671747457998701717

theorem tailTrace_4962485 : CollatzResearch.WordTrace tailWord_4962485 prefixEnd_4962485 283126671747457998701717 := by
  unfold tailWord_4962485
  simp only [CollatzResearch.WordTrace]
  refine ⟨180996697426771844808200909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120664464951181229872133939 180996697426771844808200909)
  ·
    refine ⟨67873761535039441803075341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 180996697426771844808200909 67873761535039441803075341)
    ·
      refine ⟨25452660575639790676153253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67873761535039441803075341 25452660575639790676153253)
      ·
        refine ⟨4772373857932460751778735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25452660575639790676153253 4772373857932460751778735)
        ·
          refine ⟨7158560786898691127668103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772373857932460751778735 7158560786898691127668103)
          ·
            refine ⟨10737841180348036691502155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158560786898691127668103 10737841180348036691502155)
            ·
              refine ⟨16106761770522055037253233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10737841180348036691502155 16106761770522055037253233)
              ·
                refine ⟨12080071327891541277939925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16106761770522055037253233 12080071327891541277939925)
                ·
                  refine ⟨283126671747457998701717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12080071327891541277939925 283126671747457998701717)
                  ·
                    rfl

theorem cell23_4962485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_4962485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962485 prefixEnd_4962485 := by exact prefixLift 4962485
  have htrace : WordTrace (prefixWord ++ tailWord_4962485) baseStart_4962485 baseEnd_4962485 := by
    simpa [prefixWord, tailWord_4962485, baseEnd_4962485] using wordTrace_append hprefix tailTrace_4962485
  have hstable : (prefixWord ++ tailWord_4962485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962485).length < 2 ^ (prefixWord ++ tailWord_4962485).sum := by decide
  have hdescent : baseEnd_4962485 < baseStart_4962485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962488 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 2, 5, 2]
def baseStart_4962488 : Nat := 118140960795 + 4962488 * 2 ^ 59
def prefixEnd_4962488 : Nat := 4983230072969 + 3 ^ 40 * 4962488 * 2
def baseEnd_4962488 : Nat := 2548141586169085476577939

theorem tailTrace_4962488 : CollatzResearch.WordTrace tailWord_4962488 prefixEnd_4962488 2548141586169085476577939 := by
  unfold tailWord_4962488
  simp only [CollatzResearch.WordTrace]
  refine ⟨90498403422880488160280059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120664537897173984213706745 90498403422880488160280059)
  ·
    refine ⟨135747605134320732240420089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90498403422880488160280059 135747605134320732240420089)
    ·
      refine ⟨101810703850740549180315067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135747605134320732240420089 101810703850740549180315067)
      ·
        refine ⟨152716055776110823770472601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101810703850740549180315067 152716055776110823770472601)
        ·
          refine ⟨114537041832083117827854451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152716055776110823770472601 114537041832083117827854451)
          ·
            refine ⟨171805562748124676741781677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114537041832083117827854451 171805562748124676741781677)
            ·
              refine ⟨64427086030546753778168129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171805562748124676741781677 64427086030546753778168129)
              ·
                refine ⟨48320314522910065333626097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64427086030546753778168129 48320314522910065333626097)
                ·
                  refine ⟨36240235892182549000219573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48320314522910065333626097 36240235892182549000219573)
                  ·
                    refine ⟨3397522114892113968770585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36240235892182549000219573 3397522114892113968770585)
                    ·
                      refine ⟨2548141586169085476577939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397522114892113968770585 2548141586169085476577939)
                      ·
                        rfl

theorem cell23_4962488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_4962488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962488 prefixEnd_4962488 := by exact prefixLift 4962488
  have htrace : WordTrace (prefixWord ++ tailWord_4962488) baseStart_4962488 baseEnd_4962488 := by
    simpa [prefixWord, tailWord_4962488, baseEnd_4962488] using wordTrace_append hprefix tailTrace_4962488
  have hstable : (prefixWord ++ tailWord_4962488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962488).length < 2 ^ (prefixWord ++ tailWord_4962488).sum := by decide
  have hdescent : baseEnd_4962488 < baseStart_4962488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962521 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_4962521 : Nat := 118140960795 + 4962521 * 2 ^ 59
def prefixEnd_4962521 : Nat := 4983230072969 + 3 ^ 40 * 4962521 * 2
def baseEnd_4962521 : Nat := 2548158531030683847465287

theorem tailTrace_4962521 : CollatzResearch.WordTrace tailWord_4962521 prefixEnd_4962521 2548158531030683847465287 := by
  unfold tailWord_4962521
  simp only [CollatzResearch.WordTrace]
  refine ⟨180998010454641422956511417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120665340303094281971007611 180998010454641422956511417)
  ·
    refine ⟨135748507840981067217383563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180998010454641422956511417 135748507840981067217383563)
    ·
      refine ⟨203622761761471600826075345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135748507840981067217383563 203622761761471600826075345)
      ·
        refine ⟨152717071321103700619556509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203622761761471600826075345 152717071321103700619556509)
        ·
          refine ⟨57268901745413887732333691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152717071321103700619556509 57268901745413887732333691)
          ·
            refine ⟨85903352618120831598500537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57268901745413887732333691 85903352618120831598500537)
            ·
              refine ⟨64427514463590623698875403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85903352618120831598500537 64427514463590623698875403)
              ·
                refine ⟨96641271695385935548313105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64427514463590623698875403 96641271695385935548313105)
                ·
                  refine ⟨72480953771539451661234829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96641271695385935548313105 72480953771539451661234829)
                  ·
                    refine ⟨27180357664327294372963061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72480953771539451661234829 27180357664327294372963061)
                    ·
                      refine ⟨2548158531030683847465287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27180357664327294372963061 2548158531030683847465287)
                      ·
                        rfl

theorem cell23_4962521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_4962521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962521 prefixEnd_4962521 := by exact prefixLift 4962521
  have htrace : WordTrace (prefixWord ++ tailWord_4962521) baseStart_4962521 baseEnd_4962521 := by
    simpa [prefixWord, tailWord_4962521, baseEnd_4962521] using wordTrace_append hprefix tailTrace_4962521
  have hstable : (prefixWord ++ tailWord_4962521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962521).length < 2 ^ (prefixWord ++ tailWord_4962521).sum := by decide
  have hdescent : baseEnd_4962521 < baseStart_4962521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962530 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4962530 : Nat := 118140960795 + 4962530 * 2 ^ 59
def prefixEnd_4962530 : Nat := 4983230072969 + 3 ^ 40 * 4962530 * 2
def baseEnd_4962530 : Nat := 2548163152356574312252747

theorem tailTrace_4962530 : CollatzResearch.WordTrace tailWord_4962530 prefixEnd_4962530 2548163152356574312252747 := by
  unfold tailWord_4962530
  simp only [CollatzResearch.WordTrace]
  refine ⟨45249584677902204373397261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120665559141072544995726029 45249584677902204373397261)
  ·
    refine ⟨16968594254213326640023973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45249584677902204373397261 16968594254213326640023973)
    ·
      refine ⟨3181611422664998745004495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16968594254213326640023973 3181611422664998745004495)
      ·
        refine ⟨4772417133997498117506743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3181611422664998745004495 4772417133997498117506743)
        ·
          refine ⟨7158625700996247176260115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772417133997498117506743 7158625700996247176260115)
          ·
            refine ⟨10737938551494370764390173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158625700996247176260115 10737938551494370764390173)
            ·
              refine ⟨4026726956810389036646315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10737938551494370764390173 4026726956810389036646315)
              ·
                refine ⟨6040090435215583554969473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026726956810389036646315 6040090435215583554969473)
                ·
                  refine ⟨4530067826411687666227105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6040090435215583554969473 4530067826411687666227105)
                  ·
                    refine ⟨3397550869808765749670329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4530067826411687666227105 3397550869808765749670329)
                    ·
                      refine ⟨2548163152356574312252747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397550869808765749670329 2548163152356574312252747)
                      ·
                        rfl

theorem cell23_4962530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4962530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962530 prefixEnd_4962530 := by exact prefixLift 4962530
  have htrace : WordTrace (prefixWord ++ tailWord_4962530) baseStart_4962530 baseEnd_4962530 := by
    simpa [prefixWord, tailWord_4962530, baseEnd_4962530] using wordTrace_append hprefix tailTrace_4962530
  have hstable : (prefixWord ++ tailWord_4962530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962530).length < 2 ^ (prefixWord ++ tailWord_4962530).sum := by decide
  have hdescent : baseEnd_4962530 < baseStart_4962530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962538 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_4962538 : Nat := 118140960795 + 4962538 * 2 ^ 59
def prefixEnd_4962538 : Nat := 4983230072969 + 3 ^ 40 * 4962538 * 2
def baseEnd_4962538 : Nat := 2548167260201810280952709

theorem tailTrace_4962538 : CollatzResearch.WordTrace tailWord_4962538 prefixEnd_4962538 2548167260201810280952709 := by
  unfold tailWord_4962538
  simp only [CollatzResearch.WordTrace]
  refine ⟨45249657623894958714970067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120665753663719889906586845 45249657623894958714970067)
  ·
    refine ⟨67874486435842438072455101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45249657623894958714970067 67874486435842438072455101)
    ·
      refine ⟨25452932413440914277170663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67874486435842438072455101 25452932413440914277170663)
      ·
        refine ⟨38179398620161371415755995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25452932413440914277170663 38179398620161371415755995)
        ·
          refine ⟨57269097930242057123633993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38179398620161371415755995 57269097930242057123633993)
          ·
            refine ⟨42951823447681542842725495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57269097930242057123633993 42951823447681542842725495)
            ·
              refine ⟨64427735171522314264088243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42951823447681542842725495 64427735171522314264088243)
              ·
                refine ⟨96641602757283471396132365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64427735171522314264088243 96641602757283471396132365)
                ·
                  refine ⟨36240601033981301773549637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96641602757283471396132365 36240601033981301773549637)
                  ·
                    refine ⟨6795112693871494082540557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36240601033981301773549637 6795112693871494082540557)
                    ·
                      refine ⟨2548167260201810280952709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6795112693871494082540557 2548167260201810280952709)
                      ·
                        rfl

theorem cell23_4962538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_4962538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962538 prefixEnd_4962538 := by exact prefixLift 4962538
  have htrace : WordTrace (prefixWord ++ tailWord_4962538) baseStart_4962538 baseEnd_4962538 := by
    simpa [prefixWord, tailWord_4962538, baseEnd_4962538] using wordTrace_append hprefix tailTrace_4962538
  have hstable : (prefixWord ++ tailWord_4962538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962538).length < 2 ^ (prefixWord ++ tailWord_4962538).sum := by decide
  have hdescent : baseEnd_4962538 < baseStart_4962538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962558 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_4962558 : Nat := 118140960795 + 4962558 * 2 ^ 59
def prefixEnd_4962558 : Nat := 4983230072969 + 3 ^ 40 * 4962558 * 2
def baseEnd_4962558 : Nat := 283130836646100022522513

theorem tailTrace_4962558 : CollatzResearch.WordTrace tailWord_4962558 prefixEnd_4962558 283130836646100022522513 := by
  unfold tailWord_4962558
  simp only [CollatzResearch.WordTrace]
  refine ⟨22624919994438422284451041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120666239970338252183738885 22624919994438422284451041)
  ·
    refine ⟨16968689995828816713338281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22624919994438422284451041 16968689995828816713338281)
    ·
      refine ⟨12726517496871612535003711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16968689995828816713338281 12726517496871612535003711)
      ·
        refine ⟨19089776245307418802505567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12726517496871612535003711 19089776245307418802505567)
        ·
          refine ⟨28634664367961128203758351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19089776245307418802505567 28634664367961128203758351)
          ·
            refine ⟨42951996551941692305637527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28634664367961128203758351 42951996551941692305637527)
            ·
              refine ⟨64427994827912538458456291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42951996551941692305637527 64427994827912538458456291)
              ·
                refine ⟨96641992241868807687684437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64427994827912538458456291 96641992241868807687684437)
                ·
                  refine ⟨283130836646100022522513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 96641992241868807687684437 283130836646100022522513)
                  ·
                    rfl

theorem cell23_4962558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_4962558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962558 prefixEnd_4962558 := by exact prefixLift 4962558
  have htrace : WordTrace (prefixWord ++ tailWord_4962558) baseStart_4962558 baseEnd_4962558 := by
    simpa [prefixWord, tailWord_4962558, baseEnd_4962558] using wordTrace_append hprefix tailTrace_4962558
  have hstable : (prefixWord ++ tailWord_4962558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962558).length < 2 ^ (prefixWord ++ tailWord_4962558).sum := by decide
  have hdescent : baseEnd_4962558 < baseStart_4962558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962588 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_4962588 : Nat := 118140960795 + 4962588 * 2 ^ 59
def prefixEnd_4962588 : Nat := 4983230072969 + 3 ^ 40 * 4962588 * 2
def baseEnd_4962588 : Nat := 849397644744845028442493

theorem tailTrace_4962588 : CollatzResearch.WordTrace tailWord_4962588 prefixEnd_4962588 849397644744845028442493 := by
  unfold tailWord_4962588
  simp only [CollatzResearch.WordTrace]
  refine ⟨90500227072699346699600209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120666969430265795599466945 90500227072699346699600209)
  ·
    refine ⟨67875170304524510024700157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90500227072699346699600209 67875170304524510024700157)
    ·
      refine ⟨25453188864196691259262559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67875170304524510024700157 25453188864196691259262559)
      ·
        refine ⟨38179783296295036888893839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25453188864196691259262559 38179783296295036888893839)
        ·
          refine ⟨57269674944442555333340759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38179783296295036888893839 57269674944442555333340759)
          ·
            refine ⟨85904512416663833000011139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57269674944442555333340759 85904512416663833000011139)
            ·
              refine ⟨128856768624995749500016709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85904512416663833000011139 128856768624995749500016709)
              ·
                refine ⟨24160644117186703031253133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128856768624995749500016709 24160644117186703031253133)
                ·
                  refine ⟨9060241543945013636719925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24160644117186703031253133 9060241543945013636719925)
                  ·
                    refine ⟨849397644744845028442493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9060241543945013636719925 849397644744845028442493)
                    ·
                      rfl

theorem cell23_4962588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_4962588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962588 prefixEnd_4962588 := by exact prefixLift 4962588
  have htrace : WordTrace (prefixWord ++ tailWord_4962588) baseStart_4962588 baseEnd_4962588 := by
    simpa [prefixWord, tailWord_4962588, baseEnd_4962588] using wordTrace_append hprefix tailTrace_4962588
  have hstable : (prefixWord ++ tailWord_4962588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962588).length < 2 ^ (prefixWord ++ tailWord_4962588).sum := by decide
  have hdescent : baseEnd_4962588 < baseStart_4962588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962592 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 6]
def baseStart_4962592 : Nat := 118140960795 + 4962592 * 2 ^ 59
def prefixEnd_4962592 : Nat := 4983230072969 + 3 ^ 40 * 4962592 * 2
def baseEnd_4962592 : Nat := 283132776461905896630829

theorem tailTrace_4962592 : CollatzResearch.WordTrace tailWord_4962592 prefixEnd_4962592 283132776461905896630829 := by
  unfold tailWord_4962592
  simp only [CollatzResearch.WordTrace]
  refine ⟨90500300018692101041173015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120667066691589468054897353 90500300018692101041173015)
  ·
    refine ⟨135750450028038151561759523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90500300018692101041173015 135750450028038151561759523)
    ·
      refine ⟨203625675042057227342639285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135750450028038151561759523 203625675042057227342639285)
      ·
        refine ⟨19089907035192865063372433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203625675042057227342639285 19089907035192865063372433)
        ·
          refine ⟨14317430276394648797529325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19089907035192865063372433 14317430276394648797529325)
          ·
            refine ⟨5369036353647993299073497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14317430276394648797529325 5369036353647993299073497)
            ·
              refine ⟨4026777265235994974305123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5369036353647993299073497 4026777265235994974305123)
              ·
                refine ⟨6040165897853992461457685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026777265235994974305123 6040165897853992461457685)
                ·
                  refine ⟨283132776461905896630829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6040165897853992461457685 283132776461905896630829)
                  ·
                    rfl

theorem cell23_4962592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 6].length) (baseStart_4962592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962592 prefixEnd_4962592 := by exact prefixLift 4962592
  have htrace : WordTrace (prefixWord ++ tailWord_4962592) baseStart_4962592 baseEnd_4962592 := by
    simpa [prefixWord, tailWord_4962592, baseEnd_4962592] using wordTrace_append hprefix tailTrace_4962592
  have hstable : (prefixWord ++ tailWord_4962592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962592).length < 2 ^ (prefixWord ++ tailWord_4962592).sum := by decide
  have hdescent : baseEnd_4962592 < baseStart_4962592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962595 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 4, 3, 2]
def baseStart_4962595 : Nat := 118140960795 + 4962595 * 2 ^ 59
def prefixEnd_4962595 : Nat := 4983230072969 + 3 ^ 40 * 4962595 * 2
def baseEnd_4962595 : Nat := 2548196528599116557939947

theorem tailTrace_4962595 : CollatzResearch.WordTrace tailWord_4962595 prefixEnd_4962595 2548196528599116557939947 := by
  unfold tailWord_4962595
  simp only [CollatzResearch.WordTrace]
  refine ⟨181000709456373333594705239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120667139637582222396470159 181000709456373333594705239)
  ·
    refine ⟨271501064184560000392057859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181000709456373333594705239 271501064184560000392057859)
    ·
      refine ⟨407251596276840000588086789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271501064184560000392057859 407251596276840000588086789)
      ·
        refine ⟨76359674301907500110266273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407251596276840000588086789 76359674301907500110266273)
        ·
          refine ⟨57269755726430625082699705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76359674301907500110266273 57269755726430625082699705)
          ·
            refine ⟨42952316794822968812024779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57269755726430625082699705 42952316794822968812024779)
            ·
              refine ⟨64428475192234453218037169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42952316794822968812024779 64428475192234453218037169)
              ·
                refine ⟨48321356394175839913527877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64428475192234453218037169 48321356394175839913527877)
                ·
                  refine ⟨9060254323907969983786477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48321356394175839913527877 9060254323907969983786477)
                  ·
                    refine ⟨3397595371465488743919929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9060254323907969983786477 3397595371465488743919929)
                    ·
                      refine ⟨2548196528599116557939947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397595371465488743919929 2548196528599116557939947)
                      ·
                        rfl

theorem cell23_4962595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_4962595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962595 prefixEnd_4962595 := by exact prefixLift 4962595
  have htrace : WordTrace (prefixWord ++ tailWord_4962595) baseStart_4962595 baseEnd_4962595 := by
    simpa [prefixWord, tailWord_4962595, baseEnd_4962595] using wordTrace_append hprefix tailTrace_4962595
  have hstable : (prefixWord ++ tailWord_4962595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962595).length < 2 ^ (prefixWord ++ tailWord_4962595).sum := by decide
  have hdescent : baseEnd_4962595 < baseStart_4962595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962601 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 12]
def baseStart_4962601 : Nat := 118140960795 + 4962601 * 2 ^ 59
def prefixEnd_4962601 : Nat := 4983230072969 + 3 ^ 40 * 4962601 * 2
def baseEnd_4962601 : Nat := 849399869827681178154973

theorem tailTrace_4962601 : CollatzResearch.WordTrace tailWord_4962601 prefixEnd_4962601 849399869827681178154973 := by
  unfold tailWord_4962601
  simp only [CollatzResearch.WordTrace]
  refine ⟨181000928294351596619423657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120667285529567731079615771 181000928294351596619423657)
  ·
    refine ⟨135750696220763697464567743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181000928294351596619423657 135750696220763697464567743)
    ·
      refine ⟨203626044331145546196851615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135750696220763697464567743 203626044331145546196851615)
      ·
        refine ⟨305439066496718319295277423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203626044331145546196851615 305439066496718319295277423)
        ·
          refine ⟨458158599745077478942916135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305439066496718319295277423 458158599745077478942916135)
          ·
            refine ⟨687237899617616218414374203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458158599745077478942916135 687237899617616218414374203)
            ·
              refine ⟨1030856849426424327621561305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687237899617616218414374203 1030856849426424327621561305)
              ·
                refine ⟨773142637069818245716170979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030856849426424327621561305 773142637069818245716170979)
                ·
                  refine ⟨1159713955604727368574256469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773142637069818245716170979 1159713955604727368574256469)
                  ·
                    refine ⟨849399869827681178154973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1159713955604727368574256469 849399869827681178154973)
                    ·
                      rfl

theorem cell23_4962601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_4962601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962601 prefixEnd_4962601 := by exact prefixLift 4962601
  have htrace : WordTrace (prefixWord ++ tailWord_4962601) baseStart_4962601 baseEnd_4962601 := by
    simpa [prefixWord, tailWord_4962601, baseEnd_4962601] using wordTrace_append hprefix tailTrace_4962601
  have hstable : (prefixWord ++ tailWord_4962601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962601).length < 2 ^ (prefixWord ++ tailWord_4962601).sum := by decide
  have hdescent : baseEnd_4962601 < baseStart_4962601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962618 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_4962618 : Nat := 118140960795 + 4962618 * 2 ^ 59
def prefixEnd_4962618 : Nat := 4983230072969 + 3 ^ 40 * 4962618 * 2
def baseEnd_4962618 : Nat := 849402779551389989317447

theorem tailTrace_4962618 : CollatzResearch.WordTrace tailWord_4962618 prefixEnd_4962618 849402779551389989317447 := by
  unfold tailWord_4962618
  simp only [CollatzResearch.WordTrace]
  refine ⟨45250387083822502130698127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120667698890193339015195005 45250387083822502130698127)
  ·
    refine ⟨67875580625733753196047191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45250387083822502130698127 67875580625733753196047191)
    ·
      refine ⟨101813370938600629794070787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67875580625733753196047191 101813370938600629794070787)
      ·
        refine ⟨152720056407900944691106181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101813370938600629794070787 152720056407900944691106181)
        ·
          refine ⟨28635010576481427129582409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152720056407900944691106181 28635010576481427129582409)
          ·
            refine ⟨21476257932361070347186807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28635010576481427129582409 21476257932361070347186807)
            ·
              refine ⟨32214386898541605520780211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21476257932361070347186807 32214386898541605520780211)
              ·
                refine ⟨48321580347812408281170317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32214386898541605520780211 48321580347812408281170317)
                ·
                  refine ⟨18120592630429653105438869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48321580347812408281170317 18120592630429653105438869)
                  ·
                    refine ⟨849402779551389989317447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18120592630429653105438869 849402779551389989317447)
                    ·
                      rfl

theorem cell23_4962618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_4962618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962618 prefixEnd_4962618 := by exact prefixLift 4962618
  have htrace : WordTrace (prefixWord ++ tailWord_4962618) baseStart_4962618 baseEnd_4962618 := by
    simpa [prefixWord, tailWord_4962618, baseEnd_4962618] using wordTrace_append hprefix tailTrace_4962618
  have hstable : (prefixWord ++ tailWord_4962618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962618).length < 2 ^ (prefixWord ++ tailWord_4962618).sum := by decide
  have hdescent : baseEnd_4962618 < baseStart_4962618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962638 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_4962638 : Nat := 118140960795 + 4962638 * 2 ^ 59
def prefixEnd_4962638 : Nat := 4983230072969 + 3 ^ 40 * 4962638 * 2
def baseEnd_4962638 : Nat := 2548218608267259889702249

theorem tailTrace_4962638 : CollatzResearch.WordTrace tailWord_4962638 prefixEnd_4962638 2548218608267259889702249 := by
  unfold tailWord_4962638
  simp only [CollatzResearch.WordTrace]
  refine ⟨22625284724402193992315071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120668185196811701292347045 22625284724402193992315071)
  ·
    refine ⟨33937927086603290988472607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22625284724402193992315071 33937927086603290988472607)
    ·
      refine ⟨50906890629904936482708911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33937927086603290988472607 50906890629904936482708911)
      ·
        refine ⟨76360335944857404724063367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50906890629904936482708911 76360335944857404724063367)
        ·
          refine ⟨114540503917286107086095051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76360335944857404724063367 114540503917286107086095051)
          ·
            refine ⟨171810755875929160629142577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114540503917286107086095051 171810755875929160629142577)
            ·
              refine ⟨128858066906946870471856933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171810755875929160629142577 128858066906946870471856933)
              ·
                refine ⟨24160887545052538213473175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128858066906946870471856933 24160887545052538213473175)
                ·
                  refine ⟨36241331317578807320209763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24160887545052538213473175 36241331317578807320209763)
                  ·
                    refine ⟨54361996976368210980314645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36241331317578807320209763 54361996976368210980314645)
                    ·
                      refine ⟨2548218608267259889702249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54361996976368210980314645 2548218608267259889702249)
                      ·
                        rfl

theorem cell23_4962638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_4962638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962638 prefixEnd_4962638 := by exact prefixLift 4962638
  have htrace : WordTrace (prefixWord ++ tailWord_4962638) baseStart_4962638 baseEnd_4962638 := by
    simpa [prefixWord, tailWord_4962638, baseEnd_4962638] using wordTrace_append hprefix tailTrace_4962638
  have hstable : (prefixWord ++ tailWord_4962638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962638).length < 2 ^ (prefixWord ++ tailWord_4962638).sum := by decide
  have hdescent : baseEnd_4962638 < baseStart_4962638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962675 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 3]
def baseStart_4962675 : Nat := 118140960795 + 4962675 * 2 ^ 59
def prefixEnd_4962675 : Nat := 4983230072969 + 3 ^ 40 * 4962675 * 2
def baseEnd_4962675 : Nat := 2548237607051476244939579

theorem tailTrace_4962675 : CollatzResearch.WordTrace tailWord_4962675 prefixEnd_4962675 2548237607051476244939579 := by
  unfold tailWord_4962675
  simp only [CollatzResearch.WordTrace]
  refine ⟨181003627296083507257617479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120669084864055671505078319 181003627296083507257617479)
  ·
    refine ⟨271505440944125260886426219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181003627296083507257617479 271505440944125260886426219)
    ·
      refine ⟨407258161416187891329639329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271505440944125260886426219 407258161416187891329639329)
      ·
        refine ⟨305443621062140918497229497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407258161416187891329639329 305443621062140918497229497)
        ·
          refine ⟨229082715796605688872922123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305443621062140918497229497 229082715796605688872922123)
          ·
            refine ⟨343624073694908533309383185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229082715796605688872922123 343624073694908533309383185)
            ·
              refine ⟨257718055271181399982037389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343624073694908533309383185 257718055271181399982037389)
              ·
                refine ⟨96644270726693024993264021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257718055271181399982037389 96644270726693024993264021)
                ·
                  refine ⟨4530200190313735546559251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96644270726693024993264021 4530200190313735546559251)
                  ·
                    refine ⟨6795300285470603319838877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4530200190313735546559251 6795300285470603319838877)
                    ·
                      refine ⟨2548237607051476244939579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6795300285470603319838877 2548237607051476244939579)
                      ·
                        rfl

theorem cell23_4962675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 3].length) (baseStart_4962675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962675 prefixEnd_4962675 := by exact prefixLift 4962675
  have htrace : WordTrace (prefixWord ++ tailWord_4962675) baseStart_4962675 baseEnd_4962675 := by
    simpa [prefixWord, tailWord_4962675, baseEnd_4962675] using wordTrace_append hprefix tailTrace_4962675
  have hstable : (prefixWord ++ tailWord_4962675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962675).length < 2 ^ (prefixWord ++ tailWord_4962675).sum := by decide
  have hdescent : baseEnd_4962675 < baseStart_4962675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962692 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_4962692 : Nat := 118140960795 + 4962692 * 2 ^ 59
def prefixEnd_4962692 : Nat := 4983230072969 + 3 ^ 40 * 4962692 * 2
def baseEnd_4962692 : Nat := 2548246336222602678427001

theorem tailTrace_4962692 : CollatzResearch.WordTrace tailWord_4962692 prefixEnd_4962692 2548246336222602678427001 := by
  unfold tailWord_4962692
  simp only [CollatzResearch.WordTrace]
  refine ⟨90502123668510959580493165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120669498224681279440657553 90502123668510959580493165)
  ·
    refine ⟨33938296375691609842684937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90502123668510959580493165 33938296375691609842684937)
    ·
      refine ⟨25453722281768707382013703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33938296375691609842684937 25453722281768707382013703)
      ·
        refine ⟨38180583422653061073020555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25453722281768707382013703 38180583422653061073020555)
        ·
          refine ⟨57270875133979591609530833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38180583422653061073020555 57270875133979591609530833)
          ·
            refine ⟨42953156350484693707148125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57270875133979591609530833 42953156350484693707148125)
            ·
              refine ⟨16107433631431760140180547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42953156350484693707148125 16107433631431760140180547)
              ·
                refine ⟨24161150447147640210270821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16107433631431760140180547 24161150447147640210270821)
                ·
                  refine ⟨4530215708840182539425779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24161150447147640210270821 4530215708840182539425779)
                  ·
                    refine ⟨6795323563260273809138669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4530215708840182539425779 6795323563260273809138669)
                    ·
                      refine ⟨2548246336222602678427001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6795323563260273809138669 2548246336222602678427001)
                      ·
                        rfl

theorem cell23_4962692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_4962692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962692 prefixEnd_4962692 := by exact prefixLift 4962692
  have htrace : WordTrace (prefixWord ++ tailWord_4962692) baseStart_4962692 baseEnd_4962692 := by
    simpa [prefixWord, tailWord_4962692, baseEnd_4962692] using wordTrace_append hprefix tailTrace_4962692
  have hstable : (prefixWord ++ tailWord_4962692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962692).length < 2 ^ (prefixWord ++ tailWord_4962692).sum := by decide
  have hdescent : baseEnd_4962692 < baseStart_4962692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962719 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 1, 3, 2]
def baseStart_4962719 : Nat := 118140960795 + 4962719 * 2 ^ 59
def prefixEnd_4962719 : Nat := 4983230072969 + 3 ^ 40 * 4962719 * 2
def baseEnd_4962719 : Nat := 2548260200200274072789377

theorem tailTrace_4962719 : CollatzResearch.WordTrace tailWord_4962719 prefixEnd_4962719 2548260200200274072789377 := by
  unfold tailWord_4962719
  simp only [CollatzResearch.WordTrace]
  refine ⟨181005232107924102772219211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120670154738616068514812807 181005232107924102772219211)
  ·
    refine ⟨271507848161886154158328817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181005232107924102772219211 271507848161886154158328817)
    ·
      refine ⟨203630886121414615618746613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271507848161886154158328817 203630886121414615618746613)
      ·
        refine ⟨19090395573882620214257495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203630886121414615618746613 19090395573882620214257495)
        ·
          refine ⟨28635593360823930321386243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19090395573882620214257495 28635593360823930321386243)
          ·
            refine ⟨42953390041235895482079365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28635593360823930321386243 42953390041235895482079365)
            ·
              refine ⟨8053760632731730402889881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42953390041235895482079365 8053760632731730402889881)
              ·
                refine ⟨6040320474548797802167411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8053760632731730402889881 6040320474548797802167411)
                ·
                  refine ⟨9060480711823196703251117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6040320474548797802167411 9060480711823196703251117)
                  ·
                    refine ⟨3397680266933698763719169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9060480711823196703251117 3397680266933698763719169)
                    ·
                      refine ⟨2548260200200274072789377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397680266933698763719169 2548260200200274072789377)
                      ·
                        rfl

theorem cell23_4962719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_4962719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962719 prefixEnd_4962719 := by exact prefixLift 4962719
  have htrace : WordTrace (prefixWord ++ tailWord_4962719) baseStart_4962719 baseEnd_4962719 := by
    simpa [prefixWord, tailWord_4962719, baseEnd_4962719] using wordTrace_append hprefix tailTrace_4962719
  have hstable : (prefixWord ++ tailWord_4962719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962719).length < 2 ^ (prefixWord ++ tailWord_4962719).sum := by decide
  have hdescent : baseEnd_4962719 < baseStart_4962719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962749 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_4962749 : Nat := 118140960795 + 4962749 * 2 ^ 59
def prefixEnd_4962749 : Nat := 4983230072969 + 3 ^ 40 * 4962749 * 2
def baseEnd_4962749 : Nat := 2548275604619908955414239

theorem tailTrace_4962749 : CollatzResearch.WordTrace tailWord_4962749 prefixEnd_4962749 2548275604619908955414239 := by
  unfold tailWord_4962749
  simp only [CollatzResearch.WordTrace]
  refine ⟨181006326297815417895811301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120670884198543611930540867 181006326297815417895811301)
  ·
    refine ⟨33938686180840390855464619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181006326297815417895811301 33938686180840390855464619)
    ·
      refine ⟨50908029271260586283196929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33938686180840390855464619 50908029271260586283196929)
      ·
        refine ⟨38181021953445439712397697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50908029271260586283196929 38181021953445439712397697)
        ·
          refine ⟨28635766465084079784298273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38181021953445439712397697 28635766465084079784298273)
          ·
            refine ⟨21476824848813059838223705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28635766465084079784298273 21476824848813059838223705)
            ·
              refine ⟨16107618636609794878667779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21476824848813059838223705 16107618636609794878667779)
              ·
                refine ⟨24161427954914692318001669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16107618636609794878667779 24161427954914692318001669)
                ·
                  refine ⟨4530267741546504809625313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24161427954914692318001669 4530267741546504809625313)
                  ·
                    refine ⟨3397700806159878607218985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4530267741546504809625313 3397700806159878607218985)
                    ·
                      refine ⟨2548275604619908955414239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397700806159878607218985 2548275604619908955414239)
                      ·
                        rfl

theorem cell23_4962749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_4962749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962749 prefixEnd_4962749 := by exact prefixLift 4962749
  have htrace : WordTrace (prefixWord ++ tailWord_4962749) baseStart_4962749 baseEnd_4962749 := by
    simpa [prefixWord, tailWord_4962749, baseEnd_4962749] using wordTrace_append hprefix tailTrace_4962749
  have hstable : (prefixWord ++ tailWord_4962749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962749).length < 2 ^ (prefixWord ++ tailWord_4962749).sum := by decide
  have hdescent : baseEnd_4962749 < baseStart_4962749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962770 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_4962770 : Nat := 118140960795 + 4962770 * 2 ^ 59
def prefixEnd_4962770 : Nat := 4983230072969 + 3 ^ 40 * 4962770 * 2
def baseEnd_4962770 : Nat := 2548286387713653373251643

theorem tailTrace_4962770 : CollatzResearch.WordTrace tailWord_4962770 prefixEnd_4962770 2548286387713653373251643 := by
  unfold tailWord_4962770
  simp only [CollatzResearch.WordTrace]
  refine ⟨45251773057684834620581441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120671394820492892321550509 45251773057684834620581441)
  ·
    refine ⟨33938829793263625965436081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45251773057684834620581441 33938829793263625965436081)
    ·
      refine ⟨25454122344947719474077061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33938829793263625965436081 25454122344947719474077061)
      ·
        refine ⟨4772647939677697401389449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25454122344947719474077061 4772647939677697401389449)
        ·
          refine ⟨3579485954758273051042087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4772647939677697401389449 3579485954758273051042087)
          ·
            refine ⟨5369228932137409576563131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579485954758273051042087 5369228932137409576563131)
            ·
              refine ⟨8053843398206114364844697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5369228932137409576563131 8053843398206114364844697)
              ·
                refine ⟨6040382548654585773633523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8053843398206114364844697 6040382548654585773633523)
                ·
                  refine ⟨9060573822981878660450285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6040382548654585773633523 9060573822981878660450285)
                  ·
                    refine ⟨3397715183618204497668857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9060573822981878660450285 3397715183618204497668857)
                    ·
                      refine ⟨2548286387713653373251643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397715183618204497668857 2548286387713653373251643)
                      ·
                        rfl

theorem cell23_4962770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_4962770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962770 prefixEnd_4962770 := by exact prefixLift 4962770
  have htrace : WordTrace (prefixWord ++ tailWord_4962770) baseStart_4962770 baseEnd_4962770 := by
    simpa [prefixWord, tailWord_4962770, baseEnd_4962770] using wordTrace_append hprefix tailTrace_4962770
  have hstable : (prefixWord ++ tailWord_4962770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962770).length < 2 ^ (prefixWord ++ tailWord_4962770).sum := by decide
  have hdescent : baseEnd_4962770 < baseStart_4962770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962836 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4962836 : Nat := 118140960795 + 4962836 * 2 ^ 59
def prefixEnd_4962836 : Nat := 4983230072969 + 3 ^ 40 * 4962836 * 2
def baseEnd_4962836 : Nat := 849440092478950038342113

theorem tailTrace_4962836 : CollatzResearch.WordTrace tailWord_4962836 prefixEnd_4962836 849440092478950038342113 := by
  unfold tailWord_4962836
  simp only [CollatzResearch.WordTrace]
  refine ⟨90504749724250115877114181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120672999632333487836152241 90504749724250115877114181)
  ·
    refine ⟨16969640573296896726958909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90504749724250115877114181 16969640573296896726958909)
    ·
      refine ⟨6363615214986336272609591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16969640573296896726958909 6363615214986336272609591)
      ·
        refine ⟨9545422822479504408914387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6363615214986336272609591 9545422822479504408914387)
        ·
          refine ⟨14318134233719256613371581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9545422822479504408914387 14318134233719256613371581)
          ·
            refine ⟨5369300337644721230014343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14318134233719256613371581 5369300337644721230014343)
            ·
              refine ⟨8053950506467081845021515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5369300337644721230014343 8053950506467081845021515)
              ·
                refine ⟨12080925759700622767532273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8053950506467081845021515 12080925759700622767532273)
                ·
                  refine ⟨9060694319775467075649205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12080925759700622767532273 9060694319775467075649205)
                  ·
                    refine ⟨849440092478950038342113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9060694319775467075649205 849440092478950038342113)
                    ·
                      rfl

theorem cell23_4962836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4962836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962836 prefixEnd_4962836 := by exact prefixLift 4962836
  have htrace : WordTrace (prefixWord ++ tailWord_4962836) baseStart_4962836 baseEnd_4962836 := by
    simpa [prefixWord, tailWord_4962836, baseEnd_4962836] using wordTrace_append hprefix tailTrace_4962836
  have hstable : (prefixWord ++ tailWord_4962836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962836).length < 2 ^ (prefixWord ++ tailWord_4962836).sum := by decide
  have hdescent : baseEnd_4962836 < baseStart_4962836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962839 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_4962839 : Nat := 118140960795 + 4962839 * 2 ^ 59
def prefixEnd_4962839 : Nat := 4983230072969 + 3 ^ 40 * 4962839 * 2
def baseEnd_4962839 : Nat := 2548321817878813603288825

theorem tailTrace_4962839 : CollatzResearch.WordTrace tailWord_4962839 prefixEnd_4962839 2548321817878813603288825 := by
  unfold tailWord_4962839
  simp only [CollatzResearch.WordTrace]
  refine ⟨181009608867489363266587571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120673072578326242177725047 181009608867489363266587571)
  ·
    refine ⟨271514413301234044899881357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181009608867489363266587571 271514413301234044899881357)
    ·
      refine ⟨101817904987962766837455509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271514413301234044899881357 101817904987962766837455509)
      ·
        refine ⟨4772714296310754695505727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 101817904987962766837455509 4772714296310754695505727)
        ·
          refine ⟨7159071444466132043258591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772714296310754695505727 7159071444466132043258591)
          ·
            refine ⟨10738607166699198064887887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7159071444466132043258591 10738607166699198064887887)
            ·
              refine ⟨16107910750048797097331831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10738607166699198064887887 16107910750048797097331831)
              ·
                refine ⟨24161866125073195645997747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16107910750048797097331831 24161866125073195645997747)
                ·
                  refine ⟨36242799187609793468996621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24161866125073195645997747 36242799187609793468996621)
                  ·
                    refine ⟨13591049695353672550873733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36242799187609793468996621 13591049695353672550873733)
                    ·
                      refine ⟨2548321817878813603288825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13591049695353672550873733 2548321817878813603288825)
                      ·
                        rfl

theorem cell23_4962839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_4962839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962839 prefixEnd_4962839 := by exact prefixLift 4962839
  have htrace : WordTrace (prefixWord ++ tailWord_4962839) baseStart_4962839 baseEnd_4962839 := by
    simpa [prefixWord, tailWord_4962839, baseEnd_4962839] using wordTrace_append hprefix tailTrace_4962839
  have hstable : (prefixWord ++ tailWord_4962839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962839).length < 2 ^ (prefixWord ++ tailWord_4962839).sum := by decide
  have hdescent : baseEnd_4962839 < baseStart_4962839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962865 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_4962865 : Nat := 118140960795 + 4962865 * 2 ^ 59
def prefixEnd_4962865 : Nat := 4983230072969 + 3 ^ 40 * 4962865 * 2
def baseEnd_4962865 : Nat := 2548335168375830501563705

theorem tailTrace_4962865 : CollatzResearch.WordTrace tailWord_4962865 prefixEnd_4962865 2548335168375830501563705 := by
  unfold tailWord_4962865
  simp only [CollatzResearch.WordTrace]
  refine ⟨181010557165395169707034049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120673704776930113138022699 181010557165395169707034049)
  ·
    refine ⟨135757917874046377280275537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181010557165395169707034049 135757917874046377280275537)
    ·
      refine ⟨101818438405534782960206653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135757917874046377280275537 101818438405534782960206653)
      ·
        refine ⟨38181914402075543610077495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101818438405534782960206653 38181914402075543610077495)
        ·
          refine ⟨57272871603113315415116243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38181914402075543610077495 57272871603113315415116243)
          ·
            refine ⟨85909307404669973122674365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57272871603113315415116243 85909307404669973122674365)
            ·
              refine ⟨32215990276751239921002887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85909307404669973122674365 32215990276751239921002887)
              ·
                refine ⟨48323985415126859881504331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32215990276751239921002887 48323985415126859881504331)
                ·
                  refine ⟨72485978122690289822256497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48323985415126859881504331 72485978122690289822256497)
                  ·
                    refine ⟨54364483592017717366692373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72485978122690289822256497 54364483592017717366692373)
                    ·
                      refine ⟨2548335168375830501563705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54364483592017717366692373 2548335168375830501563705)
                      ·
                        rfl

theorem cell23_4962865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_4962865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962865 prefixEnd_4962865 := by exact prefixLift 4962865
  have htrace : WordTrace (prefixWord ++ tailWord_4962865) baseStart_4962865 baseEnd_4962865 := by
    simpa [prefixWord, tailWord_4962865, baseEnd_4962865] using wordTrace_append hprefix tailTrace_4962865
  have hstable : (prefixWord ++ tailWord_4962865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962865).length < 2 ^ (prefixWord ++ tailWord_4962865).sum := by decide
  have hdescent : baseEnd_4962865 < baseStart_4962865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962910 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4962910 : Nat := 118140960795 + 4962910 * 2 ^ 59
def prefixEnd_4962910 : Nat := 4983230072969 + 3 ^ 40 * 4962910 * 2
def baseEnd_4962910 : Nat := 2548358275005282825500999

theorem tailTrace_4962910 : CollatzResearch.WordTrace tailWord_4962910 prefixEnd_4962910 2548358275005282825500999 := by
  unfold tailWord_4962910
  simp only [CollatzResearch.WordTrace]
  refine ⟨22626524806279017799052773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120674798966821428261614789 22626524806279017799052773)
  ·
    refine ⟨4242473401177315837322395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22626524806279017799052773 4242473401177315837322395)
    ·
      refine ⟨6363710101765973755983593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4242473401177315837322395 6363710101765973755983593)
      ·
        refine ⟨4772782576324480316987695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6363710101765973755983593 4772782576324480316987695)
        ·
          refine ⟨7159173864486720475481543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772782576324480316987695 7159173864486720475481543)
          ·
            refine ⟨10738760796730080713222315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7159173864486720475481543 10738760796730080713222315)
            ·
              refine ⟨16108141195095121069833473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10738760796730080713222315 16108141195095121069833473)
              ·
                refine ⟨12081105896321340802375105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16108141195095121069833473 12081105896321340802375105)
                ·
                  refine ⟨9060829422241005601781329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12081105896321340802375105 9060829422241005601781329)
                  ·
                    refine ⟨6795622066680754201335997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9060829422241005601781329 6795622066680754201335997)
                    ·
                      refine ⟨2548358275005282825500999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6795622066680754201335997 2548358275005282825500999)
                      ·
                        rfl

theorem cell23_4962910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4962910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962910 prefixEnd_4962910 := by exact prefixLift 4962910
  have htrace : WordTrace (prefixWord ++ tailWord_4962910) baseStart_4962910 baseEnd_4962910 := by
    simpa [prefixWord, tailWord_4962910, baseEnd_4962910] using wordTrace_append hprefix tailTrace_4962910
  have hstable : (prefixWord ++ tailWord_4962910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962910).length < 2 ^ (prefixWord ++ tailWord_4962910).sum := by decide
  have hdescent : baseEnd_4962910 < baseStart_4962910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962935 : List Nat := [1, 1, 3, 1, 1, 3, 3, 10]
def baseStart_4962935 : Nat := 118140960795 + 4962935 * 2 ^ 59
def prefixEnd_4962935 : Nat := 4983230072969 + 3 ^ 40 * 4962935 * 2
def baseEnd_4962935 : Nat := 94384115260060934358829

theorem tailTrace_4962935 : CollatzResearch.WordTrace tailWord_4962935 prefixEnd_4962935 94384115260060934358829 := by
  unfold tailWord_4962935
  simp only [CollatzResearch.WordTrace]
  refine ⟨181013110275141571662082259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120675406850094381108054839 181013110275141571662082259)
  ·
    refine ⟨271519665412712357493123389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181013110275141571662082259 271519665412712357493123389)
    ·
      refine ⟨101819874529767134059921271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271519665412712357493123389 101819874529767134059921271)
      ·
        refine ⟨152729811794650701089881907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101819874529767134059921271 152729811794650701089881907)
        ·
          refine ⟨229094717691976051634822861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152729811794650701089881907 229094717691976051634822861)
          ·
            refine ⟨85910519134491019363058573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229094717691976051634822861 85910519134491019363058573)
            ·
              refine ⟨32216444675434132261146965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85910519134491019363058573 32216444675434132261146965)
              ·
                refine ⟨94384115260060934358829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32216444675434132261146965 94384115260060934358829)
                ·
                  rfl

theorem cell23_4962935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 10].length) (baseStart_4962935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962935 prefixEnd_4962935 := by exact prefixLift 4962935
  have htrace : WordTrace (prefixWord ++ tailWord_4962935) baseStart_4962935 baseEnd_4962935 := by
    simpa [prefixWord, tailWord_4962935, baseEnd_4962935] using wordTrace_append hprefix tailTrace_4962935
  have hstable : (prefixWord ++ tailWord_4962935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962935).length < 2 ^ (prefixWord ++ tailWord_4962935).sum := by decide
  have hdescent : baseEnd_4962935 < baseStart_4962935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4962949 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_4962949 : Nat := 118140960795 + 4962949 * 2 ^ 59
def prefixEnd_4962949 : Nat := 4983230072969 + 3 ^ 40 * 4962949 * 2
def baseEnd_4962949 : Nat := 2548378300750808172913319

theorem tailTrace_4962949 : CollatzResearch.WordTrace tailWord_4962949 prefixEnd_4962949 2548378300750808172913319 := by
  unfold tailWord_4962949
  simp only [CollatzResearch.WordTrace]
  refine ⟨181013620897090852053091901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120675747264727234702061267 181013620897090852053091901)
  ·
    refine ⟨67880107836409069519909463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181013620897090852053091901 67880107836409069519909463)
    ·
      refine ⟨101820161754613604279864195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67880107836409069519909463 101820161754613604279864195)
      ·
        refine ⟨152730242631920406419796293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101820161754613604279864195 152730242631920406419796293)
        ·
          refine ⟨28636920493485076203711805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152730242631920406419796293 28636920493485076203711805)
          ·
            refine ⟨10738845185056903576391927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28636920493485076203711805 10738845185056903576391927)
            ·
              refine ⟨16108267777585355364587891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10738845185056903576391927 16108267777585355364587891)
              ·
                refine ⟨24162401666378033046881837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16108267777585355364587891 24162401666378033046881837)
                ·
                  refine ⟨9060900624891762392580689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24162401666378033046881837 9060900624891762392580689)
                  ·
                    refine ⟨6795675468668821794435517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9060900624891762392580689 6795675468668821794435517)
                    ·
                      refine ⟨2548378300750808172913319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6795675468668821794435517 2548378300750808172913319)
                      ·
                        rfl

theorem cell23_4962949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_4962949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4962949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4962949 prefixEnd_4962949 := by exact prefixLift 4962949
  have htrace : WordTrace (prefixWord ++ tailWord_4962949) baseStart_4962949 baseEnd_4962949 := by
    simpa [prefixWord, tailWord_4962949, baseEnd_4962949] using wordTrace_append hprefix tailTrace_4962949
  have hstable : (prefixWord ++ tailWord_4962949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4962949).length < 2 ^ (prefixWord ++ tailWord_4962949).sum := by decide
  have hdescent : baseEnd_4962949 < baseStart_4962949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4962949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963002 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_4963002 : Nat := 118140960795 + 4963002 * 2 ^ 59
def prefixEnd_4963002 : Nat := 4983230072969 + 3 ^ 40 * 4963002 * 2
def baseEnd_4963002 : Nat := 2548405515225496465550575

theorem tailTrace_4963002 : CollatzResearch.WordTrace tailWord_4963002 prefixEnd_4963002 2548405515225496465550575 := by
  unfold tailWord_4963002
  simp only [CollatzResearch.WordTrace]
  refine ⟨45253888491474710526192815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120677035977265894736514173 45253888491474710526192815)
  ·
    refine ⟨67880832737212065789289223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45253888491474710526192815 67880832737212065789289223)
    ·
      refine ⟨101821249105818098683933835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67880832737212065789289223 101821249105818098683933835)
      ·
        refine ⟨152731873658727148025900753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101821249105818098683933835 152731873658727148025900753)
        ·
          refine ⟨114548905244045361019425565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152731873658727148025900753 114548905244045361019425565)
          ·
            refine ⟨42955839466517010382284587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114548905244045361019425565 42955839466517010382284587)
            ·
              refine ⟨64433759199775515573426881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42955839466517010382284587 64433759199775515573426881)
              ·
                refine ⟨48325319399831636680070161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64433759199775515573426881 48325319399831636680070161)
                ·
                  refine ⟨36243989549873727510052621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48325319399831636680070161 36243989549873727510052621)
                  ·
                    refine ⟨13591496081202647816269733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36243989549873727510052621 13591496081202647816269733)
                    ·
                      refine ⟨2548405515225496465550575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13591496081202647816269733 2548405515225496465550575)
                      ·
                        rfl

theorem cell23_4963002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_4963002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963002 prefixEnd_4963002 := by exact prefixLift 4963002
  have htrace : WordTrace (prefixWord ++ tailWord_4963002) baseStart_4963002 baseEnd_4963002 := by
    simpa [prefixWord, tailWord_4963002, baseEnd_4963002] using wordTrace_append hprefix tailTrace_4963002
  have hstable : (prefixWord ++ tailWord_4963002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963002).length < 2 ^ (prefixWord ++ tailWord_4963002).sum := by decide
  have hdescent : baseEnd_4963002 < baseStart_4963002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963006 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_4963006 : Nat := 118140960795 + 4963006 * 2 ^ 59
def prefixEnd_4963006 : Nat := 4983230072969 + 3 ^ 40 * 4963006 * 2
def baseEnd_4963006 : Nat := 2548407569148114449900557

theorem tailTrace_4963006 : CollatzResearch.WordTrace tailWord_4963006 prefixEnd_4963006 2548407569148114449900557 := by
  unfold tailWord_4963006
  simp only [CollatzResearch.WordTrace]
  refine ⟨22626962482235543848489609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120677133238589567191944581 22626962482235543848489609)
  ·
    refine ⟨16970221861676657886367207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22626962482235543848489609 16970221861676657886367207)
    ·
      refine ⟨25455332792514986829550811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16970221861676657886367207 25455332792514986829550811)
      ·
        refine ⟨38182999188772480244326217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25455332792514986829550811 38182999188772480244326217)
        ·
          refine ⟨28637249391579360183244663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38182999188772480244326217 28637249391579360183244663)
          ·
            refine ⟨42955874087369040274866995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28637249391579360183244663 42955874087369040274866995)
            ·
              refine ⟨64433811131053560412300493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42955874087369040274866995 64433811131053560412300493)
              ·
                refine ⟨24162679174145085154612685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64433811131053560412300493 24162679174145085154612685)
                ·
                  refine ⟨9061004690304406932979757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24162679174145085154612685 9061004690304406932979757)
                  ·
                    refine ⟨3397876758864152599867409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9061004690304406932979757 3397876758864152599867409)
                    ·
                      refine ⟨2548407569148114449900557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3397876758864152599867409 2548407569148114449900557)
                      ·
                        rfl

theorem cell23_4963006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_4963006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963006 prefixEnd_4963006 := by exact prefixLift 4963006
  have htrace : WordTrace (prefixWord ++ tailWord_4963006) baseStart_4963006 baseEnd_4963006 := by
    simpa [prefixWord, tailWord_4963006, baseEnd_4963006] using wordTrace_append hprefix tailTrace_4963006
  have hstable : (prefixWord ++ tailWord_4963006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963006).length < 2 ^ (prefixWord ++ tailWord_4963006).sum := by decide
  have hdescent : baseEnd_4963006 < baseStart_4963006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963014 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_4963014 : Nat := 118140960795 + 4963014 * 2 ^ 59
def prefixEnd_4963014 : Nat := 4983230072969 + 3 ^ 40 * 4963014 * 2
def baseEnd_4963014 : Nat := 2548411676993350418600521

theorem tailTrace_4963014 : CollatzResearch.WordTrace tailWord_4963014 prefixEnd_4963014 2548411676993350418600521 := by
  unfold tailWord_4963014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5656749738807980254819003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120677327761236912102805397 5656749738807980254819003)
  ·
    refine ⟨8485124608211970382228505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5656749738807980254819003 8485124608211970382228505)
    ·
      refine ⟨6363843456158977786671379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8485124608211970382228505 6363843456158977786671379)
      ·
        refine ⟨9545765184238466680007069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6363843456158977786671379 9545765184238466680007069)
        ·
          refine ⟨3579661944089425005002651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9545765184238466680007069 3579661944089425005002651)
          ·
            refine ⟨5369492916134137507503977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579661944089425005002651 5369492916134137507503977)
            ·
              refine ⟨4027119687100603130627983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5369492916134137507503977 4027119687100603130627983)
              ·
                refine ⟨6040679530650904695941975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4027119687100603130627983 6040679530650904695941975)
                ·
                  refine ⟨9061019295976357043912963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6040679530650904695941975 9061019295976357043912963)
                  ·
                    refine ⟨13591528943964535565869445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9061019295976357043912963 13591528943964535565869445)
                    ·
                      refine ⟨2548411676993350418600521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13591528943964535565869445 2548411676993350418600521)
                      ·
                        rfl

theorem cell23_4963014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_4963014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963014 prefixEnd_4963014 := by exact prefixLift 4963014
  have htrace : WordTrace (prefixWord ++ tailWord_4963014) baseStart_4963014 baseEnd_4963014 := by
    simpa [prefixWord, tailWord_4963014, baseEnd_4963014] using wordTrace_append hprefix tailTrace_4963014
  have hstable : (prefixWord ++ tailWord_4963014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963014).length < 2 ^ (prefixWord ++ tailWord_4963014).sum := by decide
  have hdescent : baseEnd_4963014 < baseStart_4963014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963109 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_4963109 : Nat := 118140960795 + 4963109 * 2 ^ 59
def prefixEnd_4963109 : Nat := 4983230072969 + 3 ^ 40 * 4963109 * 2
def baseEnd_4963109 : Nat := 2548460457655527546912583

theorem tailTrace_4963109 : CollatzResearch.WordTrace tailWord_4963109 prefixEnd_4963109 2548460457655527546912583 := by
  unfold tailWord_4963109
  simp only [CollatzResearch.WordTrace]
  refine ⟨181019456576511199378916381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120679637717674132919277587 181019456576511199378916381)
  ·
    refine ⟨67882296216191699767093643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181019456576511199378916381 67882296216191699767093643)
    ·
      refine ⟨101823444324287549650640465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67882296216191699767093643 101823444324287549650640465)
      ·
        refine ⟨76367583243215662237980349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101823444324287549650640465 76367583243215662237980349)
        ·
          refine ⟨28637843716205873339242631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76367583243215662237980349 28637843716205873339242631)
          ·
            refine ⟨42956765574308810008863947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28637843716205873339242631 42956765574308810008863947)
            ·
              refine ⟨64435148361463215013295921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42956765574308810008863947 64435148361463215013295921)
              ·
                refine ⟨48326361271097411259971941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64435148361463215013295921 48326361271097411259971941)
                ·
                  refine ⟨9061192738330764611244739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48326361271097411259971941 9061192738330764611244739)
                  ·
                    refine ⟨13591789107496146916867109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9061192738330764611244739 13591789107496146916867109)
                    ·
                      refine ⟨2548460457655527546912583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13591789107496146916867109 2548460457655527546912583)
                      ·
                        rfl

theorem cell23_4963109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_4963109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963109 prefixEnd_4963109 := by exact prefixLift 4963109
  have htrace : WordTrace (prefixWord ++ tailWord_4963109) baseStart_4963109 baseEnd_4963109 := by
    simpa [prefixWord, tailWord_4963109, baseEnd_4963109] using wordTrace_append hprefix tailTrace_4963109
  have hstable : (prefixWord ++ tailWord_4963109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963109).length < 2 ^ (prefixWord ++ tailWord_4963109).sum := by decide
  have hdescent : baseEnd_4963109 < baseStart_4963109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963179 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 3, 5]
def baseStart_4963179 : Nat := 118140960795 + 4963179 * 2 ^ 59
def prefixEnd_4963179 : Nat := 4983230072969 + 3 ^ 40 * 4963179 * 2
def baseEnd_4963179 : Nat := 849498800433780757679087

theorem tailTrace_4963179 : CollatzResearch.WordTrace tailWord_4963179 prefixEnd_4963179 849498800433780757679087 := by
  unfold tailWord_4963179
  simp only [CollatzResearch.WordTrace]
  refine ⟨181022009686257601333964591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120681339790838400889309727 181022009686257601333964591)
  ·
    refine ⟨271533014529386402000946887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181022009686257601333964591 271533014529386402000946887)
    ·
      refine ⟨407299521794079603001420331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271533014529386402000946887 407299521794079603001420331)
      ·
        refine ⟨610949282691119404502130497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407299521794079603001420331 610949282691119404502130497)
        ·
          refine ⟨458211962018339553376597873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610949282691119404502130497 458211962018339553376597873)
          ·
            refine ⟨343658971513754665032448405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458211962018339553376597873 343658971513754665032448405)
            ·
              refine ⟨16109014289707249923396019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 343658971513754665032448405 16109014289707249923396019)
              ·
                refine ⟨24163521434560874885094029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16109014289707249923396019 24163521434560874885094029)
                ·
                  refine ⟨9061320537960328081910261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24163521434560874885094029 9061320537960328081910261)
                  ·
                    refine ⟨849498800433780757679087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9061320537960328081910261 849498800433780757679087)
                    ·
                      rfl

theorem cell23_4963179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 5].length) (baseStart_4963179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963179 prefixEnd_4963179 := by exact prefixLift 4963179
  have htrace : WordTrace (prefixWord ++ tailWord_4963179) baseStart_4963179 baseEnd_4963179 := by
    simpa [prefixWord, tailWord_4963179, baseEnd_4963179] using wordTrace_append hprefix tailTrace_4963179
  have hstable : (prefixWord ++ tailWord_4963179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963179).length < 2 ^ (prefixWord ++ tailWord_4963179).sum := by decide
  have hdescent : baseEnd_4963179 < baseStart_4963179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963210 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_4963210 : Nat := 118140960795 + 4963210 * 2 ^ 59
def prefixEnd_4963210 : Nat := 4983230072969 + 3 ^ 40 * 4963210 * 2
def baseEnd_4963210 : Nat := 2548512319201631651749619

theorem tailTrace_4963210 : CollatzResearch.WordTrace tailWord_4963210 prefixEnd_4963210 2548512319201631651749619 := by
  unfold tailWord_4963210
  simp only [CollatzResearch.WordTrace]
  refine ⟨45255785087286323407085771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120682093566096862418895389 45255785087286323407085771)
  ·
    refine ⟨67883677630929485110628657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45255785087286323407085771 67883677630929485110628657)
    ·
      refine ⟨50912758223197113832971493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67883677630929485110628657 50912758223197113832971493)
      ·
        refine ⟨9546142166849458843682155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50912758223197113832971493 9546142166849458843682155)
        ·
          refine ⟨14319213250274188265523233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546142166849458843682155 14319213250274188265523233)
          ·
            refine ⟨10739409937705641199142425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14319213250274188265523233 10739409937705641199142425)
            ·
              refine ⟨8054557453279230899356819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10739409937705641199142425 8054557453279230899356819)
              ·
                refine ⟨12081836179918846349035229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8054557453279230899356819 12081836179918846349035229)
                ·
                  refine ⟨4530688567469567380888211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12081836179918846349035229 4530688567469567380888211)
                  ·
                    refine ⟨6796032851204351071332317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4530688567469567380888211 6796032851204351071332317)
                    ·
                      refine ⟨2548512319201631651749619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6796032851204351071332317 2548512319201631651749619)
                      ·
                        rfl

theorem cell23_4963210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_4963210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963210 prefixEnd_4963210 := by exact prefixLift 4963210
  have htrace : WordTrace (prefixWord ++ tailWord_4963210) baseStart_4963210 baseEnd_4963210 := by
    simpa [prefixWord, tailWord_4963210, baseEnd_4963210] using wordTrace_append hprefix tailTrace_4963210
  have hstable : (prefixWord ++ tailWord_4963210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963210).length < 2 ^ (prefixWord ++ tailWord_4963210).sum := by decide
  have hdescent : baseEnd_4963210 < baseStart_4963210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963219 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 3]
def baseStart_4963219 : Nat := 118140960795 + 4963219 * 2 ^ 59
def prefixEnd_4963219 : Nat := 4983230072969 + 3 ^ 40 * 4963219 * 2
def baseEnd_4963219 : Nat := 2548516940527522116537077

theorem tailTrace_4963219 : CollatzResearch.WordTrace tailWord_4963219 prefixEnd_4963219 2548516940527522116537077 := by
  unfold tailWord_4963219
  simp only [CollatzResearch.WordTrace]
  refine ⟨181023468606112688165420711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120682312404075125443613807 181023468606112688165420711)
  ·
    refine ⟨271535202909169032248131067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181023468606112688165420711 271535202909169032248131067)
    ·
      refine ⟨407302804363753548372196601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271535202909169032248131067 407302804363753548372196601)
      ·
        refine ⟨305477103272815161279147451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407302804363753548372196601 305477103272815161279147451)
        ·
          refine ⟨458215654909222741918721177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305477103272815161279147451 458215654909222741918721177)
          ·
            refine ⟨343661741181917056439040883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458215654909222741918721177 343661741181917056439040883)
            ·
              refine ⟨515492611772875584658561325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343661741181917056439040883 515492611772875584658561325)
              ·
                refine ⟨193309729414828344246960497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 515492611772875584658561325 193309729414828344246960497)
                ·
                  refine ⟨144982297061121258185220373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193309729414828344246960497 144982297061121258185220373)
                  ·
                    refine ⟨6796045174740058977432205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 144982297061121258185220373 6796045174740058977432205)
                    ·
                      refine ⟨2548516940527522116537077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6796045174740058977432205 2548516940527522116537077)
                      ·
                        rfl

theorem cell23_4963219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_4963219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963219 prefixEnd_4963219 := by exact prefixLift 4963219
  have htrace : WordTrace (prefixWord ++ tailWord_4963219) baseStart_4963219 baseEnd_4963219 := by
    simpa [prefixWord, tailWord_4963219, baseEnd_4963219] using wordTrace_append hprefix tailTrace_4963219
  have hstable : (prefixWord ++ tailWord_4963219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963219).length < 2 ^ (prefixWord ++ tailWord_4963219).sum := by decide
  have hdescent : baseEnd_4963219 < baseStart_4963219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963233 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4963233 : Nat := 118140960795 + 4963233 * 2 ^ 59
def prefixEnd_4963233 : Nat := 4983230072969 + 3 ^ 40 * 4963233 * 2
def baseEnd_4963233 : Nat := 2548524129256685061762013

theorem tailTrace_4963233 : CollatzResearch.WordTrace tailWord_4963233 prefixEnd_4963233 2548524129256685061762013 := by
  unfold tailWord_4963233
  simp only [CollatzResearch.WordTrace]
  refine ⟨181023979228061968556430353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120682652818707979037620235 181023979228061968556430353)
  ·
    refine ⟨135767984421046476417322765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181023979228061968556430353 135767984421046476417322765)
    ·
      refine ⟨50912994157892428656496037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135767984421046476417322765 50912994157892428656496037)
      ·
        refine ⟨9546186404604830373093007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50912994157892428656496037 9546186404604830373093007)
        ·
          refine ⟨14319279606907245559639511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546186404604830373093007 14319279606907245559639511)
          ·
            refine ⟨21478919410360868339459267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14319279606907245559639511 21478919410360868339459267)
            ·
              refine ⟨32218379115541302509188901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21478919410360868339459267 32218379115541302509188901)
              ·
                refine ⟨6040946084163994220472919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32218379115541302509188901 6040946084163994220472919)
                ·
                  refine ⟨9061419126245991330709379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6040946084163994220472919 9061419126245991330709379)
                  ·
                    refine ⟨13592128689368986996064069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9061419126245991330709379 13592128689368986996064069)
                    ·
                      refine ⟨2548524129256685061762013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13592128689368986996064069 2548524129256685061762013)
                      ·
                        rfl

theorem cell23_4963233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4963233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963233 prefixEnd_4963233 := by exact prefixLift 4963233
  have htrace : WordTrace (prefixWord ++ tailWord_4963233) baseStart_4963233 baseEnd_4963233 := by
    simpa [prefixWord, tailWord_4963233, baseEnd_4963233] using wordTrace_append hprefix tailTrace_4963233
  have hstable : (prefixWord ++ tailWord_4963233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963233).length < 2 ^ (prefixWord ++ tailWord_4963233).sum := by decide
  have hdescent : baseEnd_4963233 < baseStart_4963233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963253 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_4963253 : Nat := 118140960795 + 4963253 * 2 ^ 59
def prefixEnd_4963253 : Nat := 4983230072969 + 3 ^ 40 * 4963253 * 2
def baseEnd_4963253 : Nat := 2548534398869774983511921

theorem tailTrace_4963253 : CollatzResearch.WordTrace tailWord_4963253 prefixEnd_4963253 2548534398869774983511921 := by
  unfold tailWord_4963253
  simp only [CollatzResearch.WordTrace]
  refine ⟨181024708687989511972158413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120683139125326341314772275 181024708687989511972158413)
  ·
    refine ⟨67884265757996066989559405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181024708687989511972158413 67884265757996066989559405)
    ·
      refine ⟨25456599659248525121084777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67884265757996066989559405 25456599659248525121084777)
      ·
        refine ⟨19092449744436393840813583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25456599659248525121084777 19092449744436393840813583)
        ·
          refine ⟨28638674616654590761220375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19092449744436393840813583 28638674616654590761220375)
          ·
            refine ⟨42958011924981886141830563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28638674616654590761220375 42958011924981886141830563)
            ·
              refine ⟨64437017887472829212745845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42958011924981886141830563 64437017887472829212745845)
              ·
                refine ⟨6040970426950577738694923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64437017887472829212745845 6040970426950577738694923)
                ·
                  refine ⟨9061455640425866608042385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6040970426950577738694923 9061455640425866608042385)
                  ·
                    refine ⟨6796091730319399956031789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9061455640425866608042385 6796091730319399956031789)
                    ·
                      refine ⟨2548534398869774983511921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6796091730319399956031789 2548534398869774983511921)
                      ·
                        rfl

theorem cell23_4963253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_4963253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963253 prefixEnd_4963253 := by exact prefixLift 4963253
  have htrace : WordTrace (prefixWord ++ tailWord_4963253) baseStart_4963253 baseEnd_4963253 := by
    simpa [prefixWord, tailWord_4963253, baseEnd_4963253] using wordTrace_append hprefix tailTrace_4963253
  have hstable : (prefixWord ++ tailWord_4963253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963253).length < 2 ^ (prefixWord ++ tailWord_4963253).sum := by decide
  have hdescent : baseEnd_4963253 < baseStart_4963253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963336 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_4963336 : Nat := 118140960795 + 4963336 * 2 ^ 59
def prefixEnd_4963336 : Nat := 4983230072969 + 3 ^ 40 * 4963336 * 2
def baseEnd_4963336 : Nat := 2548577017764098158774039

theorem tailTrace_4963336 : CollatzResearch.WordTrace tailWord_4963336 prefixEnd_4963336 2548577017764098158774039 := by
  unfold tailWord_4963336
  simp only [CollatzResearch.WordTrace]
  refine ⟨90513867973344408573714931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120685157297792544764953241 90513867973344408573714931)
  ·
    refine ⟨135770801960016612860572397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90513867973344408573714931 135770801960016612860572397)
    ·
      refine ⟨50914050735006229822714649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135770801960016612860572397 50914050735006229822714649)
      ·
        refine ⟨38185538051254672367035987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50914050735006229822714649 38185538051254672367035987)
        ·
          refine ⟨57278307076882008550553981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38185538051254672367035987 57278307076882008550553981)
          ·
            refine ⟨21479365153830753206457743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57278307076882008550553981 21479365153830753206457743)
            ·
              refine ⟨32219047730746129809686615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21479365153830753206457743 32219047730746129809686615)
              ·
                refine ⟨48328571596119194714529923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32219047730746129809686615 48328571596119194714529923)
                ·
                  refine ⟨72492857394178792071794885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48328571596119194714529923 72492857394178792071794885)
                  ·
                    refine ⟨13592410761408523513461541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72492857394178792071794885 13592410761408523513461541)
                    ·
                      refine ⟨2548577017764098158774039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13592410761408523513461541 2548577017764098158774039)
                      ·
                        rfl

theorem cell23_4963336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_4963336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963336 prefixEnd_4963336 := by exact prefixLift 4963336
  have htrace : WordTrace (prefixWord ++ tailWord_4963336) baseStart_4963336 baseEnd_4963336 := by
    simpa [prefixWord, tailWord_4963336, baseEnd_4963336] using wordTrace_append hprefix tailTrace_4963336
  have hstable : (prefixWord ++ tailWord_4963336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963336).length < 2 ^ (prefixWord ++ tailWord_4963336).sum := by decide
  have hdescent : baseEnd_4963336 < baseStart_4963336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963340 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 1, 4, 2]
def baseStart_4963340 : Nat := 118140960795 + 4963340 * 2 ^ 59
def prefixEnd_4963340 : Nat := 4983230072969 + 3 ^ 40 * 4963340 * 2
def baseEnd_4963340 : Nat := 2548579071686716143124021

theorem tailTrace_4963340 : CollatzResearch.WordTrace tailWord_4963340 prefixEnd_4963340 2548579071686716143124021 := by
  unfold tailWord_4963340
  simp only [CollatzResearch.WordTrace]
  refine ⟨90513940919337162915287737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120685254559116217220383649 90513940919337162915287737)
  ·
    refine ⟨67885455689502872186465803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90513940919337162915287737 67885455689502872186465803)
    ·
      refine ⟨101828183534254308279698705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67885455689502872186465803 101828183534254308279698705)
      ·
        refine ⟨76371137650690731209774029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101828183534254308279698705 76371137650690731209774029)
        ·
          refine ⟨28639176619009024203665261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76371137650690731209774029 28639176619009024203665261)
          ·
            refine ⟨10739691232128384076374473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28639176619009024203665261 10739691232128384076374473)
            ·
              refine ⟨8054768424096288057280855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10739691232128384076374473 8054768424096288057280855)
              ·
                refine ⟨12082152636144432085921283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8054768424096288057280855 12082152636144432085921283)
                ·
                  refine ⟨18123228954216648128881925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12082152636144432085921283 18123228954216648128881925)
                  ·
                    refine ⟨3398105428915621524165361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18123228954216648128881925 3398105428915621524165361)
                    ·
                      refine ⟨2548579071686716143124021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398105428915621524165361 2548579071686716143124021)
                      ·
                        rfl

theorem cell23_4963340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_4963340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963340 prefixEnd_4963340 := by exact prefixLift 4963340
  have htrace : WordTrace (prefixWord ++ tailWord_4963340) baseStart_4963340 baseEnd_4963340 := by
    simpa [prefixWord, tailWord_4963340, baseEnd_4963340] using wordTrace_append hprefix tailTrace_4963340
  have hstable : (prefixWord ++ tailWord_4963340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963340).length < 2 ^ (prefixWord ++ tailWord_4963340).sum := by decide
  have hdescent : baseEnd_4963340 < baseStart_4963340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963363 : List Nat := [1, 1, 1, 4, 3, 2, 1, 5, 5]
def baseStart_4963363 : Nat := 118140960795 + 4963363 * 2 ^ 59
def prefixEnd_4963363 : Nat := 4983230072969 + 3 ^ 40 * 4963363 * 2
def baseEnd_4963363 : Nat := 283176764637974394792935

theorem tailTrace_4963363 : CollatzResearch.WordTrace tailWord_4963363 prefixEnd_4963363 283176764637974394792935 := by
  unfold tailWord_4963363
  simp only [CollatzResearch.WordTrace]
  refine ⟨181028720717591000758662743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120685813811727333839108495 181028720717591000758662743)
  ·
    refine ⟨271543081076386501137994115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181028720717591000758662743 271543081076386501137994115)
    ·
      refine ⟨407314621614579751706991173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271543081076386501137994115 407314621614579751706991173)
      ·
        refine ⟨76371491552733703445060845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407314621614579751706991173 76371491552733703445060845)
        ·
          refine ⟨28639309332275138791897817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76371491552733703445060845 28639309332275138791897817)
          ·
            refine ⟨21479481999206354093923363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28639309332275138791897817 21479481999206354093923363)
            ·
              refine ⟨32219222998809531140885045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21479481999206354093923363 32219222998809531140885045)
              ·
                refine ⟨3020552156138393544457973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32219222998809531140885045 3020552156138393544457973)
                ·
                  refine ⟨283176764637974394792935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3020552156138393544457973 283176764637974394792935)
                  ·
                    rfl

theorem cell23_4963363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 5].length) (baseStart_4963363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963363 prefixEnd_4963363 := by exact prefixLift 4963363
  have htrace : WordTrace (prefixWord ++ tailWord_4963363) baseStart_4963363 baseEnd_4963363 := by
    simpa [prefixWord, tailWord_4963363, baseEnd_4963363] using wordTrace_append hprefix tailTrace_4963363
  have hstable : (prefixWord ++ tailWord_4963363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963363).length < 2 ^ (prefixWord ++ tailWord_4963363).sum := by decide
  have hdescent : baseEnd_4963363 < baseStart_4963363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963376 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 4, 5]
def baseStart_4963376 : Nat := 118140960795 + 4963376 * 2 ^ 59
def prefixEnd_4963376 : Nat := 4983230072969 + 3 ^ 40 * 4963376 * 2
def baseEnd_4963376 : Nat := 849532518996759334091285

theorem tailTrace_4963376 : CollatzResearch.WordTrace tailWord_4963376 prefixEnd_4963376 849532518996759334091285 := by
  unfold tailWord_4963376
  simp only [CollatzResearch.WordTrace]
  refine ⟨90514597433271951989442991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120686129911029269319257321 90514597433271951989442991)
  ·
    refine ⟨135771896149907927984164487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90514597433271951989442991 135771896149907927984164487)
    ·
      refine ⟨203657844224861891976246731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135771896149907927984164487 203657844224861891976246731)
      ·
        refine ⟨305486766337292837964370097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203657844224861891976246731 305486766337292837964370097)
        ·
          refine ⟨229115074752969628473277573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305486766337292837964370097 229115074752969628473277573)
          ·
            refine ⟨42959076516181805338739545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229115074752969628473277573 42959076516181805338739545)
            ·
              refine ⟨32219307387136354004054659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42959076516181805338739545 32219307387136354004054659)
              ·
                refine ⟨48328961080704531006081989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32219307387136354004054659 48328961080704531006081989)
                ·
                  refine ⟨9061680202632099563640373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48328961080704531006081989 9061680202632099563640373)
                  ·
                    refine ⟨849532518996759334091285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9061680202632099563640373 849532518996759334091285)
                    ·
                      rfl

theorem cell23_4963376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_4963376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963376 prefixEnd_4963376 := by exact prefixLift 4963376
  have htrace : WordTrace (prefixWord ++ tailWord_4963376) baseStart_4963376 baseEnd_4963376 := by
    simpa [prefixWord, tailWord_4963376, baseEnd_4963376] using wordTrace_append hprefix tailTrace_4963376
  have hstable : (prefixWord ++ tailWord_4963376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963376).length < 2 ^ (prefixWord ++ tailWord_4963376).sum := by decide
  have hdescent : baseEnd_4963376 < baseStart_4963376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963380 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 7]
def baseStart_4963380 : Nat := 118140960795 + 4963380 * 2 ^ 59
def prefixEnd_4963380 : Nat := 4983230072969 + 3 ^ 40 * 4963380 * 2
def baseEnd_4963380 : Nat := 283177734545877331847093

theorem tailTrace_4963380 : CollatzResearch.WordTrace tailWord_4963380 prefixEnd_4963380 283177734545877331847093 := by
  unfold tailWord_4963380
  simp only [CollatzResearch.WordTrace]
  refine ⟨90514670379264706331015797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120686227172352941774687729 90514670379264706331015797)
  ·
    refine ⟨8485750348056066218532731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90514670379264706331015797 8485750348056066218532731)
    ·
      refine ⟨12728625522084099327799097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8485750348056066218532731 12728625522084099327799097)
      ·
        refine ⟨9546469141563074495849323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12728625522084099327799097 9546469141563074495849323)
        ·
          refine ⟨14319703712344611743773985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546469141563074495849323 14319703712344611743773985)
          ·
            refine ⟨10739777784258458807830489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14319703712344611743773985 10739777784258458807830489)
            ·
              refine ⟨8054833338193844105872867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10739777784258458807830489 8054833338193844105872867)
              ·
                refine ⟨12082250007290766158809301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8054833338193844105872867 12082250007290766158809301)
                ·
                  refine ⟨283177734545877331847093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12082250007290766158809301 283177734545877331847093)
                  ·
                    rfl

theorem cell23_4963380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_4963380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963380 prefixEnd_4963380 := by exact prefixLift 4963380
  have htrace : WordTrace (prefixWord ++ tailWord_4963380) baseStart_4963380 baseEnd_4963380 := by
    simpa [prefixWord, tailWord_4963380, baseEnd_4963380] using wordTrace_append hprefix tailTrace_4963380
  have hstable : (prefixWord ++ tailWord_4963380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963380).length < 2 ^ (prefixWord ++ tailWord_4963380).sum := by decide
  have hdescent : baseEnd_4963380 < baseStart_4963380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963386 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_4963386 : Nat := 118140960795 + 4963386 * 2 ^ 59
def prefixEnd_4963386 : Nat := 4983230072969 + 3 ^ 40 * 4963386 * 2
def baseEnd_4963386 : Nat := 2548602691796822963148809

theorem tailTrace_4963386 : CollatzResearch.WordTrace tailWord_4963386 prefixEnd_4963386 2548602691796822963148809 := by
  unfold tailWord_4963386
  simp only [CollatzResearch.WordTrace]
  refine ⟨45257389899126918921687503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120686373064338450457833341 45257389899126918921687503)
  ·
    refine ⟨67886084848690378382531255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45257389899126918921687503 67886084848690378382531255)
    ·
      refine ⟨101829127273035567573796883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67886084848690378382531255 101829127273035567573796883)
      ·
        refine ⟨152743690909553351360695325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101829127273035567573796883 152743690909553351360695325)
        ·
          refine ⟨57278884091082506760260747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152743690909553351360695325 57278884091082506760260747)
          ·
            refine ⟨85918326136623760140391121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57278884091082506760260747 85918326136623760140391121)
            ·
              refine ⟨64438744602467820105293341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85918326136623760140391121 64438744602467820105293341)
              ·
                refine ⟨24164529225925432539485003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64438744602467820105293341 24164529225925432539485003)
                ·
                  refine ⟨36246793838888148809227505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24164529225925432539485003 36246793838888148809227505)
                  ·
                    refine ⟨27185095379166111606920629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36246793838888148809227505 27185095379166111606920629)
                    ·
                      refine ⟨2548602691796822963148809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27185095379166111606920629 2548602691796822963148809)
                      ·
                        rfl

theorem cell23_4963386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_4963386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963386 prefixEnd_4963386 := by exact prefixLift 4963386
  have htrace : WordTrace (prefixWord ++ tailWord_4963386) baseStart_4963386 baseEnd_4963386 := by
    simpa [prefixWord, tailWord_4963386, baseEnd_4963386] using wordTrace_append hprefix tailTrace_4963386
  have hstable : (prefixWord ++ tailWord_4963386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963386).length < 2 ^ (prefixWord ++ tailWord_4963386).sum := by decide
  have hdescent : baseEnd_4963386 < baseStart_4963386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963390 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_4963390 : Nat := 118140960795 + 4963390 * 2 ^ 59
def prefixEnd_4963390 : Nat := 4983230072969 + 3 ^ 40 * 4963390 * 2
def baseEnd_4963390 : Nat := 2548604745719440947498791

theorem tailTrace_4963390 : CollatzResearch.WordTrace tailWord_4963390 prefixEnd_4963390 2548604745719440947498791 := by
  unfold tailWord_4963390
  simp only [CollatzResearch.WordTrace]
  refine ⟨22628713186061648046236953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120686470325662122913263749 22628713186061648046236953)
  ·
    refine ⟨16971534889546236034677715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22628713186061648046236953 16971534889546236034677715)
    ·
      refine ⟨25457302334319354052016573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16971534889546236034677715 25457302334319354052016573)
      ·
        refine ⟨9546488375369757769506215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25457302334319354052016573 9546488375369757769506215)
        ·
          refine ⟨14319732563054636654259323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9546488375369757769506215 14319732563054636654259323)
          ·
            refine ⟨21479598844581954981388985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14319732563054636654259323 21479598844581954981388985)
            ·
              refine ⟨16109699133436466236041739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21479598844581954981388985 16109699133436466236041739)
              ·
                refine ⟨24164548700154699354062609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16109699133436466236041739 24164548700154699354062609)
                ·
                  refine ⟨18123411525116024515546957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24164548700154699354062609 18123411525116024515546957)
                  ·
                    refine ⟨6796279321918509193330109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18123411525116024515546957 6796279321918509193330109)
                    ·
                      refine ⟨2548604745719440947498791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6796279321918509193330109 2548604745719440947498791)
                      ·
                        rfl

theorem cell23_4963390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_4963390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963390 prefixEnd_4963390 := by exact prefixLift 4963390
  have htrace : WordTrace (prefixWord ++ tailWord_4963390) baseStart_4963390 baseEnd_4963390 := by
    simpa [prefixWord, tailWord_4963390, baseEnd_4963390] using wordTrace_append hprefix tailTrace_4963390
  have hstable : (prefixWord ++ tailWord_4963390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963390).length < 2 ^ (prefixWord ++ tailWord_4963390).sum := by decide
  have hdescent : baseEnd_4963390 < baseStart_4963390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963406 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_4963406 : Nat := 118140960795 + 4963406 * 2 ^ 59
def prefixEnd_4963406 : Nat := 4983230072969 + 3 ^ 40 * 4963406 * 2
def baseEnd_4963406 : Nat := 849537653803304294966239

theorem tailTrace_4963406 : CollatzResearch.WordTrace tailWord_4963406 prefixEnd_4963406 849537653803304294966239 := by
  unfold tailWord_4963406
  simp only [CollatzResearch.WordTrace]
  refine ⟨22628786132054402387809759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120686859370956812734985381 22628786132054402387809759)
  ·
    refine ⟨33943179198081603581714639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22628786132054402387809759 33943179198081603581714639)
    ·
      refine ⟨50914768797122405372571959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33943179198081603581714639 50914768797122405372571959)
      ·
        refine ⟨76372153195683608058857939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50914768797122405372571959 76372153195683608058857939)
        ·
          refine ⟨114558229793525412088286909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76372153195683608058857939 114558229793525412088286909)
          ·
            refine ⟨42959336172572029533107591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114558229793525412088286909 42959336172572029533107591)
            ·
              refine ⟨64439004258858044299661387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42959336172572029533107591 64439004258858044299661387)
              ·
                refine ⟨96658506388287066449492081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64439004258858044299661387 96658506388287066449492081)
                ·
                  refine ⟨72493879791215299837119061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96658506388287066449492081 72493879791215299837119061)
                  ·
                    refine ⟨849537653803304294966239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72493879791215299837119061 849537653803304294966239)
                    ·
                      rfl

theorem cell23_4963406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_4963406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963406 prefixEnd_4963406 := by exact prefixLift 4963406
  have htrace : WordTrace (prefixWord ++ tailWord_4963406) baseStart_4963406 baseEnd_4963406 := by
    simpa [prefixWord, tailWord_4963406, baseEnd_4963406] using wordTrace_append hprefix tailTrace_4963406
  have hstable : (prefixWord ++ tailWord_4963406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963406).length < 2 ^ (prefixWord ++ tailWord_4963406).sum := by decide
  have hdescent : baseEnd_4963406 < baseStart_4963406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963413 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_4963413 : Nat := 118140960795 + 4963413 * 2 ^ 59
def prefixEnd_4963413 : Nat := 4983230072969 + 3 ^ 40 * 4963413 * 2
def baseEnd_4963413 : Nat := 2548616555774494357511185

theorem tailTrace_4963413 : CollatzResearch.WordTrace tailWord_4963413 prefixEnd_4963413 2548616555774494357511185 := by
  unfold tailWord_4963413
  simp only [CollatzResearch.WordTrace]
  refine ⟨181030544367409859297982893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120687029578273239531988595 181030544367409859297982893)
  ·
    refine ⟨67886454137778697236743585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181030544367409859297982893 67886454137778697236743585)
    ·
      refine ⟨50914840603334022927557689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67886454137778697236743585 50914840603334022927557689)
      ·
        refine ⟨38186130452500517195668267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50914840603334022927557689 38186130452500517195668267)
        ·
          refine ⟨57279195678750775793502401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38186130452500517195668267 57279195678750775793502401)
          ·
            refine ⟨42959396759063081845126801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57279195678750775793502401 42959396759063081845126801)
            ·
              refine ⟨32219547569297311383845101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42959396759063081845126801 32219547569297311383845101)
              ·
                refine ⟨12082330338486491768941913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32219547569297311383845101 12082330338486491768941913)
                ·
                  refine ⟨9061747753864868826706435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12082330338486491768941913 9061747753864868826706435)
                  ·
                    refine ⟨13592621630797303240059653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9061747753864868826706435 13592621630797303240059653)
                    ·
                      refine ⟨2548616555774494357511185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13592621630797303240059653 2548616555774494357511185)
                      ·
                        rfl

theorem cell23_4963413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_4963413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963413 prefixEnd_4963413 := by exact prefixLift 4963413
  have htrace : WordTrace (prefixWord ++ tailWord_4963413) baseStart_4963413 baseEnd_4963413 := by
    simpa [prefixWord, tailWord_4963413, baseEnd_4963413] using wordTrace_append hprefix tailTrace_4963413
  have hstable : (prefixWord ++ tailWord_4963413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963413).length < 2 ^ (prefixWord ++ tailWord_4963413).sum := by decide
  have hdescent : baseEnd_4963413 < baseStart_4963413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963433 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 3]
def baseStart_4963433 : Nat := 118140960795 + 4963433 * 2 ^ 59
def prefixEnd_4963433 : Nat := 4983230072969 + 3 ^ 40 * 4963433 * 2
def baseEnd_4963433 : Nat := 2548626825387584279261093

theorem tailTrace_4963433 : CollatzResearch.WordTrace tailWord_4963433 prefixEnd_4963433 2548626825387584279261093 := by
  unfold tailWord_4963433
  simp only [CollatzResearch.WordTrace]
  refine ⟨181031273827337402713710953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120687515884891601809140635 181031273827337402713710953)
  ·
    refine ⟨135773455370503052035283215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181031273827337402713710953 135773455370503052035283215)
    ·
      refine ⟨203660183055754578052924823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135773455370503052035283215 203660183055754578052924823)
      ·
        refine ⟨305490274583631867079387235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203660183055754578052924823 305490274583631867079387235)
        ·
          refine ⟨458235411875447800619080853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305490274583631867079387235 458235411875447800619080853)
          ·
            refine ⟨21479784931661615654019415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 458235411875447800619080853 21479784931661615654019415)
            ·
              refine ⟨32219677397492423481029123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21479784931661615654019415 32219677397492423481029123)
              ·
                refine ⟨48329516096238635221543685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32219677397492423481029123 48329516096238635221543685)
                ·
                  refine ⟨9061784268044744104039441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48329516096238635221543685 9061784268044744104039441)
                  ·
                    refine ⟨6796338201033558078029581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9061784268044744104039441 6796338201033558078029581)
                    ·
                      refine ⟨2548626825387584279261093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6796338201033558078029581 2548626825387584279261093)
                      ·
                        rfl

theorem cell23_4963433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_4963433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963433 prefixEnd_4963433 := by exact prefixLift 4963433
  have htrace : WordTrace (prefixWord ++ tailWord_4963433) baseStart_4963433 baseEnd_4963433 := by
    simpa [prefixWord, tailWord_4963433, baseEnd_4963433] using wordTrace_append hprefix tailTrace_4963433
  have hstable : (prefixWord ++ tailWord_4963433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963433).length < 2 ^ (prefixWord ++ tailWord_4963433).sum := by decide
  have hdescent : baseEnd_4963433 < baseStart_4963433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963436 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 8]
def baseStart_4963436 : Nat := 118140960795 + 4963436 * 2 ^ 59
def prefixEnd_4963436 : Nat := 4983230072969 + 3 ^ 40 * 4963436 * 2
def baseEnd_4963436 : Nat := 283180929536616418613731

theorem tailTrace_4963436 : CollatzResearch.WordTrace tailWord_4963436 prefixEnd_4963436 283180929536616418613731 := by
  unfold tailWord_4963436
  simp only [CollatzResearch.WordTrace]
  refine ⟨90515691623163267113035081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120687588830884356150713441 90515691623163267113035081)
  ·
    refine ⟨67886768717372450334776311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90515691623163267113035081 67886768717372450334776311)
    ·
      refine ⟨101830153076058675502164467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67886768717372450334776311 101830153076058675502164467)
      ·
        refine ⟨152745229614088013253246701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101830153076058675502164467 152745229614088013253246701)
        ·
          refine ⟨57279461105283004969967513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152745229614088013253246701 57279461105283004969967513)
          ·
            refine ⟨42959595828962253727475635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57279461105283004969967513 42959595828962253727475635)
            ·
              refine ⟨64439393743443380591213453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42959595828962253727475635 64439393743443380591213453)
              ·
                refine ⟨24164772653791267721705045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64439393743443380591213453 24164772653791267721705045)
                ·
                  refine ⟨283180929536616418613731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24164772653791267721705045 283180929536616418613731)
                  ·
                    rfl

theorem cell23_4963436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_4963436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963436 prefixEnd_4963436 := by exact prefixLift 4963436
  have htrace : WordTrace (prefixWord ++ tailWord_4963436) baseStart_4963436 baseEnd_4963436 := by
    simpa [prefixWord, tailWord_4963436, baseEnd_4963436] using wordTrace_append hprefix tailTrace_4963436
  have hstable : (prefixWord ++ tailWord_4963436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963436).length < 2 ^ (prefixWord ++ tailWord_4963436).sum := by decide
  have hdescent : baseEnd_4963436 < baseStart_4963436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963453 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 6]
def baseStart_4963453 : Nat := 118140960795 + 4963453 * 2 ^ 59
def prefixEnd_4963453 : Nat := 4983230072969 + 3 ^ 40 * 4963453 * 2
def baseEnd_4963453 : Nat := 283181899444519355667889

theorem tailTrace_4963453 : CollatzResearch.WordTrace tailWord_4963453 prefixEnd_4963453 283181899444519355667889 := by
  unfold tailWord_4963453
  simp only [CollatzResearch.WordTrace]
  refine ⟨181032003287264946129439013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120688002191509964086292675 181032003287264946129439013)
  ·
    refine ⟨33943500616362177399269815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181032003287264946129439013 33943500616362177399269815)
    ·
      refine ⟨50915250924543266098904723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33943500616362177399269815 50915250924543266098904723)
      ·
        refine ⟨76372876386814899148357085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50915250924543266098904723 76372876386814899148357085)
        ·
          refine ⟨28639828645055587180633907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76372876386814899148357085 28639828645055587180633907)
          ·
            refine ⟨42959742967583380770950861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28639828645055587180633907 42959742967583380770950861)
            ·
              refine ⟨16109903612843767789106573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42959742967583380770950861 16109903612843767789106573)
              ·
                refine ⟨6041213854816412920914965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16109903612843767789106573 6041213854816412920914965)
                ·
                  refine ⟨283181899444519355667889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6041213854816412920914965 283181899444519355667889)
                  ·
                    rfl

theorem cell23_4963453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_4963453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963453 prefixEnd_4963453 := by exact prefixLift 4963453
  have htrace : WordTrace (prefixWord ++ tailWord_4963453) baseStart_4963453 baseEnd_4963453 := by
    simpa [prefixWord, tailWord_4963453, baseEnd_4963453] using wordTrace_append hprefix tailTrace_4963453
  have hstable : (prefixWord ++ tailWord_4963453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963453).length < 2 ^ (prefixWord ++ tailWord_4963453).sum := by decide
  have hdescent : baseEnd_4963453 < baseStart_4963453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963456 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_4963456 : Nat := 118140960795 + 4963456 * 2 ^ 59
def prefixEnd_4963456 : Nat := 4983230072969 + 3 ^ 40 * 4963456 * 2
def baseEnd_4963456 : Nat := 2548638635442637689273487

theorem tailTrace_4963456 : CollatzResearch.WordTrace tailWord_4963456 prefixEnd_4963456 2548638635442637689273487 := by
  unfold tailWord_4963456
  simp only [CollatzResearch.WordTrace]
  refine ⟨90516056353127038820899111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120688075137502718427865481 90516056353127038820899111)
  ·
    refine ⟨135774084529690558231348667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90516056353127038820899111 135774084529690558231348667)
    ·
      refine ⟨203661126794535837347023001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135774084529690558231348667 203661126794535837347023001)
      ·
        refine ⟨152745845095901878010267251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203661126794535837347023001 152745845095901878010267251)
        ·
          refine ⟨229118767643852817015400877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152745845095901878010267251 229118767643852817015400877)
          ·
            refine ⟨85919537866444806380775329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229118767643852817015400877 85919537866444806380775329)
            ·
              refine ⟨64439653399833604785581497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85919537866444806380775329 64439653399833604785581497)
              ·
                refine ⟨48329740049875203589186123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64439653399833604785581497 48329740049875203589186123)
                ·
                  refine ⟨72494610074812805383779185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48329740049875203589186123 72494610074812805383779185)
                  ·
                    refine ⟨54370957556109604037834389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72494610074812805383779185 54370957556109604037834389)
                    ·
                      refine ⟨2548638635442637689273487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54370957556109604037834389 2548638635442637689273487)
                      ·
                        rfl

theorem cell23_4963456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_4963456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963456 prefixEnd_4963456 := by exact prefixLift 4963456
  have htrace : WordTrace (prefixWord ++ tailWord_4963456) baseStart_4963456 baseEnd_4963456 := by
    simpa [prefixWord, tailWord_4963456, baseEnd_4963456] using wordTrace_append hprefix tailTrace_4963456
  have hstable : (prefixWord ++ tailWord_4963456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963456).length < 2 ^ (prefixWord ++ tailWord_4963456).sum := by decide
  have hdescent : baseEnd_4963456 < baseStart_4963456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963503 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_4963503 : Nat := 118140960795 + 4963503 * 2 ^ 59
def prefixEnd_4963503 : Nat := 4983230072969 + 3 ^ 40 * 4963503 * 2
def baseEnd_4963503 : Nat := 2548662769033399005385771

theorem tailTrace_4963503 : CollatzResearch.WordTrace tailWord_4963503 prefixEnd_4963503 2548662769033399005385771 := by
  unfold tailWord_4963503
  simp only [CollatzResearch.WordTrace]
  refine ⟨181033826937083804668759163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120689217958055869779172775 181033826937083804668759163)
  ·
    refine ⟨271550740405625707003138745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181033826937083804668759163 271550740405625707003138745)
    ·
      refine ⟨203663055304219280252354059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271550740405625707003138745 203663055304219280252354059)
      ·
        refine ⟨305494582956328920378531089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203663055304219280252354059 305494582956328920378531089)
        ·
          refine ⟨229120937217246690283898317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305494582956328920378531089 229120937217246690283898317)
          ·
            refine ⟨85920351456467508856461869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229120937217246690283898317 85920351456467508856461869)
            ·
              refine ⟨32220131796175315821173201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85920351456467508856461869 32220131796175315821173201)
              ·
                refine ⟨24165098847131486865879901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32220131796175315821173201 24165098847131486865879901)
                ·
                  refine ⟨9061912067674307574704963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24165098847131486865879901 9061912067674307574704963)
                  ·
                    refine ⟨13592868101511461362057445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9061912067674307574704963 13592868101511461362057445)
                    ·
                      refine ⟨2548662769033399005385771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13592868101511461362057445 2548662769033399005385771)
                      ·
                        rfl

theorem cell23_4963503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_4963503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963503 prefixEnd_4963503 := by exact prefixLift 4963503
  have htrace : WordTrace (prefixWord ++ tailWord_4963503) baseStart_4963503 baseEnd_4963503 := by
    simpa [prefixWord, tailWord_4963503, baseEnd_4963503] using wordTrace_append hprefix tailTrace_4963503
  have hstable : (prefixWord ++ tailWord_4963503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963503).length < 2 ^ (prefixWord ++ tailWord_4963503).sum := by decide
  have hdescent : baseEnd_4963503 < baseStart_4963503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963513 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 1, 6]
def baseStart_4963513 : Nat := 118140960795 + 4963513 * 2 ^ 59
def prefixEnd_4963513 : Nat := 4983230072969 + 3 ^ 40 * 4963513 * 2
def baseEnd_4963513 : Nat := 849555967946647988753575

theorem tailTrace_4963513 : CollatzResearch.WordTrace tailWord_4963513 prefixEnd_4963513 849555967946647988753575 := by
  unfold tailWord_4963513
  simp only [CollatzResearch.WordTrace]
  refine ⟨181034191667047576376623193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120689461111365050917748795 181034191667047576376623193)
  ·
    refine ⟨135775643750285682282467395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181034191667047576376623193 135775643750285682282467395)
    ·
      refine ⟨203663465625428523423701093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135775643750285682282467395 203663465625428523423701093)
      ·
        refine ⟨38186899804767848141943955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203663465625428523423701093 38186899804767848141943955)
        ·
          refine ⟨57280349707151772212915933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38186899804767848141943955 57280349707151772212915933)
          ·
            refine ⟨21480131140181914579843475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57280349707151772212915933 21480131140181914579843475)
            ·
              refine ⟨32220196710272871869765213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21480131140181914579843475 32220196710272871869765213)
              ·
                refine ⟨12082573766352326951161955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32220196710272871869765213 12082573766352326951161955)
                ·
                  refine ⟨18123860649528490426742933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12082573766352326951161955 18123860649528490426742933)
                  ·
                    refine ⟨849555967946647988753575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18123860649528490426742933 849555967946647988753575)
                    ·
                      rfl

theorem cell23_4963513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_4963513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963513 prefixEnd_4963513 := by exact prefixLift 4963513
  have htrace : WordTrace (prefixWord ++ tailWord_4963513) baseStart_4963513 baseEnd_4963513 := by
    simpa [prefixWord, tailWord_4963513, baseEnd_4963513] using wordTrace_append hprefix tailTrace_4963513
  have hstable : (prefixWord ++ tailWord_4963513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963513).length < 2 ^ (prefixWord ++ tailWord_4963513).sum := by decide
  have hdescent : baseEnd_4963513 < baseStart_4963513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963534 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_4963534 : Nat := 118140960795 + 4963534 * 2 ^ 59
def prefixEnd_4963534 : Nat := 4983230072969 + 3 ^ 40 * 4963534 * 2
def baseEnd_4963534 : Nat := 849559562311229461366043

theorem tailTrace_4963534 : CollatzResearch.WordTrace tailWord_4963534 prefixEnd_4963534 849559562311229461366043 := by
  unfold tailWord_4963534
  simp only [CollatzResearch.WordTrace]
  refine ⟨22629369699996437120392207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120689971733314331308758437 22629369699996437120392207)
  ·
    refine ⟨33944054549994655680588311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22629369699996437120392207 33944054549994655680588311)
    ·
      refine ⟨50916081824991983520882467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33944054549994655680588311 50916081824991983520882467)
      ·
        refine ⟨76374122737487975281323701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50916081824991983520882467 76374122737487975281323701)
        ·
          refine ⟨7160074006639497682624097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76374122737487975281323701 7160074006639497682624097)
          ·
            refine ⟨5370055504979623261968073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7160074006639497682624097 5370055504979623261968073)
            ·
              refine ⟨4027541628734717446476055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5370055504979623261968073 4027541628734717446476055)
              ·
                refine ⟨6041312443102076169714083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4027541628734717446476055 6041312443102076169714083)
                ·
                  refine ⟨9061968664653114254571125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6041312443102076169714083 9061968664653114254571125)
                  ·
                    refine ⟨849559562311229461366043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9061968664653114254571125 849559562311229461366043)
                    ·
                      rfl

theorem cell23_4963534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_4963534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963534 prefixEnd_4963534 := by exact prefixLift 4963534
  have htrace : WordTrace (prefixWord ++ tailWord_4963534) baseStart_4963534 baseEnd_4963534 := by
    simpa [prefixWord, tailWord_4963534, baseEnd_4963534] using wordTrace_append hprefix tailTrace_4963534
  have hstable : (prefixWord ++ tailWord_4963534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963534).length < 2 ^ (prefixWord ++ tailWord_4963534).sum := by decide
  have hdescent : baseEnd_4963534 < baseStart_4963534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963567 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 4]
def baseStart_4963567 : Nat := 118140960795 + 4963567 * 2 ^ 59
def prefixEnd_4963567 : Nat := 4983230072969 + 3 ^ 40 * 4963567 * 2
def baseEnd_4963567 : Nat := 2548695631795286754985477

theorem tailTrace_4963567 : CollatzResearch.WordTrace tailWord_4963567 prefixEnd_4963567 2548695631795286754985477 := by
  unfold tailWord_4963567
  simp only [CollatzResearch.WordTrace]
  refine ⟨181036161208851943599088955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120690774139234629066059303 181036161208851943599088955)
  ·
    refine ⟨271554241813277915398633433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181036161208851943599088955 271554241813277915398633433)
    ·
      refine ⟨203665681359958436548975075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271554241813277915398633433 203665681359958436548975075)
      ·
        refine ⟨305498522039937654823462613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203665681359958436548975075 305498522039937654823462613)
        ·
          refine ⟨7160121610311038784924905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 305498522039937654823462613 7160121610311038784924905)
          ·
            refine ⟨5370091207733279088693679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7160121610311038784924905 5370091207733279088693679)
            ·
              refine ⟨8055136811599918633040519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370091207733279088693679 8055136811599918633040519)
              ·
                refine ⟨12082705217399877949560779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8055136811599918633040519 12082705217399877949560779)
                ·
                  refine ⟨18124057826099816924341169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12082705217399877949560779 18124057826099816924341169)
                  ·
                    refine ⟨13593043369574862693255877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18124057826099816924341169 13593043369574862693255877)
                    ·
                      refine ⟨2548695631795286754985477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13593043369574862693255877 2548695631795286754985477)
                      ·
                        rfl

theorem cell23_4963567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 4].length) (baseStart_4963567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963567 prefixEnd_4963567 := by exact prefixLift 4963567
  have htrace : WordTrace (prefixWord ++ tailWord_4963567) baseStart_4963567 baseEnd_4963567 := by
    simpa [prefixWord, tailWord_4963567, baseEnd_4963567] using wordTrace_append hprefix tailTrace_4963567
  have hstable : (prefixWord ++ tailWord_4963567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963567).length < 2 ^ (prefixWord ++ tailWord_4963567).sum := by decide
  have hdescent : baseEnd_4963567 < baseStart_4963567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963583 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_4963583 : Nat := 118140960795 + 4963583 * 2 ^ 59
def prefixEnd_4963583 : Nat := 4983230072969 + 3 ^ 40 * 4963583 * 2
def baseEnd_4963583 : Nat := 2548703847485758692385403

theorem tailTrace_4963583 : CollatzResearch.WordTrace tailWord_4963583 prefixEnd_4963583 2548703847485758692385403 := by
  unfold tailWord_4963583
  simp only [CollatzResearch.WordTrace]
  refine ⟨181036744776793978331671403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120691163184529318887780935 181036744776793978331671403)
  ·
    refine ⟨271555117165190967497507105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181036744776793978331671403 271555117165190967497507105)
    ·
      refine ⟨203666337873893225623130329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271555117165190967497507105 203666337873893225623130329)
      ·
        refine ⟨152749753405419919217347747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203666337873893225623130329 152749753405419919217347747)
        ·
          refine ⟨229124630108129878826021621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152749753405419919217347747 229124630108129878826021621)
          ·
            refine ⟨21480434072637176139939527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229124630108129878826021621 21480434072637176139939527)
            ·
              refine ⟨32220651108955764209909291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21480434072637176139939527 32220651108955764209909291)
              ·
                refine ⟨48330976663433646314863937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32220651108955764209909291 48330976663433646314863937)
                ·
                  refine ⟨36248232497575234736147953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48330976663433646314863937 36248232497575234736147953)
                  ·
                    refine ⟨27186174373181426052110965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36248232497575234736147953 27186174373181426052110965)
                    ·
                      refine ⟨2548703847485758692385403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27186174373181426052110965 2548703847485758692385403)
                      ·
                        rfl

theorem cell23_4963583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_4963583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963583 prefixEnd_4963583 := by exact prefixLift 4963583
  have htrace : WordTrace (prefixWord ++ tailWord_4963583) baseStart_4963583 baseEnd_4963583 := by
    simpa [prefixWord, tailWord_4963583, baseEnd_4963583] using wordTrace_append hprefix tailTrace_4963583
  have hstable : (prefixWord ++ tailWord_4963583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963583).length < 2 ^ (prefixWord ++ tailWord_4963583).sum := by decide
  have hdescent : baseEnd_4963583 < baseStart_4963583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963588 : List Nat := [2, 3, 2, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_4963588 : Nat := 118140960795 + 4963588 * 2 ^ 59
def prefixEnd_4963588 : Nat := 4983230072969 + 3 ^ 40 * 4963588 * 2
def baseEnd_4963588 : Nat := 2548706414889031172822881

theorem tailTrace_4963588 : CollatzResearch.WordTrace tailWord_4963588 prefixEnd_4963588 2548706414889031172822881 := by
  unfold tailWord_4963588
  simp only [CollatzResearch.WordTrace]
  refine ⟨90518463570887932092801709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120691284761183909457068945 90518463570887932092801709)
  ·
    refine ⟨33944423839082974534800641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90518463570887932092801709 33944423839082974534800641)
    ·
      refine ⟨25458317879312230901100481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33944423839082974534800641 25458317879312230901100481)
      ·
        refine ⟨19093738409484173175825361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25458317879312230901100481 19093738409484173175825361)
        ·
          refine ⟨14320303807113129881869021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19093738409484173175825361 14320303807113129881869021)
          ·
            refine ⟨5370113927667423705700883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14320303807113129881869021 5370113927667423705700883)
            ·
              refine ⟨8055170891501135558551325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370113927667423705700883 8055170891501135558551325)
              ·
                refine ⟨3020689084312925834456747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8055170891501135558551325 3020689084312925834456747)
                ·
                  refine ⟨4531033626469388751685121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020689084312925834456747 4531033626469388751685121)
                  ·
                    refine ⟨3398275219852041563763841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4531033626469388751685121 3398275219852041563763841)
                    ·
                      refine ⟨2548706414889031172822881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398275219852041563763841 2548706414889031172822881)
                      ·
                        rfl

theorem cell23_4963588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_4963588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963588 prefixEnd_4963588 := by exact prefixLift 4963588
  have htrace : WordTrace (prefixWord ++ tailWord_4963588) baseStart_4963588 baseEnd_4963588 := by
    simpa [prefixWord, tailWord_4963588, baseEnd_4963588] using wordTrace_append hprefix tailTrace_4963588
  have hstable : (prefixWord ++ tailWord_4963588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963588).length < 2 ^ (prefixWord ++ tailWord_4963588).sum := by decide
  have hdescent : baseEnd_4963588 < baseStart_4963588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963621 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 2, 1, 3]
def baseStart_4963621 : Nat := 118140960795 + 4963621 * 2 ^ 59
def prefixEnd_4963621 : Nat := 4983230072969 + 3 ^ 40 * 4963621 * 2
def baseEnd_4963621 : Nat := 2548723359750629543710229

theorem tailTrace_4963621 : CollatzResearch.WordTrace tailWord_4963621 prefixEnd_4963621 2548723359750629543710229 := by
  unfold tailWord_4963621
  simp only [CollatzResearch.WordTrace]
  refine ⟨181038130750656310821554717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120692087167104207214369811 181038130750656310821554717)
  ·
    refine ⟨67889299031496116558083019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181038130750656310821554717 67889299031496116558083019)
    ·
      refine ⟨101833948547244174837124529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67889299031496116558083019 101833948547244174837124529)
      ·
        refine ⟨76375461410433131127843397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101833948547244174837124529 76375461410433131127843397)
        ·
          refine ⟨14320399014456212086470637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76375461410433131127843397 14320399014456212086470637)
          ·
            refine ⟨5370149630421079532426489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14320399014456212086470637 5370149630421079532426489)
            ·
              refine ⟨4027612222815809649319867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5370149630421079532426489 4027612222815809649319867)
              ·
                refine ⟨6041418334223714473979801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4027612222815809649319867 6041418334223714473979801)
                ·
                  refine ⟨4531063750667785855484851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6041418334223714473979801 4531063750667785855484851)
                  ·
                    refine ⟨6796595626001678783227277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4531063750667785855484851 6796595626001678783227277)
                    ·
                      refine ⟨2548723359750629543710229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6796595626001678783227277 2548723359750629543710229)
                      ·
                        rfl

theorem cell23_4963621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_4963621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963621 prefixEnd_4963621 := by exact prefixLift 4963621
  have htrace : WordTrace (prefixWord ++ tailWord_4963621) baseStart_4963621 baseEnd_4963621 := by
    simpa [prefixWord, tailWord_4963621, baseEnd_4963621] using wordTrace_append hprefix tailTrace_4963621
  have hstable : (prefixWord ++ tailWord_4963621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963621).length < 2 ^ (prefixWord ++ tailWord_4963621).sum := by decide
  have hdescent : baseEnd_4963621 < baseStart_4963621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963717 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 2, 4, 2]
def baseStart_4963717 : Nat := 118140960795 + 4963717 * 2 ^ 59
def prefixEnd_4963717 : Nat := 4983230072969 + 3 ^ 40 * 4963717 * 2
def baseEnd_4963717 : Nat := 2548772653893461168109787

theorem tailTrace_4963717 : CollatzResearch.WordTrace tailWord_4963717 prefixEnd_4963717 2548772653893461168109787 := by
  unfold tailWord_4963717
  simp only [CollatzResearch.WordTrace]
  refine ⟨181041632158308519217049405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120694421438872346144699603 181041632158308519217049405)
  ·
    refine ⟨67890612059365694706393527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181041632158308519217049405 67890612059365694706393527)
    ·
      refine ⟨101835918089048542059590291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67890612059365694706393527 101835918089048542059590291)
      ·
        refine ⟨152753877133572813089385437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101835918089048542059590291 152753877133572813089385437)
        ·
          refine ⟨57282703925089804908519539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152753877133572813089385437 57282703925089804908519539)
          ·
            refine ⟨85924055887634707362779309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57282703925089804908519539 85924055887634707362779309)
            ·
              refine ⟨32221520957863015261042241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85924055887634707362779309 32221520957863015261042241)
              ·
                refine ⟨24166140718397261445781681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32221520957863015261042241 24166140718397261445781681)
                ·
                  refine ⟨18124605538797946084336261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24166140718397261445781681 18124605538797946084336261)
                  ·
                    refine ⟨3398363538524614890813049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18124605538797946084336261 3398363538524614890813049)
                    ·
                      refine ⟨2548772653893461168109787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398363538524614890813049 2548772653893461168109787)
                      ·
                        rfl

theorem cell23_4963717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_4963717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963717 prefixEnd_4963717 := by exact prefixLift 4963717
  have htrace : WordTrace (prefixWord ++ tailWord_4963717) baseStart_4963717 baseEnd_4963717 := by
    simpa [prefixWord, tailWord_4963717, baseEnd_4963717] using wordTrace_append hprefix tailTrace_4963717
  have hstable : (prefixWord ++ tailWord_4963717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963717).length < 2 ^ (prefixWord ++ tailWord_4963717).sum := by decide
  have hdescent : baseEnd_4963717 < baseStart_4963717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963757 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 8]
def baseStart_4963757 : Nat := 118140960795 + 4963757 * 2 ^ 59
def prefixEnd_4963757 : Nat := 4983230072969 + 3 ^ 40 * 4963757 * 2
def baseEnd_4963757 : Nat := 283199243679960112401067

theorem tailTrace_4963757 : CollatzResearch.WordTrace tailWord_4963757 prefixEnd_4963757 283199243679960112401067 := by
  unfold tailWord_4963757
  simp only [CollatzResearch.WordTrace]
  refine ⟨181043091078163606048505525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120695394052109070699003683 181043091078163606048505525)
  ·
    refine ⟨16972789788577838067047393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181043091078163606048505525 16972789788577838067047393)
    ·
      refine ⟨12729592341433378550285545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16972789788577838067047393 12729592341433378550285545)
      ·
        refine ⟨9547194256075033912714159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12729592341433378550285545 9547194256075033912714159)
        ·
          refine ⟨14320791384112550869071239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9547194256075033912714159 14320791384112550869071239)
          ·
            refine ⟨21481187076168826303606859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14320791384112550869071239 21481187076168826303606859)
            ·
              refine ⟨32221780614253239455410289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21481187076168826303606859 32221780614253239455410289)
              ·
                refine ⟨24166335460689929591557717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32221780614253239455410289 24166335460689929591557717)
                ·
                  refine ⟨283199243679960112401067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24166335460689929591557717 283199243679960112401067)
                  ·
                    rfl

theorem cell23_4963757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_4963757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963757 prefixEnd_4963757 := by exact prefixLift 4963757
  have htrace : WordTrace (prefixWord ++ tailWord_4963757) baseStart_4963757 baseEnd_4963757 := by
    simpa [prefixWord, tailWord_4963757, baseEnd_4963757] using wordTrace_append hprefix tailTrace_4963757
  have hstable : (prefixWord ++ tailWord_4963757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963757).length < 2 ^ (prefixWord ++ tailWord_4963757).sum := by decide
  have hdescent : baseEnd_4963757 < baseStart_4963757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963770 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_4963770 : Nat := 118140960795 + 4963770 * 2 ^ 59
def prefixEnd_4963770 : Nat := 4983230072969 + 3 ^ 40 * 4963770 * 2
def baseEnd_4963770 : Nat := 849599956122716486915681

theorem tailTrace_4963770 : CollatzResearch.WordTrace tailWord_4963770 prefixEnd_4963770 849599956122716486915681 := by
  unfold tailWord_4963770
  simp only [CollatzResearch.WordTrace]
  refine ⟨45260891306779127317182191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120695710151411006179152509 45260891306779127317182191)
  ·
    refine ⟨67891336960168690975773287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45260891306779127317182191 67891336960168690975773287)
    ·
      refine ⟨101837005440253036463659931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67891336960168690975773287 101837005440253036463659931)
      ·
        refine ⟨152755508160379554695489897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101837005440253036463659931 152755508160379554695489897)
        ·
          refine ⟨114566631120284666021617423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152755508160379554695489897 114566631120284666021617423)
          ·
            refine ⟨171849946680426999032426135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114566631120284666021617423 171849946680426999032426135)
            ·
              refine ⟨257774920020640498548639203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171849946680426999032426135 257774920020640498548639203)
              ·
                refine ⟨386662380030960747822958805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257774920020640498548639203 386662380030960747822958805)
                ·
                  refine ⟨9062399531975642527100597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 386662380030960747822958805 9062399531975642527100597)
                  ·
                    refine ⟨849599956122716486915681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9062399531975642527100597 849599956122716486915681)
                    ·
                      rfl

theorem cell23_4963770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_4963770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963770 prefixEnd_4963770 := by exact prefixLift 4963770
  have htrace : WordTrace (prefixWord ++ tailWord_4963770) baseStart_4963770 baseEnd_4963770 := by
    simpa [prefixWord, tailWord_4963770, baseEnd_4963770] using wordTrace_append hprefix tailTrace_4963770
  have hstable : (prefixWord ++ tailWord_4963770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963770).length < 2 ^ (prefixWord ++ tailWord_4963770).sum := by decide
  have hdescent : baseEnd_4963770 < baseStart_4963770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963807 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_4963807 : Nat := 118140960795 + 4963807 * 2 ^ 59
def prefixEnd_4963807 : Nat := 4983230072969 + 3 ^ 40 * 4963807 * 2
def baseEnd_4963807 : Nat := 2548818867152365815984373

theorem tailTrace_4963807 : CollatzResearch.WordTrace tailWord_4963807 prefixEnd_4963807 2548818867152365815984373 := by
  unfold tailWord_4963807
  simp only [CollatzResearch.WordTrace]
  refine ⟨181044914727982464587825675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120696609818654976391883783 181044914727982464587825675)
  ·
    refine ⟨271567372091973696881738513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181044914727982464587825675 271567372091973696881738513)
    ·
      refine ⟨203675529068980272661303885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271567372091973696881738513 203675529068980272661303885)
      ·
        refine ⟨76378323400867602247988957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203675529068980272661303885 76378323400867602247988957)
        ·
          refine ⟨28641871275325350842995859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76378323400867602247988957 28641871275325350842995859)
          ·
            refine ⟨42962806912988026264493789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28641871275325350842995859 42962806912988026264493789)
            ·
              refine ⟨16111052592370509849185171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42962806912988026264493789 16111052592370509849185171)
              ·
                refine ⟨24166578888555764773777757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16111052592370509849185171 24166578888555764773777757)
                ·
                  refine ⟨9062467083208411790166659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24166578888555764773777757 9062467083208411790166659)
                  ·
                    refine ⟨13593700624812617685249989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9062467083208411790166659 13593700624812617685249989)
                    ·
                      refine ⟨2548818867152365815984373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13593700624812617685249989 2548818867152365815984373)
                      ·
                        rfl

theorem cell23_4963807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_4963807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963807 prefixEnd_4963807 := by exact prefixLift 4963807
  have htrace : WordTrace (prefixWord ++ tailWord_4963807) baseStart_4963807 baseEnd_4963807 := by
    simpa [prefixWord, tailWord_4963807, baseEnd_4963807] using wordTrace_append hprefix tailTrace_4963807
  have hstable : (prefixWord ++ tailWord_4963807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963807).length < 2 ^ (prefixWord ++ tailWord_4963807).sum := by decide
  have hdescent : baseEnd_4963807 < baseStart_4963807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963811 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 2, 3, 2]
def baseStart_4963811 : Nat := 118140960795 + 4963811 * 2 ^ 59
def prefixEnd_4963811 : Nat := 4983230072969 + 3 ^ 40 * 4963811 * 2
def baseEnd_4963811 : Nat := 2548820921074983800334355

theorem tailTrace_4963811 : CollatzResearch.WordTrace tailWord_4963811 prefixEnd_4963811 2548820921074983800334355 := by
  unfold tailWord_4963811
  simp only [CollatzResearch.WordTrace]
  refine ⟨181045060619967973270971287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120696707079978648847314191 181045060619967973270971287)
  ·
    refine ⟨271567590929951959906456931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181045060619967973270971287 271567590929951959906456931)
    ·
      refine ⟨407351386394927939859685397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271567590929951959906456931 407351386394927939859685397)
      ·
        refine ⟨19094596237262247180922753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 407351386394927939859685397 19094596237262247180922753)
        ·
          refine ⟨14320947177946685385692065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19094596237262247180922753 14320947177946685385692065)
          ·
            refine ⟨10740710383460014039269049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14320947177946685385692065 10740710383460014039269049)
            ·
              refine ⟨8055532787595010529451787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10740710383460014039269049 8055532787595010529451787)
              ·
                refine ⟨12083299181392515794177681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8055532787595010529451787 12083299181392515794177681)
                ·
                  refine ⟨9062474386044386845633261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12083299181392515794177681 9062474386044386845633261)
                  ·
                    refine ⟨3398427894766645067112473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9062474386044386845633261 3398427894766645067112473)
                    ·
                      refine ⟨2548820921074983800334355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398427894766645067112473 2548820921074983800334355)
                      ·
                        rfl

theorem cell23_4963811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_4963811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963811 prefixEnd_4963811 := by exact prefixLift 4963811
  have htrace : WordTrace (prefixWord ++ tailWord_4963811) baseStart_4963811 baseEnd_4963811 := by
    simpa [prefixWord, tailWord_4963811, baseEnd_4963811] using wordTrace_append hprefix tailTrace_4963811
  have hstable : (prefixWord ++ tailWord_4963811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963811).length < 2 ^ (prefixWord ++ tailWord_4963811).sum := by decide
  have hdescent : baseEnd_4963811 < baseStart_4963811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963820 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_4963820 : Nat := 118140960795 + 4963820 * 2 ^ 59
def prefixEnd_4963820 : Nat := 4983230072969 + 3 ^ 40 * 4963820 * 2
def baseEnd_4963820 : Nat := 2548825542400874265121813

theorem tailTrace_4963820 : CollatzResearch.WordTrace tailWord_4963820 prefixEnd_4963820 2548825542400874265121813 := by
  unfold tailWord_4963820
  simp only [CollatzResearch.WordTrace]
  refine ⟨90522694438467683904024457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120696925917956911872032609 90522694438467683904024457)
  ·
    refine ⟨67892020828850762928018343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90522694438467683904024457 67892020828850762928018343)
    ·
      refine ⟨101838031243276144392027515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67892020828850762928018343 101838031243276144392027515)
      ·
        refine ⟨152757046864914216588041273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101838031243276144392027515 152757046864914216588041273)
        ·
          refine ⟨114567785148685662441030955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152757046864914216588041273 114567785148685662441030955)
          ·
            refine ⟨171851677723028493661546433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114567785148685662441030955 171851677723028493661546433)
            ·
              refine ⟨128888758292271370246159825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171851677723028493661546433 128888758292271370246159825)
              ·
                refine ⟨96666568719203527684619869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128888758292271370246159825 96666568719203527684619869)
                ·
                  refine ⟨36249963269701322881732451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96666568719203527684619869 36249963269701322881732451)
                  ·
                    refine ⟨54374944904551984322598677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36249963269701322881732451 54374944904551984322598677)
                    ·
                      refine ⟨2548825542400874265121813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54374944904551984322598677 2548825542400874265121813)
                      ·
                        rfl

theorem cell23_4963820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_4963820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963820 prefixEnd_4963820 := by exact prefixLift 4963820
  have htrace : WordTrace (prefixWord ++ tailWord_4963820) baseStart_4963820 baseEnd_4963820 := by
    simpa [prefixWord, tailWord_4963820, baseEnd_4963820] using wordTrace_append hprefix tailTrace_4963820
  have hstable : (prefixWord ++ tailWord_4963820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963820).length < 2 ^ (prefixWord ++ tailWord_4963820).sum := by decide
  have hdescent : baseEnd_4963820 < baseStart_4963820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963834 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_4963834 : Nat := 118140960795 + 4963834 * 2 ^ 59
def prefixEnd_4963834 : Nat := 4983230072969 + 3 ^ 40 * 4963834 * 2
def baseEnd_4963834 : Nat := 849610910376679070115583

theorem tailTrace_4963834 : CollatzResearch.WordTrace tailWord_4963834 prefixEnd_4963834 849610910376679070115583 := by
  unfold tailWord_4963834
  simp only [CollatzResearch.WordTrace]
  refine ⟨45261474874721162049764639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120697266332589765466039037 45261474874721162049764639)
  ·
    refine ⟨67892212312081743074646959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45261474874721162049764639 67892212312081743074646959)
    ·
      refine ⟨101838318468122614611970439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67892212312081743074646959 101838318468122614611970439)
      ·
        refine ⟨152757477702183921917955659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101838318468122614611970439 152757477702183921917955659)
        ·
          refine ⟨229136216553275882876933489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152757477702183921917955659 229136216553275882876933489)
          ·
            refine ⟨171852162414956912157700117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229136216553275882876933489 171852162414956912157700117)
            ·
              refine ⟨8055570113201105257392193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 171852162414956912157700117 8055570113201105257392193)
              ·
                refine ⟨6041677584900828943044145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8055570113201105257392193 6041677584900828943044145)
                ·
                  refine ⟨4531258188675621707283109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6041677584900828943044145 4531258188675621707283109)
                  ·
                    refine ⟨849610910376679070115583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4531258188675621707283109 849610910376679070115583)
                    ·
                      rfl

theorem cell23_4963834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_4963834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963834 prefixEnd_4963834 := by exact prefixLift 4963834
  have htrace : WordTrace (prefixWord ++ tailWord_4963834) baseStart_4963834 baseEnd_4963834 := by
    simpa [prefixWord, tailWord_4963834, baseEnd_4963834] using wordTrace_append hprefix tailTrace_4963834
  have hstable : (prefixWord ++ tailWord_4963834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963834).length < 2 ^ (prefixWord ++ tailWord_4963834).sum := by decide
  have hdescent : baseEnd_4963834 < baseStart_4963834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963847 : List Nat := [1, 1, 4, 3, 2, 1, 3, 8]
def baseStart_4963847 : Nat := 118140960795 + 4963847 * 2 ^ 59
def prefixEnd_4963847 : Nat := 4983230072969 + 3 ^ 40 * 4963847 * 2
def baseEnd_4963847 : Nat := 94401459495501691092007

theorem tailTrace_4963847 : CollatzResearch.WordTrace tailWord_4963847 prefixEnd_4963847 94401459495501691092007 := by
  unfold tailWord_4963847
  simp only [CollatzResearch.WordTrace]
  refine ⟨181046373647837551419281795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120697582431891700946187863 181046373647837551419281795)
  ·
    refine ⟨271569560471756327128922693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181046373647837551419281795 271569560471756327128922693)
    ·
      refine ⟨50919292588454311336673005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271569560471756327128922693 50919292588454311336673005)
      ·
        refine ⟨19094734720670366751252377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50919292588454311336673005 19094734720670366751252377)
        ·
          refine ⟨14321051040502775063439283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19094734720670366751252377 14321051040502775063439283)
          ·
            refine ⟨21481576560754162595158925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14321051040502775063439283 21481576560754162595158925)
            ·
              refine ⟨8055591210282810973184597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21481576560754162595158925 8055591210282810973184597)
              ·
                refine ⟨94401459495501691092007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8055591210282810973184597 94401459495501691092007)
                ·
                  rfl

theorem cell23_4963847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 8].length) (baseStart_4963847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963847 prefixEnd_4963847 := by exact prefixLift 4963847
  have htrace : WordTrace (prefixWord ++ tailWord_4963847) baseStart_4963847 baseEnd_4963847 := by
    simpa [prefixWord, tailWord_4963847, baseEnd_4963847] using wordTrace_append hprefix tailTrace_4963847
  have hstable : (prefixWord ++ tailWord_4963847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963847).length < 2 ^ (prefixWord ++ tailWord_4963847).sum := by decide
  have hdescent : baseEnd_4963847 < baseStart_4963847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963864 : List Nat := [2, 1, 2, 3, 4, 1, 3, 7]
def baseStart_4963864 : Nat := 118140960795 + 4963864 * 2 ^ 59
def prefixEnd_4963864 : Nat := 4983230072969 + 3 ^ 40 * 4963864 * 2
def baseEnd_4963864 : Nat := 94401782798136003443393

theorem tailTrace_4963864 : CollatzResearch.WordTrace tailWord_4963864 prefixEnd_4963864 94401782798136003443393 := by
  unfold tailWord_4963864
  simp only [CollatzResearch.WordTrace]
  refine ⟨90523496844387981661325323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120697995792517308881767097 90523496844387981661325323)
  ·
    refine ⟨135785245266581972491987985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90523496844387981661325323 135785245266581972491987985)
    ·
      refine ⟨101838933949936479368990989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135785245266581972491987985 101838933949936479368990989)
      ·
        refine ⟨38189600231226179763371621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101838933949936479368990989 38189600231226179763371621)
        ·
          refine ⟨7160550043354908705632179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38189600231226179763371621 7160550043354908705632179)
          ·
            refine ⟨10740825065032363058448269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7160550043354908705632179 10740825065032363058448269)
            ·
              refine ⟨4027809399387136146918101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10740825065032363058448269 4027809399387136146918101)
              ·
                refine ⟨94401782798136003443393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4027809399387136146918101 94401782798136003443393)
                ·
                  rfl

theorem cell23_4963864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 7].length) (baseStart_4963864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963864 prefixEnd_4963864 := by exact prefixLift 4963864
  have htrace : WordTrace (prefixWord ++ tailWord_4963864) baseStart_4963864 baseEnd_4963864 := by
    simpa [prefixWord, tailWord_4963864, baseEnd_4963864] using wordTrace_append hprefix tailTrace_4963864
  have hstable : (prefixWord ++ tailWord_4963864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963864).length < 2 ^ (prefixWord ++ tailWord_4963864).sum := by decide
  have hdescent : baseEnd_4963864 < baseStart_4963864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963874 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_4963874 : Nat := 118140960795 + 4963874 * 2 ^ 59
def prefixEnd_4963874 : Nat := 4983230072969 + 3 ^ 40 * 4963874 * 2
def baseEnd_4963874 : Nat := 2548853270356217053846565

theorem tailTrace_4963874 : CollatzResearch.WordTrace tailWord_4963874 prefixEnd_4963874 2548853270356217053846565 := by
  unfold tailWord_4963874
  simp only [CollatzResearch.WordTrace]
  refine ⟨45261839604684933757628669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120698238945826490020343117 45261839604684933757628669)
  ·
    refine ⟨16973189851756850159110751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45261839604684933757628669 16973189851756850159110751)
    ·
      refine ⟨25459784777635275238666127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16973189851756850159110751 25459784777635275238666127)
      ·
        refine ⟨38189677166452912857999191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25459784777635275238666127 38189677166452912857999191)
        ·
          refine ⟨57284515749679369286998787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38189677166452912857999191 57284515749679369286998787)
          ·
            refine ⟨85926773624519053930498181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57284515749679369286998787 85926773624519053930498181)
            ·
              refine ⟨16111270054597322611968409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85926773624519053930498181 16111270054597322611968409)
              ·
                refine ⟨12083452540947991958976307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16111270054597322611968409 12083452540947991958976307)
                ·
                  refine ⟨18125178811421987938464461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12083452540947991958976307 18125178811421987938464461)
                  ·
                    refine ⟨6796942054283245476924173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18125178811421987938464461 6796942054283245476924173)
                    ·
                      refine ⟨2548853270356217053846565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6796942054283245476924173 2548853270356217053846565)
                      ·
                        rfl

theorem cell23_4963874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_4963874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963874 prefixEnd_4963874 := by exact prefixLift 4963874
  have htrace : WordTrace (prefixWord ++ tailWord_4963874) baseStart_4963874 baseEnd_4963874 := by
    simpa [prefixWord, tailWord_4963874, baseEnd_4963874] using wordTrace_append hprefix tailTrace_4963874
  have hstable : (prefixWord ++ tailWord_4963874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963874).length < 2 ^ (prefixWord ++ tailWord_4963874).sum := by decide
  have hdescent : baseEnd_4963874 < baseStart_4963874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963875 : List Nat := [1, 1, 1, 4, 5, 1, 2, 3, 1, 2, 2]
def baseStart_4963875 : Nat := 118140960795 + 4963875 * 2 ^ 59
def prefixEnd_4963875 : Nat := 4983230072969 + 3 ^ 40 * 4963875 * 2
def baseEnd_4963875 : Nat := 2548853783836871549934061

theorem tailTrace_4963875 : CollatzResearch.WordTrace tailWord_4963875 prefixEnd_4963875 2548853783836871549934061 := by
  unfold tailWord_4963875
  simp only [CollatzResearch.WordTrace]
  refine ⟨181047394891736112201301079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120698263261157408134200719 181047394891736112201301079)
  ·
    refine ⟨271571092337604168301951619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181047394891736112201301079 271571092337604168301951619)
    ·
      refine ⟨407356638506406252452927429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271571092337604168301951619 407356638506406252452927429)
      ·
        refine ⟨76379369719951172334923893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407356638506406252452927429 76379369719951172334923893)
        ·
          refine ⟨7160565911245422406399115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76379369719951172334923893 7160565911245422406399115)
          ·
            refine ⟨10740848866868133609598673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7160565911245422406399115 10740848866868133609598673)
            ·
              refine ⟨8055636650151100207199005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10740848866868133609598673 8055636650151100207199005)
              ·
                refine ⟨3020863743806662577699627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8055636650151100207199005 3020863743806662577699627)
                ·
                  refine ⟨4531295615709993866549441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020863743806662577699627 4531295615709993866549441)
                  ·
                    refine ⟨3398471711782495399912081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4531295615709993866549441 3398471711782495399912081)
                    ·
                      refine ⟨2548853783836871549934061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398471711782495399912081 2548853783836871549934061)
                      ·
                        rfl

theorem cell23_4963875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_4963875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963875 prefixEnd_4963875 := by exact prefixLift 4963875
  have htrace : WordTrace (prefixWord ++ tailWord_4963875) baseStart_4963875 baseEnd_4963875 := by
    simpa [prefixWord, tailWord_4963875, baseEnd_4963875] using wordTrace_append hprefix tailTrace_4963875
  have hstable : (prefixWord ++ tailWord_4963875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963875).length < 2 ^ (prefixWord ++ tailWord_4963875).sum := by decide
  have hdescent : baseEnd_4963875 < baseStart_4963875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963891 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 3]
def baseStart_4963891 : Nat := 118140960795 + 4963891 * 2 ^ 59
def prefixEnd_4963891 : Nat := 4983230072969 + 3 ^ 40 * 4963891 * 2
def baseEnd_4963891 : Nat := 2548861999527343487333987

theorem tailTrace_4963891 : CollatzResearch.WordTrace tailWord_4963891 prefixEnd_4963891 2548861999527343487333987 := by
  unfold tailWord_4963891
  simp only [CollatzResearch.WordTrace]
  refine ⟨181047978459678146933883527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120698652306452097955922351 181047978459678146933883527)
  ·
    refine ⟨271571967689517220400825291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181047978459678146933883527 271571967689517220400825291)
    ·
      refine ⟨407357951534275830601237937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271571967689517220400825291 407357951534275830601237937)
      ·
        refine ⟨305518463650706872950928453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407357951534275830601237937 305518463650706872950928453)
        ·
          refine ⟨57284711934507538678299085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305518463650706872950928453 57284711934507538678299085)
          ·
            refine ⟨21481766975440327004362157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57284711934507538678299085 21481766975440327004362157)
            ·
              refine ⟨8055662615790122626635809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21481766975440327004362157 8055662615790122626635809)
              ·
                refine ⟨6041746961842591969976857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8055662615790122626635809 6041746961842591969976857)
                ·
                  refine ⟨4531310221381943977482643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6041746961842591969976857 4531310221381943977482643)
                  ·
                    refine ⟨6796965332072915966223965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4531310221381943977482643 6796965332072915966223965)
                    ·
                      refine ⟨2548861999527343487333987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6796965332072915966223965 2548861999527343487333987)
                      ·
                        rfl

theorem cell23_4963891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 3].length) (baseStart_4963891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963891 prefixEnd_4963891 := by exact prefixLift 4963891
  have htrace : WordTrace (prefixWord ++ tailWord_4963891) baseStart_4963891 baseEnd_4963891 := by
    simpa [prefixWord, tailWord_4963891, baseEnd_4963891] using wordTrace_append hprefix tailTrace_4963891
  have hstable : (prefixWord ++ tailWord_4963891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963891).length < 2 ^ (prefixWord ++ tailWord_4963891).sum := by decide
  have hdescent : baseEnd_4963891 < baseStart_4963891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963926 : List Nat := [5, 2, 2, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4963926 : Nat := 118140960795 + 4963926 * 2 ^ 59
def prefixEnd_4963926 : Nat := 4983230072969 + 3 ^ 40 * 4963926 * 2
def baseEnd_4963926 : Nat := 2548879971350250850396327

theorem tailTrace_4963926 : CollatzResearch.WordTrace tailWord_4963926 prefixEnd_4963926 2548879971350250850396327 := by
  unfold tailWord_4963926
  simp only [CollatzResearch.WordTrace]
  refine ⟨11315578438409459244462977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120699503343034231940938421 11315578438409459244462977)
  ·
    refine ⟨8486683828807094433347233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11315578438409459244462977 8486683828807094433347233)
    ·
      refine ⟨6365012871605320825010425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8486683828807094433347233 6365012871605320825010425)
      ·
        refine ⟨4773759653703990618757819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6365012871605320825010425 4773759653703990618757819)
        ·
          refine ⟨7160639480555985928136729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4773759653703990618757819 7160639480555985928136729)
          ·
            refine ⟨5370479610416989446102547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7160639480555985928136729 5370479610416989446102547)
            ·
              refine ⟨8055719415625484169153821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370479610416989446102547 8055719415625484169153821)
              ·
                refine ⟨3020894780859556563432683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8055719415625484169153821 3020894780859556563432683)
                ·
                  refine ⟨4531342171289334845149025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3020894780859556563432683 4531342171289334845149025)
                  ·
                    refine ⟨3398506628467001133861769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4531342171289334845149025 3398506628467001133861769)
                    ·
                      refine ⟨2548879971350250850396327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398506628467001133861769 2548879971350250850396327)
                      ·
                        rfl

theorem cell23_4963926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4963926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963926 prefixEnd_4963926 := by exact prefixLift 4963926
  have htrace : WordTrace (prefixWord ++ tailWord_4963926) baseStart_4963926 baseEnd_4963926 := by
    simpa [prefixWord, tailWord_4963926, baseEnd_4963926] using wordTrace_append hprefix tailTrace_4963926
  have hstable : (prefixWord ++ tailWord_4963926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963926).length < 2 ^ (prefixWord ++ tailWord_4963926).sum := by decide
  have hdescent : baseEnd_4963926 < baseStart_4963926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963954 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 7]
def baseStart_4963954 : Nat := 118140960795 + 4963954 * 2 ^ 59
def prefixEnd_4963954 : Nat := 4983230072969 + 3 ^ 40 * 4963954 * 2
def baseEnd_4963954 : Nat := 283210483200952971205133

theorem tailTrace_4963954 : CollatzResearch.WordTrace tailWord_4963954 prefixEnd_4963954 283210483200952971205133 := by
  unfold tailWord_4963954
  simp only [CollatzResearch.WordTrace]
  refine ⟨45262569064612477173356729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120700184172299939128951277 45262569064612477173356729)
  ·
    refine ⟨33946926798459357880017547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45262569064612477173356729 33946926798459357880017547)
    ·
      refine ⟨50920390197689036820026321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33946926798459357880017547 50920390197689036820026321)
      ·
        refine ⟨38190292648266777615019741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50920390197689036820026321 38190292648266777615019741)
        ·
          refine ⟨14321359743100041605632403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38190292648266777615019741 14321359743100041605632403)
          ·
            refine ⟨21482039614650062408448605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14321359743100041605632403 21482039614650062408448605)
            ·
              refine ⟨8055764855493773403168227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21482039614650062408448605 8055764855493773403168227)
              ·
                refine ⟨12083647283240660104752341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8055764855493773403168227 12083647283240660104752341)
                ·
                  refine ⟨283210483200952971205133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12083647283240660104752341 283210483200952971205133)
                  ·
                    rfl

theorem cell23_4963954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_4963954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963954 prefixEnd_4963954 := by exact prefixLift 4963954
  have htrace : WordTrace (prefixWord ++ tailWord_4963954) baseStart_4963954 baseEnd_4963954 := by
    simpa [prefixWord, tailWord_4963954, baseEnd_4963954] using wordTrace_append hprefix tailTrace_4963954
  have hstable : (prefixWord ++ tailWord_4963954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963954).length < 2 ^ (prefixWord ++ tailWord_4963954).sum := by decide
  have hdescent : baseEnd_4963954 < baseStart_4963954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4963965 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_4963965 : Nat := 118140960795 + 4963965 * 2 ^ 59
def prefixEnd_4963965 : Nat := 4983230072969 + 3 ^ 40 * 4963965 * 2
def baseEnd_4963965 : Nat := 2548899997095776197808647

theorem tailTrace_4963965 : CollatzResearch.WordTrace tailWord_4963965 prefixEnd_4963965 2548899997095776197808647 := by
  unfold tailWord_4963965
  simp only [CollatzResearch.WordTrace]
  refine ⟨181050677461410057572077349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120700451640940038381384899 181050677461410057572077349)
  ·
    refine ⟨33947002024014385794764503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181050677461410057572077349 33947002024014385794764503)
    ·
      refine ⟨50920503036021578692146755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33947002024014385794764503 50920503036021578692146755)
      ·
        refine ⟨76380754554032368038220133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50920503036021578692146755 76380754554032368038220133)
        ·
          refine ⟨14321391478881069007166275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76380754554032368038220133 14321391478881069007166275)
          ·
            refine ⟨21482087218321603510749413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14321391478881069007166275 21482087218321603510749413)
            ·
              refine ⟨4027891353435300658265515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21482087218321603510749413 4027891353435300658265515)
              ·
                refine ⟨6041837030152950987398273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4027891353435300658265515 6041837030152950987398273)
                ·
                  refine ⟨4531377772614713240548705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6041837030152950987398273 4531377772614713240548705)
                  ·
                    refine ⟨3398533329461034930411529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4531377772614713240548705 3398533329461034930411529)
                    ·
                      refine ⟨2548899997095776197808647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398533329461034930411529 2548899997095776197808647)
                      ·
                        rfl

theorem cell23_4963965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_4963965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4963965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4963965 prefixEnd_4963965 := by exact prefixLift 4963965
  have htrace : WordTrace (prefixWord ++ tailWord_4963965) baseStart_4963965 baseEnd_4963965 := by
    simpa [prefixWord, tailWord_4963965, baseEnd_4963965] using wordTrace_append hprefix tailTrace_4963965
  have hstable : (prefixWord ++ tailWord_4963965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4963965).length < 2 ^ (prefixWord ++ tailWord_4963965).sum := by decide
  have hdescent : baseEnd_4963965 < baseStart_4963965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4963965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964024 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_4964024 : Nat := 118140960795 + 4964024 * 2 ^ 59
def prefixEnd_4964024 : Nat := 4983230072969 + 3 ^ 40 * 4964024 * 2
def baseEnd_4964024 : Nat := 2548930292454391466970875

theorem tailTrace_4964024 : CollatzResearch.WordTrace tailWord_4964024 prefixEnd_4964024 2548930292454391466970875 := by
  unfold tailWord_4964024
  simp only [CollatzResearch.WordTrace]
  refine ⟨90526414684098155324237563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120701886245464207098983417 90526414684098155324237563)
  ·
    refine ⟨135789622026147232986356345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90526414684098155324237563 135789622026147232986356345)
    ·
      refine ⟨101842216519610424739767259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135789622026147232986356345 101842216519610424739767259)
      ·
        refine ⟨152763324779415637109650889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101842216519610424739767259 152763324779415637109650889)
        ·
          refine ⟨114572493584561727832238167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152763324779415637109650889 114572493584561727832238167)
          ·
            refine ⟨171858740376842591748357251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114572493584561727832238167 171858740376842591748357251)
            ·
              refine ⟨257788110565263887622535877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171858740376842591748357251 257788110565263887622535877)
              ·
                refine ⟨48335270730986978929225477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257788110565263887622535877 48335270730986978929225477)
                ·
                  refine ⟨9062863262060058549229777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48335270730986978929225477 9062863262060058549229777)
                  ·
                    refine ⟨6797147446545043911922333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9062863262060058549229777 6797147446545043911922333)
                    ·
                      refine ⟨2548930292454391466970875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6797147446545043911922333 2548930292454391466970875)
                      ·
                        rfl

theorem cell23_4964024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_4964024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964024 prefixEnd_4964024 := by exact prefixLift 4964024
  have htrace : WordTrace (prefixWord ++ tailWord_4964024) baseStart_4964024 baseEnd_4964024 := by
    simpa [prefixWord, tailWord_4964024, baseEnd_4964024] using wordTrace_append hprefix tailTrace_4964024
  have hstable : (prefixWord ++ tailWord_4964024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964024).length < 2 ^ (prefixWord ++ tailWord_4964024).sum := by decide
  have hdescent : baseEnd_4964024 < baseStart_4964024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964047 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_4964047 : Nat := 118140960795 + 4964047 * 2 ^ 59
def prefixEnd_4964047 : Nat := 4983230072969 + 3 ^ 40 * 4964047 * 2
def baseEnd_4964047 : Nat := 2548942102509444876983269

theorem tailTrace_4964047 : CollatzResearch.WordTrace tailWord_4964047 prefixEnd_4964047 2548942102509444876983269 := by
  unfold tailWord_4964047
  simp only [CollatzResearch.WordTrace]
  refine ⟨181053668247112985576562395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120702445498075323717708263 181053668247112985576562395)
  ·
    refine ⟨271580502370669478364843593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181053668247112985576562395 271580502370669478364843593)
    ·
      refine ⟨203685376778002108773632695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271580502370669478364843593 203685376778002108773632695)
      ·
        refine ⟨305528065167003163160449043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203685376778002108773632695 305528065167003163160449043)
        ·
          refine ⟨458292097750504744740673565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305528065167003163160449043 458292097750504744740673565)
          ·
            refine ⟨171859536656439279277752587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 458292097750504744740673565 171859536656439279277752587)
            ·
              refine ⟨257789304984658918916628881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171859536656439279277752587 257789304984658918916628881)
              ·
                refine ⟨193341978738494189187471661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257789304984658918916628881 193341978738494189187471661)
                ·
                  refine ⟨72503242026935320945301873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193341978738494189187471661 72503242026935320945301873)
                  ·
                    refine ⟨54377431520201490708976405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72503242026935320945301873 54377431520201490708976405)
                    ·
                      refine ⟨2548942102509444876983269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54377431520201490708976405 2548942102509444876983269)
                      ·
                        rfl

theorem cell23_4964047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_4964047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964047 prefixEnd_4964047 := by exact prefixLift 4964047
  have htrace : WordTrace (prefixWord ++ tailWord_4964047) baseStart_4964047 baseEnd_4964047 := by
    simpa [prefixWord, tailWord_4964047, baseEnd_4964047] using wordTrace_append hprefix tailTrace_4964047
  have hstable : (prefixWord ++ tailWord_4964047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964047).length < 2 ^ (prefixWord ++ tailWord_4964047).sum := by decide
  have hdescent : baseEnd_4964047 < baseStart_4964047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964074 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_4964074 : Nat := 118140960795 + 4964074 * 2 ^ 59
def prefixEnd_4964074 : Nat := 4983230072969 + 3 ^ 40 * 4964074 * 2
def baseEnd_4964074 : Nat := 849651988829038757115215

theorem tailTrace_4964074 : CollatzResearch.WordTrace tailWord_4964074 prefixEnd_4964074 849651988829038757115215 := by
  unfold tailWord_4964074
  simp only [CollatzResearch.WordTrace]
  refine ⟨45263663254503792296948819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120703102012010112791863517 45263663254503792296948819)
  ·
    refine ⟨67895494881755688445423229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45263663254503792296948819 67895494881755688445423229)
    ·
      refine ⟨25460810580658383167033711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67895494881755688445423229 25460810580658383167033711)
      ·
        refine ⟨38191215870987574750550567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25460810580658383167033711 38191215870987574750550567)
        ·
          refine ⟨57286823806481362125825851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38191215870987574750550567 57286823806481362125825851)
          ·
            refine ⟨85930235709722043188738777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57286823806481362125825851 85930235709722043188738777)
            ·
              refine ⟨64447676782291532391554083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85930235709722043188738777 64447676782291532391554083)
              ·
                refine ⟨96671515173437298587331125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64447676782291532391554083 96671515173437298587331125)
                ·
                  refine ⟨9062954547509746742562293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96671515173437298587331125 9062954547509746742562293)
                  ·
                    refine ⟨849651988829038757115215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9062954547509746742562293 849651988829038757115215)
                    ·
                      rfl

theorem cell23_4964074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_4964074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964074 prefixEnd_4964074 := by exact prefixLift 4964074
  have htrace : WordTrace (prefixWord ++ tailWord_4964074) baseStart_4964074 baseEnd_4964074 := by
    simpa [prefixWord, tailWord_4964074, baseEnd_4964074] using wordTrace_append hprefix tailTrace_4964074
  have hstable : (prefixWord ++ tailWord_4964074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964074).length < 2 ^ (prefixWord ++ tailWord_4964074).sum := by decide
  have hdescent : baseEnd_4964074 < baseStart_4964074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964081 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 1, 5, 2]
def baseStart_4964081 : Nat := 118140960795 + 4964081 * 2 ^ 59
def prefixEnd_4964081 : Nat := 4983230072969 + 3 ^ 40 * 4964081 * 2
def baseEnd_4964081 : Nat := 2548959560851697743958113

theorem tailTrace_4964081 : CollatzResearch.WordTrace tailWord_4964081 prefixEnd_4964081 2548959560851697743958113 := by
  unfold tailWord_4964081
  simp only [CollatzResearch.WordTrace]
  refine ⟨181054908328989809383300097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120703272219326539588866731 181054908328989809383300097)
  ·
    refine ⟨135791181246742357037475073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181054908328989809383300097 135791181246742357037475073)
    ·
      refine ⟨101843385935056767778106305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135791181246742357037475073 101843385935056767778106305)
      ·
        refine ⟨76382539451292575833579729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101843385935056767778106305 76382539451292575833579729)
        ·
          refine ⟨57286904588469431875184797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76382539451292575833579729 57286904588469431875184797)
          ·
            refine ⟨21482589220676036953194299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57286904588469431875184797 21482589220676036953194299)
            ·
              refine ⟨32223883831014055429791449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21482589220676036953194299 32223883831014055429791449)
              ·
                refine ⟨24167912873260541572343587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32223883831014055429791449 24167912873260541572343587)
                ·
                  refine ⟨36251869309890812358515381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24167912873260541572343587 36251869309890812358515381)
                  ·
                    refine ⟨3398612747802263658610817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36251869309890812358515381 3398612747802263658610817)
                    ·
                      refine ⟨2548959560851697743958113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398612747802263658610817 2548959560851697743958113)
                      ·
                        rfl

theorem cell23_4964081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_4964081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964081 prefixEnd_4964081 := by exact prefixLift 4964081
  have htrace : WordTrace (prefixWord ++ tailWord_4964081) baseStart_4964081 baseEnd_4964081 := by
    simpa [prefixWord, tailWord_4964081, baseEnd_4964081] using wordTrace_append hprefix tailTrace_4964081
  have hstable : (prefixWord ++ tailWord_4964081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964081).length < 2 ^ (prefixWord ++ tailWord_4964081).sum := by decide
  have hdescent : baseEnd_4964081 < baseStart_4964081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964098 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_4964098 : Nat := 118140960795 + 4964098 * 2 ^ 59
def prefixEnd_4964098 : Nat := 4983230072969 + 3 ^ 40 * 4964098 * 2
def baseEnd_4964098 : Nat := 2548968290022824177445535

theorem tailTrace_4964098 : CollatzResearch.WordTrace tailWord_4964098 prefixEnd_4964098 2548968290022824177445535 := by
  unfold tailWord_4964098
  simp only [CollatzResearch.WordTrace]
  refine ⟨45263882092482055321667237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120703685579952147524445965 45263882092482055321667237)
  ·
    refine ⟨8486977892340385372812607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45263882092482055321667237 8486977892340385372812607)
    ·
      refine ⟨12730466838510578059218911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8486977892340385372812607 12730466838510578059218911)
      ·
        refine ⟨19095700257765867088828367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12730466838510578059218911 19095700257765867088828367)
        ·
          refine ⟨28643550386648800633242551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19095700257765867088828367 28643550386648800633242551)
          ·
            refine ⟨42965325579973200949863827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28643550386648800633242551 42965325579973200949863827)
            ·
              refine ⟨64447988369959801424795741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42965325579973200949863827 64447988369959801424795741)
              ·
                refine ⟨24167995638734925534298403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64447988369959801424795741 24167995638734925534298403)
                ·
                  refine ⟨36251993458102388301447605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24167995638734925534298403 36251993458102388301447605)
                  ·
                    refine ⟨3398624386697098903260713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36251993458102388301447605 3398624386697098903260713)
                    ·
                      refine ⟨2548968290022824177445535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398624386697098903260713 2548968290022824177445535)
                      ·
                        rfl

theorem cell23_4964098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_4964098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964098 prefixEnd_4964098 := by exact prefixLift 4964098
  have htrace : WordTrace (prefixWord ++ tailWord_4964098) baseStart_4964098 baseEnd_4964098 := by
    simpa [prefixWord, tailWord_4964098, baseEnd_4964098] using wordTrace_append hprefix tailTrace_4964098
  have hstable : (prefixWord ++ tailWord_4964098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964098).length < 2 ^ (prefixWord ++ tailWord_4964098).sum := by decide
  have hdescent : baseEnd_4964098 < baseStart_4964098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964104 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 3, 6]
def baseStart_4964104 : Nat := 118140960795 + 4964104 * 2 ^ 59
def prefixEnd_4964104 : Nat := 4983230072969 + 3 ^ 40 * 4964104 * 2
def baseEnd_4964104 : Nat := 849657123635583717990169

theorem tailTrace_4964104 : CollatzResearch.WordTrace tailWord_4964104 prefixEnd_4964104 849657123635583717990169 := by
  unfold tailWord_4964104
  simp only [CollatzResearch.WordTrace]
  refine ⟨90527873603953242155693683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120703831471937656207591577 90527873603953242155693683)
  ·
    refine ⟨135791810405929863233540525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90527873603953242155693683 135791810405929863233540525)
    ·
      refine ⟨50921928902223698712577697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135791810405929863233540525 50921928902223698712577697)
      ·
        refine ⟨38191446676667774034433273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50921928902223698712577697 38191446676667774034433273)
        ·
          refine ⟨28643585007500830525824955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38191446676667774034433273 28643585007500830525824955)
          ·
            refine ⟨42965377511251245788737433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28643585007500830525824955 42965377511251245788737433)
            ·
              refine ⟨32224033133438434341553075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42965377511251245788737433 32224033133438434341553075)
              ·
                refine ⟨48336049700157651512329613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32224033133438434341553075 48336049700157651512329613)
                ·
                  refine ⟨18126018637559119317123605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48336049700157651512329613 18126018637559119317123605)
                  ·
                    refine ⟨849657123635583717990169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18126018637559119317123605 849657123635583717990169)
                    ·
                      rfl

theorem cell23_4964104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_4964104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964104 prefixEnd_4964104 := by exact prefixLift 4964104
  have htrace : WordTrace (prefixWord ++ tailWord_4964104) baseStart_4964104 baseEnd_4964104 := by
    simpa [prefixWord, tailWord_4964104, baseEnd_4964104] using wordTrace_append hprefix tailTrace_4964104
  have hstable : (prefixWord ++ tailWord_4964104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964104).length < 2 ^ (prefixWord ++ tailWord_4964104).sum := by decide
  have hdescent : baseEnd_4964104 < baseStart_4964104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964109 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_4964109 : Nat := 118140960795 + 4964109 * 2 ^ 59
def prefixEnd_4964109 : Nat := 4983230072969 + 3 ^ 40 * 4964109 * 2
def baseEnd_4964109 : Nat := 2548973938310023634407985

theorem tailTrace_4964109 : CollatzResearch.WordTrace tailWord_4964109 prefixEnd_4964109 2548973938310023634407985 := by
  unfold tailWord_4964109
  simp only [CollatzResearch.WordTrace]
  refine ⟨181055929572888370165319381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120703953048592246776879587 181055929572888370165319381)
  ·
    refine ⟨4243498349364571175749673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 181055929572888370165319381 4243498349364571175749673)
    ·
      refine ⟨3182623762023428381812255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4243498349364571175749673 3182623762023428381812255)
      ·
        refine ⟨4773935643035142572718383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182623762023428381812255 4773935643035142572718383)
        ·
          refine ⟨7160903464552713859077575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4773935643035142572718383 7160903464552713859077575)
          ·
            refine ⟨10741355196829070788616363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7160903464552713859077575 10741355196829070788616363)
            ·
              refine ⟨16112032795243606182924545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10741355196829070788616363 16112032795243606182924545)
              ·
                refine ⟨12084024596432704637193409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16112032795243606182924545 12084024596432704637193409)
                ·
                  refine ⟨9063018447324528477895057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12084024596432704637193409 9063018447324528477895057)
                  ·
                    refine ⟨6797263835493396358421293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9063018447324528477895057 6797263835493396358421293)
                    ·
                      refine ⟨2548973938310023634407985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6797263835493396358421293 2548973938310023634407985)
                      ·
                        rfl

theorem cell23_4964109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_4964109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964109 prefixEnd_4964109 := by exact prefixLift 4964109
  have htrace : WordTrace (prefixWord ++ tailWord_4964109) baseStart_4964109 baseEnd_4964109 := by
    simpa [prefixWord, tailWord_4964109, baseEnd_4964109] using wordTrace_append hprefix tailTrace_4964109
  have hstable : (prefixWord ++ tailWord_4964109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964109).length < 2 ^ (prefixWord ++ tailWord_4964109).sum := by decide
  have hdescent : baseEnd_4964109 < baseStart_4964109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964116 : List Nat := [2, 4, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4964116 : Nat := 118140960795 + 4964116 * 2 ^ 59
def prefixEnd_4964116 : Nat := 4983230072969 + 3 ^ 40 * 4964116 * 2
def baseEnd_4964116 : Nat := 849659177558201702340151

theorem tailTrace_4964116 : CollatzResearch.WordTrace tailWord_4964116 prefixEnd_4964116 849659177558201702340151 := by
  unfold tailWord_4964116
  simp only [CollatzResearch.WordTrace]
  refine ⟨90528092441931505180412101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120704123255908673573882801 90528092441931505180412101)
  ·
    refine ⟨16974017332862157221327269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90528092441931505180412101 16974017332862157221327269)
    ·
      refine ⟨3182628249911654478998863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16974017332862157221327269 3182628249911654478998863)
      ·
        refine ⟨4773942374867481718498295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182628249911654478998863 4773942374867481718498295)
        ·
          refine ⟨7160913562301222577747443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4773942374867481718498295 7160913562301222577747443)
          ·
            refine ⟨10741370343451833866621165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7160913562301222577747443 10741370343451833866621165)
            ·
              refine ⟨4028013878794437699982937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10741370343451833866621165 4028013878794437699982937)
              ·
                refine ⟨3021010409095828274987203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4028013878794437699982937 3021010409095828274987203)
                ·
                  refine ⟨4531515613643742412480805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021010409095828274987203 4531515613643742412480805)
                  ·
                    refine ⟨849659177558201702340151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4531515613643742412480805 849659177558201702340151)
                    ·
                      rfl

theorem cell23_4964116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4964116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964116 prefixEnd_4964116 := by exact prefixLift 4964116
  have htrace : WordTrace (prefixWord ++ tailWord_4964116) baseStart_4964116 baseEnd_4964116 := by
    simpa [prefixWord, tailWord_4964116, baseEnd_4964116] using wordTrace_append hprefix tailTrace_4964116
  have hstable : (prefixWord ++ tailWord_4964116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964116).length < 2 ^ (prefixWord ++ tailWord_4964116).sum := by decide
  have hdescent : baseEnd_4964116 < baseStart_4964116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964122 : List Nat := [3, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3]
def baseStart_4964122 : Nat := 118140960795 + 4964122 * 2 ^ 59
def prefixEnd_4964122 : Nat := 4983230072969 + 3 ^ 40 * 4964122 * 2
def baseEnd_4964122 : Nat := 2548980613558532083545425

theorem tailTrace_4964122 : CollatzResearch.WordTrace tailWord_4964122 prefixEnd_4964122 2548980613558532083545425 := by
  unfold tailWord_4964122
  simp only [CollatzResearch.WordTrace]
  refine ⟨45264100930460318346385655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120704269147894182257028413 45264100930460318346385655)
  ·
    refine ⟨67896151395690477519578483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45264100930460318346385655 67896151395690477519578483)
    ·
      refine ⟨101844227093535716279367725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67896151395690477519578483 101844227093535716279367725)
      ·
        refine ⟨38191585160075893604762897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101844227093535716279367725 38191585160075893604762897)
        ·
          refine ⟨28643688870056920203572173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38191585160075893604762897 28643688870056920203572173)
          ·
            refine ⟨10741383326271345076339565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28643688870056920203572173 10741383326271345076339565)
            ·
              refine ⟨4028018747351754403627337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10741383326271345076339565 4028018747351754403627337)
              ·
                refine ⟨3021014060513815802720503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4028018747351754403627337 3021014060513815802720503)
                ·
                  refine ⟨4531521090770723704080755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021014060513815802720503 4531521090770723704080755)
                  ·
                    refine ⟨6797281636156085556121133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4531521090770723704080755 6797281636156085556121133)
                    ·
                      refine ⟨2548980613558532083545425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6797281636156085556121133 2548980613558532083545425)
                      ·
                        rfl

theorem cell23_4964122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_4964122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964122 prefixEnd_4964122 := by exact prefixLift 4964122
  have htrace : WordTrace (prefixWord ++ tailWord_4964122) baseStart_4964122 baseEnd_4964122 := by
    simpa [prefixWord, tailWord_4964122, baseEnd_4964122] using wordTrace_append hprefix tailTrace_4964122
  have hstable : (prefixWord ++ tailWord_4964122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964122).length < 2 ^ (prefixWord ++ tailWord_4964122).sum := by decide
  have hdescent : baseEnd_4964122 < baseStart_4964122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964124 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4964124 : Nat := 118140960795 + 4964124 * 2 ^ 59
def prefixEnd_4964124 : Nat := 4983230072969 + 3 ^ 40 * 4964124 * 2
def baseEnd_4964124 : Nat := 2548981640519841075720415

theorem tailTrace_4964124 : CollatzResearch.WordTrace tailWord_4964124 prefixEnd_4964124 2548981640519841075720415 := by
  unfold tailWord_4964124
  simp only [CollatzResearch.WordTrace]
  refine ⟨90528238333917013863557713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120704317778556018484743617 90528238333917013863557713)
  ·
    refine ⟨67896178750437760397668285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90528238333917013863557713 67896178750437760397668285)
    ·
      refine ⟨25461067031414160149125607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67896178750437760397668285 25461067031414160149125607)
      ·
        refine ⟨38191600547121240223688411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25461067031414160149125607 38191600547121240223688411)
        ·
          refine ⟨57287400820681860335532617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38191600547121240223688411 57287400820681860335532617)
          ·
            refine ⟨42965550615511395251649463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57287400820681860335532617 42965550615511395251649463)
            ·
              refine ⟨64448325923267092877474195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42965550615511395251649463 64448325923267092877474195)
              ·
                refine ⟨96672488884900639316211293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64448325923267092877474195 96672488884900639316211293)
                ·
                  refine ⟨36252183331837739743579235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96672488884900639316211293 36252183331837739743579235)
                  ·
                    refine ⟨54378274997756609615368853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36252183331837739743579235 54378274997756609615368853)
                    ·
                      refine ⟨2548981640519841075720415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54378274997756609615368853 2548981640519841075720415)
                      ·
                        rfl

theorem cell23_4964124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4964124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964124 prefixEnd_4964124 := by exact prefixLift 4964124
  have htrace : WordTrace (prefixWord ++ tailWord_4964124) baseStart_4964124 baseEnd_4964124 := by
    simpa [prefixWord, tailWord_4964124, baseEnd_4964124] using wordTrace_append hprefix tailTrace_4964124
  have hstable : (prefixWord ++ tailWord_4964124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964124).length < 2 ^ (prefixWord ++ tailWord_4964124).sum := by decide
  have hdescent : baseEnd_4964124 < baseStart_4964124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964142 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_4964142 : Nat := 118140960795 + 4964142 * 2 ^ 59
def prefixEnd_4964142 : Nat := 4983230072969 + 3 ^ 40 * 4964142 * 2
def baseEnd_4964142 : Nat := 849663627723874001765111

theorem tailTrace_4964142 : CollatzResearch.WordTrace tailWord_4964142 prefixEnd_4964142 849663627723874001765111 := by
  unfold tailWord_4964142
  simp only [CollatzResearch.WordTrace]
  refine ⟨22632141647721102100158835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120704755454512544534180453 22632141647721102100158835)
  ·
    refine ⟨33948212471581653150238253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22632141647721102100158835 33948212471581653150238253)
    ·
      refine ⟨12730579676843119931339345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33948212471581653150238253 12730579676843119931339345)
      ·
        refine ⟨9547934757632339948504509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12730579676843119931339345 9547934757632339948504509)
        ·
          refine ⟨3580475534112127480689191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9547934757632339948504509 3580475534112127480689191)
          ·
            refine ⟨5370713301168191221033787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580475534112127480689191 5370713301168191221033787)
            ·
              refine ⟨8056069951752286831550681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370713301168191221033787 8056069951752286831550681)
              ·
                refine ⟨6042052463814215123663011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8056069951752286831550681 6042052463814215123663011)
                ·
                  refine ⟨9063078695721322685494517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6042052463814215123663011 9063078695721322685494517)
                  ·
                    refine ⟨849663627723874001765111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9063078695721322685494517 849663627723874001765111)
                    ·
                      rfl

theorem cell23_4964142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_4964142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964142 prefixEnd_4964142 := by exact prefixLift 4964142
  have htrace : WordTrace (prefixWord ++ tailWord_4964142) baseStart_4964142 baseEnd_4964142 := by
    simpa [prefixWord, tailWord_4964142, baseEnd_4964142] using wordTrace_append hprefix tailTrace_4964142
  have hstable : (prefixWord ++ tailWord_4964142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964142).length < 2 ^ (prefixWord ++ tailWord_4964142).sum := by decide
  have hdescent : baseEnd_4964142 < baseStart_4964142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964158 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4964158 : Nat := 118140960795 + 4964158 * 2 ^ 59
def prefixEnd_4964158 : Nat := 4983230072969 + 3 ^ 40 * 4964158 * 2
def baseEnd_4964158 : Nat := 2548999098862093942695259

theorem tailTrace_4964158 : CollatzResearch.WordTrace tailWord_4964158 prefixEnd_4964158 2548999098862093942695259 := by
  unfold tailWord_4964158
  simp only [CollatzResearch.WordTrace]
  refine ⟨22632214593713856441731641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120705144499807234355902085 22632214593713856441731641)
  ·
    refine ⟨16974160945285392331298731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22632214593713856441731641 16974160945285392331298731)
    ·
      refine ⟨25461241417928088496948097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16974160945285392331298731 25461241417928088496948097)
      ·
        refine ⟨19095931063446066372711073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25461241417928088496948097 19095931063446066372711073)
        ·
          refine ⟨14321948297584549779533305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19095931063446066372711073 14321948297584549779533305)
          ·
            refine ⟨10741461223188412334649979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14321948297584549779533305 10741461223188412334649979)
            ·
              refine ⟨16112191834782618501974969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10741461223188412334649979 16112191834782618501974969)
              ·
                refine ⟨12084143876086963876481227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16112191834782618501974969 12084143876086963876481227)
                ·
                  refine ⟨18126215814130445814721841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12084143876086963876481227 18126215814130445814721841)
                  ·
                    refine ⟨13594661860597834361041381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18126215814130445814721841 13594661860597834361041381)
                    ·
                      refine ⟨2548999098862093942695259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13594661860597834361041381 2548999098862093942695259)
                      ·
                        rfl

theorem cell23_4964158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4964158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964158 prefixEnd_4964158 := by exact prefixLift 4964158
  have htrace : WordTrace (prefixWord ++ tailWord_4964158) baseStart_4964158 baseEnd_4964158 := by
    simpa [prefixWord, tailWord_4964158, baseEnd_4964158] using wordTrace_append hprefix tailTrace_4964158
  have hstable : (prefixWord ++ tailWord_4964158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964158).length < 2 ^ (prefixWord ++ tailWord_4964158).sum := by decide
  have hdescent : baseEnd_4964158 < baseStart_4964158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964174 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_4964174 : Nat := 118140960795 + 4964174 * 2 ^ 59
def prefixEnd_4964174 : Nat := 4983230072969 + 3 ^ 40 * 4964174 * 2
def baseEnd_4964174 : Nat := 2549007314552565880095185

theorem tailTrace_4964174 : CollatzResearch.WordTrace tailWord_4964174 prefixEnd_4964174 2549007314552565880095185 := by
  unfold tailWord_4964174
  simp only [CollatzResearch.WordTrace]
  refine ⟨22632287539706610783304447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120705533545101924177623717 22632287539706610783304447)
  ·
    refine ⟨33948431309559916174956671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22632287539706610783304447 33948431309559916174956671)
    ·
      refine ⟨50922646964339874262435007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33948431309559916174956671 50922646964339874262435007)
      ·
        refine ⟨76383970446509811393652511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50922646964339874262435007 76383970446509811393652511)
        ·
          refine ⟨114575955669764717090478767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76383970446509811393652511 114575955669764717090478767)
          ·
            refine ⟨171863933504647075635718151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114575955669764717090478767 171863933504647075635718151)
            ·
              refine ⟨257795900256970613453577227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171863933504647075635718151 257795900256970613453577227)
              ·
                refine ⟨386693850385455920180365841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257795900256970613453577227 386693850385455920180365841)
                ·
                  refine ⟨290020387789091940135274381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 386693850385455920180365841 290020387789091940135274381)
                  ·
                    refine ⟨108757645420909477550727893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 290020387789091940135274381 108757645420909477550727893)
                    ·
                      refine ⟨2549007314552565880095185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108757645420909477550727893 2549007314552565880095185)
                      ·
                        rfl

theorem cell23_4964174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_4964174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964174 prefixEnd_4964174 := by exact prefixLift 4964174
  have htrace : WordTrace (prefixWord ++ tailWord_4964174) baseStart_4964174 baseEnd_4964174 := by
    simpa [prefixWord, tailWord_4964174, baseEnd_4964174] using wordTrace_append hprefix tailTrace_4964174
  have hstable : (prefixWord ++ tailWord_4964174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964174).length < 2 ^ (prefixWord ++ tailWord_4964174).sum := by decide
  have hdescent : baseEnd_4964174 < baseStart_4964174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964218 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2]
def baseStart_4964218 : Nat := 118140960795 + 4964218 * 2 ^ 59
def prefixEnd_4964218 : Nat := 4983230072969 + 3 ^ 40 * 4964218 * 2
def baseEnd_4964218 : Nat := 2549029907701363707944983

theorem tailTrace_4964218 : CollatzResearch.WordTrace tailWord_4964218 prefixEnd_4964218 2549029907701363707944983 := by
  unfold tailWord_4964218
  simp only [CollatzResearch.WordTrace]
  refine ⟨45264976282373370445259327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120706603419662321187358205 45264976282373370445259327)
  ·
    refine ⟨67897464423560055667888991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45264976282373370445259327 67897464423560055667888991)
    ·
      refine ⟨101846196635340083501833487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67897464423560055667888991 101846196635340083501833487)
      ·
        refine ⟨152769294953010125252750231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101846196635340083501833487 152769294953010125252750231)
        ·
          refine ⟨229153942429515187879125347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152769294953010125252750231 229153942429515187879125347)
          ·
            refine ⟨343730913644272781818688021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229153942429515187879125347 343730913644272781818688021)
            ·
              refine ⟨16112386577075286647751001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 343730913644272781818688021 16112386577075286647751001)
              ·
                refine ⟨12084289932806464985813251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16112386577075286647751001 12084289932806464985813251)
                ·
                  refine ⟨18126434899209697478719877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12084289932806464985813251 18126434899209697478719877)
                  ·
                    refine ⟨3398706543601818277259977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18126434899209697478719877 3398706543601818277259977)
                    ·
                      refine ⟨2549029907701363707944983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398706543601818277259977 2549029907701363707944983)
                      ·
                        rfl

theorem cell23_4964218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_4964218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964218 prefixEnd_4964218 := by exact prefixLift 4964218
  have htrace : WordTrace (prefixWord ++ tailWord_4964218) baseStart_4964218 baseEnd_4964218 := by
    simpa [prefixWord, tailWord_4964218, baseEnd_4964218] using wordTrace_append hprefix tailTrace_4964218
  have hstable : (prefixWord ++ tailWord_4964218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964218).length < 2 ^ (prefixWord ++ tailWord_4964218).sum := by decide
  have hdescent : baseEnd_4964218 < baseStart_4964218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964224 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 9]
def baseStart_4964224 : Nat := 118140960795 + 4964224 * 2 ^ 59
def prefixEnd_4964224 : Nat := 4983230072969 + 3 ^ 40 * 4964224 * 2
def baseEnd_4964224 : Nat := 283225887620587853829995

theorem tailTrace_4964224 : CollatzResearch.WordTrace tailWord_4964224 prefixEnd_4964224 283225887620587853829995 := by
  unfold tailWord_4964224
  simp only [CollatzResearch.WordTrace]
  refine ⟨90530061983735872402877863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120706749311647829870503817 90530061983735872402877863)
  ·
    refine ⟨135795092975603808604316795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90530061983735872402877863 135795092975603808604316795)
    ·
      refine ⟨203692639463405712906475193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135795092975603808604316795 203692639463405712906475193)
      ·
        refine ⟨152769479597554284679856395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203692639463405712906475193 152769479597554284679856395)
        ·
          refine ⟨229154219396331427019784593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152769479597554284679856395 229154219396331427019784593)
          ·
            refine ⟨171865664547248570264838445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229154219396331427019784593 171865664547248570264838445)
            ·
              refine ⟨64449624205218213849314417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171865664547248570264838445 64449624205218213849314417)
              ·
                refine ⟨48337218153913660386985813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64449624205218213849314417 48337218153913660386985813)
                ·
                  refine ⟨283225887620587853829995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48337218153913660386985813 283225887620587853829995)
                  ·
                    rfl

theorem cell23_4964224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 9].length) (baseStart_4964224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964224 prefixEnd_4964224 := by exact prefixLift 4964224
  have htrace : WordTrace (prefixWord ++ tailWord_4964224) baseStart_4964224 baseEnd_4964224 := by
    simpa [prefixWord, tailWord_4964224, baseEnd_4964224] using wordTrace_append hprefix tailTrace_4964224
  have hstable : (prefixWord ++ tailWord_4964224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964224).length < 2 ^ (prefixWord ++ tailWord_4964224).sum := by decide
  have hdescent : baseEnd_4964224 < baseStart_4964224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964246 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4964246 : Nat := 118140960795 + 4964246 * 2 ^ 59
def prefixEnd_4964246 : Nat := 4983230072969 + 3 ^ 40 * 4964246 * 2
def baseEnd_4964246 : Nat := 2549044285159689598394855

theorem tailTrace_4964246 : CollatzResearch.WordTrace tailWord_4964246 prefixEnd_4964246 2549044285159689598394855 := by
  unfold tailWord_4964246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11316307898337002660191037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120707284248928028375371061 11316307898337002660191037)
  ·
    refine ⟨4243615461876375997571639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11316307898337002660191037 4243615461876375997571639)
    ·
      refine ⟨6365423192814563996357459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4243615461876375997571639 6365423192814563996357459)
      ·
        refine ⟨9548134789221845994536189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6365423192814563996357459 9548134789221845994536189)
        ·
          refine ⟨3580550545958192247951071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9548134789221845994536189 3580550545958192247951071)
          ·
            refine ⟨5370825818937288371926607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580550545958192247951071 5370825818937288371926607)
            ·
              refine ⟨8056238728405932557889911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370825818937288371926607 8056238728405932557889911)
              ·
                refine ⟨12084358092608898836834867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8056238728405932557889911 12084358092608898836834867)
                ·
                  refine ⟨18126537138913348255252301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12084358092608898836834867 18126537138913348255252301)
                  ·
                    refine ⟨6797451427092505595719613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18126537138913348255252301 6797451427092505595719613)
                    ·
                      refine ⟨2549044285159689598394855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6797451427092505595719613 2549044285159689598394855)
                      ·
                        rfl

theorem cell23_4964246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4964246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964246 prefixEnd_4964246 := by exact prefixLift 4964246
  have htrace : WordTrace (prefixWord ++ tailWord_4964246) baseStart_4964246 baseEnd_4964246 := by
    simpa [prefixWord, tailWord_4964246, baseEnd_4964246] using wordTrace_append hprefix tailTrace_4964246
  have hstable : (prefixWord ++ tailWord_4964246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964246).length < 2 ^ (prefixWord ++ tailWord_4964246).sum := by decide
  have hdescent : baseEnd_4964246 < baseStart_4964246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964252 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4964252 : Nat := 118140960795 + 4964252 * 2 ^ 59
def prefixEnd_4964252 : Nat := 4983230072969 + 3 ^ 40 * 4964252 * 2
def baseEnd_4964252 : Nat := 2549047366043616574919827

theorem tailTrace_4964252 : CollatzResearch.WordTrace tailWord_4964252 prefixEnd_4964252 2549047366043616574919827 := by
  unfold tailWord_4964252
  simp only [CollatzResearch.WordTrace]
  refine ⟨90530572605685152793887505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120707430140913537058516673 90530572605685152793887505)
  ·
    refine ⟨67897929454263864595415629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90530572605685152793887505 67897929454263864595415629)
    ·
      refine ⟨25461723545348949223280861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67897929454263864595415629 25461723545348949223280861)
      ·
        refine ⟨9548146329505855958730323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25461723545348949223280861 9548146329505855958730323)
        ·
          refine ⟨14322219494258783938095485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9548146329505855958730323 14322219494258783938095485)
          ·
            refine ⟨5370832310347043976785807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14322219494258783938095485 5370832310347043976785807)
            ·
              refine ⟨8056248465520565965178711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5370832310347043976785807 8056248465520565965178711)
              ·
                refine ⟨12084372698280848947768067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8056248465520565965178711 12084372698280848947768067)
                ·
                  refine ⟨18126559047421273421652101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12084372698280848947768067 18126559047421273421652101)
                  ·
                    refine ⟨3398729821391488766559769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18126559047421273421652101 3398729821391488766559769)
                    ·
                      refine ⟨2549047366043616574919827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398729821391488766559769 2549047366043616574919827)
                      ·
                        rfl

theorem cell23_4964252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4964252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964252 prefixEnd_4964252 := by exact prefixLift 4964252
  have htrace : WordTrace (prefixWord ++ tailWord_4964252) baseStart_4964252 baseEnd_4964252 := by
    simpa [prefixWord, tailWord_4964252, baseEnd_4964252] using wordTrace_append hprefix tailTrace_4964252
  have hstable : (prefixWord ++ tailWord_4964252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964252).length < 2 ^ (prefixWord ++ tailWord_4964252).sum := by decide
  have hdescent : baseEnd_4964252 < baseStart_4964252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964271 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 2, 5]
def baseStart_4964271 : Nat := 118140960795 + 4964271 * 2 ^ 59
def prefixEnd_4964271 : Nat := 4983230072969 + 3 ^ 40 * 4964271 * 2
def baseEnd_4964271 : Nat := 849685707392017333527413

theorem tailTrace_4964271 : CollatzResearch.WordTrace tailWord_4964271 prefixEnd_4964271 849685707392017333527413 := by
  unfold tailWord_4964271
  simp only [CollatzResearch.WordTrace]
  refine ⟨181061838198301471832716667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120707892132200981221811111 181061838198301471832716667)
  ·
    refine ⟨271592757297452207749075001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181061838198301471832716667 271592757297452207749075001)
    ·
      refine ⟨203694567973089155811806251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271592757297452207749075001 203694567973089155811806251)
      ·
        refine ⟨305541851959633733717709377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203694567973089155811806251 305541851959633733717709377)
        ·
          refine ⟨229156388969725300288282033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305541851959633733717709377 229156388969725300288282033)
          ·
            refine ⟨171867291727293975216211525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229156388969725300288282033 171867291727293975216211525)
            ·
              refine ⟨32225117198867620353039661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171867291727293975216211525 32225117198867620353039661)
              ·
                refine ⟨12084418949575357632389873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32225117198867620353039661 12084418949575357632389873)
                ·
                  refine ⟨9063314212181518224292405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12084418949575357632389873 9063314212181518224292405)
                  ·
                    refine ⟨849685707392017333527413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9063314212181518224292405 849685707392017333527413)
                    ·
                      rfl

theorem cell23_4964271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_4964271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964271 prefixEnd_4964271 := by exact prefixLift 4964271
  have htrace : WordTrace (prefixWord ++ tailWord_4964271) baseStart_4964271 baseEnd_4964271 := by
    simpa [prefixWord, tailWord_4964271, baseEnd_4964271] using wordTrace_append hprefix tailTrace_4964271
  have hstable : (prefixWord ++ tailWord_4964271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964271).length < 2 ^ (prefixWord ++ tailWord_4964271).sum := by decide
  have hdescent : baseEnd_4964271 < baseStart_4964271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964281 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_4964281 : Nat := 118140960795 + 4964281 * 2 ^ 59
def prefixEnd_4964281 : Nat := 4983230072969 + 3 ^ 40 * 4964281 * 2
def baseEnd_4964281 : Nat := 2549062256982596961457193

theorem tailTrace_4964281 : CollatzResearch.WordTrace tailWord_4964281 prefixEnd_4964281 2549062256982596961457193 := by
  unfold tailWord_4964281
  simp only [CollatzResearch.WordTrace]
  refine ⟨181062202928265243540580697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120708135285510162360387131 181062202928265243540580697)
  ·
    refine ⟨135796652196198932655435523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181062202928265243540580697 135796652196198932655435523)
    ·
      refine ⟨203694978294298398983153285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135796652196198932655435523 203694978294298398983153285)
      ·
        refine ⟨38192808430180949809341241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203694978294298398983153285 38192808430180949809341241)
        ·
          refine ⟨28644606322635712357005931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38192808430180949809341241 28644606322635712357005931)
          ·
            refine ⟨42966909483953568535508897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28644606322635712357005931 42966909483953568535508897)
            ·
              refine ⟨32225182112965176401631673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42966909483953568535508897 32225182112965176401631673)
              ·
                refine ⟨24168886584723882301223755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32225182112965176401631673 24168886584723882301223755)
                ·
                  refine ⟨36253329877085823451835633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24168886584723882301223755 36253329877085823451835633)
                  ·
                    refine ⟨27189997407814367588876725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36253329877085823451835633 27189997407814367588876725)
                    ·
                      refine ⟨2549062256982596961457193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27189997407814367588876725 2549062256982596961457193)
                      ·
                        rfl

theorem cell23_4964281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_4964281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964281 prefixEnd_4964281 := by exact prefixLift 4964281
  have htrace : WordTrace (prefixWord ++ tailWord_4964281) baseStart_4964281 baseEnd_4964281 := by
    simpa [prefixWord, tailWord_4964281, baseEnd_4964281] using wordTrace_append hprefix tailTrace_4964281
  have hstable : (prefixWord ++ tailWord_4964281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964281).length < 2 ^ (prefixWord ++ tailWord_4964281).sum := by decide
  have hdescent : baseEnd_4964281 < baseStart_4964281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964308 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4964308 : Nat := 118140960795 + 4964308 * 2 ^ 59
def prefixEnd_4964308 : Nat := 4983230072969 + 3 ^ 40 * 4964308 * 2
def baseEnd_4964308 : Nat := 2549076120960268355819569

theorem tailTrace_4964308 : CollatzResearch.WordTrace tailWord_4964308 prefixEnd_4964308 2549076120960268355819569 := by
  unfold tailWord_4964308
  simp only [CollatzResearch.WordTrace]
  refine ⟨90531593849583713575906789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120708791799444951434542385 90531593849583713575906789)
  ·
    refine ⟨16974673846796946295482523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90531593849583713575906789 16974673846796946295482523)
    ·
      refine ⟨25462010770195419443223785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16974673846796946295482523 25462010770195419443223785)
      ·
        refine ⟨19096508077646564582417839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25462010770195419443223785 19096508077646564582417839)
        ·
          refine ⟨28644762116469846873626759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19096508077646564582417839 28644762116469846873626759)
          ·
            refine ⟨42967143174704770310440139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28644762116469846873626759 42967143174704770310440139)
            ·
              refine ⟨64450714762057155465660209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42967143174704770310440139 64450714762057155465660209)
              ·
                refine ⟨48338036071542866599245157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64450714762057155465660209 48338036071542866599245157)
                ·
                  refine ⟨9063381763414287487358467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48338036071542866599245157 9063381763414287487358467)
                  ·
                    refine ⟨13595072645121431231037701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9063381763414287487358467 13595072645121431231037701)
                    ·
                      refine ⟨2549076120960268355819569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13595072645121431231037701 2549076120960268355819569)
                      ·
                        rfl

theorem cell23_4964308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4964308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964308 prefixEnd_4964308 := by exact prefixLift 4964308
  have htrace : WordTrace (prefixWord ++ tailWord_4964308) baseStart_4964308 baseEnd_4964308 := by
    simpa [prefixWord, tailWord_4964308, baseEnd_4964308] using wordTrace_append hprefix tailTrace_4964308
  have hstable : (prefixWord ++ tailWord_4964308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964308).length < 2 ^ (prefixWord ++ tailWord_4964308).sum := by decide
  have hdescent : baseEnd_4964308 < baseStart_4964308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964321 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_4964321 : Nat := 118140960795 + 4964321 * 2 ^ 59
def prefixEnd_4964321 : Nat := 4983230072969 + 3 ^ 40 * 4964321 * 2
def baseEnd_4964321 : Nat := 2549082796208776804957009

theorem tailTrace_4964321 : CollatzResearch.WordTrace tailWord_4964321 prefixEnd_4964321 2549082796208776804957009 := by
  unfold tailWord_4964321
  simp only [CollatzResearch.WordTrace]
  refine ⟨181063661848120330372036817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120709107898746886914691211 181063661848120330372036817)
  ·
    refine ⟨135797746386090247779027613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181063661848120330372036817 135797746386090247779027613)
    ·
      refine ⟨50924154894783842917135355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135797746386090247779027613 50924154894783842917135355)
      ·
        refine ⟨76386232342175764375703033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50924154894783842917135355 76386232342175764375703033)
        ·
          refine ⟨57289674256631823281777275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76386232342175764375703033 57289674256631823281777275)
          ·
            refine ⟨85934511384947734922665913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57289674256631823281777275 85934511384947734922665913)
            ·
              refine ⟨64450883538710801191999435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85934511384947734922665913 64450883538710801191999435)
              ·
                refine ⟨96676325308066201787999153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64450883538710801191999435 96676325308066201787999153)
                ·
                  refine ⟨72507243981049651340999365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96676325308066201787999153 72507243981049651340999365)
                  ·
                    refine ⟨13595108246446809626437381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72507243981049651340999365 13595108246446809626437381)
                    ·
                      refine ⟨2549082796208776804957009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13595108246446809626437381 2549082796208776804957009)
                      ·
                        rfl

theorem cell23_4964321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_4964321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964321 prefixEnd_4964321 := by exact prefixLift 4964321
  have htrace : WordTrace (prefixWord ++ tailWord_4964321) baseStart_4964321 baseEnd_4964321 := by
    simpa [prefixWord, tailWord_4964321, baseEnd_4964321] using wordTrace_append hprefix tailTrace_4964321
  have hstable : (prefixWord ++ tailWord_4964321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964321).length < 2 ^ (prefixWord ++ tailWord_4964321).sum := by decide
  have hdescent : baseEnd_4964321 < baseStart_4964321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964322 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_4964322 : Nat := 118140960795 + 4964322 * 2 ^ 59
def prefixEnd_4964322 : Nat := 4983230072969 + 3 ^ 40 * 4964322 * 2
def baseEnd_4964322 : Nat := 849694436563143767014835

theorem tailTrace_4964322 : CollatzResearch.WordTrace tailWord_4964322 prefixEnd_4964322 849694436563143767014835 := by
  unfold tailWord_4964322
  simp only [CollatzResearch.WordTrace]
  refine ⟨45265924580279176885705805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120709132214077805028548813 45265924580279176885705805)
  ·
    refine ⟨16974721717604691332139677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45265924580279176885705805 16974721717604691332139677)
    ·
      refine ⟨6365520644101759249552379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16974721717604691332139677 6365520644101759249552379)
      ·
        refine ⟨9548280966152638874328569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6365520644101759249552379 9548280966152638874328569)
        ·
          refine ⟨7161210724614479155746427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9548280966152638874328569 7161210724614479155746427)
          ·
            refine ⟨10741816086921718733619641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7161210724614479155746427 10741816086921718733619641)
            ·
              refine ⟨8056362065191289050214731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10741816086921718733619641 8056362065191289050214731)
              ·
                refine ⟨12084543097786933575322097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8056362065191289050214731 12084543097786933575322097)
                ·
                  refine ⟨9063407323340200181491573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12084543097786933575322097 9063407323340200181491573)
                  ·
                    refine ⟨849694436563143767014835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9063407323340200181491573 849694436563143767014835)
                    ·
                      rfl

theorem cell23_4964322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_4964322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964322 prefixEnd_4964322 := by exact prefixLift 4964322
  have htrace : WordTrace (prefixWord ++ tailWord_4964322) baseStart_4964322 baseEnd_4964322 := by
    simpa [prefixWord, tailWord_4964322, baseEnd_4964322] using wordTrace_append hprefix tailTrace_4964322
  have hstable : (prefixWord ++ tailWord_4964322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964322).length < 2 ^ (prefixWord ++ tailWord_4964322).sum := by decide
  have hdescent : baseEnd_4964322 < baseStart_4964322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964335 : List Nat := [1, 1, 2, 1, 4, 2, 2, 5, 1, 4]
def baseStart_4964335 : Nat := 118140960795 + 4964335 * 2 ^ 59
def prefixEnd_4964335 : Nat := 4983230072969 + 3 ^ 40 * 4964335 * 2
def baseEnd_4964335 : Nat := 849696661645979916727315

theorem tailTrace_4964335 : CollatzResearch.WordTrace tailWord_4964335 prefixEnd_4964335 849696661645979916727315 := by
  unfold tailWord_4964335
  simp only [CollatzResearch.WordTrace]
  refine ⟨181064172470069610763046459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120709448313379740508697639 181064172470069610763046459)
  ·
    refine ⟨271596258705104416144569689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181064172470069610763046459 271596258705104416144569689)
    ·
      refine ⟨203697194028828312108427267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271596258705104416144569689 203697194028828312108427267)
      ·
        refine ⟨305545791043242468162640901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203697194028828312108427267 305545791043242468162640901)
        ·
          refine ⟨57289835820607962780495169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305545791043242468162640901 57289835820607962780495169)
          ·
            refine ⟨42967376865455972085371377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57289835820607962780495169 42967376865455972085371377)
            ·
              refine ⟨32225532649091979064028533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42967376865455972085371377 32225532649091979064028533)
              ·
                refine ⟨3021143685852373037252675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32225532649091979064028533 3021143685852373037252675)
                ·
                  refine ⟨4531715528778559555879013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021143685852373037252675 4531715528778559555879013)
                  ·
                    refine ⟨849696661645979916727315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4531715528778559555879013 849696661645979916727315)
                    ·
                      rfl

theorem cell23_4964335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 4].length) (baseStart_4964335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964335 prefixEnd_4964335 := by exact prefixLift 4964335
  have htrace : WordTrace (prefixWord ++ tailWord_4964335) baseStart_4964335 baseEnd_4964335 := by
    simpa [prefixWord, tailWord_4964335, baseEnd_4964335] using wordTrace_append hprefix tailTrace_4964335
  have hstable : (prefixWord ++ tailWord_4964335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964335).length < 2 ^ (prefixWord ++ tailWord_4964335).sum := by decide
  have hdescent : baseEnd_4964335 < baseStart_4964335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964348 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 6]
def baseStart_4964348 : Nat := 118140960795 + 4964348 * 2 ^ 59
def prefixEnd_4964348 : Nat := 4983230072969 + 3 ^ 40 * 4964348 * 2
def baseEnd_4964348 : Nat := 283232962242938688813265

theorem tailTrace_4964348 : CollatzResearch.WordTrace tailWord_4964348 prefixEnd_4964348 283232962242938688813265 := by
  unfold tailWord_4964348
  simp only [CollatzResearch.WordTrace]
  refine ⟨90532323309511256991634849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120709764412681675988846465 90532323309511256991634849)
  ·
    refine ⟨67899242482133442743726137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90532323309511256991634849 67899242482133442743726137)
    ·
      refine ⟨50924431861600082057794603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67899242482133442743726137 50924431861600082057794603)
      ·
        refine ⟨76386647792400123086691905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50924431861600082057794603 76386647792400123086691905)
        ·
          refine ⟨57289985844300092315018929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76386647792400123086691905 57289985844300092315018929)
          ·
            refine ⟨42967489383225069236264197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57289985844300092315018929 42967489383225069236264197)
            ·
              refine ⟨8056404259354700481799537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42967489383225069236264197 8056404259354700481799537)
              ·
                refine ⟨6042303194516025361349653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8056404259354700481799537 6042303194516025361349653)
                ·
                  refine ⟨283232962242938688813265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6042303194516025361349653 283232962242938688813265)
                  ·
                    rfl

theorem cell23_4964348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_4964348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964348 prefixEnd_4964348 := by exact prefixLift 4964348
  have htrace : WordTrace (prefixWord ++ tailWord_4964348) baseStart_4964348 baseEnd_4964348 := by
    simpa [prefixWord, tailWord_4964348, baseEnd_4964348] using wordTrace_append hprefix tailTrace_4964348
  have hstable : (prefixWord ++ tailWord_4964348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964348).length < 2 ^ (prefixWord ++ tailWord_4964348).sum := by decide
  have hdescent : baseEnd_4964348 < baseStart_4964348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964368 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 3, 5, 2]
def baseStart_4964368 : Nat := 118140960795 + 4964368 * 2 ^ 59
def prefixEnd_4964368 : Nat := 4983230072969 + 3 ^ 40 * 4964368 * 2
def baseEnd_4964368 : Nat := 2549106929799538121069293

theorem tailTrace_4964368 : CollatzResearch.WordTrace tailWord_4964368 prefixEnd_4964368 2549106929799538121069293 := by
  unfold tailWord_4964368
  simp only [CollatzResearch.WordTrace]
  refine ⟨90532688039475028699498879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120710250719300038265998505 90532688039475028699498879)
  ·
    refine ⟨135799032059212543049248319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90532688039475028699498879 135799032059212543049248319)
    ·
      refine ⟨203698548088818814573872479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135799032059212543049248319 203698548088818814573872479)
      ·
        refine ⟨305547822133228221860808719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203698548088818814573872479 305547822133228221860808719)
        ·
          refine ⟨458321733199842332791213079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305547822133228221860808719 458321733199842332791213079)
          ·
            refine ⟨687482599799763499186819619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458321733199842332791213079 687482599799763499186819619)
            ·
              refine ⟨1031223899699645248780229429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687482599799763499186819619 1031223899699645248780229429)
              ·
                refine ⟨96677240596841742073146509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1031223899699645248780229429 96677240596841742073146509)
                ·
                  refine ⟨36253965223815653277429941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96677240596841742073146509 36253965223815653277429941)
                  ·
                    refine ⟨3398809239732717494759057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36253965223815653277429941 3398809239732717494759057)
                    ·
                      refine ⟨2549106929799538121069293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398809239732717494759057 2549106929799538121069293)
                      ·
                        rfl

theorem cell23_4964368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 5, 2].length) (baseStart_4964368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964368 prefixEnd_4964368 := by exact prefixLift 4964368
  have htrace : WordTrace (prefixWord ++ tailWord_4964368) baseStart_4964368 baseEnd_4964368 := by
    simpa [prefixWord, tailWord_4964368, baseEnd_4964368] using wordTrace_append hprefix tailTrace_4964368
  have hstable : (prefixWord ++ tailWord_4964368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964368).length < 2 ^ (prefixWord ++ tailWord_4964368).sum := by decide
  have hdescent : baseEnd_4964368 < baseStart_4964368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964378 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_4964378 : Nat := 118140960795 + 4964378 * 2 ^ 59
def prefixEnd_4964378 : Nat := 4983230072969 + 3 ^ 40 * 4964378 * 2
def baseEnd_4964378 : Nat := 849704021535361027314749

theorem tailTrace_4964378 : CollatzResearch.WordTrace tailWord_4964378 prefixEnd_4964378 849704021535361027314749 := by
  unfold tailWord_4964378
  simp only [CollatzResearch.WordTrace]
  refine ⟨45266435202228457276715447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120710493872609219404574525 45266435202228457276715447)
  ·
    refine ⟨67899652803342685915073171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45266435202228457276715447 67899652803342685915073171)
    ·
      refine ⟨101849479205014028872609757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67899652803342685915073171 101849479205014028872609757)
      ·
        refine ⟨38193554701880260827228659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101849479205014028872609757 38193554701880260827228659)
        ·
          refine ⟨57290332052820391240842989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38193554701880260827228659 57290332052820391240842989)
          ·
            refine ⟨21483874519807646715316121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57290332052820391240842989 21483874519807646715316121)
            ·
              refine ⟨16112905889855735036487091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21483874519807646715316121 16112905889855735036487091)
              ·
                refine ⟨24169358834783602554730637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16112905889855735036487091 24169358834783602554730637)
                ·
                  refine ⟨9063509563043850958023989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24169358834783602554730637 9063509563043850958023989)
                  ·
                    refine ⟨849704021535361027314749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9063509563043850958023989 849704021535361027314749)
                    ·
                      rfl

theorem cell23_4964378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_4964378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964378 prefixEnd_4964378 := by exact prefixLift 4964378
  have htrace : WordTrace (prefixWord ++ tailWord_4964378) baseStart_4964378 baseEnd_4964378 := by
    simpa [prefixWord, tailWord_4964378, baseEnd_4964378] using wordTrace_append hprefix tailTrace_4964378
  have hstable : (prefixWord ++ tailWord_4964378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964378).length < 2 ^ (prefixWord ++ tailWord_4964378).sum := by decide
  have hdescent : baseEnd_4964378 < baseStart_4964378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964411 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 6]
def baseStart_4964411 : Nat := 118140960795 + 4964411 * 2 ^ 59
def prefixEnd_4964411 : Nat := 4983230072969 + 3 ^ 40 * 4964411 * 2
def baseEnd_4964411 : Nat := 2549129009467681452831595

theorem tailTrace_4964411 : CollatzResearch.WordTrace tailWord_4964411 prefixEnd_4964411 2549129009467681452831595 := by
  unfold tailWord_4964411
  simp only [CollatzResearch.WordTrace]
  refine ⟨181066944417794275742813087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120711296278529517161875391 181066944417794275742813087)
  ·
    refine ⟨271600416626691413614219631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181066944417794275742813087 271600416626691413614219631)
    ·
      refine ⟨407400624940037120421329447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271600416626691413614219631 407400624940037120421329447)
      ·
        refine ⟨611100937410055680631994171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407400624940037120421329447 611100937410055680631994171)
        ·
          refine ⟨916651406115083520947991257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611100937410055680631994171 916651406115083520947991257)
          ·
            refine ⟨687488554586312640710993443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916651406115083520947991257 687488554586312640710993443)
            ·
              refine ⟨1031232831879468961066490165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687488554586312640710993443 1031232831879468961066490165)
              ·
                refine ⟨96678077988700215099983453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1031232831879468961066490165 96678077988700215099983453)
                ·
                  refine ⟨36254279245762580662493795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96678077988700215099983453 36254279245762580662493795)
                  ·
                    refine ⟨54381418868643870993740693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36254279245762580662493795 54381418868643870993740693)
                    ·
                      refine ⟨2549129009467681452831595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54381418868643870993740693 2549129009467681452831595)
                      ·
                        rfl

theorem cell23_4964411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_4964411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964411 prefixEnd_4964411 := by exact prefixLift 4964411
  have htrace : WordTrace (prefixWord ++ tailWord_4964411) baseStart_4964411 baseEnd_4964411 := by
    simpa [prefixWord, tailWord_4964411, baseEnd_4964411] using wordTrace_append hprefix tailTrace_4964411
  have hstable : (prefixWord ++ tailWord_4964411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964411).length < 2 ^ (prefixWord ++ tailWord_4964411).sum := by decide
  have hdescent : baseEnd_4964411 < baseStart_4964411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964421 : List Nat := [1, 3, 1, 1, 1, 3, 1, 12]
def baseStart_4964421 : Nat := 118140960795 + 4964421 * 2 ^ 59
def prefixEnd_4964421 : Nat := 4983230072969 + 3 ^ 40 * 4964421 * 2
def baseEnd_4964421 : Nat := 94412375713860237544687

theorem tailTrace_4964421 : CollatzResearch.WordTrace tailWord_4964421 prefixEnd_4964421 94412375713860237544687 := by
  unfold tailWord_4964421
  simp only [CollatzResearch.WordTrace]
  refine ⟨181067309147758047450677117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120711539431838698300451411 181067309147758047450677117)
  ·
    refine ⟨67900240930409267794003919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181067309147758047450677117 67900240930409267794003919)
    ·
      refine ⟨101850361395613901691005879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67900240930409267794003919 101850361395613901691005879)
      ·
        refine ⟨152775542093420852536508819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101850361395613901691005879 152775542093420852536508819)
        ·
          refine ⟨229163313140131278804763229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152775542093420852536508819 229163313140131278804763229)
          ·
            refine ⟨85936242427549229551786211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229163313140131278804763229 85936242427549229551786211)
            ·
              refine ⟨128904363641323844327679317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85936242427549229551786211 128904363641323844327679317)
              ·
                refine ⟨94412375713860237544687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 128904363641323844327679317 94412375713860237544687)
                ·
                  rfl

theorem cell23_4964421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 12].length) (baseStart_4964421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964421 prefixEnd_4964421 := by exact prefixLift 4964421
  have htrace : WordTrace (prefixWord ++ tailWord_4964421) baseStart_4964421 baseEnd_4964421 := by
    simpa [prefixWord, tailWord_4964421, baseEnd_4964421] using wordTrace_append hprefix tailTrace_4964421
  have hstable : (prefixWord ++ tailWord_4964421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964421).length < 2 ^ (prefixWord ++ tailWord_4964421).sum := by decide
  have hdescent : baseEnd_4964421 < baseStart_4964421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964431 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_4964431 : Nat := 118140960795 + 4964431 * 2 ^ 59
def prefixEnd_4964431 : Nat := 4983230072969 + 3 ^ 40 * 4964431 * 2
def baseEnd_4964431 : Nat := 2549139279080771374581503

theorem tailTrace_4964431 : CollatzResearch.WordTrace tailWord_4964431 prefixEnd_4964431 2549139279080771374581503 := by
  unfold tailWord_4964431
  simp only [CollatzResearch.WordTrace]
  refine ⟨181067673877721819158541147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120711782585147879439027431 181067673877721819158541147)
  ·
    refine ⟨271601510816582728737811721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181067673877721819158541147 271601510816582728737811721)
    ·
      refine ⟨203701133112437046553358791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271601510816582728737811721 203701133112437046553358791)
      ·
        refine ⟨305551699668655569830038187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203701133112437046553358791 305551699668655569830038187)
        ·
          refine ⟨458327549502983354745057281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305551699668655569830038187 458327549502983354745057281)
          ·
            refine ⟨343745662127237516058792961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458327549502983354745057281 343745662127237516058792961)
            ·
              refine ⟨257809246595428137044094721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343745662127237516058792961 257809246595428137044094721)
              ·
                refine ⟨193356934946571102783071041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257809246595428137044094721 193356934946571102783071041)
                ·
                  refine ⟨145017701209928327087303281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193356934946571102783071041 145017701209928327087303281)
                  ·
                    refine ⟨108763275907446245315477461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145017701209928327087303281 108763275907446245315477461)
                    ·
                      refine ⟨2549139279080771374581503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108763275907446245315477461 2549139279080771374581503)
                      ·
                        rfl

theorem cell23_4964431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_4964431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964431 prefixEnd_4964431 := by exact prefixLift 4964431
  have htrace : WordTrace (prefixWord ++ tailWord_4964431) baseStart_4964431 baseEnd_4964431 := by
    simpa [prefixWord, tailWord_4964431, baseEnd_4964431] using wordTrace_append hprefix tailTrace_4964431
  have hstable : (prefixWord ++ tailWord_4964431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964431).length < 2 ^ (prefixWord ++ tailWord_4964431).sum := by decide
  have hdescent : baseEnd_4964431 < baseStart_4964431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964465 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_4964465 : Nat := 118140960795 + 4964465 * 2 ^ 59
def prefixEnd_4964465 : Nat := 4983230072969 + 3 ^ 40 * 4964465 * 2
def baseEnd_4964465 : Nat := 2549156737423024241556347

theorem tailTrace_4964465 : CollatzResearch.WordTrace tailWord_4964465 prefixEnd_4964465 2549156737423024241556347 := by
  unfold tailWord_4964465
  simp only [CollatzResearch.WordTrace]
  refine ⟨181068913959598642965278849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120712609306399095310185899 181068913959598642965278849)
  ·
    refine ⟨135801685469698982223959137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181068913959598642965278849 135801685469698982223959137)
    ·
      refine ⟨101851264102274236667969353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135801685469698982223959137 101851264102274236667969353)
      ·
        refine ⟨76388448076705677500977015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101851264102274236667969353 76388448076705677500977015)
        ·
          refine ⟨114582672115058516251465523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76388448076705677500977015 114582672115058516251465523)
          ·
            refine ⟨171874008172587774377198285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114582672115058516251465523 171874008172587774377198285)
            ·
              refine ⟨64452753064720415391449357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171874008172587774377198285 64452753064720415391449357)
              ·
                refine ⟨24169782399270155771793509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64452753064720415391449357 24169782399270155771793509)
                ·
                  refine ⟨4531834199863154207211283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24169782399270155771793509 4531834199863154207211283)
                  ·
                    refine ⟨6797751299794731310816925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4531834199863154207211283 6797751299794731310816925)
                    ·
                      refine ⟨2549156737423024241556347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6797751299794731310816925 2549156737423024241556347)
                      ·
                        rfl

theorem cell23_4964465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_4964465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964465 prefixEnd_4964465 := by exact prefixLift 4964465
  have htrace : WordTrace (prefixWord ++ tailWord_4964465) baseStart_4964465 baseEnd_4964465 := by
    simpa [prefixWord, tailWord_4964465, baseEnd_4964465] using wordTrace_append hprefix tailTrace_4964465
  have hstable : (prefixWord ++ tailWord_4964465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964465).length < 2 ^ (prefixWord ++ tailWord_4964465).sum := by decide
  have hdescent : baseEnd_4964465 < baseStart_4964465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964535 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_4964535 : Nat := 118140960795 + 4964535 * 2 ^ 59
def prefixEnd_4964535 : Nat := 4983230072969 + 3 ^ 40 * 4964535 * 2
def baseEnd_4964535 : Nat := 2549192681068838967681025

theorem tailTrace_4964535 : CollatzResearch.WordTrace tailWord_4964535 prefixEnd_4964535 2549192681068838967681025 := by
  unfold tailWord_4964535
  simp only [CollatzResearch.WordTrace]
  refine ⟨181071467069345044920327059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120714311379563363280218039 181071467069345044920327059)
  ·
    refine ⟨271607200604017567380490589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181071467069345044920327059 271607200604017567380490589)
    ·
      refine ⟨101852700226506587767683971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271607200604017567380490589 101852700226506587767683971)
      ·
        refine ⟨152779050339759881651525957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101852700226506587767683971 152779050339759881651525957)
        ·
          refine ⟨28646071938704977809661117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152779050339759881651525957 28646071938704977809661117)
          ·
            refine ⟨10742276977014366678622919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28646071938704977809661117 10742276977014366678622919)
            ·
              refine ⟨16113415465521550017934379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10742276977014366678622919 16113415465521550017934379)
              ·
                refine ⟨24170123198282325026901569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16113415465521550017934379 24170123198282325026901569)
                ·
                  refine ⟨18127592398711743770176177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24170123198282325026901569 18127592398711743770176177)
                  ·
                    refine ⟨13595694299033807827632133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18127592398711743770176177 13595694299033807827632133)
                    ·
                      refine ⟨2549192681068838967681025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13595694299033807827632133 2549192681068838967681025)
                      ·
                        rfl

theorem cell23_4964535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_4964535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964535 prefixEnd_4964535 := by exact prefixLift 4964535
  have htrace : WordTrace (prefixWord ++ tailWord_4964535) baseStart_4964535 baseEnd_4964535 := by
    simpa [prefixWord, tailWord_4964535, baseEnd_4964535] using wordTrace_append hprefix tailTrace_4964535
  have hstable : (prefixWord ++ tailWord_4964535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964535).length < 2 ^ (prefixWord ++ tailWord_4964535).sum := by decide
  have hdescent : baseEnd_4964535 < baseStart_4964535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964562 : List Nat := [3, 2, 2, 2, 1, 2, 1, 5, 5]
def baseStart_4964562 : Nat := 118140960795 + 4964562 * 2 ^ 59
def prefixEnd_4964562 : Nat := 4983230072969 + 3 ^ 40 * 4964562 * 2
def baseEnd_4964562 : Nat := 283245171671834484671489

theorem tailTrace_4964562 : CollatzResearch.WordTrace tailWord_4964562 prefixEnd_4964562 283245171671834484671489 := by
  unfold tailWord_4964562
  simp only [CollatzResearch.WordTrace]
  refine ⟨45268112960061807132889985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120714967893498152354373293 45268112960061807132889985)
  ·
    refine ⟨33951084720046355349667489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45268112960061807132889985 33951084720046355349667489)
    ·
      refine ⟨25463313540034766512250617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33951084720046355349667489 25463313540034766512250617)
      ·
        refine ⟨19097485155026074884187963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25463313540034766512250617 19097485155026074884187963)
        ·
          refine ⟨28646227732539112326281945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19097485155026074884187963 28646227732539112326281945)
          ·
            refine ⟨21484670799404334244711459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28646227732539112326281945 21484670799404334244711459)
            ·
              refine ⟨32227006199106501367067189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21484670799404334244711459 32227006199106501367067189)
              ·
                refine ⟨3021281831166234503162549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32227006199106501367067189 3021281831166234503162549)
                ·
                  refine ⟨283245171671834484671489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021281831166234503162549 283245171671834484671489)
                  ·
                    rfl

theorem cell23_4964562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_4964562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964562 prefixEnd_4964562 := by exact prefixLift 4964562
  have htrace : WordTrace (prefixWord ++ tailWord_4964562) baseStart_4964562 baseEnd_4964562 := by
    simpa [prefixWord, tailWord_4964562, baseEnd_4964562] using wordTrace_append hprefix tailTrace_4964562
  have hstable : (prefixWord ++ tailWord_4964562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964562).length < 2 ^ (prefixWord ++ tailWord_4964562).sum := by decide
  have hdescent : baseEnd_4964562 < baseStart_4964562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964573 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4964573 : Nat := 118140960795 + 4964573 * 2 ^ 59
def prefixEnd_4964573 : Nat := 4983230072969 + 3 ^ 40 * 4964573 * 2
def baseEnd_4964573 : Nat := 2549212193333709819005851

theorem tailTrace_4964573 : CollatzResearch.WordTrace tailWord_4964573 prefixEnd_4964573 2549212193333709819005851 := by
  unfold tailWord_4964573
  simp only [CollatzResearch.WordTrace]
  refine ⟨181072853043207377410210373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120715235362138251606806915 181072853043207377410210373)
  ·
    refine ⟨33951159945601383264414445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181072853043207377410210373 33951159945601383264414445)
    ·
      refine ⟨12731684979600518724155417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33951159945601383264414445 12731684979600518724155417)
      ·
        refine ⟨9548763734700389043116563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12731684979600518724155417 9548763734700389043116563)
        ·
          refine ⟨14323145602050583564674845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9548763734700389043116563 14323145602050583564674845)
          ·
            refine ⟨5371179600768968836753067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14323145602050583564674845 5371179600768968836753067)
            ·
              refine ⟨8056769401153453255129601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5371179600768968836753067 8056769401153453255129601)
              ·
                refine ⟨6042577050865089941347201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8056769401153453255129601 6042577050865089941347201)
                ·
                  refine ⟨4531932788148817456010401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6042577050865089941347201 4531932788148817456010401)
                  ·
                    refine ⟨3398949591111613092007801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4531932788148817456010401 3398949591111613092007801)
                    ·
                      refine ⟨2549212193333709819005851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3398949591111613092007801 2549212193333709819005851)
                      ·
                        rfl

theorem cell23_4964573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4964573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964573 prefixEnd_4964573 := by exact prefixLift 4964573
  have htrace : WordTrace (prefixWord ++ tailWord_4964573) baseStart_4964573 baseEnd_4964573 := by
    simpa [prefixWord, tailWord_4964573, baseEnd_4964573] using wordTrace_append hprefix tailTrace_4964573
  have hstable : (prefixWord ++ tailWord_4964573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964573).length < 2 ^ (prefixWord ++ tailWord_4964573).sum := by decide
  have hdescent : baseEnd_4964573 < baseStart_4964573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964632 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_4964632 : Nat := 118140960795 + 4964632 * 2 ^ 59
def prefixEnd_4964632 : Nat := 4983230072969 + 3 ^ 40 * 4964632 * 2
def baseEnd_4964632 : Nat := 2549242488692325088168079

theorem tailTrace_4964632 : CollatzResearch.WordTrace tailWord_4964632 prefixEnd_4964632 2549242488692325088168079 := by
  unfold tailWord_4964632
  simp only [CollatzResearch.WordTrace]
  refine ⟨90537502474996815243304075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120716669966662420324405433 90537502474996815243304075)
  ·
    refine ⟨135806253712495222864956113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90537502474996815243304075 135806253712495222864956113)
    ·
      refine ⟨101854690284371417148717085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135806253712495222864956113 101854690284371417148717085)
      ·
        refine ⟨38195508856639281430768907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101854690284371417148717085 38195508856639281430768907)
        ·
          refine ⟨57293263284958922146153361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38195508856639281430768907 57293263284958922146153361)
          ·
            refine ⟨42969947463719191609615021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57293263284958922146153361 42969947463719191609615021)
            ·
              refine ⟨16113730298894696853605633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42969947463719191609615021 16113730298894696853605633)
              ·
                refine ⟨12085297724171022640204225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16113730298894696853605633 12085297724171022640204225)
                ·
                  refine ⟨9063973293128266980153169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12085297724171022640204225 9063973293128266980153169)
                  ·
                    refine ⟨6797979969846200235114877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9063973293128266980153169 6797979969846200235114877)
                    ·
                      refine ⟨2549242488692325088168079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6797979969846200235114877 2549242488692325088168079)
                      ·
                        rfl

theorem cell23_4964632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_4964632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964632 prefixEnd_4964632 := by exact prefixLift 4964632
  have htrace : WordTrace (prefixWord ++ tailWord_4964632) baseStart_4964632 baseEnd_4964632 := by
    simpa [prefixWord, tailWord_4964632, baseEnd_4964632] using wordTrace_append hprefix tailTrace_4964632
  have hstable : (prefixWord ++ tailWord_4964632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964632).length < 2 ^ (prefixWord ++ tailWord_4964632).sum := by decide
  have hdescent : baseEnd_4964632 < baseStart_4964632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964639 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 3, 4]
def baseStart_4964639 : Nat := 118140960795 + 4964639 * 2 ^ 59
def prefixEnd_4964639 : Nat := 4983230072969 + 3 ^ 40 * 4964639 * 2
def baseEnd_4964639 : Nat := 849748694352302186926849

theorem tailTrace_4964639 : CollatzResearch.WordTrace tailWord_4964639 prefixEnd_4964639 849748694352302186926849 := by
  unfold tailWord_4964639
  simp only [CollatzResearch.WordTrace]
  refine ⟨181075260260968270682112971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120716840173978847121408647 181075260260968270682112971)
  ·
    refine ⟨271612890391452406023169457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181075260260968270682112971 271612890391452406023169457)
    ·
      refine ⟨203709667793589304517377093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271612890391452406023169457 203709667793589304517377093)
      ·
        refine ⟨38195562711297994597008205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203709667793589304517377093 38195562711297994597008205)
        ·
          refine ⟨14323336016736747973878077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38195562711297994597008205 14323336016736747973878077)
          ·
            refine ⟨5371251006276280490204279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14323336016736747973878077 5371251006276280490204279)
            ·
              refine ⟨8056876509414420735306419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5371251006276280490204279 8056876509414420735306419)
              ·
                refine ⟨12085314764121631102959629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8056876509414420735306419 12085314764121631102959629)
                ·
                  refine ⟨4531993036545611663609861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12085314764121631102959629 4531993036545611663609861)
                  ·
                    refine ⟨849748694352302186926849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4531993036545611663609861 849748694352302186926849)
                    ·
                      rfl

theorem cell23_4964639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 4].length) (baseStart_4964639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964639 prefixEnd_4964639 := by exact prefixLift 4964639
  have htrace : WordTrace (prefixWord ++ tailWord_4964639) baseStart_4964639 baseEnd_4964639 := by
    simpa [prefixWord, tailWord_4964639, baseEnd_4964639] using wordTrace_append hprefix tailTrace_4964639
  have hstable : (prefixWord ++ tailWord_4964639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964639).length < 2 ^ (prefixWord ++ tailWord_4964639).sum := by decide
  have hdescent : baseEnd_4964639 < baseStart_4964639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964652 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 6]
def baseStart_4964652 : Nat := 118140960795 + 4964652 * 2 ^ 59
def prefixEnd_4964652 : Nat := 4983230072969 + 3 ^ 40 * 4964652 * 2
def baseEnd_4964652 : Nat := 283250306478379445546443

theorem tailTrace_4964652 : CollatzResearch.WordTrace tailWord_4964652 prefixEnd_4964652 283250306478379445546443 := by
  unfold tailWord_4964652
  simp only [CollatzResearch.WordTrace]
  refine ⟨90537867204960586951168105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120717156273280782601557473 90537867204960586951168105)
  ·
    refine ⟨67903400403720440213376079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90537867204960586951168105 67903400403720440213376079)
    ·
      refine ⟨101855100605580660320064119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67903400403720440213376079 101855100605580660320064119)
      ·
        refine ⟨152782650908370990480096179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101855100605580660320064119 152782650908370990480096179)
        ·
          refine ⟨229173976362556485720144269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152782650908370990480096179 229173976362556485720144269)
          ·
            refine ⟨85940241135958682145054101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229173976362556485720144269 85940241135958682145054101)
            ·
              refine ⟨4028448803248063225549411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85940241135958682145054101 4028448803248063225549411)
              ·
                refine ⟨6042673204872094838324117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028448803248063225549411 6042673204872094838324117)
                ·
                  refine ⟨283250306478379445546443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6042673204872094838324117 283250306478379445546443)
                  ·
                    rfl

theorem cell23_4964652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_4964652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964652 prefixEnd_4964652 := by exact prefixLift 4964652
  have htrace : WordTrace (prefixWord ++ tailWord_4964652) baseStart_4964652 baseEnd_4964652 := by
    simpa [prefixWord, tailWord_4964652, baseEnd_4964652] using wordTrace_append hprefix tailTrace_4964652
  have hstable : (prefixWord ++ tailWord_4964652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964652).length < 2 ^ (prefixWord ++ tailWord_4964652).sum := by decide
  have hdescent : baseEnd_4964652 < baseStart_4964652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964689 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 2, 3, 2]
def baseStart_4964689 : Nat := 118140960795 + 4964689 * 2 ^ 59
def prefixEnd_4964689 : Nat := 4983230072969 + 3 ^ 40 * 4964689 * 2
def baseEnd_4964689 : Nat := 2549271757089631365155317

theorem tailTrace_4964689 : CollatzResearch.WordTrace tailWord_4964689 prefixEnd_4964689 2549271757089631365155317 := by
  unfold tailWord_4964689
  simp only [CollatzResearch.WordTrace]
  refine ⟨181077083910787129221433121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120718055940524752814288747 181077083910787129221433121)
  ·
    refine ⟨135807812933090346916074841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181077083910787129221433121 135807812933090346916074841)
    ·
      refine ⟨101855859699817760187056131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135807812933090346916074841 101855859699817760187056131)
      ·
        refine ⟨152783789549726640280584197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101855859699817760187056131 152783789549726640280584197)
        ·
          refine ⟨28646960540573745052609537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152783789549726640280584197 28646960540573745052609537)
          ·
            refine ⟨21485220405430308789457153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28646960540573745052609537 21485220405430308789457153)
            ·
              refine ⟨16113915304072731592092865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21485220405430308789457153 16113915304072731592092865)
              ·
                refine ⟨12085436478054548694069649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16113915304072731592092865 12085436478054548694069649)
                ·
                  refine ⟨9064077358540911520552237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12085436478054548694069649 9064077358540911520552237)
                  ·
                    refine ⟨3399029009452841820207089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9064077358540911520552237 3399029009452841820207089)
                    ·
                      refine ⟨2549271757089631365155317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399029009452841820207089 2549271757089631365155317)
                      ·
                        rfl

theorem cell23_4964689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_4964689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964689 prefixEnd_4964689 := by exact prefixLift 4964689
  have htrace : WordTrace (prefixWord ++ tailWord_4964689) baseStart_4964689 baseEnd_4964689 := by
    simpa [prefixWord, tailWord_4964689, baseEnd_4964689] using wordTrace_append hprefix tailTrace_4964689
  have hstable : (prefixWord ++ tailWord_4964689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964689).length < 2 ^ (prefixWord ++ tailWord_4964689).sum := by decide
  have hdescent : baseEnd_4964689 < baseStart_4964689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964695 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 3, 6]
def baseStart_4964695 : Nat := 118140960795 + 4964695 * 2 ^ 59
def prefixEnd_4964695 : Nat := 4983230072969 + 3 ^ 40 * 4964695 * 2
def baseEnd_4964695 : Nat := 849758279324519447226763

theorem tailTrace_4964695 : CollatzResearch.WordTrace tailWord_4964695 prefixEnd_4964695 849758279324519447226763 := by
  unfold tailWord_4964695
  simp only [CollatzResearch.WordTrace]
  refine ⟨181077302748765392246151539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120718201832510261497434359 181077302748765392246151539)
  ·
    refine ⟨271615954123148088369227309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181077302748765392246151539 271615954123148088369227309)
    ·
      refine ⟨101855982796180533138460241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271615954123148088369227309 101855982796180533138460241)
      ·
        refine ⟨76391987097135399853845181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101855982796180533138460241 76391987097135399853845181)
        ·
          refine ⟨28646995161425774945191943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76391987097135399853845181 28646995161425774945191943)
          ·
            refine ⟨42970492742138662417787915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28646995161425774945191943 42970492742138662417787915)
            ·
              refine ⟨64455739113207993626681873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42970492742138662417787915 64455739113207993626681873)
              ·
                refine ⟨48341804334905995220011405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64455739113207993626681873 48341804334905995220011405)
                ·
                  refine ⟨18128176625589748207504277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48341804334905995220011405 18128176625589748207504277)
                  ·
                    refine ⟨849758279324519447226763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18128176625589748207504277 849758279324519447226763)
                    ·
                      rfl

theorem cell23_4964695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_4964695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964695 prefixEnd_4964695 := by exact prefixLift 4964695
  have htrace : WordTrace (prefixWord ++ tailWord_4964695) baseStart_4964695 baseEnd_4964695 := by
    simpa [prefixWord, tailWord_4964695, baseEnd_4964695] using wordTrace_append hprefix tailTrace_4964695
  have hstable : (prefixWord ++ tailWord_4964695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964695).length < 2 ^ (prefixWord ++ tailWord_4964695).sum := by decide
  have hdescent : baseEnd_4964695 < baseStart_4964695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964712 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 1, 6]
def baseStart_4964712 : Nat := 118140960795 + 4964712 * 2 ^ 59
def prefixEnd_4964712 : Nat := 4983230072969 + 3 ^ 40 * 4964712 * 2
def baseEnd_4964712 : Nat := 849761189048228258389237

theorem tailTrace_4964712 : CollatzResearch.WordTrace tailWord_4964712 prefixEnd_4964712 849761189048228258389237 := by
  unfold tailWord_4964712
  simp only [CollatzResearch.WordTrace]
  refine ⟨90538961394851902074760195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120718615193135869433013593 90538961394851902074760195)
  ·
    refine ⟨135808442092277853112140293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90538961394851902074760195 135808442092277853112140293)
    ·
      refine ⟨25464082892302097458526305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135808442092277853112140293 25464082892302097458526305)
      ·
        refine ⟨19098062169226573093894729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25464082892302097458526305 19098062169226573093894729)
        ·
          refine ⟨14323546626919929820421047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19098062169226573093894729 14323546626919929820421047)
          ·
            refine ⟨21485319940379894730631571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14323546626919929820421047 21485319940379894730631571)
            ·
              refine ⟨32227979910569842095947357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21485319940379894730631571 32227979910569842095947357)
              ·
                refine ⟨12085492466463690785980259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32227979910569842095947357 12085492466463690785980259)
                ·
                  refine ⟨18128238699695536178970389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12085492466463690785980259 18128238699695536178970389)
                  ·
                    refine ⟨849761189048228258389237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18128238699695536178970389 849761189048228258389237)
                    ·
                      rfl

theorem cell23_4964712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_4964712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964712 prefixEnd_4964712 := by exact prefixLift 4964712
  have htrace : WordTrace (prefixWord ++ tailWord_4964712) baseStart_4964712 baseEnd_4964712 := by
    simpa [prefixWord, tailWord_4964712, baseEnd_4964712] using wordTrace_append hprefix tailTrace_4964712
  have hstable : (prefixWord ++ tailWord_4964712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964712).length < 2 ^ (prefixWord ++ tailWord_4964712).sum := by decide
  have hdescent : baseEnd_4964712 < baseStart_4964712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964715 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 4]
def baseStart_4964715 : Nat := 118140960795 + 4964715 * 2 ^ 59
def prefixEnd_4964715 : Nat := 4983230072969 + 3 ^ 40 * 4964715 * 2
def baseEnd_4964715 : Nat := 2549285107586648263430197

theorem tailTrace_4964715 : CollatzResearch.WordTrace tailWord_4964715 prefixEnd_4964715 2549285107586648263430197 := by
  unfold tailWord_4964715
  simp only [CollatzResearch.WordTrace]
  refine ⟨181078032208692935661879599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120718688139128623774586399 181078032208692935661879599)
  ·
    refine ⟨271617048313039403492819399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181078032208692935661879599 271617048313039403492819399)
    ·
      refine ⟨407425572469559105239229099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271617048313039403492819399 407425572469559105239229099)
      ·
        refine ⟨611138358704338657858843649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407425572469559105239229099 611138358704338657858843649)
        ·
          refine ⟨458353769028253993394132737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611138358704338657858843649 458353769028253993394132737)
          ·
            refine ⟨343765326771190495045599553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458353769028253993394132737 343765326771190495045599553)
            ·
              refine ⟨257823995078392871284199665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343765326771190495045599553 257823995078392871284199665)
              ·
                refine ⟨193367996308794653463149749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257823995078392871284199665 193367996308794653463149749)
                ·
                  refine ⟨18128249653949498762170289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193367996308794653463149749 18128249653949498762170289)
                  ·
                    refine ⟨13596187240462124071627717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18128249653949498762170289 13596187240462124071627717)
                    ·
                      refine ⟨2549285107586648263430197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13596187240462124071627717 2549285107586648263430197)
                      ·
                        rfl

theorem cell23_4964715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 4].length) (baseStart_4964715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964715 prefixEnd_4964715 := by exact prefixLift 4964715
  have htrace : WordTrace (prefixWord ++ tailWord_4964715) baseStart_4964715 baseEnd_4964715 := by
    simpa [prefixWord, tailWord_4964715, baseEnd_4964715] using wordTrace_append hprefix tailTrace_4964715
  have hstable : (prefixWord ++ tailWord_4964715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964715).length < 2 ^ (prefixWord ++ tailWord_4964715).sum := by decide
  have hdescent : baseEnd_4964715 < baseStart_4964715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964746 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_4964746 : Nat := 118140960795 + 4964746 * 2 ^ 59
def prefixEnd_4964746 : Nat := 4983230072969 + 3 ^ 40 * 4964746 * 2
def baseEnd_4964746 : Nat := 849767008495645880714185

theorem tailTrace_4964746 : CollatzResearch.WordTrace tailWord_4964746 prefixEnd_4964746 849767008495645880714185 := by
  unfold tailWord_4964746
  simp only [CollatzResearch.WordTrace]
  refine ⟨45269790717895156989064523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120719441914387085304172061 45269790717895156989064523)
  ·
    refine ⟨67904686076842735483596785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45269790717895156989064523 67904686076842735483596785)
    ·
      refine ⟨50928514557632051612697589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67904686076842735483596785 50928514557632051612697589)
      ·
        refine ⟨4774548239778004838690399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50928514557632051612697589 4774548239778004838690399)
        ·
          refine ⟨7161822359667007258035599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4774548239778004838690399 7161822359667007258035599)
          ·
            refine ⟨10742733539500510887053399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7161822359667007258035599 10742733539500510887053399)
            ·
              refine ⟨16114100309250766330580099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10742733539500510887053399 16114100309250766330580099)
              ·
                refine ⟨24171150463876149495870149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16114100309250766330580099 24171150463876149495870149)
                ·
                  refine ⟨4532090711976778030475653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24171150463876149495870149 4532090711976778030475653)
                  ·
                    refine ⟨849767008495645880714185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4532090711976778030475653 849767008495645880714185)
                    ·
                      rfl

theorem cell23_4964746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_4964746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964746 prefixEnd_4964746 := by exact prefixLift 4964746
  have htrace : WordTrace (prefixWord ++ tailWord_4964746) baseStart_4964746 baseEnd_4964746 := by
    simpa [prefixWord, tailWord_4964746, baseEnd_4964746] using wordTrace_append hprefix tailTrace_4964746
  have hstable : (prefixWord ++ tailWord_4964746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964746).length < 2 ^ (prefixWord ++ tailWord_4964746).sum := by decide
  have hdescent : baseEnd_4964746 < baseStart_4964746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964766 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4964766 : Nat := 118140960795 + 4964766 * 2 ^ 59
def prefixEnd_4964766 : Nat := 4983230072969 + 3 ^ 40 * 4964766 * 2
def baseEnd_4964766 : Nat := 2549311295100027563892463

theorem tailTrace_4964766 : CollatzResearch.WordTrace tailWord_4964766 prefixEnd_4964766 2549311295100027563892463 := by
  unfold tailWord_4964766
  simp only [CollatzResearch.WordTrace]
  refine ⟨22634986541438521421498269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120719928221005447581324101 22634986541438521421498269)
  ·
    refine ⟨8488119953039445533061851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22634986541438521421498269 8488119953039445533061851)
    ·
      refine ⟨12732179929559168299592777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8488119953039445533061851 12732179929559168299592777)
      ·
        refine ⟨9549134947169376224694583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12732179929559168299592777 9549134947169376224694583)
        ·
          refine ⟨14323702420754064337041875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9549134947169376224694583 14323702420754064337041875)
          ·
            refine ⟨21485553631131096505562813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14323702420754064337041875 21485553631131096505562813)
            ·
              refine ⟨8057082611674161189586055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21485553631131096505562813 8057082611674161189586055)
              ·
                refine ⟨12085623917511241784379083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8057082611674161189586055 12085623917511241784379083)
                ·
                  refine ⟨18128435876266862676568625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12085623917511241784379083 18128435876266862676568625)
                  ·
                    refine ⟨13596326907200147007426469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18128435876266862676568625 13596326907200147007426469)
                    ·
                      refine ⟨2549311295100027563892463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13596326907200147007426469 2549311295100027563892463)
                      ·
                        rfl

theorem cell23_4964766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4964766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964766 prefixEnd_4964766 := by exact prefixLift 4964766
  have htrace : WordTrace (prefixWord ++ tailWord_4964766) baseStart_4964766 baseEnd_4964766 := by
    simpa [prefixWord, tailWord_4964766, baseEnd_4964766] using wordTrace_append hprefix tailTrace_4964766
  have hstable : (prefixWord ++ tailWord_4964766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964766).length < 2 ^ (prefixWord ++ tailWord_4964766).sum := by decide
  have hdescent : baseEnd_4964766 < baseStart_4964766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964776 : List Nat := [2, 1, 6, 1, 1, 3, 2, 7]
def baseStart_4964776 : Nat := 118140960795 + 4964776 * 2 ^ 59
def prefixEnd_4964776 : Nat := 4983230072969 + 3 ^ 40 * 4964776 * 2
def baseEnd_4964776 : Nat := 94419127033576760176571

theorem tailTrace_4964776 : CollatzResearch.WordTrace tailWord_4964776 prefixEnd_4964776 94419127033576760176571 := by
  unfold tailWord_4964776
  simp only [CollatzResearch.WordTrace]
  refine ⟨90540128530735971539925091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120720171374314628719900121 90540128530735971539925091)
  ·
    refine ⟨135810192796103957309887637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90540128530735971539925091 135810192796103957309887637)
    ·
      refine ⟨6366102787317372998900983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 135810192796103957309887637 6366102787317372998900983)
      ·
        refine ⟨9549154180976059498351475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6366102787317372998900983 9549154180976059498351475)
        ·
          refine ⟨14323731271464089247527213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9549154180976059498351475 14323731271464089247527213)
          ·
            refine ⟨5371399226799033467822705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14323731271464089247527213 5371399226799033467822705)
            ·
              refine ⟨4028549420099275100867029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5371399226799033467822705 4028549420099275100867029)
              ·
                refine ⟨94419127033576760176571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4028549420099275100867029 94419127033576760176571)
                ·
                  rfl

theorem cell23_4964776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 7].length) (baseStart_4964776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964776 prefixEnd_4964776 := by exact prefixLift 4964776
  have htrace : WordTrace (prefixWord ++ tailWord_4964776) baseStart_4964776 baseEnd_4964776 := by
    simpa [prefixWord, tailWord_4964776, baseEnd_4964776] using wordTrace_append hprefix tailTrace_4964776
  have hstable : (prefixWord ++ tailWord_4964776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964776).length < 2 ^ (prefixWord ++ tailWord_4964776).sum := by decide
  have hdescent : baseEnd_4964776 < baseStart_4964776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964820 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_4964820 : Nat := 118140960795 + 4964820 * 2 ^ 59
def prefixEnd_4964820 : Nat := 4983230072969 + 3 ^ 40 * 4964820 * 2
def baseEnd_4964820 : Nat := 2549339023055370352617215

theorem tailTrace_4964820 : CollatzResearch.WordTrace tailWord_4964820 prefixEnd_4964820 2549339023055370352617215 := by
  unfold tailWord_4964820
  simp only [CollatzResearch.WordTrace]
  refine ⟨90540930936656269297225957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120721241248875025729634609 90540930936656269297225957)
  ·
    refine ⟨16976424550623050493229867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90540930936656269297225957 16976424550623050493229867)
    ·
      refine ⟨25464636825934575739844801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16976424550623050493229867 25464636825934575739844801)
      ·
        refine ⟨19098477619450931804883601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25464636825934575739844801 19098477619450931804883601)
        ·
          refine ⟨14323858214588198853662701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19098477619450931804883601 14323858214588198853662701)
          ·
            refine ⟨5371446830470574570123513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14323858214588198853662701 5371446830470574570123513)
            ·
              refine ⟨4028585122852930927592635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5371446830470574570123513 4028585122852930927592635)
              ·
                refine ⟨6042877684279396391388953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028585122852930927592635 6042877684279396391388953)
                ·
                  refine ⟨4532158263209547293541715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6042877684279396391388953 4532158263209547293541715)
                  ·
                    refine ⟨6798237394814320940312573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4532158263209547293541715 6798237394814320940312573)
                    ·
                      refine ⟨2549339023055370352617215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6798237394814320940312573 2549339023055370352617215)
                      ·
                        rfl

theorem cell23_4964820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_4964820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964820 prefixEnd_4964820 := by exact prefixLift 4964820
  have htrace : WordTrace (prefixWord ++ tailWord_4964820) baseStart_4964820 baseEnd_4964820 := by
    simpa [prefixWord, tailWord_4964820, baseEnd_4964820] using wordTrace_append hprefix tailTrace_4964820
  have hstable : (prefixWord ++ tailWord_4964820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964820).length < 2 ^ (prefixWord ++ tailWord_4964820).sum := by decide
  have hdescent : baseEnd_4964820 < baseStart_4964820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964849 : List Nat := [1, 2, 2, 2, 3, 1, 2, 5, 5]
def baseStart_4964849 : Nat := 118140960795 + 4964849 * 2 ^ 59
def prefixEnd_4964849 : Nat := 4983230072969 + 3 ^ 40 * 4964849 * 2
def baseEnd_4964849 : Nat := 283261545999372304350509

theorem tailTrace_4964849 : CollatzResearch.WordTrace tailWord_4964849 prefixEnd_4964849 283261545999372304350509 := by
  unfold tailWord_4964849
  simp only [CollatzResearch.WordTrace]
  refine ⟨181082919590207476547257601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120721946393471651031505067 181082919590207476547257601)
  ·
    refine ⟨135812189692655607410443201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181082919590207476547257601 135812189692655607410443201)
    ·
      refine ⟨101859142269491705557832401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135812189692655607410443201 101859142269491705557832401)
      ·
        refine ⟨76394356702118779168374301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101859142269491705557832401 76394356702118779168374301)
        ·
          refine ⟨28647883763294542188140363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76394356702118779168374301 28647883763294542188140363)
          ·
            refine ⟨42971825644941813282210545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28647883763294542188140363 42971825644941813282210545)
            ·
              refine ⟨32228869233706359961657909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42971825644941813282210545 32228869233706359961657909)
              ·
                refine ⟨3021456490659971246405429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32228869233706359961657909 3021456490659971246405429)
                ·
                  refine ⟨283261545999372304350509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021456490659971246405429 283261545999372304350509)
                  ·
                    rfl

theorem cell23_4964849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 5].length) (baseStart_4964849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964849 prefixEnd_4964849 := by exact prefixLift 4964849
  have htrace : WordTrace (prefixWord ++ tailWord_4964849) baseStart_4964849 baseEnd_4964849 := by
    simpa [prefixWord, tailWord_4964849, baseEnd_4964849] using wordTrace_append hprefix tailTrace_4964849
  have hstable : (prefixWord ++ tailWord_4964849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964849).length < 2 ^ (prefixWord ++ tailWord_4964849).sum := by decide
  have hdescent : baseEnd_4964849 < baseStart_4964849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964869 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 2, 5, 2]
def baseStart_4964869 : Nat := 118140960795 + 4964869 * 2 ^ 59
def prefixEnd_4964869 : Nat := 4983230072969 + 3 ^ 40 * 4964869 * 2
def baseEnd_4964869 : Nat := 2549364183607440660904489

theorem tailTrace_4964869 : CollatzResearch.WordTrace tailWord_4964869 prefixEnd_4964869 2549364183607440660904489 := by
  unfold tailWord_4964869
  simp only [CollatzResearch.WordTrace]
  refine ⟨181083649050135019962985661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120722432700090013308657107 181083649050135019962985661)
  ·
    refine ⟨67906368393800632486119623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181083649050135019962985661 67906368393800632486119623)
    ·
      refine ⟨101859552590700948729179435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67906368393800632486119623 101859552590700948729179435)
      ·
        refine ⟨152789328886051423093769153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101859552590700948729179435 152789328886051423093769153)
        ·
          refine ⟨114591996664538567320326865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152789328886051423093769153 114591996664538567320326865)
          ·
            refine ⟨85943997498403925490245149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114591996664538567320326865 85943997498403925490245149)
            ·
              refine ⟨32228999061901472058841931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85943997498403925490245149 32228999061901472058841931)
              ·
                refine ⟨48343498592852208088262897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32228999061901472058841931 48343498592852208088262897)
                ·
                  refine ⟨36257623944639156066197173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48343498592852208088262897 36257623944639156066197173)
                  ·
                    refine ⟨3399152244809920881205985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36257623944639156066197173 3399152244809920881205985)
                    ·
                      refine ⟨2549364183607440660904489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399152244809920881205985 2549364183607440660904489)
                      ·
                        rfl

theorem cell23_4964869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_4964869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964869 prefixEnd_4964869 := by exact prefixLift 4964869
  have htrace : WordTrace (prefixWord ++ tailWord_4964869) baseStart_4964869 baseEnd_4964869 := by
    simpa [prefixWord, tailWord_4964869, baseEnd_4964869] using wordTrace_append hprefix tailTrace_4964869
  have hstable : (prefixWord ++ tailWord_4964869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964869).length < 2 ^ (prefixWord ++ tailWord_4964869).sum := by decide
  have hdescent : baseEnd_4964869 < baseStart_4964869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964877 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_4964877 : Nat := 118140960795 + 4964877 * 2 ^ 59
def prefixEnd_4964877 : Nat := 4983230072969 + 3 ^ 40 * 4964877 * 2
def baseEnd_4964877 : Nat := 2549368291452676629604453

theorem tailTrace_4964877 : CollatzResearch.WordTrace tailWord_4964877 prefixEnd_4964877 2549368291452676629604453 := by
  unfold tailWord_4964877
  simp only [CollatzResearch.WordTrace]
  refine ⟨181083940834106037329276885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120722627222737358219517923 181083940834106037329276885)
  ·
    refine ⟨4244154863299360249904927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 181083940834106037329276885 4244154863299360249904927)
    ·
      refine ⟨6366232294949040374857391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4244154863299360249904927 6366232294949040374857391)
      ·
        refine ⟨9549348442423560562286087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6366232294949040374857391 9549348442423560562286087)
        ·
          refine ⟨14324022663635340843429131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9549348442423560562286087 14324022663635340843429131)
          ·
            refine ⟨21486033995453011265143697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14324022663635340843429131 21486033995453011265143697)
            ·
              refine ⟨16114525496589758448857773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21486033995453011265143697 16114525496589758448857773)
              ·
                refine ⟨6042947061221159418321665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16114525496589758448857773 6042947061221159418321665)
                ·
                  refine ⟨4532210295915869563741249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6042947061221159418321665 4532210295915869563741249)
                  ·
                    refine ⟨3399157721936902172805937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4532210295915869563741249 3399157721936902172805937)
                    ·
                      refine ⟨2549368291452676629604453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399157721936902172805937 2549368291452676629604453)
                      ·
                        rfl

theorem cell23_4964877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_4964877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964877 prefixEnd_4964877 := by exact prefixLift 4964877
  have htrace : WordTrace (prefixWord ++ tailWord_4964877) baseStart_4964877 baseEnd_4964877 := by
    simpa [prefixWord, tailWord_4964877, baseEnd_4964877] using wordTrace_append hprefix tailTrace_4964877
  have hstable : (prefixWord ++ tailWord_4964877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964877).length < 2 ^ (prefixWord ++ tailWord_4964877).sum := by decide
  have hdescent : baseEnd_4964877 < baseStart_4964877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964899 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 4]
def baseStart_4964899 : Nat := 118140960795 + 4964899 * 2 ^ 59
def prefixEnd_4964899 : Nat := 4983230072969 + 3 ^ 40 * 4964899 * 2
def baseEnd_4964899 : Nat := 2549379588027075543529351

theorem tailTrace_4964899 : CollatzResearch.WordTrace tailWord_4964899 prefixEnd_4964899 2549379588027075543529351 := by
  unfold tailWord_4964899
  simp only [CollatzResearch.WordTrace]
  refine ⟨181084743240026335086577751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120723162160017556724385167 181084743240026335086577751)
  ·
    refine ⟨271627114860039502629866627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181084743240026335086577751 271627114860039502629866627)
    ·
      refine ⟨407440672290059253944799941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271627114860039502629866627 407440672290059253944799941)
      ·
        refine ⟨76395126054386110114649989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407440672290059253944799941 76395126054386110114649989)
        ·
          refine ⟨14324086135197395646496873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76395126054386110114649989 14324086135197395646496873)
          ·
            refine ⟨10743064601398046734872655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14324086135197395646496873 10743064601398046734872655)
            ·
              refine ⟨16114596902097070102308983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10743064601398046734872655 16114596902097070102308983)
              ·
                refine ⟨24171895353145605153463475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16114596902097070102308983 24171895353145605153463475)
                ·
                  refine ⟨36257843029718407730195213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24171895353145605153463475 36257843029718407730195213)
                  ·
                    refine ⟨13596691136144402898823205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36257843029718407730195213 13596691136144402898823205)
                    ·
                      refine ⟨2549379588027075543529351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13596691136144402898823205 2549379588027075543529351)
                      ·
                        rfl

theorem cell23_4964899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_4964899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964899 prefixEnd_4964899 := by exact prefixLift 4964899
  have htrace : WordTrace (prefixWord ++ tailWord_4964899) baseStart_4964899 baseEnd_4964899 := by
    simpa [prefixWord, tailWord_4964899, baseEnd_4964899] using wordTrace_append hprefix tailTrace_4964899
  have hstable : (prefixWord ++ tailWord_4964899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964899).length < 2 ^ (prefixWord ++ tailWord_4964899).sum := by decide
  have hdescent : baseEnd_4964899 < baseStart_4964899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964912 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_4964912 : Nat := 118140960795 + 4964912 * 2 ^ 59
def prefixEnd_4964912 : Nat := 4983230072969 + 3 ^ 40 * 4964912 * 2
def baseEnd_4964912 : Nat := 2549386263275583992666791

theorem tailTrace_4964912 : CollatzResearch.WordTrace tailWord_4964912 prefixEnd_4964912 2549386263275583992666791 := by
  unfold tailWord_4964912
  simp only [CollatzResearch.WordTrace]
  refine ⟨90542608694489619153400495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120723478259319492204533993 90542608694489619153400495)
  ·
    refine ⟨135813913041734428730100743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90542608694489619153400495 135813913041734428730100743)
    ·
      refine ⟨203720869562601643095151115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135813913041734428730100743 203720869562601643095151115)
      ·
        refine ⟨305581304343902464642726673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203720869562601643095151115 305581304343902464642726673)
        ·
          refine ⟨229185978257926848482045005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305581304343902464642726673 229185978257926848482045005)
          ·
            refine ⟨85944741846722568180766877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229185978257926848482045005 85944741846722568180766877)
            ·
              refine ⟨32229278192520963067787579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85944741846722568180766877 32229278192520963067787579)
              ·
                refine ⟨48343917288781444601681369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32229278192520963067787579 48343917288781444601681369)
                ·
                  refine ⟨36257937966586083451261027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48343917288781444601681369 36257937966586083451261027)
                  ·
                    refine ⟨54386906949879125176891541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36257937966586083451261027 54386906949879125176891541)
                    ·
                      refine ⟨2549386263275583992666791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54386906949879125176891541 2549386263275583992666791)
                      ·
                        rfl

theorem cell23_4964912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_4964912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964912 prefixEnd_4964912 := by exact prefixLift 4964912
  have htrace : WordTrace (prefixWord ++ tailWord_4964912) baseStart_4964912 baseEnd_4964912 := by
    simpa [prefixWord, tailWord_4964912, baseEnd_4964912] using wordTrace_append hprefix tailTrace_4964912
  have hstable : (prefixWord ++ tailWord_4964912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964912).length < 2 ^ (prefixWord ++ tailWord_4964912).sum := by decide
  have hdescent : baseEnd_4964912 < baseStart_4964912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964919 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_4964919 : Nat := 118140960795 + 4964919 * 2 ^ 59
def prefixEnd_4964919 : Nat := 4983230072969 + 3 ^ 40 * 4964919 * 2
def baseEnd_4964919 : Nat := 2549389857640165465279259

theorem tailTrace_4964919 : CollatzResearch.WordTrace tailWord_4964919 prefixEnd_4964919 2549389857640165465279259 := by
  unfold tailWord_4964919
  simp only [CollatzResearch.WordTrace]
  refine ⟨181085472699953878502305811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120723648466635919001537207 181085472699953878502305811)
  ·
    refine ⟨271628209049930817753458717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181085472699953878502305811 271628209049930817753458717)
    ·
      refine ⟨101860578393724056657547019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271628209049930817753458717 101860578393724056657547019)
      ·
        refine ⟨152790867590586084986320529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101860578393724056657547019 152790867590586084986320529)
        ·
          refine ⟨114593150692939563739740397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152790867590586084986320529 114593150692939563739740397)
          ·
            refine ⟨42972431509852336402402649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114593150692939563739740397 42972431509852336402402649)
            ·
              refine ⟨32229323632389252301801987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42972431509852336402402649 32229323632389252301801987)
              ·
                refine ⟨48343985448583878452702981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32229323632389252301801987 48343985448583878452702981)
                ·
                  refine ⟨9064497271609477209881809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48343985448583878452702981 9064497271609477209881809)
                  ·
                    refine ⟨6798372953707107907411357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9064497271609477209881809 6798372953707107907411357)
                    ·
                      refine ⟨2549389857640165465279259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6798372953707107907411357 2549389857640165465279259)
                      ·
                        rfl

theorem cell23_4964919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_4964919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964919 prefixEnd_4964919 := by exact prefixLift 4964919
  have htrace : WordTrace (prefixWord ++ tailWord_4964919) baseStart_4964919 baseEnd_4964919 := by
    simpa [prefixWord, tailWord_4964919, baseEnd_4964919] using wordTrace_append hprefix tailTrace_4964919
  have hstable : (prefixWord ++ tailWord_4964919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964919).length < 2 ^ (prefixWord ++ tailWord_4964919).sum := by decide
  have hdescent : baseEnd_4964919 < baseStart_4964919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964983 : List Nat := [1, 1, 3, 1, 1, 3, 2, 6, 1, 1, 3]
def baseStart_4964983 : Nat := 118140960795 + 4964983 * 2 ^ 59
def prefixEnd_4964983 : Nat := 4983230072969 + 3 ^ 40 * 4964983 * 2
def baseEnd_4964983 : Nat := 2549422720402053214878965

theorem tailTrace_4964983 : CollatzResearch.WordTrace tailWord_4964983 prefixEnd_4964983 2549422720402053214878965 := by
  unfold tailWord_4964983
  simp only [CollatzResearch.WordTrace]
  refine ⟨181087806971722017432635603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120725204647814678288423735 181087806971722017432635603)
  ·
    refine ⟨271631710457583026148953405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181087806971722017432635603 271631710457583026148953405)
    ·
      refine ⟨101861891421593634805857527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271631710457583026148953405 101861891421593634805857527)
      ·
        refine ⟨152792837132390452208786291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101861891421593634805857527 152792837132390452208786291)
        ·
          refine ⟨229189255698585678313179437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152792837132390452208786291 229189255698585678313179437)
          ·
            refine ⟨85945970886969629367442289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229189255698585678313179437 85945970886969629367442289)
            ·
              refine ⟨64459478165227222025581717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85945970886969629367442289 64459478165227222025581717)
              ·
                refine ⟨3021538038995026032449143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64459478165227222025581717 3021538038995026032449143)
                ·
                  refine ⟨4532307058492539048673715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021538038995026032449143 4532307058492539048673715)
                  ·
                    refine ⟨6798460587738808573010573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4532307058492539048673715 6798460587738808573010573)
                    ·
                      refine ⟨2549422720402053214878965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6798460587738808573010573 2549422720402053214878965)
                      ·
                        rfl

theorem cell23_4964983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_4964983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964983 prefixEnd_4964983 := by exact prefixLift 4964983
  have htrace : WordTrace (prefixWord ++ tailWord_4964983) baseStart_4964983 baseEnd_4964983 := by
    simpa [prefixWord, tailWord_4964983, baseEnd_4964983] using wordTrace_append hprefix tailTrace_4964983
  have hstable : (prefixWord ++ tailWord_4964983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964983).length < 2 ^ (prefixWord ++ tailWord_4964983).sum := by decide
  have hdescent : baseEnd_4964983 < baseStart_4964983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4964999 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 1, 6]
def baseStart_4964999 : Nat := 118140960795 + 4964999 * 2 ^ 59
def prefixEnd_4964999 : Nat := 4983230072969 + 3 ^ 40 * 4964999 * 2
def baseEnd_4964999 : Nat := 849810312030841717426297

theorem tailTrace_4964999 : CollatzResearch.WordTrace tailWord_4964999 prefixEnd_4964999 849810312030841717426297 := by
  unfold tailWord_4964999
  simp only [CollatzResearch.WordTrace]
  refine ⟨181088390539664052165218051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120725593693109368110145367 181088390539664052165218051)
  ·
    refine ⟨271632585809496078247827077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181088390539664052165218051 271632585809496078247827077)
    ·
      refine ⟨50931109839280514671467577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271632585809496078247827077 50931109839280514671467577)
      ·
        refine ⟨38198332379460386003600683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50931109839280514671467577 38198332379460386003600683)
        ·
          refine ⟨57297498569190579005401025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38198332379460386003600683 57297498569190579005401025)
          ·
            refine ⟨42973123926892934254050769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57297498569190579005401025 42973123926892934254050769)
            ·
              refine ⟨32229842945169700690538077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42973123926892934254050769 32229842945169700690538077)
              ·
                refine ⟨12086191104438637758951779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32229842945169700690538077 12086191104438637758951779)
                ·
                  refine ⟨18129286656657956638427669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12086191104438637758951779 18129286656657956638427669)
                  ·
                    refine ⟨849810312030841717426297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18129286656657956638427669 849810312030841717426297)
                    ·
                      rfl

theorem cell23_4964999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_4964999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4964999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4964999 prefixEnd_4964999 := by exact prefixLift 4964999
  have htrace : WordTrace (prefixWord ++ tailWord_4964999) baseStart_4964999 baseEnd_4964999 := by
    simpa [prefixWord, tailWord_4964999, baseEnd_4964999] using wordTrace_append hprefix tailTrace_4964999
  have hstable : (prefixWord ++ tailWord_4964999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4964999).length < 2 ^ (prefixWord ++ tailWord_4964999).sum := by decide
  have hdescent : baseEnd_4964999 < baseStart_4964999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4964999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965006 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4965006 : Nat := 118140960795 + 4965006 * 2 ^ 59
def prefixEnd_4965006 : Nat := 4983230072969 + 3 ^ 40 * 4965006 * 2
def baseEnd_4965006 : Nat := 2549434530457106624891359

theorem tailTrace_4965006 : CollatzResearch.WordTrace tailWord_4965006 prefixEnd_4965006 2549434530457106624891359 := by
  unfold tailWord_4965006
  simp only [CollatzResearch.WordTrace]
  refine ⟨22636080731329836545090359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120725763900425794907148581 22636080731329836545090359)
  ·
    refine ⟨33954121096994754817635539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22636080731329836545090359 33954121096994754817635539)
    ·
      refine ⟨50931181645492132226453309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33954121096994754817635539 50931181645492132226453309)
      ·
        refine ⟨19099193117059549584919991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50931181645492132226453309 19099193117059549584919991)
        ·
          refine ⟨28648789675589324377379987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19099193117059549584919991 28648789675589324377379987)
          ·
            refine ⟨42973184513383986566069981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28648789675589324377379987 42973184513383986566069981)
            ·
              refine ⟨16114944192518994962276243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42973184513383986566069981 16114944192518994962276243)
              ·
                refine ⟨24172416288778492443414365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16114944192518994962276243 24172416288778492443414365)
                ·
                  refine ⟨9064656108291934666280387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24172416288778492443414365 9064656108291934666280387)
                  ·
                    refine ⟨13596984162437901999420581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9064656108291934666280387 13596984162437901999420581)
                    ·
                      refine ⟨2549434530457106624891359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13596984162437901999420581 2549434530457106624891359)
                      ·
                        rfl

theorem cell23_4965006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4965006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965006 prefixEnd_4965006 := by exact prefixLift 4965006
  have htrace : WordTrace (prefixWord ++ tailWord_4965006) baseStart_4965006 baseEnd_4965006 := by
    simpa [prefixWord, tailWord_4965006, baseEnd_4965006] using wordTrace_append hprefix tailTrace_4965006
  have hstable : (prefixWord ++ tailWord_4965006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965006).length < 2 ^ (prefixWord ++ tailWord_4965006).sum := by decide
  have hdescent : baseEnd_4965006 < baseStart_4965006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965010 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_4965010 : Nat := 118140960795 + 4965010 * 2 ^ 59
def prefixEnd_4965010 : Nat := 4983230072969 + 3 ^ 40 * 4965010 * 2
def baseEnd_4965010 : Nat := 2549436584379724609241341

theorem tailTrace_4965010 : CollatzResearch.WordTrace tailWord_4965010 prefixEnd_4965010 2549436584379724609241341 := by
  unfold tailWord_4965010
  simp only [CollatzResearch.WordTrace]
  refine ⟨45272197935656050260967121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120725861161749467362578989 45272197935656050260967121)
  ·
    refine ⟨33954148451742037695725341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45272197935656050260967121 33954148451742037695725341)
    ·
      refine ⟨12732805669403264135897003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33954148451742037695725341 12732805669403264135897003)
      ·
        refine ⟨19099208504104896203845505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12732805669403264135897003 19099208504104896203845505)
        ·
          refine ⟨14324406378078672152884129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19099208504104896203845505 14324406378078672152884129)
          ·
            refine ⟨10743304783559004114663097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14324406378078672152884129 10743304783559004114663097)
            ·
              refine ⟨8057478587669253085997323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10743304783559004114663097 8057478587669253085997323)
              ·
                refine ⟨12086217881503879628995985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8057478587669253085997323 12086217881503879628995985)
                ·
                  refine ⟨9064663411127909721746989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12086217881503879628995985 9064663411127909721746989)
                  ·
                    refine ⟨3399248779172966145655121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9064663411127909721746989 3399248779172966145655121)
                    ·
                      refine ⟨2549436584379724609241341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399248779172966145655121 2549436584379724609241341)
                      ·
                        rfl

theorem cell23_4965010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_4965010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965010 prefixEnd_4965010 := by exact prefixLift 4965010
  have htrace : WordTrace (prefixWord ++ tailWord_4965010) baseStart_4965010 baseEnd_4965010 := by
    simpa [prefixWord, tailWord_4965010, baseEnd_4965010] using wordTrace_append hprefix tailTrace_4965010
  have hstable : (prefixWord ++ tailWord_4965010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965010).length < 2 ^ (prefixWord ++ tailWord_4965010).sum := by decide
  have hdescent : baseEnd_4965010 < baseStart_4965010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965034 : List Nat := [3, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_4965034 : Nat := 118140960795 + 4965034 * 2 ^ 59
def prefixEnd_4965034 : Nat := 4983230072969 + 3 ^ 40 * 4965034 * 2
def baseEnd_4965034 : Nat := 2549448907915432515341231

theorem tailTrace_4965034 : CollatzResearch.WordTrace tailWord_4965034 prefixEnd_4965034 2549448907915432515341231 := by
  unfold tailWord_4965034
  simp only [CollatzResearch.WordTrace]
  refine ⟨45272416773634313285685539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120726444729691502095161437 45272416773634313285685539)
  ·
    refine ⟨67908625160451469928528309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45272416773634313285685539 67908625160451469928528309)
    ·
      refine ⟨6366433608792325305799529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67908625160451469928528309 6366433608792325305799529)
      ·
        refine ⟨4774825206594243979349647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6366433608792325305799529 4774825206594243979349647)
        ·
          refine ⟨7162237809891365969024471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4774825206594243979349647 7162237809891365969024471)
          ·
            refine ⟨10743356714837048953536707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162237809891365969024471 10743356714837048953536707)
            ·
              refine ⟨16115035072255573430305061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10743356714837048953536707 16115035072255573430305061)
              ·
                refine ⟨3021569076047920018182199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16115035072255573430305061 3021569076047920018182199)
                ·
                  refine ⟨4532353614071880027273299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021569076047920018182199 4532353614071880027273299)
                  ·
                    refine ⟨6798530421107820040909949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4532353614071880027273299 6798530421107820040909949)
                    ·
                      refine ⟨2549448907915432515341231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6798530421107820040909949 2549448907915432515341231)
                      ·
                        rfl

theorem cell23_4965034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_4965034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965034 prefixEnd_4965034 := by exact prefixLift 4965034
  have htrace : WordTrace (prefixWord ++ tailWord_4965034) baseStart_4965034 baseEnd_4965034 := by
    simpa [prefixWord, tailWord_4965034, baseEnd_4965034] using wordTrace_append hprefix tailTrace_4965034
  have hstable : (prefixWord ++ tailWord_4965034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965034).length < 2 ^ (prefixWord ++ tailWord_4965034).sum := by decide
  have hdescent : baseEnd_4965034 < baseStart_4965034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965056 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 3]
def baseStart_4965056 : Nat := 118140960795 + 4965056 * 2 ^ 59
def prefixEnd_4965056 : Nat := 4983230072969 + 3 ^ 40 * 4965056 * 2
def baseEnd_4965056 : Nat := 2549460204489831429266129

theorem tailTrace_4965056 : CollatzResearch.WordTrace tailWord_4965056 prefixEnd_4965056 2549460204489831429266129 := by
  unfold tailWord_4965056
  simp only [CollatzResearch.WordTrace]
  refine ⟨90545234750228775450021511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120726979666971700600028681 90545234750228775450021511)
  ·
    refine ⟨135817852125343163175032267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90545234750228775450021511 135817852125343163175032267)
    ·
      refine ⟨203726778188014744762548401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135817852125343163175032267 203726778188014744762548401)
      ·
        refine ⟨152795083641011058571911301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203726778188014744762548401 152795083641011058571911301)
        ·
          refine ⟨28649078182689573482233369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152795083641011058571911301 28649078182689573482233369)
          ·
            refine ⟨21486808637017180111675027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28649078182689573482233369 21486808637017180111675027)
            ·
              refine ⟨32230212955525770167512541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21486808637017180111675027 32230212955525770167512541)
              ·
                refine ⟨12086329858322163812817203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32230212955525770167512541 12086329858322163812817203)
                ·
                  refine ⟨18129494787483245719225805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12086329858322163812817203 18129494787483245719225805)
                  ·
                    refine ⟨6798560545306217144709677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18129494787483245719225805 6798560545306217144709677)
                    ·
                      refine ⟨2549460204489831429266129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6798560545306217144709677 2549460204489831429266129)
                      ·
                        rfl

theorem cell23_4965056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_4965056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965056 prefixEnd_4965056 := by exact prefixLift 4965056
  have htrace : WordTrace (prefixWord ++ tailWord_4965056) baseStart_4965056 baseEnd_4965056 := by
    simpa [prefixWord, tailWord_4965056, baseEnd_4965056] using wordTrace_append hprefix tailTrace_4965056
  have hstable : (prefixWord ++ tailWord_4965056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965056).length < 2 ^ (prefixWord ++ tailWord_4965056).sum := by decide
  have hdescent : baseEnd_4965056 < baseStart_4965056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965074 : List Nat := [3, 2, 2, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_4965074 : Nat := 118140960795 + 4965074 * 2 ^ 59
def prefixEnd_4965074 : Nat := 4983230072969 + 3 ^ 40 * 4965074 * 2
def baseEnd_4965074 : Nat := 2549469447141612358841047

theorem tailTrace_4965074 : CollatzResearch.WordTrace tailWord_4965074 prefixEnd_4965074 2549469447141612358841047 := by
  unfold tailWord_4965074
  simp only [CollatzResearch.WordTrace]
  refine ⟨45272781503598084993549569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120727417342928226649465517 45272781503598084993549569)
  ·
    refine ⟨33954586127698563745162177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45272781503598084993549569 33954586127698563745162177)
    ·
      refine ⟨25465939595773922808871633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33954586127698563745162177 25465939595773922808871633)
      ·
        refine ⟨19099454696830442106653725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25465939595773922808871633 19099454696830442106653725)
        ·
          refine ⟨7162295511311415789995147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19099454696830442106653725 7162295511311415789995147)
          ·
            refine ⟨10743443266967123684992721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162295511311415789995147 10743443266967123684992721)
            ·
              refine ⟨8057582450225342763744541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10743443266967123684992721 8057582450225342763744541)
              ·
                refine ⟨3021593418834503536404203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8057582450225342763744541 3021593418834503536404203)
                ·
                  refine ⟨4532390128251755304606305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021593418834503536404203 4532390128251755304606305)
                  ·
                    refine ⟨3399292596188816478454729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4532390128251755304606305 3399292596188816478454729)
                    ·
                      refine ⟨2549469447141612358841047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399292596188816478454729 2549469447141612358841047)
                      ·
                        rfl

theorem cell23_4965074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_4965074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965074 prefixEnd_4965074 := by exact prefixLift 4965074
  have htrace : WordTrace (prefixWord ++ tailWord_4965074) baseStart_4965074 baseEnd_4965074 := by
    simpa [prefixWord, tailWord_4965074, baseEnd_4965074] using wordTrace_append hprefix tailTrace_4965074
  have hstable : (prefixWord ++ tailWord_4965074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965074).length < 2 ^ (prefixWord ++ tailWord_4965074).sum := by decide
  have hdescent : baseEnd_4965074 < baseStart_4965074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965099 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 5]
def baseStart_4965099 : Nat := 118140960795 + 4965099 * 2 ^ 59
def prefixEnd_4965099 : Nat := 4983230072969 + 3 ^ 40 * 4965099 * 2
def baseEnd_4965099 : Nat := 2549482284157974761028431

theorem tailTrace_4965099 : CollatzResearch.WordTrace tailWord_4965099 prefixEnd_4965099 2549482284157974761028431 := by
  unfold tailWord_4965099
  simp only [CollatzResearch.WordTrace]
  refine ⟨181092037839301769243858351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120728025226201179495905567 181092037839301769243858351)
  ·
    refine ⟨271638056758952653865787527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181092037839301769243858351 271638056758952653865787527)
    ·
      refine ⟨407457085138428980798681291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271638056758952653865787527 407457085138428980798681291)
      ·
        refine ⟨611185627707643471198021937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407457085138428980798681291 611185627707643471198021937)
        ·
          refine ⟨458389220780732603398516453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611185627707643471198021937 458389220780732603398516453)
          ·
            refine ⟨85947978896387363137221835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 458389220780732603398516453 85947978896387363137221835)
            ·
              refine ⟨128921968344581044705832753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85947978896387363137221835 128921968344581044705832753)
              ·
                refine ⟨96691476258435783529374565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128921968344581044705832753 96691476258435783529374565)
                ·
                  refine ⟨18129651798456709411757731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96691476258435783529374565 18129651798456709411757731)
                  ·
                    refine ⟨27194477697685064117636597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18129651798456709411757731 27194477697685064117636597)
                    ·
                      refine ⟨2549482284157974761028431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27194477697685064117636597 2549482284157974761028431)
                      ·
                        rfl

theorem cell23_4965099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_4965099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965099 prefixEnd_4965099 := by exact prefixLift 4965099
  have htrace : WordTrace (prefixWord ++ tailWord_4965099) baseStart_4965099 baseEnd_4965099 := by
    simpa [prefixWord, tailWord_4965099, baseEnd_4965099] using wordTrace_append hprefix tailTrace_4965099
  have hstable : (prefixWord ++ tailWord_4965099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965099).length < 2 ^ (prefixWord ++ tailWord_4965099).sum := by decide
  have hdescent : baseEnd_4965099 < baseStart_4965099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965106 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_4965106 : Nat := 118140960795 + 4965106 * 2 ^ 59
def prefixEnd_4965106 : Nat := 4983230072969 + 3 ^ 40 * 4965106 * 2
def baseEnd_4965106 : Nat := 849828626174185411213633

theorem tailTrace_4965106 : CollatzResearch.WordTrace tailWord_4965106 prefixEnd_4965106 849828626174185411213633 := by
  unfold tailWord_4965106
  simp only [CollatzResearch.WordTrace]
  refine ⟨45273073287569102359840793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120728195433517606292908781 45273073287569102359840793)
  ·
    refine ⟨33954804965676826769880595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45273073287569102359840793 33954804965676826769880595)
    ·
      refine ⟨50932207448515240154820893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33954804965676826769880595 50932207448515240154820893)
      ·
        refine ⟨19099577793193215058057835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50932207448515240154820893 19099577793193215058057835)
        ·
          refine ⟨28649366689789822587086753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19099577793193215058057835 28649366689789822587086753)
          ·
            refine ⟨21487025017342366940315065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28649366689789822587086753 21487025017342366940315065)
            ·
              refine ⟨16115268763006775205236299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21487025017342366940315065 16115268763006775205236299)
              ·
                refine ⟨24172903144510162807854449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16115268763006775205236299 24172903144510162807854449)
                ·
                  refine ⟨18129677358382622105890837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24172903144510162807854449 18129677358382622105890837)
                  ·
                    refine ⟨849828626174185411213633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18129677358382622105890837 849828626174185411213633)
                    ·
                      rfl

theorem cell23_4965106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_4965106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965106 prefixEnd_4965106 := by exact prefixLift 4965106
  have htrace : WordTrace (prefixWord ++ tailWord_4965106) baseStart_4965106 baseEnd_4965106 := by
    simpa [prefixWord, tailWord_4965106, baseEnd_4965106] using wordTrace_append hprefix tailTrace_4965106
  have hstable : (prefixWord ++ tailWord_4965106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965106).length < 2 ^ (prefixWord ++ tailWord_4965106).sum := by decide
  have hdescent : baseEnd_4965106 < baseStart_4965106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965183 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 2, 5]
def baseStart_4965183 : Nat := 118140960795 + 4965183 * 2 ^ 59
def prefixEnd_4965183 : Nat := 4983230072969 + 3 ^ 40 * 4965183 * 2
def baseEnd_4965183 : Nat := 849841805510984144126015

theorem tailTrace_4965183 : CollatzResearch.WordTrace tailWord_4965183 prefixEnd_4965183 849841805510984144126015 := by
  unfold tailWord_4965183
  simp only [CollatzResearch.WordTrace]
  refine ⟨181095101570997451589916203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120730067713998301059944135 181095101570997451589916203)
  ·
    refine ⟨271642652356496177384874305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181095101570997451589916203 271642652356496177384874305)
    ·
      refine ⟨203731989267372133038655729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271642652356496177384874305 203731989267372133038655729)
      ·
        refine ⟨152798991950529099778991797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203731989267372133038655729 152798991950529099778991797)
        ·
          refine ⟨14324905495362103104280481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152798991950529099778991797 14324905495362103104280481)
          ·
            refine ⟨10743679121521577328210361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14324905495362103104280481 10743679121521577328210361)
            ·
              refine ⟨8057759341141182996157771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10743679121521577328210361 8057759341141182996157771)
              ·
                refine ⟨12086639011711774494236657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8057759341141182996157771 12086639011711774494236657)
                ·
                  refine ⟨9064979258783830870677493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12086639011711774494236657 9064979258783830870677493)
                  ·
                    refine ⟨849841805510984144126015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9064979258783830870677493 849841805510984144126015)
                    ·
                      rfl

theorem cell23_4965183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_4965183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965183 prefixEnd_4965183 := by exact prefixLift 4965183
  have htrace : WordTrace (prefixWord ++ tailWord_4965183) baseStart_4965183 baseEnd_4965183 := by
    simpa [prefixWord, tailWord_4965183, baseEnd_4965183] using wordTrace_append hprefix tailTrace_4965183
  have hstable : (prefixWord ++ tailWord_4965183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965183).length < 2 ^ (prefixWord ++ tailWord_4965183).sum := by decide
  have hdescent : baseEnd_4965183 < baseStart_4965183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965204 : List Nat := [2, 4, 1, 1, 5, 1, 2, 2, 5]
def baseStart_4965204 : Nat := 118140960795 + 4965204 * 2 ^ 59
def prefixEnd_4965204 : Nat := 4983230072969 + 3 ^ 40 * 4965204 * 2
def baseEnd_4965204 : Nat := 283281799958521872246161

theorem tailTrace_4965204 : CollatzResearch.WordTrace tailWord_4965204 prefixEnd_4965204 283281799958521872246161 := by
  unfold tailWord_4965204
  simp only [CollatzResearch.WordTrace]
  refine ⟨90547933751960686088215333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120730578335947581450953777 90547933751960686088215333)
  ·
    refine ⟨16977737578492628641540375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90547933751960686088215333 16977737578492628641540375)
    ·
      refine ⟨25466606367738942962310563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16977737578492628641540375 25466606367738942962310563)
      ·
        refine ⟨38199909551608414443465845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25466606367738942962310563 38199909551608414443465845)
        ·
          refine ⟨3581241520463288854074923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38199909551608414443465845 3581241520463288854074923)
          ·
            refine ⟨5371862280694933281112385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581241520463288854074923 5371862280694933281112385)
            ·
              refine ⟨4028896710521199960834289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5371862280694933281112385 4028896710521199960834289)
              ·
                refine ⟨3021672532890899970625717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4028896710521199960834289 3021672532890899970625717)
                ·
                  refine ⟨283281799958521872246161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021672532890899970625717 283281799958521872246161)
                  ·
                    rfl

theorem cell23_4965204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_4965204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965204 prefixEnd_4965204 := by exact prefixLift 4965204
  have htrace : WordTrace (prefixWord ++ tailWord_4965204) baseStart_4965204 baseEnd_4965204 := by
    simpa [prefixWord, tailWord_4965204, baseEnd_4965204] using wordTrace_append hprefix tailTrace_4965204
  have hstable : (prefixWord ++ tailWord_4965204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965204).length < 2 ^ (prefixWord ++ tailWord_4965204).sum := by decide
  have hdescent : baseEnd_4965204 < baseStart_4965204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965220 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_4965220 : Nat := 118140960795 + 4965220 * 2 ^ 59
def prefixEnd_4965220 : Nat := 4983230072969 + 3 ^ 40 * 4965220 * 2
def baseEnd_4965220 : Nat := 2549544415317168787615375

theorem tailTrace_4965220 : CollatzResearch.WordTrace tailWord_4965220 prefixEnd_4965220 2549544415317168787615375 := by
  unfold tailWord_4965220
  simp only [CollatzResearch.WordTrace]
  refine ⟨90548225535931703454506557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120730967381242271272675409 90548225535931703454506557)
  ·
    refine ⟨33955584575974388795439959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90548225535931703454506557 33955584575974388795439959)
    ·
      refine ⟨50933376863961583193159939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33955584575974388795439959 50933376863961583193159939)
      ·
        refine ⟨76400065295942374789739909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50933376863961583193159939 76400065295942374789739909)
        ·
          refine ⟨14325012242989195273076233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76400065295942374789739909 14325012242989195273076233)
          ·
            refine ⟨10743759182241896454807175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14325012242989195273076233 10743759182241896454807175)
            ·
              refine ⟨16115638773362844682210763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10743759182241896454807175 16115638773362844682210763)
              ·
                refine ⟨24173458160044267023316145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16115638773362844682210763 24173458160044267023316145)
                ·
                  refine ⟨18130093620033200267487109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24173458160044267023316145 18130093620033200267487109)
                  ·
                    refine ⟨3399392553756225050153833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18130093620033200267487109 3399392553756225050153833)
                    ·
                      refine ⟨2549544415317168787615375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399392553756225050153833 2549544415317168787615375)
                      ·
                        rfl

theorem cell23_4965220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_4965220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965220 prefixEnd_4965220 := by exact prefixLift 4965220
  have htrace : WordTrace (prefixWord ++ tailWord_4965220) baseStart_4965220 baseEnd_4965220 := by
    simpa [prefixWord, tailWord_4965220, baseEnd_4965220] using wordTrace_append hprefix tailTrace_4965220
  have hstable : (prefixWord ++ tailWord_4965220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965220).length < 2 ^ (prefixWord ++ tailWord_4965220).sum := by decide
  have hdescent : baseEnd_4965220 < baseStart_4965220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965303 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 4, 4]
def baseStart_4965303 : Nat := 118140960795 + 4965303 * 2 ^ 59
def prefixEnd_4965303 : Nat := 4983230072969 + 3 ^ 40 * 4965303 * 2
def baseEnd_4965303 : Nat := 849862344737163987625831

theorem tailTrace_4965303 : CollatzResearch.WordTrace tailWord_4965303 prefixEnd_4965303 849862344737163987625831 := by
  unfold tailWord_4965303
  simp only [CollatzResearch.WordTrace]
  refine ⟨181099478330562712084284563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120732985553708474722856375 181099478330562712084284563)
  ·
    refine ⟨271649217495844068126426845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181099478330562712084284563 271649217495844068126426845)
    ·
      refine ⟨101868456560941525547410067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271649217495844068126426845 101868456560941525547410067)
      ·
        refine ⟨152802684841412288321115101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101868456560941525547410067 152802684841412288321115101)
        ·
          refine ⟨57301006815529608120418163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152802684841412288321115101 57301006815529608120418163)
          ·
            refine ⟨85951510223294412180627245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57301006815529608120418163 85951510223294412180627245)
            ·
              refine ⟨32231816333735404567735217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85951510223294412180627245 32231816333735404567735217)
              ·
                refine ⟨24173862250301553425801413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32231816333735404567735217 24173862250301553425801413)
                ·
                  refine ⟨4532599171931541267337765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24173862250301553425801413 4532599171931541267337765)
                  ·
                    refine ⟨849862344737163987625831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4532599171931541267337765 849862344737163987625831)
                    ·
                      rfl

theorem cell23_4965303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_4965303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965303 prefixEnd_4965303 := by exact prefixLift 4965303
  have htrace : WordTrace (prefixWord ++ tailWord_4965303) baseStart_4965303 baseEnd_4965303 := by
    simpa [prefixWord, tailWord_4965303, baseEnd_4965303] using wordTrace_append hprefix tailTrace_4965303
  have hstable : (prefixWord ++ tailWord_4965303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965303).length < 2 ^ (prefixWord ++ tailWord_4965303).sum := by decide
  have hdescent : baseEnd_4965303 < baseStart_4965303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965304 : List Nat := [2, 1, 2, 1, 2, 6, 1, 3, 1, 1, 3]
def baseStart_4965304 : Nat := 118140960795 + 4965304 * 2 ^ 59
def prefixEnd_4965304 : Nat := 4983230072969 + 3 ^ 40 * 4965304 * 2
def baseEnd_4965304 : Nat := 2549587547692146458964989

theorem tailTrace_4965304 : CollatzResearch.WordTrace tailWord_4965304 prefixEnd_4965304 2549587547692146458964989 := by
  unfold tailWord_4965304
  simp only [CollatzResearch.WordTrace]
  refine ⟨90549757401779544627535483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120733009869039392836713977 90549757401779544627535483)
  ·
    refine ⟨135824636102669316941303225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90549757401779544627535483 135824636102669316941303225)
    ·
      refine ⟨101868477077001987705977419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135824636102669316941303225 101868477077001987705977419)
      ·
        refine ⟨152802715615502981558966129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101868477077001987705977419 152802715615502981558966129)
        ·
          refine ⟨114602036711627236169224597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152802715615502981558966129 114602036711627236169224597)
          ·
            refine ⟨5371970470857526695432403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114602036711627236169224597 5371970470857526695432403)
            ·
              refine ⟨8057955706286290043148605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5371970470857526695432403 8057955706286290043148605)
              ·
                refine ⟨3021733389857358766180727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8057955706286290043148605 3021733389857358766180727)
                ·
                  refine ⟨4532600084786038149271091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021733389857358766180727 4532600084786038149271091)
                  ·
                    refine ⟨6798900127179057223906637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4532600084786038149271091 6798900127179057223906637)
                    ·
                      refine ⟨2549587547692146458964989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6798900127179057223906637 2549587547692146458964989)
                      ·
                        rfl

theorem cell23_4965304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_4965304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965304 prefixEnd_4965304 := by exact prefixLift 4965304
  have htrace : WordTrace (prefixWord ++ tailWord_4965304) baseStart_4965304 baseEnd_4965304 := by
    simpa [prefixWord, tailWord_4965304, baseEnd_4965304] using wordTrace_append hprefix tailTrace_4965304
  have hstable : (prefixWord ++ tailWord_4965304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965304).length < 2 ^ (prefixWord ++ tailWord_4965304).sum := by decide
  have hdescent : baseEnd_4965304 < baseStart_4965304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965310 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_4965310 : Nat := 118140960795 + 4965310 * 2 ^ 59
def prefixEnd_4965310 : Nat := 4983230072969 + 3 ^ 40 * 4965310 * 2
def baseEnd_4965310 : Nat := 2549590628576073435489961

theorem tailTrace_4965310 : CollatzResearch.WordTrace tailWord_4965310 prefixEnd_4965310 2549590628576073435489961 := by
  unfold tailWord_4965310
  simp only [CollatzResearch.WordTrace]
  refine ⟨22637466705192169034973673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120733155761024901519859589 22637466705192169034973673)
  ·
    refine ⟨16978100028894126776230255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22637466705192169034973673 16978100028894126776230255)
    ·
      refine ⟨25467150043341190164345383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16978100028894126776230255 25467150043341190164345383)
      ·
        refine ⟨38200725065011785246518075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25467150043341190164345383 38200725065011785246518075)
        ·
          refine ⟨57301087597517677869777113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38200725065011785246518075 57301087597517677869777113)
          ·
            refine ⟨42975815698138258402332835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57301087597517677869777113 42975815698138258402332835)
            ·
              refine ⟨64463723547207387603499253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42975815698138258402332835 64463723547207387603499253)
              ·
                refine ⟨6043474082550692587828055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64463723547207387603499253 6043474082550692587828055)
                ·
                  refine ⟨9065211123826038881742083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6043474082550692587828055 9065211123826038881742083)
                  ·
                    refine ⟨13597816685739058322613125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9065211123826038881742083 13597816685739058322613125)
                    ·
                      refine ⟨2549590628576073435489961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13597816685739058322613125 2549590628576073435489961)
                      ·
                        rfl

theorem cell23_4965310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_4965310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965310 prefixEnd_4965310 := by exact prefixLift 4965310
  have htrace : WordTrace (prefixWord ++ tailWord_4965310) baseStart_4965310 baseEnd_4965310 := by
    simpa [prefixWord, tailWord_4965310, baseEnd_4965310] using wordTrace_append hprefix tailTrace_4965310
  have hstable : (prefixWord ++ tailWord_4965310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965310).length < 2 ^ (prefixWord ++ tailWord_4965310).sum := by decide
  have hdescent : baseEnd_4965310 < baseStart_4965310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
