import V185TrunkScan22Chunk243

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2175081 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 2, 3]
def baseStart_2175081 : Nat := 118140960795 + 2175081 * 2 ^ 59
def prefixEnd_2175081 : Nat := 4983230072969 + 3 ^ 40 * 2175081 * 2
def baseEnd_2175081 : Nat := 744574676974739812856327

theorem tailTrace_2175081 : CollatzResearch.WordTrace tailWord_2175081 prefixEnd_2175081 744574676974739812856327 := by
  unfold tailWord_2175081
  simp only [CollatzResearch.WordTrace]
  refine ⟨79331721433060486105333097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52887814288706990736888731 79331721433060486105333097)
  ·
    refine ⟨59498791074795364578999823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79331721433060486105333097 59498791074795364578999823)
    ·
      refine ⟨89248186612193046868499735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59498791074795364578999823 89248186612193046868499735)
      ·
        refine ⟨133872279918289570302749603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89248186612193046868499735 133872279918289570302749603)
        ·
          refine ⟨200808419877434355454124405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133872279918289570302749603 200808419877434355454124405)
          ·
            refine ⟨18825789363509470823824163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200808419877434355454124405 18825789363509470823824163)
            ·
              refine ⟨28238684045264206235736245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18825789363509470823824163 28238684045264206235736245)
              ·
                refine ⟨2647376629243519334600273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28238684045264206235736245 2647376629243519334600273)
                ·
                  refine ⟨1985532471932639500950205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2647376629243519334600273 1985532471932639500950205)
                  ·
                    refine ⟨744574676974739812856327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1985532471932639500950205 744574676974739812856327)
                    ·
                      rfl

theorem cell22_2175081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_2175081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175081 prefixEnd_2175081 := by exact prefixLift 2175081
  have htrace : WordTrace (prefixWord ++ tailWord_2175081) baseStart_2175081 baseEnd_2175081 := by
    simpa [prefixWord, tailWord_2175081, baseEnd_2175081] using wordTrace_append hprefix tailTrace_2175081
  have hstable : (prefixWord ++ tailWord_2175081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175081).length < 2 ^ (prefixWord ++ tailWord_2175081).sum := by decide
  have hdescent : baseEnd_2175081 < baseStart_2175081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175190 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2175190 : Nat := 118140960795 + 2175190 * 2 ^ 59
def prefixEnd_2175190 : Nat := 4983230072969 + 3 ^ 40 * 2175190 * 2
def baseEnd_2175190 : Nat := 248203996634099953960331

theorem tailTrace_2175190 : CollatzResearch.WordTrace tailWord_2175190 prefixEnd_2175190 248203996634099953960331 := by
  unfold tailWord_2175190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4958481061854099857565689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52890464659777065147367349 4958481061854099857565689)
  ·
    refine ⟨3718860796390574893174267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4958481061854099857565689 3718860796390574893174267)
    ·
      refine ⟨5578291194585862339761401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718860796390574893174267 5578291194585862339761401)
      ·
        refine ⟨4183718395939396754821051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5578291194585862339761401 4183718395939396754821051)
        ·
          refine ⟨6275577593909095132231577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4183718395939396754821051 6275577593909095132231577)
          ·
            refine ⟨4706683195431821349173683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6275577593909095132231577 4706683195431821349173683)
            ·
              refine ⟨7060024793147732023760525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4706683195431821349173683 7060024793147732023760525)
              ·
                refine ⟨2647509297430399508910197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7060024793147732023760525 2647509297430399508910197)
                ·
                  refine ⟨248203996634099953960331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2647509297430399508910197 248203996634099953960331)
                  ·
                    rfl

theorem cell22_2175190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2175190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175190 prefixEnd_2175190 := by exact prefixLift 2175190
  have htrace : WordTrace (prefixWord ++ tailWord_2175190) baseStart_2175190 baseEnd_2175190 := by
    simpa [prefixWord, tailWord_2175190, baseEnd_2175190] using wordTrace_append hprefix tailTrace_2175190
  have hstable : (prefixWord ++ tailWord_2175190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175190).length < 2 ^ (prefixWord ++ tailWord_2175190).sum := by decide
  have hdescent : baseEnd_2175190 < baseStart_2175190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175216 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 6, 3]
def baseStart_2175216 : Nat := 118140960795 + 2175216 * 2 ^ 59
def prefixEnd_2175216 : Nat := 4983230072969 + 3 ^ 40 * 2175216 * 2
def baseEnd_2175216 : Nat := 744620890233644460730913

theorem tailTrace_2175216 : CollatzResearch.WordTrace tailWord_2175216 prefixEnd_2175216 744620890233644460730913 := by
  unfold tailWord_2175216
  simp only [CollatzResearch.WordTrace]
  refine ⟨39668322643785702080748751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52891096858380936107665001 39668322643785702080748751)
  ·
    refine ⟨59502483965678553121123127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39668322643785702080748751 59502483965678553121123127)
    ·
      refine ⟨89253725948517829681684691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59502483965678553121123127 89253725948517829681684691)
      ·
        refine ⟨133880588922776744522527037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89253725948517829681684691 133880588922776744522527037)
        ·
          refine ⟨50205220846041279195947639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133880588922776744522527037 50205220846041279195947639)
          ·
            refine ⟨75307831269061918793921459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50205220846041279195947639 75307831269061918793921459)
            ·
              refine ⟨112961746903592878190882189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75307831269061918793921459 112961746903592878190882189)
              ·
                refine ⟨42360655088847329321580821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112961746903592878190882189 42360655088847329321580821)
                ·
                  refine ⟨1985655707289718561949101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42360655088847329321580821 1985655707289718561949101)
                  ·
                    refine ⟨744620890233644460730913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1985655707289718561949101 744620890233644460730913)
                    ·
                      rfl

theorem cell22_2175216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_2175216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175216 prefixEnd_2175216 := by exact prefixLift 2175216
  have htrace : WordTrace (prefixWord ++ tailWord_2175216) baseStart_2175216 baseEnd_2175216 := by
    simpa [prefixWord, tailWord_2175216, baseEnd_2175216] using wordTrace_append hprefix tailTrace_2175216
  have hstable : (prefixWord ++ tailWord_2175216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175216).length < 2 ^ (prefixWord ++ tailWord_2175216).sum := by decide
  have hdescent : baseEnd_2175216 < baseStart_2175216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175231 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 2, 4]
def baseStart_2175231 : Nat := 118140960795 + 2175231 * 2 ^ 59
def prefixEnd_2175231 : Nat := 4983230072969 + 3 ^ 40 * 2175231 * 2
def baseEnd_2175231 : Nat := 744626025040189421605867

theorem tailTrace_2175231 : CollatzResearch.WordTrace tailWord_2175231 prefixEnd_2175231 744626025040189421605867 := by
  unfold tailWord_2175231
  simp only [CollatzResearch.WordTrace]
  refine ⟨79337192382517061723293547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52891461588344707815529031 79337192382517061723293547)
  ·
    refine ⟨119005788573775592584940321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79337192382517061723293547 119005788573775592584940321)
    ·
      refine ⟨89254341430331694438705241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119005788573775592584940321 89254341430331694438705241)
      ·
        refine ⟨66940756072748770829028931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89254341430331694438705241 66940756072748770829028931)
        ·
          refine ⟨100411134109123156243543397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66940756072748770829028931 100411134109123156243543397)
          ·
            refine ⟨18827087645460591795664387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100411134109123156243543397 18827087645460591795664387)
            ·
              refine ⟨28240631468190887693496581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18827087645460591795664387 28240631468190887693496581)
              ·
                refine ⟨5295118400285791442530609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28240631468190887693496581 5295118400285791442530609)
                ·
                  refine ⟨3971338800214343581897957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5295118400285791442530609 3971338800214343581897957)
                  ·
                    refine ⟨744626025040189421605867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971338800214343581897957 744626025040189421605867)
                    ·
                      rfl

theorem cell22_2175231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_2175231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175231 prefixEnd_2175231 := by exact prefixLift 2175231
  have htrace : WordTrace (prefixWord ++ tailWord_2175231) baseStart_2175231 baseEnd_2175231 := by
    simpa [prefixWord, tailWord_2175231, baseEnd_2175231] using wordTrace_append hprefix tailTrace_2175231
  have hstable : (prefixWord ++ tailWord_2175231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175231).length < 2 ^ (prefixWord ++ tailWord_2175231).sum := by decide
  have hdescent : baseEnd_2175231 < baseStart_2175231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175263 : List Nat := [1, 1, 2, 4, 3, 2, 3, 6]
def baseStart_2175263 : Nat := 118140960795 + 2175263 * 2 ^ 59
def prefixEnd_2175263 : Nat := 4983230072969 + 3 ^ 40 * 2175263 * 2
def baseEnd_2175263 : Nat := 82737442143794667200641

theorem tailTrace_2175263 : CollatzResearch.WordTrace tailWord_2175263 prefixEnd_2175263 82737442143794667200641 := by
  unfold tailWord_2175263
  simp only [CollatzResearch.WordTrace]
  refine ⟨79338359518401131188458443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52892239678934087458972295 79338359518401131188458443)
  ·
    refine ⟨119007539277601696782687665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79338359518401131188458443 119007539277601696782687665)
    ·
      refine ⟨89255654458201272587015749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119007539277601696782687665 89255654458201272587015749)
      ·
        refine ⟨16735435210912738610065453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89255654458201272587015749 16735435210912738610065453)
        ·
          refine ⟨6275788204092276978774545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16735435210912738610065453 6275788204092276978774545)
          ·
            refine ⟨4706841153069207734080909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6275788204092276978774545 4706841153069207734080909)
            ·
              refine ⟨1765065432400952900280341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4706841153069207734080909 1765065432400952900280341)
              ·
                refine ⟨82737442143794667200641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1765065432400952900280341 82737442143794667200641)
                ·
                  rfl

theorem cell22_2175263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 6].length) (baseStart_2175263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175263 prefixEnd_2175263 := by exact prefixLift 2175263
  have htrace : WordTrace (prefixWord ++ tailWord_2175263) baseStart_2175263 baseEnd_2175263 := by
    simpa [prefixWord, tailWord_2175263, baseEnd_2175263] using wordTrace_append hprefix tailTrace_2175263
  have hstable : (prefixWord ++ tailWord_2175263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175263).length < 2 ^ (prefixWord ++ tailWord_2175263).sum := by decide
  have hdescent : baseEnd_2175263 < baseStart_2175263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175271 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2175271 : Nat := 118140960795 + 2175271 * 2 ^ 59
def prefixEnd_2175271 : Nat := 4983230072969 + 3 ^ 40 * 2175271 * 2
def baseEnd_2175271 : Nat := 744639717857642650605745

theorem tailTrace_2175271 : CollatzResearch.WordTrace tailWord_2175271 prefixEnd_2175271 744639717857642650605745 := by
  unfold tailWord_2175271
  simp only [CollatzResearch.WordTrace]
  refine ⟨79338651302372148554749667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52892434201581432369833111 79338651302372148554749667)
  ·
    refine ⟨119007976953558222832124501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79338651302372148554749667 119007976953558222832124501)
    ·
      refine ⟨1394624729924510423813959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 119007976953558222832124501 1394624729924510423813959)
      ·
        refine ⟨2091937094886765635720939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394624729924510423813959 2091937094886765635720939)
        ·
          refine ⟨3137905642330148453581409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2091937094886765635720939 3137905642330148453581409)
          ·
            refine ⟨2353429231747611340186057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3137905642330148453581409 2353429231747611340186057)
            ·
              refine ⟨1765071923810708505139543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2353429231747611340186057 1765071923810708505139543)
              ·
                refine ⟨2647607885716062757709315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765071923810708505139543 2647607885716062757709315)
                ·
                  refine ⟨3971411828574094136563973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647607885716062757709315 3971411828574094136563973)
                  ·
                    refine ⟨744639717857642650605745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971411828574094136563973 744639717857642650605745)
                    ·
                      rfl

theorem cell22_2175271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2175271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175271 prefixEnd_2175271 := by exact prefixLift 2175271
  have htrace : WordTrace (prefixWord ++ tailWord_2175271) baseStart_2175271 baseEnd_2175271 := by
    simpa [prefixWord, tailWord_2175271, baseEnd_2175271] using wordTrace_append hprefix tailTrace_2175271
  have hstable : (prefixWord ++ tailWord_2175271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175271).length < 2 ^ (prefixWord ++ tailWord_2175271).sum := by decide
  have hdescent : baseEnd_2175271 < baseStart_2175271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175295 : List Nat := [1, 1, 2, 2, 4, 1, 1, 6, 1, 3]
def baseStart_2175295 : Nat := 118140960795 + 2175295 * 2 ^ 59
def prefixEnd_2175295 : Nat := 4983230072969 + 3 ^ 40 * 2175295 * 2
def baseEnd_2175295 : Nat := 744647933548114588005671

theorem tailTrace_2175295 : CollatzResearch.WordTrace tailWord_2175295 prefixEnd_2175295 744647933548114588005671 := by
  unfold tailWord_2175295
  simp only [CollatzResearch.WordTrace]
  refine ⟨79339526654285200653623339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52893017769523467102415559 79339526654285200653623339)
  ·
    refine ⟨119009289981427800980435009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79339526654285200653623339 119009289981427800980435009)
    ·
      refine ⟨89256967486070850735326257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119009289981427800980435009 89256967486070850735326257)
      ·
        refine ⟨66942725614553138051494693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89256967486070850735326257 66942725614553138051494693)
        ·
          refine ⟨12551761052728713384655255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66942725614553138051494693 12551761052728713384655255)
          ·
            refine ⟨18827641579093070076982883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12551761052728713384655255 18827641579093070076982883)
            ·
              refine ⟨28241462368639605115474325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18827641579093070076982883 28241462368639605115474325)
              ·
                refine ⟨1323818548529981489787859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28241462368639605115474325 1323818548529981489787859)
                ·
                  refine ⟨1985727822794972234681789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323818548529981489787859 1985727822794972234681789)
                  ·
                    refine ⟨744647933548114588005671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1985727822794972234681789 744647933548114588005671)
                    ·
                      rfl

theorem cell22_2175295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 1, 3].length) (baseStart_2175295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175295 prefixEnd_2175295 := by exact prefixLift 2175295
  have htrace : WordTrace (prefixWord ++ tailWord_2175295) baseStart_2175295 baseEnd_2175295 := by
    simpa [prefixWord, tailWord_2175295, baseEnd_2175295] using wordTrace_append hprefix tailTrace_2175295
  have hstable : (prefixWord ++ tailWord_2175295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175295).length < 2 ^ (prefixWord ++ tailWord_2175295).sum := by decide
  have hdescent : baseEnd_2175295 < baseStart_2175295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175351 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 5, 5]
def baseStart_2175351 : Nat := 118140960795 + 2175351 * 2 ^ 59
def prefixEnd_2175351 : Nat := 4983230072969 + 3 ^ 40 * 2175351 * 2
def baseEnd_2175351 : Nat := 744667103492549108605499

theorem tailTrace_2175351 : CollatzResearch.WordTrace tailWord_2175351 prefixEnd_2175351 744667103492549108605499 := by
  unfold tailWord_2175351
  simp only [CollatzResearch.WordTrace]
  refine ⟨79341569142082322217661907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52894379428054881478441271 79341569142082322217661907)
  ·
    refine ⟨119012353713123483326492861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79341569142082322217661907 119012353713123483326492861)
    ·
      refine ⟨44629632642421306247434823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119012353713123483326492861 44629632642421306247434823)
      ·
        refine ⟨66944448963631959371152235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44629632642421306247434823 66944448963631959371152235)
        ·
          refine ⟨100416673445447939056728353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66944448963631959371152235 100416673445447939056728353)
          ·
            refine ⟨75312505084085954292546265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100416673445447939056728353 75312505084085954292546265)
            ·
              refine ⟨56484378813064465719409699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75312505084085954292546265 56484378813064465719409699)
              ·
                refine ⟨84726568219596698579114549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56484378813064465719409699 84726568219596698579114549)
                ·
                  refine ⟨7943115770587190491791989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84726568219596698579114549 7943115770587190491791989)
                  ·
                    refine ⟨744667103492549108605499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7943115770587190491791989 744667103492549108605499)
                    ·
                      rfl

theorem cell22_2175351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_2175351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175351 prefixEnd_2175351 := by exact prefixLift 2175351
  have htrace : WordTrace (prefixWord ++ tailWord_2175351) baseStart_2175351 baseEnd_2175351 := by
    simpa [prefixWord, tailWord_2175351, baseEnd_2175351] using wordTrace_append hprefix tailTrace_2175351
  have hstable : (prefixWord ++ tailWord_2175351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175351).length < 2 ^ (prefixWord ++ tailWord_2175351).sum := by decide
  have hdescent : baseEnd_2175351 < baseStart_2175351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175368 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_2175368 : Nat := 118140960795 + 2175368 * 2 ^ 59
def prefixEnd_2175368 : Nat := 4983230072969 + 3 ^ 40 * 2175368 * 2
def baseEnd_2175368 : Nat := 744672922939966730930447

theorem tailTrace_2175368 : CollatzResearch.WordTrace tailWord_2175368 prefixEnd_2175368 744672922939966730930447 := by
  unfold tailWord_2175368
  simp only [CollatzResearch.WordTrace]
  refine ⟨39671094591510367060515379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52894792788680489414020505 39671094591510367060515379)
  ·
    refine ⟨59506641887265550590773069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39671094591510367060515379 59506641887265550590773069)
    ·
      refine ⟨22314990707724581471539901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59506641887265550590773069 22314990707724581471539901)
      ·
        refine ⟨8368121515396718051827463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22314990707724581471539901 8368121515396718051827463)
        ·
          refine ⟨12552182273095077077741195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8368121515396718051827463 12552182273095077077741195)
          ·
            refine ⟨18828273409642615616611793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12552182273095077077741195 18828273409642615616611793)
            ·
              refine ⟨14121205057231961712458845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18828273409642615616611793 14121205057231961712458845)
              ·
                refine ⟨5295451896461985642172067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14121205057231961712458845 5295451896461985642172067)
                ·
                  refine ⟨7943177844692978463258101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5295451896461985642172067 7943177844692978463258101)
                  ·
                    refine ⟨744672922939966730930447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7943177844692978463258101 744672922939966730930447)
                    ·
                      rfl

theorem cell22_2175368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_2175368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175368 prefixEnd_2175368 := by exact prefixLift 2175368
  have htrace : WordTrace (prefixWord ++ tailWord_2175368) baseStart_2175368 baseEnd_2175368 := by
    simpa [prefixWord, tailWord_2175368, baseEnd_2175368] using wordTrace_append hprefix tailTrace_2175368
  have hstable : (prefixWord ++ tailWord_2175368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175368).length < 2 ^ (prefixWord ++ tailWord_2175368).sum := by decide
  have hdescent : baseEnd_2175368 < baseStart_2175368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175383 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 2, 4]
def baseStart_2175383 : Nat := 118140960795 + 2175383 * 2 ^ 59
def prefixEnd_2175383 : Nat := 4983230072969 + 3 ^ 40 * 2175383 * 2
def baseEnd_2175383 : Nat := 744678057746511691805401

theorem tailTrace_2175383 : CollatzResearch.WordTrace tailWord_2175383 prefixEnd_2175383 744678057746511691805401 := by
  unfold tailWord_2175383
  simp only [CollatzResearch.WordTrace]
  refine ⟨79342736277966391682826803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52895157518644261121884535 79342736277966391682826803)
  ·
    refine ⟨119014104416949587524240205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79342736277966391682826803 119014104416949587524240205)
    ·
      refine ⟨44630289156356095321590077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119014104416949587524240205 44630289156356095321590077)
      ·
        refine ⟨16736358433633535745596279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44630289156356095321590077 16736358433633535745596279)
        ·
          refine ⟨25104537650450303618394419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16736358433633535745596279 25104537650450303618394419)
          ·
            refine ⟨37656806475675455427591629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25104537650450303618394419 37656806475675455427591629)
            ·
              refine ⟨14121302428378295785346861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37656806475675455427591629 14121302428378295785346861)
              ·
                refine ⟨5295488410641860919505073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14121302428378295785346861 5295488410641860919505073)
                ·
                  refine ⟨3971616307981395689628805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5295488410641860919505073 3971616307981395689628805)
                  ·
                    refine ⟨744678057746511691805401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3971616307981395689628805 744678057746511691805401)
                    ·
                      rfl

theorem cell22_2175383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_2175383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175383 prefixEnd_2175383 := by exact prefixLift 2175383
  have htrace : WordTrace (prefixWord ++ tailWord_2175383) baseStart_2175383 baseEnd_2175383 := by
    simpa [prefixWord, tailWord_2175383, baseEnd_2175383] using wordTrace_append hprefix tailTrace_2175383
  have hstable : (prefixWord ++ tailWord_2175383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175383).length < 2 ^ (prefixWord ++ tailWord_2175383).sum := by decide
  have hdescent : baseEnd_2175383 < baseStart_2175383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175494 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2175494 : Nat := 118140960795 + 2175494 * 2 ^ 59
def prefixEnd_2175494 : Nat := 4983230072969 + 3 ^ 40 * 2175494 * 2
def baseEnd_2175494 : Nat := 248238685104981467426687

theorem tailTrace_2175494 : CollatzResearch.WordTrace tailWord_2175494 prefixEnd_2175494 248238685104981467426687 := by
  unfold tailWord_2175494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479587024392633051253673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52897856520376171760078357 2479587024392633051253673)
  ·
    refine ⟨1859690268294474788440255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2479587024392633051253673 1859690268294474788440255)
    ·
      refine ⟨2789535402441712182660383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859690268294474788440255 2789535402441712182660383)
      ·
        refine ⟨4184303103662568273990575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2789535402441712182660383 4184303103662568273990575)
        ·
          refine ⟨6276454655493852410985863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4184303103662568273990575 6276454655493852410985863)
          ·
            refine ⟨9414681983240778616478795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6276454655493852410985863 9414681983240778616478795)
            ·
              refine ⟨14122022974861167924718193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9414681983240778616478795 14122022974861167924718193)
              ·
                refine ⟨10591517231145875943538645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14122022974861167924718193 10591517231145875943538645)
                ·
                  refine ⟨248238685104981467426687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10591517231145875943538645 248238685104981467426687)
                  ·
                    rfl

theorem cell22_2175494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2175494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175494 prefixEnd_2175494 := by exact prefixLift 2175494
  have htrace : WordTrace (prefixWord ++ tailWord_2175494) baseStart_2175494 baseEnd_2175494 := by
    simpa [prefixWord, tailWord_2175494, baseEnd_2175494] using wordTrace_append hprefix tailTrace_2175494
  have hstable : (prefixWord ++ tailWord_2175494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175494).length < 2 ^ (prefixWord ++ tailWord_2175494).sum := by decide
  have hdescent : baseEnd_2175494 < baseStart_2175494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175505 : List Nat := [1, 2, 2, 1, 1, 2, 2, 7, 4]
def baseStart_2175505 : Nat := 118140960795 + 2175505 * 2 ^ 59
def prefixEnd_2175505 : Nat := 4983230072969 + 3 ^ 40 * 2175505 * 2
def baseEnd_2175505 : Nat := 248239940279914680085009

theorem tailTrace_2175505 : CollatzResearch.WordTrace tailWord_2175505 prefixEnd_2175505 248239940279914680085009 := by
  unfold tailWord_2175505
  simp only [CollatzResearch.WordTrace]
  refine ⟨79347185983524406518767969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52898123989016271012511979 79347185983524406518767969)
  ·
    refine ⟨59510389487643304889075977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79347185983524406518767969 59510389487643304889075977)
    ·
      refine ⟨44632792115732478666806983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59510389487643304889075977 44632792115732478666806983)
      ·
        refine ⟨66949188173598718000210475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44632792115732478666806983 66949188173598718000210475)
        ·
          refine ⟨100423782260398077000315713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66949188173598718000210475 100423782260398077000315713)
          ·
            refine ⟨75317836695298557750236785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100423782260398077000315713 75317836695298557750236785)
            ·
              refine ⟨56488377521473918312677589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75317836695298557750236785 56488377521473918312677589)
              ·
                refine ⟨1323946348159544960453381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56488377521473918312677589 1323946348159544960453381)
                ·
                  refine ⟨248239940279914680085009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323946348159544960453381 248239940279914680085009)
                  ·
                    rfl

theorem cell22_2175505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 4].length) (baseStart_2175505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175505 prefixEnd_2175505 := by exact prefixLift 2175505
  have htrace : WordTrace (prefixWord ++ tailWord_2175505) baseStart_2175505 baseEnd_2175505 := by
    simpa [prefixWord, tailWord_2175505, baseEnd_2175505] using wordTrace_append hprefix tailTrace_2175505
  have hstable : (prefixWord ++ tailWord_2175505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175505).length < 2 ^ (prefixWord ++ tailWord_2175505).sum := by decide
  have hdescent : baseEnd_2175505 < baseStart_2175505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175777 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2175777 : Nat := 118140960795 + 2175777 * 2 ^ 59
def prefixEnd_2175777 : Nat := 4983230072969 + 3 ^ 40 * 2175777 * 2
def baseEnd_2175777 : Nat := 744812931998425997454193

theorem tailTrace_2175777 : CollatzResearch.WordTrace tailWord_2175777 prefixEnd_2175777 744812931998425997454193 := by
  unfold tailWord_2175777
  simp only [CollatzResearch.WordTrace]
  refine ⟨79357106638538996972669585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52904737759025997981779723 79357106638538996972669585)
  ·
    refine ⟨59517829978904247729502189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79357106638538996972669585 59517829978904247729502189)
    ·
      refine ⟨22319186242089092898563321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59517829978904247729502189 22319186242089092898563321)
      ·
        refine ⟨16739389681566819673922491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22319186242089092898563321 16739389681566819673922491)
        ·
          refine ⟨25109084522350229510883737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16739389681566819673922491 25109084522350229510883737)
          ·
            refine ⟨18831813391762672133162803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25109084522350229510883737 18831813391762672133162803)
            ·
              refine ⟨28247720087644008199744205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18831813391762672133162803 28247720087644008199744205)
              ·
                refine ⟨10592895032866503074904077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28247720087644008199744205 10592895032866503074904077)
                ·
                  refine ⟨3972335637324938653089029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10592895032866503074904077 3972335637324938653089029)
                  ·
                    refine ⟨744812931998425997454193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972335637324938653089029 744812931998425997454193)
                    ·
                      rfl

theorem cell22_2175777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2175777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175777 prefixEnd_2175777 := by exact prefixLift 2175777
  have htrace : WordTrace (prefixWord ++ tailWord_2175777) baseStart_2175777 baseEnd_2175777 := by
    simpa [prefixWord, tailWord_2175777, baseEnd_2175777] using wordTrace_append hprefix tailTrace_2175777
  have hstable : (prefixWord ++ tailWord_2175777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175777).length < 2 ^ (prefixWord ++ tailWord_2175777).sum := by decide
  have hdescent : baseEnd_2175777 < baseStart_2175777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175794 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_2175794 : Nat := 118140960795 + 2175794 * 2 ^ 59
def prefixEnd_2175794 : Nat := 4983230072969 + 3 ^ 40 * 2175794 * 2
def baseEnd_2175794 : Nat := 744818751445843619779141

theorem tailTrace_2175794 : CollatzResearch.WordTrace tailWord_2175794 prefixEnd_2175794 744818751445843619779141 := by
  unfold tailWord_2175794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19839431669869352219009609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52905151119651605917358957 19839431669869352219009609)
  ·
    refine ⟨14879573752402014164257207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19839431669869352219009609 14879573752402014164257207)
    ·
      refine ⟨22319360628603021246385811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14879573752402014164257207 22319360628603021246385811)
      ·
        refine ⟨33479040942904531869578717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22319360628603021246385811 33479040942904531869578717)
        ·
          refine ⟨12554640353589199451092019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33479040942904531869578717 12554640353589199451092019)
          ·
            refine ⟨18831960530383799176638029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12554640353589199451092019 18831960530383799176638029)
            ·
              refine ⟨7061985198893924691239261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18831960530383799176638029 7061985198893924691239261)
              ·
                refine ⟨2648244449585221759214723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7061985198893924691239261 2648244449585221759214723)
                ·
                  refine ⟨3972366674377832638822085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648244449585221759214723 3972366674377832638822085)
                  ·
                    refine ⟨744818751445843619779141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972366674377832638822085 744818751445843619779141)
                    ·
                      rfl

theorem cell22_2175794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_2175794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175794 prefixEnd_2175794 := by exact prefixLift 2175794
  have htrace : WordTrace (prefixWord ++ tailWord_2175794) baseStart_2175794 baseEnd_2175794 := by
    simpa [prefixWord, tailWord_2175794, baseEnd_2175794] using wordTrace_append hprefix tailTrace_2175794
  have hstable : (prefixWord ++ tailWord_2175794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175794).length < 2 ^ (prefixWord ++ tailWord_2175794).sum := by decide
  have hdescent : baseEnd_2175794 < baseStart_2175794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175798 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_2175798 : Nat := 118140960795 + 2175798 * 2 ^ 59
def prefixEnd_2175798 : Nat := 4983230072969 + 3 ^ 40 * 2175798 * 2
def baseEnd_2175798 : Nat := 248273373575862980893043

theorem tailTrace_2175798 : CollatzResearch.WordTrace tailWord_2175798 prefixEnd_2175798 248273373575862980893043 := by
  unfold tailWord_2175798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959867035716432347449003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52905248380975278372789365 4959867035716432347449003)
  ·
    refine ⟨7439800553574648521173505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4959867035716432347449003 7439800553574648521173505)
    ·
      refine ⟨5579850415180986390880129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7439800553574648521173505 5579850415180986390880129)
      ·
        refine ⟨4184887811385739793160097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5579850415180986390880129 4184887811385739793160097)
        ·
          refine ⟨3138665858539304844870073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4184887811385739793160097 3138665858539304844870073)
          ·
            refine ⟨2353999393904478633652555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3138665858539304844870073 2353999393904478633652555)
            ·
              refine ⟨3530999090856717950478833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2353999393904478633652555 3530999090856717950478833)
              ·
                refine ⟨2648249318142538462859125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3530999090856717950478833 2648249318142538462859125)
                ·
                  refine ⟨248273373575862980893043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2648249318142538462859125 248273373575862980893043)
                  ·
                    rfl

theorem cell22_2175798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_2175798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175798 prefixEnd_2175798 := by exact prefixLift 2175798
  have htrace : WordTrace (prefixWord ++ tailWord_2175798) baseStart_2175798 baseEnd_2175798 := by
    simpa [prefixWord, tailWord_2175798, baseEnd_2175798] using wordTrace_append hprefix tailTrace_2175798
  have hstable : (prefixWord ++ tailWord_2175798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175798).length < 2 ^ (prefixWord ++ tailWord_2175798).sum := by decide
  have hdescent : baseEnd_2175798 < baseStart_2175798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175824 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 2, 3]
def baseStart_2175824 : Nat := 118140960795 + 2175824 * 2 ^ 59
def prefixEnd_2175824 : Nat := 4983230072969 + 3 ^ 40 * 2175824 * 2
def baseEnd_2175824 : Nat := 744829021058933541529049

theorem tailTrace_2175824 : CollatzResearch.WordTrace tailWord_2175824 prefixEnd_2175824 744829021058933541529049 := by
  unfold tailWord_2175824
  simp only [CollatzResearch.WordTrace]
  refine ⟨39679410434684361999815263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52905880579579149333087017 39679410434684361999815263)
  ·
    refine ⟨59519115652026542999722895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39679410434684361999815263 59519115652026542999722895)
    ·
      refine ⟨89278673478039814499584343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59519115652026542999722895 89278673478039814499584343)
      ·
        refine ⟨133918010217059721749376515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89278673478039814499584343 133918010217059721749376515)
        ·
          refine ⟨200877015325589582624064773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133918010217059721749376515 200877015325589582624064773)
          ·
            refine ⟨37664440373548046742012145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200877015325589582624064773 37664440373548046742012145)
            ·
              refine ⟨28248330280161035056509109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37664440373548046742012145 28248330280161035056509109)
              ·
                refine ⟨2648280963765097036547729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28248330280161035056509109 2648280963765097036547729)
                ·
                  refine ⟨1986210722823822777410797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2648280963765097036547729 1986210722823822777410797)
                  ·
                    refine ⟨744829021058933541529049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1986210722823822777410797 744829021058933541529049)
                    ·
                      rfl

theorem cell22_2175824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_2175824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175824 prefixEnd_2175824 := by exact prefixLift 2175824
  have htrace : WordTrace (prefixWord ++ tailWord_2175824) baseStart_2175824 baseEnd_2175824 := by
    simpa [prefixWord, tailWord_2175824, baseEnd_2175824] using wordTrace_append hprefix tailTrace_2175824
  have hstable : (prefixWord ++ tailWord_2175824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175824).length < 2 ^ (prefixWord ++ tailWord_2175824).sum := by decide
  have hdescent : baseEnd_2175824 < baseStart_2175824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175897 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_2175897 : Nat := 118140960795 + 2175897 * 2 ^ 59
def prefixEnd_2175897 : Nat := 4983230072969 + 3 ^ 40 * 2175897 * 2
def baseEnd_2175897 : Nat := 744854010450785684453825

theorem tailTrace_2175897 : CollatzResearch.WordTrace tailWord_2175897 prefixEnd_2175897 744854010450785684453825 := by
  unfold tailWord_2175897
  simp only [CollatzResearch.WordTrace]
  refine ⟨79361483398104257467037945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52907655598736171644691963 79361483398104257467037945)
  ·
    refine ⟨59521112548578193100278459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79361483398104257467037945 59521112548578193100278459)
    ·
      refine ⟨89281668822867289650417689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59521112548578193100278459 89281668822867289650417689)
      ·
        refine ⟨66961251617150467237813267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89281668822867289650417689 66961251617150467237813267)
        ·
          refine ⟨100441877425725700856719901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66961251617150467237813267 100441877425725700856719901)
          ·
            refine ⟨37665704034647137821269963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100441877425725700856719901 37665704034647137821269963)
            ·
              refine ⟨56498556051970706731904945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37665704034647137821269963 56498556051970706731904945)
              ·
                refine ⟨42373917038978030048928709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56498556051970706731904945 42373917038978030048928709)
                ·
                  refine ⟨7945109444808380634174133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42373917038978030048928709 7945109444808380634174133)
                  ·
                    refine ⟨744854010450785684453825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7945109444808380634174133 744854010450785684453825)
                    ·
                      rfl

theorem cell22_2175897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_2175897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175897 prefixEnd_2175897 := by exact prefixLift 2175897
  have htrace : WordTrace (prefixWord ++ tailWord_2175897) baseStart_2175897 baseEnd_2175897 := by
    simpa [prefixWord, tailWord_2175897, baseEnd_2175897] using wordTrace_append hprefix tailTrace_2175897
  have hstable : (prefixWord ++ tailWord_2175897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175897).length < 2 ^ (prefixWord ++ tailWord_2175897).sum := by decide
  have hdescent : baseEnd_2175897 < baseStart_2175897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175929 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_2175929 : Nat := 118140960795 + 2175929 * 2 ^ 59
def prefixEnd_2175929 : Nat := 4983230072969 + 3 ^ 40 * 2175929 * 2
def baseEnd_2175929 : Nat := 744864964704748267653727

theorem tailTrace_2175929 : CollatzResearch.WordTrace tailWord_2175929 prefixEnd_2175929 744864964704748267653727 := by
  unfold tailWord_2175929
  simp only [CollatzResearch.WordTrace]
  refine ⟨79362650533988326932202841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52908433689325551288135227 79362650533988326932202841)
  ·
    refine ⟨59521987900491245199152131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79362650533988326932202841 59521987900491245199152131)
    ·
      refine ⟨89282981850736867798728197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59521987900491245199152131 89282981850736867798728197)
      ·
        refine ⟨16740559097013162712261537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89282981850736867798728197 16740559097013162712261537)
        ·
          refine ⟨12555419322759872034196153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16740559097013162712261537 12555419322759872034196153)
          ·
            refine ⟨9416564492069904025647115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12555419322759872034196153 9416564492069904025647115)
            ·
              refine ⟨14124846738104856038470673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9416564492069904025647115 14124846738104856038470673)
              ·
                refine ⟨10593635053578642028853005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14124846738104856038470673 10593635053578642028853005)
                ·
                  refine ⟨3972613145091990760819877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10593635053578642028853005 3972613145091990760819877)
                  ·
                    refine ⟨744864964704748267653727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972613145091990760819877 744864964704748267653727)
                    ·
                      rfl

theorem cell22_2175929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_2175929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175929 prefixEnd_2175929 := by exact prefixLift 2175929
  have htrace : WordTrace (prefixWord ++ tailWord_2175929) baseStart_2175929 baseEnd_2175929 := by
    simpa [prefixWord, tailWord_2175929, baseEnd_2175929] using wordTrace_append hprefix tailTrace_2175929
  have hstable : (prefixWord ++ tailWord_2175929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175929).length < 2 ^ (prefixWord ++ tailWord_2175929).sum := by decide
  have hdescent : baseEnd_2175929 < baseStart_2175929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175961 : List Nat := [1, 2, 1, 2, 5, 1, 1, 5, 4]
def baseStart_2175961 : Nat := 118140960795 + 2175961 * 2 ^ 59
def prefixEnd_2175961 : Nat := 4983230072969 + 3 ^ 40 * 2175961 * 2
def baseEnd_2175961 : Nat := 248291972986236950284543

theorem tailTrace_2175961 : CollatzResearch.WordTrace tailWord_2175961 prefixEnd_2175961 248291972986236950284543 := by
  unfold tailWord_2175961
  simp only [CollatzResearch.WordTrace]
  refine ⟨79363817669872396397367737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52909211779914930931578491 79363817669872396397367737)
  ·
    refine ⟨59522863252404297298025803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79363817669872396397367737 59522863252404297298025803)
    ·
      refine ⟨89284294878606445947038705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59522863252404297298025803 89284294878606445947038705)
      ·
        refine ⟨66963221158954834460279029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89284294878606445947038705 66963221158954834460279029)
        ·
          refine ⟨6277801983652015730651159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66963221158954834460279029 6277801983652015730651159)
          ·
            refine ⟨9416702975478023595976739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6277801983652015730651159 9416702975478023595976739)
            ·
              refine ⟨14125054463217035393965109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9416702975478023595976739 14125054463217035393965109)
              ·
                refine ⟨1324223855926597068184229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14125054463217035393965109 1324223855926597068184229)
                ·
                  refine ⟨248291972986236950284543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324223855926597068184229 248291972986236950284543)
                  ·
                    rfl

theorem cell22_2175961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 4].length) (baseStart_2175961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175961 prefixEnd_2175961 := by exact prefixLift 2175961
  have htrace : WordTrace (prefixWord ++ tailWord_2175961) baseStart_2175961 baseEnd_2175961 := by
    simpa [prefixWord, tailWord_2175961, baseEnd_2175961] using wordTrace_append hprefix tailTrace_2175961
  have hstable : (prefixWord ++ tailWord_2175961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175961).length < 2 ^ (prefixWord ++ tailWord_2175961).sum := by decide
  have hdescent : baseEnd_2175961 < baseStart_2175961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175993 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 2, 3]
def baseStart_2175993 : Nat := 118140960795 + 2175993 * 2 ^ 59
def prefixEnd_2175993 : Nat := 4983230072969 + 3 ^ 40 * 2175993 * 2
def baseEnd_2175993 : Nat := 744886873212673434053531

theorem tailTrace_2175993 : CollatzResearch.WordTrace tailWord_2175993 prefixEnd_2175993 744886873212673434053531 := by
  unfold tailWord_2175993
  simp only [CollatzResearch.WordTrace]
  refine ⟨79364984805756465862532633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52909989870504310575021755 79364984805756465862532633)
  ·
    refine ⟨59523738604317349396899475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79364984805756465862532633 59523738604317349396899475)
    ·
      refine ⟨89285607906476024095349213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59523738604317349396899475 89285607906476024095349213)
      ·
        refine ⟨33482102964928509035755955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89285607906476024095349213 33482102964928509035755955)
        ·
          refine ⟨50223154447392763553633933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33482102964928509035755955 50223154447392763553633933)
          ·
            refine ⟨18833682917772286332612725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50223154447392763553633933 18833682917772286332612725)
            ·
              refine ⟨1765657773541151843682443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18833682917772286332612725 1765657773541151843682443)
              ·
                refine ⟨2648486660311727765523665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765657773541151843682443 2648486660311727765523665)
                ·
                  refine ⟨1986364995233795824142749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2648486660311727765523665 1986364995233795824142749)
                  ·
                    refine ⟨744886873212673434053531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1986364995233795824142749 744886873212673434053531)
                    ·
                      rfl

theorem cell22_2175993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 3].length) (baseStart_2175993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175993 prefixEnd_2175993 := by exact prefixLift 2175993
  have htrace : WordTrace (prefixWord ++ tailWord_2175993) baseStart_2175993 baseEnd_2175993 := by
    simpa [prefixWord, tailWord_2175993, baseEnd_2175993] using wordTrace_append hprefix tailTrace_2175993
  have hstable : (prefixWord ++ tailWord_2175993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175993).length < 2 ^ (prefixWord ++ tailWord_2175993).sum := by decide
  have hdescent : baseEnd_2175993 < baseStart_2175993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176049 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_2176049 : Nat := 118140960795 + 2176049 * 2 ^ 59
def prefixEnd_2176049 : Nat := 4983230072969 + 3 ^ 40 * 2176049 * 2
def baseEnd_2176049 : Nat := 744906043157107954653359

theorem tailTrace_2176049 : CollatzResearch.WordTrace tailWord_2176049 prefixEnd_2176049 744906043157107954653359 := by
  unfold tailWord_2176049
  simp only [CollatzResearch.WordTrace]
  refine ⟨79367027293553587426571201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52911351529035724951047467 79367027293553587426571201)
  ·
    refine ⟨59525270470165190569928401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79367027293553587426571201 59525270470165190569928401)
    ·
      refine ⟨44643952852623892927446301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59525270470165190569928401 44643952852623892927446301)
      ·
        refine ⟨16741482319733959847792363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44643952852623892927446301 16741482319733959847792363)
        ·
          refine ⟨25112223479600939771688545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16741482319733959847792363 25112223479600939771688545)
          ·
            refine ⟨18834167609700704828766409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25112223479600939771688545 18834167609700704828766409)
            ·
              refine ⟨14125625707275528621574807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18834167609700704828766409 14125625707275528621574807)
              ·
                refine ⟨21188438560913292932362211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14125625707275528621574807 21188438560913292932362211)
                ·
                  refine ⟨31782657841369939398543317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21188438560913292932362211 31782657841369939398543317)
                  ·
                    refine ⟨744906043157107954653359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31782657841369939398543317 744906043157107954653359)
                    ·
                      rfl

theorem cell22_2176049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_2176049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176049 prefixEnd_2176049 := by exact prefixLift 2176049
  have htrace : WordTrace (prefixWord ++ tailWord_2176049) baseStart_2176049 baseEnd_2176049 := by
    simpa [prefixWord, tailWord_2176049, baseEnd_2176049] using wordTrace_append hprefix tailTrace_2176049
  have hstable : (prefixWord ++ tailWord_2176049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176049).length < 2 ^ (prefixWord ++ tailWord_2176049).sum := by decide
  have hdescent : baseEnd_2176049 < baseStart_2176049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176081 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 1, 4]
def baseStart_2176081 : Nat := 118140960795 + 2176081 * 2 ^ 59
def prefixEnd_2176081 : Nat := 4983230072969 + 3 ^ 40 * 2176081 * 2
def baseEnd_2176081 : Nat := 744916997411070537853261

theorem tailTrace_2176081 : CollatzResearch.WordTrace tailWord_2176081 prefixEnd_2176081 744916997411070537853261 := by
  unfold tailWord_2176081
  simp only [CollatzResearch.WordTrace]
  refine ⟨79368194429437656891736097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52912129619625104594490731 79368194429437656891736097)
  ·
    refine ⟨59526145822078242668802073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79368194429437656891736097 59526145822078242668802073)
    ·
      refine ⟨44644609366558682001601555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59526145822078242668802073 44644609366558682001601555)
      ·
        refine ⟨66966914049838023002402333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44644609366558682001601555 66966914049838023002402333)
        ·
          refine ⟨25112592768689258625900875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66966914049838023002402333 25112592768689258625900875)
          ·
            refine ⟨37668889153033887938851313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25112592768689258625900875 37668889153033887938851313)
            ·
              refine ⟨28251666864775415954138485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37668889153033887938851313 28251666864775415954138485)
              ·
                refine ⟨2648593768572695245700483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28251666864775415954138485 2648593768572695245700483)
                ·
                  refine ⟨3972890652859042868550725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648593768572695245700483 3972890652859042868550725)
                  ·
                    refine ⟨744916997411070537853261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972890652859042868550725 744916997411070537853261)
                    ·
                      rfl

theorem cell22_2176081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_2176081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176081 prefixEnd_2176081 := by exact prefixLift 2176081
  have htrace : WordTrace (prefixWord ++ tailWord_2176081) baseStart_2176081 baseEnd_2176081 := by
    simpa [prefixWord, tailWord_2176081, baseEnd_2176081] using wordTrace_append hprefix tailTrace_2176081
  have hstable : (prefixWord ++ tailWord_2176081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176081).length < 2 ^ (prefixWord ++ tailWord_2176081).sum := by decide
  have hdescent : baseEnd_2176081 < baseStart_2176081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176098 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2176098 : Nat := 118140960795 + 2176098 * 2 ^ 59
def prefixEnd_2176098 : Nat := 4983230072969 + 3 ^ 40 * 2176098 * 2
def baseEnd_2176098 : Nat := 744922816858488160178209

theorem tailTrace_2176098 : CollatzResearch.WordTrace tailWord_2176098 prefixEnd_2176098 744922816858488160178209 := by
  unfold tailWord_2176098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19842203617594017198776237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52912542980250712530069965 19842203617594017198776237)
  ·
    refine ⟨7440826356597756449541089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19842203617594017198776237 7440826356597756449541089)
    ·
      refine ⟨5580619767448317337155817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7440826356597756449541089 5580619767448317337155817)
      ·
        refine ⟨4185464825586238002866863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5580619767448317337155817 4185464825586238002866863)
        ·
          refine ⟨6278197238379357004300295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4185464825586238002866863 6278197238379357004300295)
          ·
            refine ⟨9417295857569035506450443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6278197238379357004300295 9417295857569035506450443)
            ·
              refine ⟨14125943786353553259675665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9417295857569035506450443 14125943786353553259675665)
              ·
                refine ⟨10594457839765164944756749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14125943786353553259675665 10594457839765164944756749)
                ·
                  refine ⟨3972921689911936854283781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10594457839765164944756749 3972921689911936854283781)
                  ·
                    refine ⟨744922816858488160178209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3972921689911936854283781 744922816858488160178209)
                    ·
                      rfl

theorem cell22_2176098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2176098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176098 prefixEnd_2176098 := by exact prefixLift 2176098
  have htrace : WordTrace (prefixWord ++ tailWord_2176098) baseStart_2176098 baseEnd_2176098 := by
    simpa [prefixWord, tailWord_2176098, baseEnd_2176098] using wordTrace_append hprefix tailTrace_2176098
  have hstable : (prefixWord ++ tailWord_2176098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176098).length < 2 ^ (prefixWord ++ tailWord_2176098).sum := by decide
  have hdescent : baseEnd_2176098 < baseStart_2176098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176111 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 1, 5]
def baseStart_2176111 : Nat := 118140960795 + 2176111 * 2 ^ 59
def prefixEnd_2176111 : Nat := 4983230072969 + 3 ^ 40 * 2176111 * 2
def baseEnd_2176111 : Nat := 744927267024160459603169

theorem tailTrace_2176111 : CollatzResearch.WordTrace tailWord_2176111 prefixEnd_2176111 744927267024160459603169 := by
  unfold tailWord_2176111
  simp only [CollatzResearch.WordTrace]
  refine ⟨79369288619328972015328187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52912859079552648010218791 79369288619328972015328187)
  ·
    refine ⟨119053932928993458022992281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79369288619328972015328187 119053932928993458022992281)
    ·
      refine ⟨89290449696745093517244211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119053932928993458022992281 89290449696745093517244211)
      ·
        refine ⟨133935674545117640275866317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89290449696745093517244211 133935674545117640275866317)
        ·
          refine ⟨50225877954419115103449869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133935674545117640275866317 50225877954419115103449869)
          ·
            refine ⟨18834704232907168163793701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50225877954419115103449869 18834704232907168163793701)
            ·
              refine ⟨3531507043670094030711319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18834704232907168163793701 3531507043670094030711319)
              ·
                refine ⟨5297260565505141046066979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531507043670094030711319 5297260565505141046066979)
                ·
                  refine ⟨7945890848257711569100469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297260565505141046066979 7945890848257711569100469)
                  ·
                    refine ⟨744927267024160459603169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7945890848257711569100469 744927267024160459603169)
                    ·
                      rfl

theorem cell22_2176111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_2176111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176111 prefixEnd_2176111 := by exact prefixLift 2176111
  have htrace : WordTrace (prefixWord ++ tailWord_2176111) baseStart_2176111 baseEnd_2176111 := by
    simpa [prefixWord, tailWord_2176111, baseEnd_2176111] using wordTrace_append hprefix tailTrace_2176111
  have hstable : (prefixWord ++ tailWord_2176111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176111).length < 2 ^ (prefixWord ++ tailWord_2176111).sum := by decide
  have hdescent : baseEnd_2176111 < baseStart_2176111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176139 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 9]
def baseStart_2176139 : Nat := 118140960795 + 2176139 * 2 ^ 59
def prefixEnd_2176139 : Nat := 4983230072969 + 3 ^ 40 * 2176139 * 2
def baseEnd_2176139 : Nat := 744936851996377719903083

theorem tailTrace_2176139 : CollatzResearch.WordTrace tailWord_2176139 prefixEnd_2176139 744936851996377719903083 := by
  unfold tailWord_2176139
  simp only [CollatzResearch.WordTrace]
  refine ⟨79370309863227532797347471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52913539908818355198231647 79370309863227532797347471)
  ·
    refine ⟨119055464794841299196021207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79370309863227532797347471 119055464794841299196021207)
    ·
      refine ⟨178583197192261948794031811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119055464794841299196021207 178583197192261948794031811)
      ·
        refine ⟨267874795788392923191047717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178583197192261948794031811 267874795788392923191047717)
        ·
          refine ⟨50226524210323673098321447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267874795788392923191047717 50226524210323673098321447)
          ·
            refine ⟨75339786315485509647482171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50226524210323673098321447 75339786315485509647482171)
            ·
              refine ⟨113009679473228264471223257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75339786315485509647482171 113009679473228264471223257)
              ·
                refine ⟨84757259604921198353417443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113009679473228264471223257 84757259604921198353417443)
                ·
                  refine ⟨127135889407381797530126165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84757259604921198353417443 127135889407381797530126165)
                  ·
                    refine ⟨744936851996377719903083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127135889407381797530126165 744936851996377719903083)
                    ·
                      rfl

theorem cell22_2176139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_2176139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176139 prefixEnd_2176139 := by exact prefixLift 2176139
  have htrace : WordTrace (prefixWord ++ tailWord_2176139) baseStart_2176139 baseEnd_2176139 := by
    simpa [prefixWord, tailWord_2176139, baseEnd_2176139] using wordTrace_append hprefix tailTrace_2176139
  have hstable : (prefixWord ++ tailWord_2176139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176139).length < 2 ^ (prefixWord ++ tailWord_2176139).sum := by decide
  have hdescent : baseEnd_2176139 < baseStart_2176139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176162 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2176162 : Nat := 118140960795 + 2176162 * 2 ^ 59
def prefixEnd_2176162 : Nat := 4983230072969 + 3 ^ 40 * 2176162 * 2
def baseEnd_2176162 : Nat := 744944725366413326578013

theorem tailTrace_2176162 : CollatzResearch.WordTrace tailWord_2176162 prefixEnd_2176162 744944725366413326578013 := by
  unfold tailWord_2176162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19842787185536051931358685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52914099161429471816956493 19842787185536051931358685)
  ·
    refine ⟨7441045194576019474259507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19842787185536051931358685 7441045194576019474259507)
    ·
      refine ⟨11161567791864029211389261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7441045194576019474259507 11161567791864029211389261)
      ·
        refine ⟨4185587921949010954270973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11161567791864029211389261 4185587921949010954270973)
        ·
          refine ⟨1569595470730879107851615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4185587921949010954270973 1569595470730879107851615)
          ·
            refine ⟨2354393206096318661777423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569595470730879107851615 2354393206096318661777423)
            ·
              refine ⟨3531589809144477992666135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354393206096318661777423 3531589809144477992666135)
              ·
                refine ⟨5297384713716716988999203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3531589809144477992666135 5297384713716716988999203)
                ·
                  refine ⟨7946077070575075483498805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5297384713716716988999203 7946077070575075483498805)
                  ·
                    refine ⟨744944725366413326578013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7946077070575075483498805 744944725366413326578013)
                    ·
                      rfl

theorem cell22_2176162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2176162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176162 prefixEnd_2176162 := by exact prefixLift 2176162
  have htrace : WordTrace (prefixWord ++ tailWord_2176162) baseStart_2176162 baseEnd_2176162 := by
    simpa [prefixWord, tailWord_2176162, baseEnd_2176162] using wordTrace_append hprefix tailTrace_2176162
  have hstable : (prefixWord ++ tailWord_2176162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176162).length < 2 ^ (prefixWord ++ tailWord_2176162).sum := by decide
  have hdescent : baseEnd_2176162 < baseStart_2176162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176250 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_2176250 : Nat := 118140960795 + 2176250 * 2 ^ 59
def prefixEnd_2176250 : Nat := 4983230072969 + 3 ^ 40 * 2176250 * 2
def baseEnd_2176250 : Nat := 744974849564810430377743

theorem tailTrace_2176250 : CollatzResearch.WordTrace tailWord_2176250 prefixEnd_2176250 744974849564810430377743 := by
  unfold tailWord_2176250
  simp only [CollatzResearch.WordTrace]
  refine ⟨19843589591456349688659551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52916238910550265836425469 19843589591456349688659551)
  ·
    refine ⟨29765384387184524532989327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19843589591456349688659551 29765384387184524532989327)
    ·
      refine ⟨44648076580776786799483991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29765384387184524532989327 44648076580776786799483991)
      ·
        refine ⟨66972114871165180199225987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44648076580776786799483991 66972114871165180199225987)
        ·
          refine ⟨100458172306747770298838981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66972114871165180199225987 100458172306747770298838981)
          ·
            refine ⟨18835907307515206931032309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100458172306747770298838981 18835907307515206931032309)
            ·
              refine ⟨1765866310079550649784279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18835907307515206931032309 1765866310079550649784279)
              ·
                refine ⟨2648799465119325974676419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765866310079550649784279 2648799465119325974676419)
                ·
                  refine ⟨3973199197678988962014629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648799465119325974676419 3973199197678988962014629)
                  ·
                    refine ⟨744974849564810430377743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3973199197678988962014629 744974849564810430377743)
                    ·
                      rfl

theorem cell22_2176250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_2176250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176250 prefixEnd_2176250 := by exact prefixLift 2176250
  have htrace : WordTrace (prefixWord ++ tailWord_2176250) baseStart_2176250 baseEnd_2176250 := by
    simpa [prefixWord, tailWord_2176250, baseEnd_2176250] using wordTrace_append hprefix tailTrace_2176250
  have hstable : (prefixWord ++ tailWord_2176250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176250).length < 2 ^ (prefixWord ++ tailWord_2176250).sum := by decide
  have hdescent : baseEnd_2176250 < baseStart_2176250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176258 : List Nat := [3, 4, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2176258 : Nat := 118140960795 + 2176258 * 2 ^ 59
def prefixEnd_2176258 : Nat := 4983230072969 + 3 ^ 40 * 2176258 * 2
def baseEnd_2176258 : Nat := 744977588128301076177719

theorem tailTrace_2176258 : CollatzResearch.WordTrace tailWord_2176258 prefixEnd_2176258 744977588128301076177719 := by
  unfold tailWord_2176258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19843662537449104030232357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52916433433197610747286285 19843662537449104030232357)
  ·
    refine ⟨3720686725771707005668567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19843662537449104030232357 3720686725771707005668567)
    ·
      refine ⟨5581030088657560508502851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3720686725771707005668567 5581030088657560508502851)
      ·
        refine ⟨8371545132986340762754277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5581030088657560508502851 8371545132986340762754277)
        ·
          refine ⟨1569664712434938893016427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8371545132986340762754277 1569664712434938893016427)
          ·
            refine ⟨2354497068652408339524641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569664712434938893016427 2354497068652408339524641)
            ·
              refine ⟨1765872801489306254643481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2354497068652408339524641 1765872801489306254643481)
              ·
                refine ⟨1324404601116979690982611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1765872801489306254643481 1324404601116979690982611)
                ·
                  refine ⟨1986606901675469536473917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324404601116979690982611 1986606901675469536473917)
                  ·
                    refine ⟨744977588128301076177719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1986606901675469536473917 744977588128301076177719)
                    ·
                      rfl

theorem cell22_2176258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2176258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176258 prefixEnd_2176258 := by exact prefixLift 2176258
  have htrace : WordTrace (prefixWord ++ tailWord_2176258) baseStart_2176258 baseEnd_2176258 := by
    simpa [prefixWord, tailWord_2176258, baseEnd_2176258] using wordTrace_append hprefix tailTrace_2176258
  have hstable : (prefixWord ++ tailWord_2176258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176258).length < 2 ^ (prefixWord ++ tailWord_2176258).sum := by decide
  have hdescent : baseEnd_2176258 < baseStart_2176258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176280 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 2, 3]
def baseStart_2176280 : Nat := 118140960795 + 2176280 * 2 ^ 59
def prefixEnd_2176280 : Nat := 4983230072969 + 3 ^ 40 * 2176280 * 2
def baseEnd_2176280 : Nat := 744985119177900352127651

theorem tailTrace_2176280 : CollatzResearch.WordTrace tailWord_2176280 prefixEnd_2176280 744985119177900352127651 := by
  unfold tailWord_2176280
  simp only [CollatzResearch.WordTrace]
  refine ⟨39687726277858356939115147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52916968370477809252153529 39687726277858356939115147)
  ·
    refine ⟨59531589416787535408672721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39687726277858356939115147 59531589416787535408672721)
    ·
      refine ⟨44648692062590651556504541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59531589416787535408672721 44648692062590651556504541)
      ·
        refine ⟨16743259523471494333689203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44648692062590651556504541 16743259523471494333689203)
        ·
          refine ⟨25114889285207241500533805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16743259523471494333689203 25114889285207241500533805)
          ·
            refine ⟨9418083481952715562700177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25114889285207241500533805 9418083481952715562700177)
            ·
              refine ⟨7063562611464536672025133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9418083481952715562700177 7063562611464536672025133)
              ·
                refine ⟨2648835979299201252009425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7063562611464536672025133 2648835979299201252009425)
                ·
                  refine ⟨1986626984474400939007069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2648835979299201252009425 1986626984474400939007069)
                  ·
                    refine ⟨744985119177900352127651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1986626984474400939007069 744985119177900352127651)
                    ·
                      rfl

theorem cell22_2176280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_2176280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176280 prefixEnd_2176280 := by exact prefixLift 2176280
  have htrace : WordTrace (prefixWord ++ tailWord_2176280) baseStart_2176280 baseEnd_2176280 := by
    simpa [prefixWord, tailWord_2176280, baseEnd_2176280] using wordTrace_append hprefix tailTrace_2176280
  have hstable : (prefixWord ++ tailWord_2176280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176280).length < 2 ^ (prefixWord ++ tailWord_2176280).sum := by decide
  have hdescent : baseEnd_2176280 < baseStart_2176280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176415 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 1, 5]
def baseStart_2176415 : Nat := 118140960795 + 2176415 * 2 ^ 59
def prefixEnd_2176415 : Nat := 4983230072969 + 3 ^ 40 * 2176415 * 2
def baseEnd_2176415 : Nat := 745031332436805000002237

theorem tailTrace_2176415 : CollatzResearch.WordTrace tailWord_2176415 prefixEnd_2176415 745031332436805000002237 := by
  unfold tailWord_2176415
  simp only [CollatzResearch.WordTrace]
  refine ⟨79380376410227631934394699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52920250940151754622929799 79380376410227631934394699)
  ·
    refine ⟨119070564615341447901592049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79380376410227631934394699 119070564615341447901592049)
    ·
      refine ⟨89302923461506085926194037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119070564615341447901592049 89302923461506085926194037)
      ·
        refine ⟨8372149074516195555580691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89302923461506085926194037 8372149074516195555580691)
        ·
          refine ⟨12558223611774293333371037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8372149074516195555580691 12558223611774293333371037)
          ·
            refine ⟨4709333854415360000014139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12558223611774293333371037 4709333854415360000014139)
            ·
              refine ⟨7064000781623040000021209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4709333854415360000014139 7064000781623040000021209)
              ·
                refine ⟨5298000586217280000015907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7064000781623040000021209 5298000586217280000015907)
                ·
                  refine ⟨7947000879325920000023861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5298000586217280000015907 7947000879325920000023861)
                  ·
                    refine ⟨745031332436805000002237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7947000879325920000023861 745031332436805000002237)
                    ·
                      rfl

theorem cell22_2176415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_2176415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176415 prefixEnd_2176415 := by exact prefixLift 2176415
  have htrace : WordTrace (prefixWord ++ tailWord_2176415) baseStart_2176415 baseEnd_2176415 := by
    simpa [prefixWord, tailWord_2176415, baseEnd_2176415] using wordTrace_append hprefix tailTrace_2176415
  have hstable : (prefixWord ++ tailWord_2176415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176415).length < 2 ^ (prefixWord ++ tailWord_2176415).sum := by decide
  have hdescent : baseEnd_2176415 < baseStart_2176415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176494 : List Nat := [4, 1, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_2176494 : Nat := 118140960795 + 2176494 * 2 ^ 59
def prefixEnd_2176494 : Nat := 4983230072969 + 3 ^ 40 * 2176494 * 2
def baseEnd_2176494 : Nat := 745058375751275127276995

theorem tailTrace_2176494 : CollatzResearch.WordTrace tailWord_2176494 prefixEnd_2176494 745058375751275127276995 := by
  unfold tailWord_2176494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9922907222117678553315067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52922171851294285617680357 9922907222117678553315067)
  ·
    refine ⟨14884360833176517829972601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9922907222117678553315067 14884360833176517829972601)
    ·
      refine ⟨11163270624882388372479451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14884360833176517829972601 11163270624882388372479451)
      ·
        refine ⟨16744905937323582558719177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11163270624882388372479451 16744905937323582558719177)
        ·
          refine ⟨12558679452992686919039383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16744905937323582558719177 12558679452992686919039383)
          ·
            refine ⟨18838019179489030378559075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12558679452992686919039383 18838019179489030378559075)
            ·
              refine ⟨28257028769233545567838613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18838019179489030378559075 28257028769233545567838613)
              ·
                refine ⟨1324548223557822448492435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28257028769233545567838613 1324548223557822448492435)
                ·
                  refine ⟨1986822335336733672738653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324548223557822448492435 1986822335336733672738653)
                  ·
                    refine ⟨745058375751275127276995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1986822335336733672738653 745058375751275127276995)
                    ·
                      rfl

theorem cell22_2176494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_2176494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176494 prefixEnd_2176494 := by exact prefixLift 2176494
  have htrace : WordTrace (prefixWord ++ tailWord_2176494) baseStart_2176494 baseEnd_2176494 := by
    simpa [prefixWord, tailWord_2176494, baseEnd_2176494] using wordTrace_append hprefix tailTrace_2176494
  have hstable : (prefixWord ++ tailWord_2176494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176494).length < 2 ^ (prefixWord ++ tailWord_2176494).sum := by decide
  have hdescent : baseEnd_2176494 < baseStart_2176494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176503 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 2, 8]
def baseStart_2176503 : Nat := 118140960795 + 2176503 * 2 ^ 59
def prefixEnd_2176503 : Nat := 4983230072969 + 3 ^ 40 * 2176503 * 2
def baseEnd_2176503 : Nat := 745061456635202103801967

theorem tailTrace_2176503 : CollatzResearch.WordTrace tailWord_2176503 prefixEnd_2176503 745061456635202103801967 := by
  unfold tailWord_2176503
  simp only [CollatzResearch.WordTrace]
  refine ⟨79383586033908822963598163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52922390689272548642398775 79383586033908822963598163)
  ·
    refine ⟨119075379050863234445397245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79383586033908822963598163 119075379050863234445397245)
    ·
      refine ⟨44653267144073712917023967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119075379050863234445397245 44653267144073712917023967)
      ·
        refine ⟨66979900716110569375535951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44653267144073712917023967 66979900716110569375535951)
        ·
          refine ⟨100469851074165854063303927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66979900716110569375535951 100469851074165854063303927)
          ·
            refine ⟨150704776611248781094955891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100469851074165854063303927 150704776611248781094955891)
            ·
              refine ⟨226057164916873171642433837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150704776611248781094955891 226057164916873171642433837)
              ·
                refine ⟨84771436843827439365912689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226057164916873171642433837 84771436843827439365912689)
                ·
                  refine ⟨63578577632870579524434517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84771436843827439365912689 63578577632870579524434517)
                  ·
                    refine ⟨745061456635202103801967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63578577632870579524434517 745061456635202103801967)
                    ·
                      rfl

theorem cell22_2176503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_2176503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176503 prefixEnd_2176503 := by exact prefixLift 2176503
  have htrace : WordTrace (prefixWord ++ tailWord_2176503) baseStart_2176503 baseEnd_2176503 := by
    simpa [prefixWord, tailWord_2176503, baseEnd_2176503] using wordTrace_append hprefix tailTrace_2176503
  have hstable : (prefixWord ++ tailWord_2176503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176503).length < 2 ^ (prefixWord ++ tailWord_2176503).sum := by decide
  have hdescent : baseEnd_2176503 < baseStart_2176503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176520 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_2176520 : Nat := 118140960795 + 2176520 * 2 ^ 59
def prefixEnd_2176520 : Nat := 4983230072969 + 3 ^ 40 * 2176520 * 2
def baseEnd_2176520 : Nat := 745067276082619726126915

theorem tailTrace_2176520 : CollatzResearch.WordTrace tailWord_2176520 prefixEnd_2176520 745067276082619726126915 := by
  unfold tailWord_2176520
  simp only [CollatzResearch.WordTrace]
  refine ⟨39692103037423617433483507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52922804049898156577978009 39692103037423617433483507)
  ·
    refine ⟨59538154556135426150225261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39692103037423617433483507 59538154556135426150225261)
    ·
      refine ⟨22326807958550784806334473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59538154556135426150225261 22326807958550784806334473)
      ·
        refine ⟨16745105968913088604750855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22326807958550784806334473 16745105968913088604750855)
        ·
          refine ⟨25117658953369632907126283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16745105968913088604750855 25117658953369632907126283)
          ·
            refine ⟨37676488430054449360689425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25117658953369632907126283 37676488430054449360689425)
            ·
              refine ⟨28257366322540837020517069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37676488430054449360689425 28257366322540837020517069)
              ·
                refine ⟨10596512370952813882693901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28257366322540837020517069 10596512370952813882693901)
                ·
                  refine ⟨3973692139107305206010213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10596512370952813882693901 3973692139107305206010213)
                  ·
                    refine ⟨745067276082619726126915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3973692139107305206010213 745067276082619726126915)
                    ·
                      rfl

theorem cell22_2176520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_2176520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176520 prefixEnd_2176520 := by exact prefixLift 2176520
  have htrace : WordTrace (prefixWord ++ tailWord_2176520) baseStart_2176520 baseEnd_2176520 := by
    simpa [prefixWord, tailWord_2176520, baseEnd_2176520] using wordTrace_append hprefix tailTrace_2176520
  have hstable : (prefixWord ++ tailWord_2176520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176520).length < 2 ^ (prefixWord ++ tailWord_2176520).sum := by decide
  have hdescent : baseEnd_2176520 < baseStart_2176520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176629 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2176629 : Nat := 118140960795 + 2176629 * 2 ^ 59
def prefixEnd_2176629 : Nat := 4983230072969 + 3 ^ 40 * 2176629 * 2
def baseEnd_2176629 : Nat := 745104589010179775151581

theorem tailTrace_2176629 : CollatzResearch.WordTrace tailWord_2176629 prefixEnd_2176629 745104589010179775151581 := by
  unfold tailWord_2176629
  simp only [CollatzResearch.WordTrace]
  refine ⟨79388181631452346482684941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52925454420968230988456627 79388181631452346482684941)
  ·
    refine ⟨29770568111794629931006853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79388181631452346482684941 29770568111794629931006853)
    ·
      refine ⟨5581981520961493112063785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29770568111794629931006853 5581981520961493112063785)
      ·
        refine ⟨4186486140721119834047839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5581981520961493112063785 4186486140721119834047839)
        ·
          refine ⟨6279729211081679751071759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4186486140721119834047839 6279729211081679751071759)
          ·
            refine ⟨9419593816622519626607639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6279729211081679751071759 9419593816622519626607639)
            ·
              refine ⟨14129390724933779439911459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9419593816622519626607639 14129390724933779439911459)
              ·
                refine ⟨21194086087400669159867189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14129390724933779439911459 21194086087400669159867189)
                ·
                  refine ⟨1986945570693812733737549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21194086087400669159867189 1986945570693812733737549)
                  ·
                    refine ⟨745104589010179775151581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1986945570693812733737549 745104589010179775151581)
                    ·
                      rfl

theorem cell22_2176629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2176629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176629 prefixEnd_2176629 := by exact prefixLift 2176629
  have htrace : WordTrace (prefixWord ++ tailWord_2176629) baseStart_2176629 baseEnd_2176629 := by
    simpa [prefixWord, tailWord_2176629, baseEnd_2176629] using wordTrace_append hprefix tailTrace_2176629
  have hstable : (prefixWord ++ tailWord_2176629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176629).length < 2 ^ (prefixWord ++ tailWord_2176629).sum := by decide
  have hdescent : baseEnd_2176629 < baseStart_2176629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176640 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_2176640 : Nat := 118140960795 + 2176640 * 2 ^ 59
def prefixEnd_2176640 : Nat := 4983230072969 + 3 ^ 40 * 2176640 * 2
def baseEnd_2176640 : Nat := 745108354534979413126547

theorem tailTrace_2176640 : CollatzResearch.WordTrace tailWord_2176640 prefixEnd_2176640 745108354534979413126547 := by
  unfold tailWord_2176640
  simp only [CollatzResearch.WordTrace]
  refine ⟨39694291417206247680667687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52925721889608330240890249 39694291417206247680667687)
  ·
    refine ⟨59541437125809371521001531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39694291417206247680667687 59541437125809371521001531)
    ·
      refine ⟨89312155688714057281502297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59541437125809371521001531 89312155688714057281502297)
      ·
        refine ⟨66984116766535542961126723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89312155688714057281502297 66984116766535542961126723)
        ·
          refine ⟨100476175149803314441690085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66984116766535542961126723 100476175149803314441690085)
          ·
            refine ⟨18839282840588121457816891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100476175149803314441690085 18839282840588121457816891)
            ·
              refine ⟨28258924260882182186725337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18839282840588121457816891 28258924260882182186725337)
              ·
                refine ⟨21194193195661636640044003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28258924260882182186725337 21194193195661636640044003)
                ·
                  refine ⟨31791289793492454960066005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21194193195661636640044003 31791289793492454960066005)
                  ·
                    refine ⟨745108354534979413126547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31791289793492454960066005 745108354534979413126547)
                    ·
                      rfl

theorem cell22_2176640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_2176640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176640 prefixEnd_2176640 := by exact prefixLift 2176640
  have htrace : WordTrace (prefixWord ++ tailWord_2176640) baseStart_2176640 baseEnd_2176640 := by
    simpa [prefixWord, tailWord_2176640, baseEnd_2176640] using wordTrace_append hprefix tailTrace_2176640
  have hstable : (prefixWord ++ tailWord_2176640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176640).length < 2 ^ (prefixWord ++ tailWord_2176640).sum := by decide
  have hdescent : baseEnd_2176640 < baseStart_2176640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176721 : List Nat := [1, 2, 2, 1, 2, 5, 3, 2, 4]
def baseStart_2176721 : Nat := 118140960795 + 2176721 * 2 ^ 59
def prefixEnd_2176721 : Nat := 4983230072969 + 3 ^ 40 * 2176721 * 2
def baseEnd_2176721 : Nat := 248378694163440733950433

theorem tailTrace_2176721 : CollatzResearch.WordTrace tailWord_2176721 prefixEnd_2176721 248378694163440733950433 := by
  unfold tailWord_2176721
  simp only [CollatzResearch.WordTrace]
  refine ⟨79391537147119046195034017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52927691431412697463356011 79391537147119046195034017)
  ·
    refine ⟨59543652860339284646275513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79391537147119046195034017 59543652860339284646275513)
    ·
      refine ⟨44657739645254463484706635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59543652860339284646275513 44657739645254463484706635)
      ·
        refine ⟨66986609467881695227059953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44657739645254463484706635 66986609467881695227059953)
        ·
          refine ⟨50239957100911271420294965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66986609467881695227059953 50239957100911271420294965)
          ·
            refine ⟨4709995978210431695652653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50239957100911271420294965 4709995978210431695652653)
            ·
              refine ⟨1766248491828911885869745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4709995978210431695652653 1766248491828911885869745)
              ·
                refine ⟨1324686368871683914402309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766248491828911885869745 1324686368871683914402309)
                ·
                  refine ⟨248378694163440733950433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324686368871683914402309 248378694163440733950433)
                  ·
                    rfl

theorem cell22_2176721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 4].length) (baseStart_2176721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176721 prefixEnd_2176721 := by exact prefixLift 2176721
  have htrace : WordTrace (prefixWord ++ tailWord_2176721) baseStart_2176721 baseEnd_2176721 := by
    simpa [prefixWord, tailWord_2176721, baseEnd_2176721] using wordTrace_append hprefix tailTrace_2176721
  have hstable : (prefixWord ++ tailWord_2176721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176721).length < 2 ^ (prefixWord ++ tailWord_2176721).sum := by decide
  have hdescent : baseEnd_2176721 < baseStart_2176721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176736 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 2, 3]
def baseStart_2176736 : Nat := 118140960795 + 2176736 * 2 ^ 59
def prefixEnd_2176736 : Nat := 4983230072969 + 3 ^ 40 * 2176736 * 2
def baseEnd_2176736 : Nat := 745141217296867162726253

theorem tailTrace_2176736 : CollatzResearch.WordTrace tailWord_2176736 prefixEnd_2176736 745141217296867162726253 := by
  unfold tailWord_2176736
  simp only [CollatzResearch.WordTrace]
  refine ⟨39696042121032351878415031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52928056161376469171220041 39696042121032351878415031)
  ·
    refine ⟨59544063181548527817622547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39696042121032351878415031 59544063181548527817622547)
    ·
      refine ⟨89316094772322791726433821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59544063181548527817622547 89316094772322791726433821)
      ·
        refine ⟨33493535539621046897412683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89316094772322791726433821 33493535539621046897412683)
        ·
          refine ⟨50240303309431570346119025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33493535539621046897412683 50240303309431570346119025)
          ·
            refine ⟨37680227482073677759589269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50240303309431570346119025 37680227482073677759589269)
            ·
              refine ⟨1766260663222203644980747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37680227482073677759589269 1766260663222203644980747)
              ·
                refine ⟨2649390994833305467471121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766260663222203644980747 2649390994833305467471121)
                ·
                  refine ⟨1987043246124979100603341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2649390994833305467471121 1987043246124979100603341)
                  ·
                    refine ⟨745141217296867162726253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1987043246124979100603341 745141217296867162726253)
                    ·
                      rfl

theorem cell22_2176736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 2, 3].length) (baseStart_2176736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176736 prefixEnd_2176736 := by exact prefixLift 2176736
  have htrace : WordTrace (prefixWord ++ tailWord_2176736) baseStart_2176736 baseEnd_2176736 := by
    simpa [prefixWord, tailWord_2176736, baseEnd_2176736] using wordTrace_append hprefix tailTrace_2176736
  have hstable : (prefixWord ++ tailWord_2176736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176736).length < 2 ^ (prefixWord ++ tailWord_2176736).sum := by decide
  have hdescent : baseEnd_2176736 < baseStart_2176736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176792 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_2176792 : Nat := 118140960795 + 2176792 * 2 ^ 59
def prefixEnd_2176792 : Nat := 4983230072969 + 3 ^ 40 * 2176792 * 2
def baseEnd_2176792 : Nat := 745160387241301683326081

theorem tailTrace_2176792 : CollatzResearch.WordTrace tailWord_2176792 prefixEnd_2176792 745160387241301683326081 := by
  unfold tailWord_2176792
  simp only [CollatzResearch.WordTrace]
  refine ⟨39697063364930912660434315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52929417819907883547245753 39697063364930912660434315)
  ·
    refine ⟨59545595047396368990651473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39697063364930912660434315 59545595047396368990651473)
    ·
      refine ⟨44659196285547276742988605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59545595047396368990651473 44659196285547276742988605)
      ·
        refine ⟨16747198607080228778620727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44659196285547276742988605 16747198607080228778620727)
        ·
          refine ⟨25120797910620343167931091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16747198607080228778620727 25120797910620343167931091)
          ·
            refine ⟨37681196865930514751896637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25120797910620343167931091 37681196865930514751896637)
            ·
              refine ⟨14130448824723943031961239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37681196865930514751896637 14130448824723943031961239)
              ·
                refine ⟨21195673237085914547941859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14130448824723943031961239 21195673237085914547941859)
                ·
                  refine ⟨31793509855628871821912789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21195673237085914547941859 31793509855628871821912789)
                  ·
                    refine ⟨745160387241301683326081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31793509855628871821912789 745160387241301683326081)
                    ·
                      rfl

theorem cell22_2176792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_2176792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176792 prefixEnd_2176792 := by exact prefixLift 2176792
  have htrace : WordTrace (prefixWord ++ tailWord_2176792) baseStart_2176792 baseEnd_2176792 := by
    simpa [prefixWord, tailWord_2176792, baseEnd_2176792] using wordTrace_append hprefix tailTrace_2176792
  have hstable : (prefixWord ++ tailWord_2176792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176792).length < 2 ^ (prefixWord ++ tailWord_2176792).sum := by decide
  have hdescent : baseEnd_2176792 < baseStart_2176792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176794 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_2176794 : Nat := 118140960795 + 2176794 * 2 ^ 59
def prefixEnd_2176794 : Nat := 4983230072969 + 3 ^ 40 * 2176794 * 2
def baseEnd_2176794 : Nat := 248387023960724781592025

theorem tailTrace_2176794 : CollatzResearch.WordTrace tailWord_2176794 prefixEnd_2176794 248387023960724781592025 := by
  unfold tailWord_2176794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19848549918963644915610359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52929466450569719774960957 19848549918963644915610359)
  ·
    refine ⟨29772824878445467373415539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19848549918963644915610359 29772824878445467373415539)
    ·
      refine ⟨44659237317668201060123309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29772824878445467373415539 44659237317668201060123309)
      ·
        refine ⟨16747213994125575397546241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44659237317668201060123309 16747213994125575397546241)
        ·
          refine ⟨12560410495594181548159681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16747213994125575397546241 12560410495594181548159681)
          ·
            refine ⟨9420307871695636161119761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12560410495594181548159681 9420307871695636161119761)
            ·
              refine ⟨7065230903771727120839821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9420307871695636161119761 7065230903771727120839821)
              ·
                refine ⟨2649461588914397670314933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7065230903771727120839821 2649461588914397670314933)
                ·
                  refine ⟨248387023960724781592025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2649461588914397670314933 248387023960724781592025)
                  ·
                    rfl

theorem cell22_2176794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_2176794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176794 prefixEnd_2176794 := by exact prefixLift 2176794
  have htrace : WordTrace (prefixWord ++ tailWord_2176794) baseStart_2176794 baseEnd_2176794 := by
    simpa [prefixWord, tailWord_2176794, baseEnd_2176794] using wordTrace_append hprefix tailTrace_2176794
  have hstable : (prefixWord ++ tailWord_2176794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176794).length < 2 ^ (prefixWord ++ tailWord_2176794).sum := by decide
  have hdescent : baseEnd_2176794 < baseStart_2176794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176869 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_2176869 : Nat := 118140960795 + 2176869 * 2 ^ 59
def prefixEnd_2176869 : Nat := 4983230072969 + 3 ^ 40 * 2176869 * 2
def baseEnd_2176869 : Nat := 745186745914899149150845

theorem tailTrace_2176869 : CollatzResearch.WordTrace tailWord_2176869 prefixEnd_2176869 745186745914899149150845 := by
  unfold tailWord_2176869
  simp only [CollatzResearch.WordTrace]
  refine ⟨79396935150582867471421661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52931290100388578314281107 79396935150582867471421661)
  ·
    refine ⟨29773850681468575301783123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79396935150582867471421661 29773850681468575301783123)
    ·
      refine ⟨44660776022202862952674685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29773850681468575301783123 44660776022202862952674685)
      ·
        refine ⟨16747791008326073607253007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44660776022202862952674685 16747791008326073607253007)
        ·
          refine ⟨25121686512489110410879511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16747791008326073607253007 25121686512489110410879511)
          ·
            refine ⟨37682529768733665616319267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25121686512489110410879511 37682529768733665616319267)
            ·
              refine ⟨56523794653100498424478901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37682529768733665616319267 56523794653100498424478901)
              ·
                refine ⟨5299105748728171727294897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56523794653100498424478901 5299105748728171727294897)
                ·
                  refine ⟨3974329311546128795471173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5299105748728171727294897 3974329311546128795471173)
                  ·
                    refine ⟨745186745914899149150845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3974329311546128795471173 745186745914899149150845)
                    ·
                      rfl

theorem cell22_2176869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_2176869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176869 prefixEnd_2176869 := by exact prefixLift 2176869
  have htrace : WordTrace (prefixWord ++ tailWord_2176869) baseStart_2176869 baseEnd_2176869 := by
    simpa [prefixWord, tailWord_2176869, baseEnd_2176869] using wordTrace_append hprefix tailTrace_2176869
  have hstable : (prefixWord ++ tailWord_2176869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176869).length < 2 ^ (prefixWord ++ tailWord_2176869).sum := by decide
  have hdescent : baseEnd_2176869 < baseStart_2176869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176959 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 5, 4]
def baseStart_2176959 : Nat := 118140960795 + 2176959 * 2 ^ 59
def prefixEnd_2176959 : Nat := 4983230072969 + 3 ^ 40 * 2176959 * 2
def baseEnd_2176959 : Nat := 745217554754168914400569

theorem tailTrace_2176959 : CollatzResearch.WordTrace tailWord_2176959 prefixEnd_2176959 745217554754168914400569 := by
  unfold tailWord_2176959
  simp only [CollatzResearch.WordTrace]
  refine ⟨79400217720256812842197931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52933478480171208561465287 79400217720256812842197931)
  ·
    refine ⟨119100326580385219263296897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79400217720256812842197931 119100326580385219263296897)
    ·
      refine ⟨89325244935288914447472673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119100326580385219263296897 89325244935288914447472673)
      ·
        refine ⟨66993933701466685835604505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89325244935288914447472673 66993933701466685835604505)
        ·
          refine ⟨50245450276100014376703379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66993933701466685835604505 50245450276100014376703379)
          ·
            refine ⟨75368175414150021565055069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50245450276100014376703379 75368175414150021565055069)
            ·
              refine ⟨28263065780306258086895651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75368175414150021565055069 28263065780306258086895651)
              ·
                refine ⟨42394598670459387130343477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28263065780306258086895651 42394598670459387130343477)
                ·
                  refine ⟨3974493625355567543469701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42394598670459387130343477 3974493625355567543469701)
                  ·
                    refine ⟨745217554754168914400569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3974493625355567543469701 745217554754168914400569)
                    ·
                      rfl

theorem cell22_2176959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_2176959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176959 prefixEnd_2176959 := by exact prefixLift 2176959
  have htrace : WordTrace (prefixWord ++ tailWord_2176959) baseStart_2176959 baseEnd_2176959 := by
    simpa [prefixWord, tailWord_2176959, baseEnd_2176959] using wordTrace_append hprefix tailTrace_2176959
  have hstable : (prefixWord ++ tailWord_2176959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176959).length < 2 ^ (prefixWord ++ tailWord_2176959).sum := by decide
  have hdescent : baseEnd_2176959 < baseStart_2176959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2176993 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 1, 4]
def baseStart_2176993 : Nat := 118140960795 + 2176993 * 2 ^ 59
def prefixEnd_2176993 : Nat := 4983230072969 + 3 ^ 40 * 2176993 * 2
def baseEnd_2176993 : Nat := 745229193649004159050465

theorem tailTrace_2176993 : CollatzResearch.WordTrace tailWord_2176993 prefixEnd_2176993 745229193649004159050465 := by
  unfold tailWord_2176993
  simp only [CollatzResearch.WordTrace]
  refine ⟨79401457802133636648935633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52934305201422424432623755 79401457802133636648935633)
  ·
    refine ⟨59551093351600227486701725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79401457802133636648935633 59551093351600227486701725)
    ·
      refine ⟨22331660006850085307513147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59551093351600227486701725 22331660006850085307513147)
      ·
        refine ⟨33497490010275127961269721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22331660006850085307513147 33497490010275127961269721)
        ·
          refine ⟨25123117507706345970952291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33497490010275127961269721 25123117507706345970952291)
          ·
            refine ⟨37684676261559518956428437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25123117507706345970952291 37684676261559518956428437)
            ·
              refine ⟨1766469199760602451082583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37684676261559518956428437 1766469199760602451082583)
              ·
                refine ⟨2649703799640903676623875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766469199760602451082583 2649703799640903676623875)
                ·
                  refine ⟨3974555699461355514935813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649703799640903676623875 3974555699461355514935813)
                  ·
                    refine ⟨745229193649004159050465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3974555699461355514935813 745229193649004159050465)
                    ·
                      rfl

theorem cell22_2176993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_2176993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2176993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2176993 prefixEnd_2176993 := by exact prefixLift 2176993
  have htrace : WordTrace (prefixWord ++ tailWord_2176993) baseStart_2176993 baseEnd_2176993 := by
    simpa [prefixWord, tailWord_2176993, baseEnd_2176993] using wordTrace_append hprefix tailTrace_2176993
  have hstable : (prefixWord ++ tailWord_2176993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2176993).length < 2 ^ (prefixWord ++ tailWord_2176993).sum := by decide
  have hdescent : baseEnd_2176993 < baseStart_2176993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2176993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177049 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_2177049 : Nat := 118140960795 + 2177049 * 2 ^ 59
def prefixEnd_2177049 : Nat := 4983230072969 + 3 ^ 40 * 2177049 * 2
def baseEnd_2177049 : Nat := 745248363593438679650293

theorem tailTrace_2177049 : CollatzResearch.WordTrace tailWord_2177049 prefixEnd_2177049 745248363593438679650293 := by
  unfold tailWord_2177049
  simp only [CollatzResearch.WordTrace]
  refine ⟨79403500289930758212974201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52935666859953838808649467 79403500289930758212974201)
  ·
    refine ⟨59552625217448068659730651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79403500289930758212974201 59552625217448068659730651)
    ·
      refine ⟨89328937826172102989595977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59552625217448068659730651 89328937826172102989595977)
      ·
        refine ⟨66996703369629077242196983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89328937826172102989595977 66996703369629077242196983)
        ·
          refine ⟨100495055054443615863295475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66996703369629077242196983 100495055054443615863295475)
          ·
            refine ⟨150742582581665423794943213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100495055054443615863295475 150742582581665423794943213)
            ·
              refine ⟨56528468468124533923103705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150742582581665423794943213 56528468468124533923103705)
              ·
                refine ⟨42396351351093400442327779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56528468468124533923103705 42396351351093400442327779)
                ·
                  refine ⟨63594527026640100663491669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42396351351093400442327779 63594527026640100663491669)
                  ·
                    refine ⟨745248363593438679650293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63594527026640100663491669 745248363593438679650293)
                    ·
                      rfl

theorem cell22_2177049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_2177049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177049 prefixEnd_2177049 := by exact prefixLift 2177049
  have htrace : WordTrace (prefixWord ++ tailWord_2177049) baseStart_2177049 baseEnd_2177049 := by
    simpa [prefixWord, tailWord_2177049, baseEnd_2177049] using wordTrace_append hprefix tailTrace_2177049
  have hstable : (prefixWord ++ tailWord_2177049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177049).length < 2 ^ (prefixWord ++ tailWord_2177049).sum := by decide
  have hdescent : baseEnd_2177049 < baseStart_2177049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177160 : List Nat := [2, 1, 3, 4, 1, 1, 1, 5, 4]
def baseStart_2177160 : Nat := 118140960795 + 2177160 * 2 ^ 59
def prefixEnd_2177160 : Nat := 4983230072969 + 3 ^ 40 * 2177160 * 2
def baseEnd_2177160 : Nat := 248428787053957130041651

theorem tailTrace_2177160 : CollatzResearch.WordTrace tailWord_2177160 prefixEnd_2177160 248428787053957130041651 := by
  unfold tailWord_2177160
  simp only [CollatzResearch.WordTrace]
  refine ⟨39703774396264312085132467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52938365861685749446843289 39703774396264312085132467)
  ·
    refine ⟨59555661594396468127698701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39703774396264312085132467 59555661594396468127698701)
    ·
      refine ⟨22333373097898675547887013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59555661594396468127698701 22333373097898675547887013)
      ·
        refine ⟨4187507455856001665228815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22333373097898675547887013 4187507455856001665228815)
        ·
          refine ⟨6281261183784002497843223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4187507455856001665228815 6281261183784002497843223)
          ·
            refine ⟨9421891775676003746764835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6281261183784002497843223 9421891775676003746764835)
            ·
              refine ⟨14132837663514005620147253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9421891775676003746764835 14132837663514005620147253)
              ·
                refine ⟨1324953530954438026888805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14132837663514005620147253 1324953530954438026888805)
                ·
                  refine ⟨248428787053957130041651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1324953530954438026888805 248428787053957130041651)
                  ·
                    rfl

theorem cell22_2177160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 4].length) (baseStart_2177160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177160 prefixEnd_2177160 := by exact prefixLift 2177160
  have htrace : WordTrace (prefixWord ++ tailWord_2177160) baseStart_2177160 baseEnd_2177160 := by
    simpa [prefixWord, tailWord_2177160, baseEnd_2177160] using wordTrace_append hprefix tailTrace_2177160
  have hstable : (prefixWord ++ tailWord_2177160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177160).length < 2 ^ (prefixWord ++ tailWord_2177160).sum := by decide
  have hdescent : baseEnd_2177160 < baseStart_2177160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177162 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_2177162 : Nat := 118140960795 + 2177162 * 2 ^ 59
def prefixEnd_2177162 : Nat := 4983230072969 + 3 ^ 40 * 2177162 * 2
def baseEnd_2177162 : Nat := 745287045802744051574947

theorem tailTrace_2177162 : CollatzResearch.WordTrace tailWord_2177162 prefixEnd_2177162 745287045802744051574947 := by
  unfold tailWord_2177162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19851905434630344627959435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52938414492347585674558493 19851905434630344627959435)
  ·
    refine ⟨29777858151945516941939153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19851905434630344627959435 29777858151945516941939153)
    ·
      refine ⟨22333393613959137706454365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29777858151945516941939153 22333393613959137706454365)
      ·
        refine ⟨8375022605234676639920387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22333393613959137706454365 8375022605234676639920387)
        ·
          refine ⟨12562533907852014959880581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8375022605234676639920387 12562533907852014959880581)
          ·
            refine ⟨2355475107722252804977609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12562533907852014959880581 2355475107722252804977609)
            ·
              refine ⟨1766606330791689603733207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355475107722252804977609 1766606330791689603733207)
              ·
                refine ⟨2649909496187534405599811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766606330791689603733207 2649909496187534405599811)
                ·
                  refine ⟨3974864244281301608399717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649909496187534405599811 3974864244281301608399717)
                  ·
                    refine ⟨745287045802744051574947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3974864244281301608399717 745287045802744051574947)
                    ·
                      rfl

theorem cell22_2177162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_2177162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177162 prefixEnd_2177162 := by exact prefixLift 2177162
  have htrace : WordTrace (prefixWord ++ tailWord_2177162) baseStart_2177162 baseEnd_2177162 := by
    simpa [prefixWord, tailWord_2177162, baseEnd_2177162] using wordTrace_append hprefix tailTrace_2177162
  have hstable : (prefixWord ++ tailWord_2177162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177162).length < 2 ^ (prefixWord ++ tailWord_2177162).sum := by decide
  have hdescent : baseEnd_2177162 < baseStart_2177162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177175 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 4, 3]
def baseStart_2177175 : Nat := 118140960795 + 2177175 * 2 ^ 59
def prefixEnd_2177175 : Nat := 4983230072969 + 3 ^ 40 * 2177175 * 2
def baseEnd_2177175 : Nat := 745291495968416350999907

theorem tailTrace_2177175 : CollatzResearch.WordTrace tailWord_2177175 prefixEnd_2177175 745291495968416350999907 := by
  unfold tailWord_2177175
  simp only [CollatzResearch.WordTrace]
  refine ⟨79408095887474281732060979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52938730591649521154707319 79408095887474281732060979)
  ·
    refine ⟨119112143831211422598091469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79408095887474281732060979 119112143831211422598091469)
    ·
      refine ⟨44667053936704283474284301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119112143831211422598091469 44667053936704283474284301)
      ·
        refine ⟨16750145226264106302856613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44667053936704283474284301 16750145226264106302856613)
        ·
          refine ⟨3140652229924519931785615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16750145226264106302856613 3140652229924519931785615)
          ·
            refine ⟨4710978344886779897678423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140652229924519931785615 4710978344886779897678423)
            ·
              refine ⟨7066467517330169846517635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4710978344886779897678423 7066467517330169846517635)
              ·
                refine ⟨10599701275995254769776453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7066467517330169846517635 10599701275995254769776453)
                ·
                  refine ⟨1987443989249110269333085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10599701275995254769776453 1987443989249110269333085)
                  ·
                    refine ⟨745291495968416350999907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1987443989249110269333085 745291495968416350999907)
                    ·
                      rfl

theorem cell22_2177175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_2177175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177175 prefixEnd_2177175 := by exact prefixLift 2177175
  have htrace : WordTrace (prefixWord ++ tailWord_2177175) baseStart_2177175 baseEnd_2177175 := by
    simpa [prefixWord, tailWord_2177175, baseEnd_2177175] using wordTrace_append hprefix tailTrace_2177175
  have hstable : (prefixWord ++ tailWord_2177175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177175).length < 2 ^ (prefixWord ++ tailWord_2177175).sum := by decide
  have hdescent : baseEnd_2177175 < baseStart_2177175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177205 : List Nat := [1, 3, 3, 4, 1, 1, 1, 8]
def baseStart_2177205 : Nat := 118140960795 + 2177205 * 2 ^ 59
def prefixEnd_2177205 : Nat := 4983230072969 + 3 ^ 40 * 2177205 * 2
def baseEnd_2177205 : Nat := 82811307286834030305535

theorem tailTrace_2177205 : CollatzResearch.WordTrace tailWord_2177205 prefixEnd_2177205 82811307286834030305535 := by
  unfold tailWord_2177205
  simp only [CollatzResearch.WordTrace]
  refine ⟨79409190077365596855653069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52939460051577064570435379 79409190077365596855653069)
  ·
    refine ⟨29778446279012098820869901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79409190077365596855653069 29778446279012098820869901)
    ·
      refine ⟨11166917354629537057826213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29778446279012098820869901 11166917354629537057826213)
      ·
        refine ⟨2093797003993038198342415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11166917354629537057826213 2093797003993038198342415)
        ·
          refine ⟨3140695505989557297513623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093797003993038198342415 3140695505989557297513623)
          ·
            refine ⟨4711043258984335946270435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140695505989557297513623 4711043258984335946270435)
            ·
              refine ⟨7066564888476503919405653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711043258984335946270435 7066564888476503919405653)
              ·
                refine ⟨82811307286834030305535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7066564888476503919405653 82811307286834030305535)
                ·
                  rfl

theorem cell22_2177205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 8].length) (baseStart_2177205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177205 prefixEnd_2177205 := by exact prefixLift 2177205
  have htrace : WordTrace (prefixWord ++ tailWord_2177205) baseStart_2177205 baseEnd_2177205 := by
    simpa [prefixWord, tailWord_2177205, baseEnd_2177205] using wordTrace_append hprefix tailTrace_2177205
  have hstable : (prefixWord ++ tailWord_2177205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177205).length < 2 ^ (prefixWord ++ tailWord_2177205).sum := by decide
  have hdescent : baseEnd_2177205 < baseStart_2177205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177308 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2177308 : Nat := 118140960795 + 2177308 * 2 ^ 59
def prefixEnd_2177308 : Nat := 4983230072969 + 3 ^ 40 * 2177308 * 2
def baseEnd_2177308 : Nat := 745337024586448337424499

theorem tailTrace_2177308 : CollatzResearch.WordTrace tailWord_2177308 prefixEnd_2177308 745337024586448337424499 := by
  unfold tailWord_2177308
  simp only [CollatzResearch.WordTrace]
  refine ⟨39706473397996222723326289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52941964530661630297768385 39706473397996222723326289)
  ·
    refine ⟨29779855048497167042494717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39706473397996222723326289 29779855048497167042494717)
    ·
      refine ⟨11167445643186437640935519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29779855048497167042494717 11167445643186437640935519)
      ·
        refine ⟨16751168464779656461403279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11167445643186437640935519 16751168464779656461403279)
        ·
          refine ⟨25126752697169484692104919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16751168464779656461403279 25126752697169484692104919)
          ·
            refine ⟨37690129045754227038157379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25126752697169484692104919 37690129045754227038157379)
            ·
              refine ⟨56535193568631340557236069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37690129045754227038157379 56535193568631340557236069)
              ·
                refine ⟨10600348794118376354481763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56535193568631340557236069 10600348794118376354481763)
                ·
                  refine ⟨15900523191177564531722645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10600348794118376354481763 15900523191177564531722645)
                  ·
                    refine ⟨745337024586448337424499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15900523191177564531722645 745337024586448337424499)
                    ·
                      rfl

theorem cell22_2177308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2177308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177308 prefixEnd_2177308 := by exact prefixLift 2177308
  have htrace : WordTrace (prefixWord ++ tailWord_2177308) baseStart_2177308 baseEnd_2177308 := by
    simpa [prefixWord, tailWord_2177308, baseEnd_2177308] using wordTrace_append hprefix tailTrace_2177308
  have hstable : (prefixWord ++ tailWord_2177308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177308).length < 2 ^ (prefixWord ++ tailWord_2177308).sum := by decide
  have hdescent : baseEnd_2177308 < baseStart_2177308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177415 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 3, 4]
def baseStart_2177415 : Nat := 118140960795 + 2177415 * 2 ^ 59
def prefixEnd_2177415 : Nat := 4983230072969 + 3 ^ 40 * 2177415 * 2
def baseEnd_2177415 : Nat := 745373652873135724999171

theorem tailTrace_2177415 : CollatzResearch.WordTrace tailWord_2177415 prefixEnd_2177415 745373652873135724999171 := by
  unfold tailWord_2177415
  simp only [CollatzResearch.WordTrace]
  refine ⟨79416849406604802720797699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52944566271069868480531799 79416849406604802720797699)
  ·
    refine ⟨119125274109907204081196549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79416849406604802720797699 119125274109907204081196549)
    ·
      refine ⟨22335988895607600765224353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119125274109907204081196549 22335988895607600765224353)
      ·
        refine ⟨16751991671705700573918265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22335988895607600765224353 16751991671705700573918265)
        ·
          refine ⟨12563993753779275430438699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16751991671705700573918265 12563993753779275430438699)
          ·
            refine ⟨18845990630668913145658049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12563993753779275430438699 18845990630668913145658049)
            ·
              refine ⟨14134492973001684859243537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18845990630668913145658049 14134492973001684859243537)
              ·
                refine ⟨10600869729751263644432653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14134492973001684859243537 10600869729751263644432653)
                ·
                  refine ⟨3975326148656723866662245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10600869729751263644432653 3975326148656723866662245)
                  ·
                    refine ⟨745373652873135724999171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3975326148656723866662245 745373652873135724999171)
                    ·
                      rfl

theorem cell22_2177415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_2177415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177415 prefixEnd_2177415 := by exact prefixLift 2177415
  have htrace : WordTrace (prefixWord ++ tailWord_2177415) baseStart_2177415 baseEnd_2177415 := by
    simpa [prefixWord, tailWord_2177415, baseEnd_2177415] using wordTrace_append hprefix tailTrace_2177415
  have hstable : (prefixWord ++ tailWord_2177415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177415).length < 2 ^ (prefixWord ++ tailWord_2177415).sum := by decide
  have hdescent : baseEnd_2177415 < baseStart_2177415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177432 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_2177432 : Nat := 118140960795 + 2177432 * 2 ^ 59
def prefixEnd_2177432 : Nat := 4983230072969 + 3 ^ 40 * 2177432 * 2
def baseEnd_2177432 : Nat := 745379472320553347324119

theorem tailTrace_2177432 : CollatzResearch.WordTrace tailWord_2177432 prefixEnd_2177432 745379472320553347324119 := by
  unfold tailWord_2177432
  simp only [CollatzResearch.WordTrace]
  refine ⟨39708734723771607312083275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52944979631695476416111033 39708734723771607312083275)
  ·
    refine ⟨59563102085657410968124913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39708734723771607312083275 59563102085657410968124913)
    ·
      refine ⟨44672326564243058226093685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59563102085657410968124913 44672326564243058226093685)
      ·
        refine ⟨4188030615397786708696283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44672326564243058226093685 4188030615397786708696283)
        ·
          refine ⟨6282045923096680063044425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4188030615397786708696283 6282045923096680063044425)
          ·
            refine ⟨4711534442322510047283319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6282045923096680063044425 4711534442322510047283319)
            ·
              refine ⟨7067301663483765070924979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711534442322510047283319 7067301663483765070924979)
              ·
                refine ⟨10600952495225647606387469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067301663483765070924979 10600952495225647606387469)
                ·
                  refine ⟨3975357185709617852395301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10600952495225647606387469 3975357185709617852395301)
                  ·
                    refine ⟨745379472320553347324119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3975357185709617852395301 745379472320553347324119)
                    ·
                      rfl

theorem cell22_2177432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_2177432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177432 prefixEnd_2177432 := by exact prefixLift 2177432
  have htrace : WordTrace (prefixWord ++ tailWord_2177432) baseStart_2177432 baseEnd_2177432 := by
    simpa [prefixWord, tailWord_2177432, baseEnd_2177432] using wordTrace_append hprefix tailTrace_2177432
  have hstable : (prefixWord ++ tailWord_2177432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177432).length < 2 ^ (prefixWord ++ tailWord_2177432).sum := by decide
  have hdescent : baseEnd_2177432 < baseStart_2177432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177445 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_2177445 : Nat := 118140960795 + 2177445 * 2 ^ 59
def prefixEnd_2177445 : Nat := 4983230072969 + 3 ^ 40 * 2177445 * 2
def baseEnd_2177445 : Nat := 745383922486225646749079

theorem tailTrace_2177445 : CollatzResearch.WordTrace tailWord_2177445 prefixEnd_2177445 745383922486225646749079 := by
  unfold tailWord_2177445
  simp only [CollatzResearch.WordTrace]
  refine ⟨79417943596496117844389789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52945295730997411896259859 79417943596496117844389789)
  ·
    refine ⟨29781728848686044191646171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79417943596496117844389789 29781728848686044191646171)
    ·
      refine ⟨44672593273029066287469257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29781728848686044191646171 44672593273029066287469257)
      ·
        refine ⟨33504444954771799715601943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44672593273029066287469257 33504444954771799715601943)
        ·
          refine ⟨50256667432157699573402915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33504444954771799715601943 50256667432157699573402915)
          ·
            refine ⟨75385001148236549360104373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50256667432157699573402915 75385001148236549360104373)
            ·
              refine ⟨7067343857647176502509785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75385001148236549360104373 7067343857647176502509785)
              ·
                refine ⟨5300507893235382376882339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7067343857647176502509785 5300507893235382376882339)
                ·
                  refine ⟨7950761839853073565323509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5300507893235382376882339 7950761839853073565323509)
                  ·
                    refine ⟨745383922486225646749079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7950761839853073565323509 745383922486225646749079)
                    ·
                      rfl

theorem cell22_2177445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_2177445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177445 prefixEnd_2177445 := by exact prefixLift 2177445
  have htrace : WordTrace (prefixWord ++ tailWord_2177445) baseStart_2177445 baseEnd_2177445 := by
    simpa [prefixWord, tailWord_2177445, baseEnd_2177445] using wordTrace_append hprefix tailTrace_2177445
  have hstable : (prefixWord ++ tailWord_2177445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177445).length < 2 ^ (prefixWord ++ tailWord_2177445).sum := by decide
  have hdescent : baseEnd_2177445 < baseStart_2177445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177520 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 7]
def baseStart_2177520 : Nat := 118140960795 + 2177520 * 2 ^ 59
def prefixEnd_2177520 : Nat := 4983230072969 + 3 ^ 40 * 2177520 * 2
def baseEnd_2177520 : Nat := 248469865506316817041283

theorem tailTrace_2177520 : CollatzResearch.WordTrace tailWord_2177520 prefixEnd_2177520 248469865506316817041283 := by
  unfold tailWord_2177520
  simp only [CollatzResearch.WordTrace]
  refine ⟨39710339535612202826685007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52947119380816270435580009 39710339535612202826685007)
  ·
    refine ⟨59565509303418304240027511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39710339535612202826685007 59565509303418304240027511)
    ·
      refine ⟨89348263955127456360041267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59565509303418304240027511 89348263955127456360041267)
      ·
        refine ⟨134022395932691184540061901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89348263955127456360041267 134022395932691184540061901)
        ·
          refine ⟨50258398474759194202523213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134022395932691184540061901 50258398474759194202523213)
          ·
            refine ⟨18846899428034697825946205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50258398474759194202523213 18846899428034697825946205)
            ·
              refine ⟨7067587285513011684729827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18846899428034697825946205 7067587285513011684729827)
              ·
                refine ⟨10601380928269517527094741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067587285513011684729827 10601380928269517527094741)
                ·
                  refine ⟨248469865506316817041283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10601380928269517527094741 248469865506316817041283)
                  ·
                    rfl

theorem cell22_2177520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_2177520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177520 prefixEnd_2177520 := by exact prefixLift 2177520
  have htrace : WordTrace (prefixWord ++ tailWord_2177520) baseStart_2177520 baseEnd_2177520 := by
    simpa [prefixWord, tailWord_2177520, baseEnd_2177520] using wordTrace_append hprefix tailTrace_2177520
  have hstable : (prefixWord ++ tailWord_2177520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177520).length < 2 ^ (prefixWord ++ tailWord_2177520).sum := by decide
  have hdescent : baseEnd_2177520 < baseStart_2177520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177535 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 2, 5]
def baseStart_2177535 : Nat := 118140960795 + 2177535 * 2 ^ 59
def prefixEnd_2177535 : Nat := 4983230072969 + 3 ^ 40 * 2177535 * 2
def baseEnd_2177535 : Nat := 745414731325495411998803

theorem tailTrace_2177535 : CollatzResearch.WordTrace tailWord_2177535 prefixEnd_2177535 745414731325495411998803 := by
  unfold tailWord_2177535
  simp only [CollatzResearch.WordTrace]
  refine ⟨79421226166170063215166059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52947484110780042143444039 79421226166170063215166059)
  ·
    refine ⟨119131839249255094822749089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79421226166170063215166059 119131839249255094822749089)
    ·
      refine ⟨89348879436941321117061817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119131839249255094822749089 89348879436941321117061817)
      ·
        refine ⟨67011659577705990837796363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89348879436941321117061817 67011659577705990837796363)
        ·
          refine ⟨100517489366558986256694545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67011659577705990837796363 100517489366558986256694545)
          ·
            refine ⟨75388117024919239692520909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100517489366558986256694545 75388117024919239692520909)
            ·
              refine ⟨28270543884344714884695341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75388117024919239692520909 28270543884344714884695341)
              ·
                refine ⟨10601453956629268081760753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28270543884344714884695341 10601453956629268081760753)
                ·
                  refine ⟨7951090467471951061320565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10601453956629268081760753 7951090467471951061320565)
                  ·
                    refine ⟨745414731325495411998803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7951090467471951061320565 745414731325495411998803)
                    ·
                      rfl

theorem cell22_2177535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_2177535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177535 prefixEnd_2177535 := by exact prefixLift 2177535
  have htrace : WordTrace (prefixWord ++ tailWord_2177535) baseStart_2177535 baseEnd_2177535 := by
    simpa [prefixWord, tailWord_2177535, baseEnd_2177535] using wordTrace_append hprefix tailTrace_2177535
  have hstable : (prefixWord ++ tailWord_2177535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177535).length < 2 ^ (prefixWord ++ tailWord_2177535).sum := by decide
  have hdescent : baseEnd_2177535 < baseStart_2177535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177575 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2177575 : Nat := 118140960795 + 2177575 * 2 ^ 59
def prefixEnd_2177575 : Nat := 4983230072969 + 3 ^ 40 * 2177575 * 2
def baseEnd_2177575 : Nat := 745428424142948640998681

theorem tailTrace_2177575 : CollatzResearch.WordTrace tailWord_2177575 prefixEnd_2177575 745428424142948640998681 := by
  unfold tailWord_2177575
  simp only [CollatzResearch.WordTrace]
  refine ⟨79422685086025150046622179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52948456724016766697748119 79422685086025150046622179)
  ·
    refine ⟨119134027629037725069933269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79422685086025150046622179 119134027629037725069933269)
    ·
      refine ⟨2792203772555571681326561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 119134027629037725069933269 2792203772555571681326561)
      ·
        refine ⟨2094152829416678760994921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2792203772555571681326561 2094152829416678760994921)
        ·
          refine ⟨1570614622062509070746191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2094152829416678760994921 1570614622062509070746191)
          ·
            refine ⟨2355921933093763606119287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570614622062509070746191 2355921933093763606119287)
            ·
              refine ⟨3533882899640645409178931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355921933093763606119287 3533882899640645409178931)
              ·
                refine ⟨5300824349460968113768397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3533882899640645409178931 5300824349460968113768397)
                ·
                  refine ⟨1987809131047863042663149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5300824349460968113768397 1987809131047863042663149)
                  ·
                    refine ⟨745428424142948640998681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1987809131047863042663149 745428424142948640998681)
                    ·
                      rfl

theorem cell22_2177575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2177575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177575 prefixEnd_2177575 := by exact prefixLift 2177575
  have htrace : WordTrace (prefixWord ++ tailWord_2177575) baseStart_2177575 baseEnd_2177575 := by
    simpa [prefixWord, tailWord_2177575, baseEnd_2177575] using wordTrace_append hprefix tailTrace_2177575
  have hstable : (prefixWord ++ tailWord_2177575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177575).length < 2 ^ (prefixWord ++ tailWord_2177575).sum := by decide
  have hdescent : baseEnd_2177575 < baseStart_2177575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177601 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2177601 : Nat := 118140960795 + 2177601 * 2 ^ 59
def prefixEnd_2177601 : Nat := 4983230072969 + 3 ^ 40 * 2177601 * 2
def baseEnd_2177601 : Nat := 745437324474293239848601

theorem tailTrace_2177601 : CollatzResearch.WordTrace tailWord_2177601 prefixEnd_2177601 745437324474293239848601 := by
  unfold tailWord_2177601
  simp only [CollatzResearch.WordTrace]
  refine ⟨79423633383930956487068657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52949088922620637658045771 79423633383930956487068657)
  ·
    refine ⟨59567725037948217365301493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79423633383930956487068657 59567725037948217365301493)
    ·
      refine ⟨5584474222307645377997015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59567725037948217365301493 5584474222307645377997015)
      ·
        refine ⟨8376711333461468066995523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5584474222307645377997015 8376711333461468066995523)
        ·
          refine ⟨12565067000192202100493285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8376711333461468066995523 12565067000192202100493285)
          ·
            refine ⟨2355950062536037893842491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12565067000192202100493285 2355950062536037893842491)
            ·
              refine ⟨3533925093804056840763737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355950062536037893842491 3533925093804056840763737)
              ·
                refine ⟨2650443820353042630572803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3533925093804056840763737 2650443820353042630572803)
                ·
                  refine ⟨3975665730529563945859205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2650443820353042630572803 3975665730529563945859205)
                  ·
                    refine ⟨745437324474293239848601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3975665730529563945859205 745437324474293239848601)
                    ·
                      rfl

theorem cell22_2177601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2177601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177601 prefixEnd_2177601 := by exact prefixLift 2177601
  have htrace : WordTrace (prefixWord ++ tailWord_2177601) baseStart_2177601 baseEnd_2177601 := by
    simpa [prefixWord, tailWord_2177601, baseEnd_2177601] using wordTrace_append hprefix tailTrace_2177601
  have hstable : (prefixWord ++ tailWord_2177601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177601).length < 2 ^ (prefixWord ++ tailWord_2177601).sum := by decide
  have hdescent : baseEnd_2177601 < baseStart_2177601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177687 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 4, 5]
def baseStart_2177687 : Nat := 118140960795 + 2177687 * 2 ^ 59
def prefixEnd_2177687 : Nat := 4983230072969 + 3 ^ 40 * 2177687 * 2
def baseEnd_2177687 : Nat := 745466764031817682198337

theorem tailTrace_2177687 : CollatzResearch.WordTrace tailWord_2177687 prefixEnd_2177687 745466764031817682198337 := by
  unfold tailWord_2177687
  simp only [CollatzResearch.WordTrace]
  refine ⟨79426770061619393174699315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52951180041079595449799543 79426770061619393174699315)
  ·
    refine ⟨119140155092429089762048973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79426770061619393174699315 119140155092429089762048973)
    ·
      refine ⟨44677558159660908660768365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119140155092429089762048973 44677558159660908660768365)
      ·
        refine ⟨16754084309872840747788137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44677558159660908660768365 16754084309872840747788137)
        ·
          refine ⟨12565563232404630560841103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16754084309872840747788137 12565563232404630560841103)
          ·
            refine ⟨18848344848606945841261655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12565563232404630560841103 18848344848606945841261655)
            ·
              refine ⟨28272517272910418761892483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18848344848606945841261655 28272517272910418761892483)
              ·
                refine ⟨42408775909365628142838725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28272517272910418761892483 42408775909365628142838725)
                ·
                  refine ⟨7951645483006055276782261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42408775909365628142838725 7951645483006055276782261)
                  ·
                    refine ⟨745466764031817682198337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7951645483006055276782261 745466764031817682198337)
                    ·
                      rfl

theorem cell22_2177687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_2177687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177687 prefixEnd_2177687 := by exact prefixLift 2177687
  have htrace : WordTrace (prefixWord ++ tailWord_2177687) baseStart_2177687 baseEnd_2177687 := by
    simpa [prefixWord, tailWord_2177687, baseEnd_2177687] using wordTrace_append hprefix tailTrace_2177687
  have hstable : (prefixWord ++ tailWord_2177687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177687).length < 2 ^ (prefixWord ++ tailWord_2177687).sum := by decide
  have hdescent : baseEnd_2177687 < baseStart_2177687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177792 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_2177792 : Nat := 118140960795 + 2177792 * 2 ^ 59
def prefixEnd_2177792 : Nat := 4983230072969 + 3 ^ 40 * 2177792 * 2
def baseEnd_2177792 : Nat := 745502707677632408323015

theorem tailTrace_2177792 : CollatzResearch.WordTrace tailWord_2177792 prefixEnd_2177792 745502707677632408323015 := by
  unfold tailWord_2177792
  simp only [CollatzResearch.WordTrace]
  refine ⟨39715299863119498053635815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52953733150825997404847753 39715299863119498053635815)
  ·
    refine ⟨59572949794679247080453723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39715299863119498053635815 59572949794679247080453723)
    ·
      refine ⟨89359424692018870620680585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59572949794679247080453723 89359424692018870620680585)
      ·
        refine ⟨67019568519014152965510439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89359424692018870620680585 67019568519014152965510439)
        ·
          refine ⟨100529352778521229448265659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67019568519014152965510439 100529352778521229448265659)
          ·
            refine ⟨150794029167781844172398489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100529352778521229448265659 150794029167781844172398489)
            ·
              refine ⟨113095521875836383129298867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150794029167781844172398489 113095521875836383129298867)
              ·
                refine ⟨169643282813754574693948301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113095521875836383129298867 169643282813754574693948301)
                ·
                  refine ⟨63616231055157965510230613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169643282813754574693948301 63616231055157965510230613)
                  ·
                    refine ⟨745502707677632408323015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63616231055157965510230613 745502707677632408323015)
                    ·
                      rfl

theorem cell22_2177792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_2177792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177792 prefixEnd_2177792 := by exact prefixLift 2177792
  have htrace : WordTrace (prefixWord ++ tailWord_2177792) baseStart_2177792 baseEnd_2177792 := by
    simpa [prefixWord, tailWord_2177792, baseEnd_2177792] using wordTrace_append hprefix tailTrace_2177792
  have hstable : (prefixWord ++ tailWord_2177792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177792).length < 2 ^ (prefixWord ++ tailWord_2177792).sum := by decide
  have hdescent : baseEnd_2177792 < baseStart_2177792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177828 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_2177828 : Nat := 118140960795 + 2177828 * 2 ^ 59
def prefixEnd_2177828 : Nat := 4983230072969 + 3 ^ 40 * 2177828 * 2
def baseEnd_2177828 : Nat := 745515031213340314422905

theorem tailTrace_2177828 : CollatzResearch.WordTrace tailWord_2177828 prefixEnd_2177828 745515031213340314422905 := by
  unfold tailWord_2177828
  simp only [CollatzResearch.WordTrace]
  refine ⟨39715956377054287127791069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52954608502739049503721425 39715956377054287127791069)
  ·
    refine ⟨14893483641395357672921651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39715956377054287127791069 14893483641395357672921651)
    ·
      refine ⟨22340225462093036509382477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14893483641395357672921651 22340225462093036509382477)
      ·
        refine ⟨8377584548284888691018429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22340225462093036509382477 8377584548284888691018429)
        ·
          refine ⟨3141594205606833259131911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8377584548284888691018429 3141594205606833259131911)
          ·
            refine ⟨4712391308410249888697867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141594205606833259131911 4712391308410249888697867)
            ·
              refine ⟨7068586962615374833046801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4712391308410249888697867 7068586962615374833046801)
              ·
                refine ⟨5301440221961531124785101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7068586962615374833046801 5301440221961531124785101)
                ·
                  refine ⟨1988040083235574171794413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5301440221961531124785101 1988040083235574171794413)
                  ·
                    refine ⟨745515031213340314422905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1988040083235574171794413 745515031213340314422905)
                    ·
                      rfl

theorem cell22_2177828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_2177828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177828 prefixEnd_2177828 := by exact prefixLift 2177828
  have htrace : WordTrace (prefixWord ++ tailWord_2177828) baseStart_2177828 baseEnd_2177828 := by
    simpa [prefixWord, tailWord_2177828, baseEnd_2177828] using wordTrace_append hprefix tailTrace_2177828
  have hstable : (prefixWord ++ tailWord_2177828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177828).length < 2 ^ (prefixWord ++ tailWord_2177828).sum := by decide
  have hdescent : baseEnd_2177828 < baseStart_2177828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177845 : List Nat := [1, 3, 3, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2177845 : Nat := 118140960795 + 2177845 * 2 ^ 59
def prefixEnd_2177845 : Nat := 4983230072969 + 3 ^ 40 * 2177845 * 2
def baseEnd_2177845 : Nat := 745520850660757936747853

theorem tailTrace_2177845 : CollatzResearch.WordTrace tailWord_2177845 prefixEnd_2177845 745520850660757936747853 := by
  unfold tailWord_2177845
  simp only [CollatzResearch.WordTrace]
  refine ⟨79432532795046986158950989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52955021863364657439300659 79432532795046986158950989)
  ·
    refine ⟨29787199798142619809606621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79432532795046986158950989 29787199798142619809606621)
    ·
      refine ⟨11170199924303482428602483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29787199798142619809606621 11170199924303482428602483)
      ·
        refine ⟨16755299886455223642903725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11170199924303482428602483 16755299886455223642903725)
        ·
          refine ⟨6283237457420708866088897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16755299886455223642903725 6283237457420708866088897)
          ·
            refine ⟨4712428093065531649566673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6283237457420708866088897 4712428093065531649566673)
            ·
              refine ⟨3534321069799148737175005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4712428093065531649566673 3534321069799148737175005)
              ·
                refine ⟨1325370401174680776440627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3534321069799148737175005 1325370401174680776440627)
                ·
                  refine ⟨1988055601762021164660941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325370401174680776440627 1988055601762021164660941)
                  ·
                    refine ⟨745520850660757936747853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1988055601762021164660941 745520850660757936747853)
                    ·
                      rfl

theorem cell22_2177845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2177845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177845 prefixEnd_2177845 := by exact prefixLift 2177845
  have htrace : WordTrace (prefixWord ++ tailWord_2177845) baseStart_2177845 baseEnd_2177845 := by
    simpa [prefixWord, tailWord_2177845, baseEnd_2177845] using wordTrace_append hprefix tailTrace_2177845
  have hstable : (prefixWord ++ tailWord_2177845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177845).length < 2 ^ (prefixWord ++ tailWord_2177845).sum := by decide
  have hdescent : baseEnd_2177845 < baseStart_2177845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177862 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2177862 : Nat := 118140960795 + 2177862 * 2 ^ 59
def prefixEnd_2177862 : Nat := 4983230072969 + 3 ^ 40 * 2177862 * 2
def baseEnd_2177862 : Nat := 745526670108175559072801

theorem tailTrace_2177862 : CollatzResearch.WordTrace tailWord_2177862 prefixEnd_2177862 745526670108175559072801 := by
  unfold tailWord_2177862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2482286026124543689447495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52955435223990265374879893 2482286026124543689447495)
  ·
    refine ⟨3723429039186815534171243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2482286026124543689447495 3723429039186815534171243)
    ·
      refine ⟨5585143558780223301256865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3723429039186815534171243 5585143558780223301256865)
      ·
        refine ⟨4188857669085167475942649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5585143558780223301256865 4188857669085167475942649)
        ·
          refine ⟨3141643251813875606956987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4188857669085167475942649 3141643251813875606956987)
          ·
            refine ⟨4712464877720813410435481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141643251813875606956987 4712464877720813410435481)
            ·
              refine ⟨3534348658290610057826611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4712464877720813410435481 3534348658290610057826611)
              ·
                refine ⟨5301522987435915086739917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534348658290610057826611 5301522987435915086739917)
                ·
                  refine ⟨1988071120288468157527469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5301522987435915086739917 1988071120288468157527469)
                  ·
                    refine ⟨745526670108175559072801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1988071120288468157527469 745526670108175559072801)
                    ·
                      rfl

theorem cell22_2177862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2177862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177862 prefixEnd_2177862 := by exact prefixLift 2177862
  have htrace : WordTrace (prefixWord ++ tailWord_2177862) baseStart_2177862 baseEnd_2177862 := by
    simpa [prefixWord, tailWord_2177862, baseEnd_2177862] using wordTrace_append hprefix tailTrace_2177862
  have hstable : (prefixWord ++ tailWord_2177862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177862).length < 2 ^ (prefixWord ++ tailWord_2177862).sum := by decide
  have hdescent : baseEnd_2177862 < baseStart_2177862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177899 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 1, 6]
def baseStart_2177899 : Nat := 118140960795 + 2177899 * 2 ^ 59
def prefixEnd_2177899 : Nat := 4983230072969 + 3 ^ 40 * 2177899 * 2
def baseEnd_2177899 : Nat := 745539335964319795897687

theorem tailTrace_2177899 : CollatzResearch.WordTrace tailWord_2177899 prefixEnd_2177899 745539335964319795897687 := by
  unfold tailWord_2177899
  simp only [CollatzResearch.WordTrace]
  refine ⟨79434502336851353381416751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52956334891234235587611167 79434502336851353381416751)
  ·
    refine ⟨119151753505277030072125127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79434502336851353381416751 119151753505277030072125127)
    ·
      refine ⟨178727630257915545108187691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119151753505277030072125127 178727630257915545108187691)
      ·
        refine ⟨268091445386873317662281537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178727630257915545108187691 268091445386873317662281537)
        ·
          refine ⟨201068584040154988246711153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268091445386873317662281537 201068584040154988246711153)
          ·
            refine ⟨150801438030116241185033365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201068584040154988246711153 150801438030116241185033365)
            ·
              refine ⟨7068817407661698805548439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150801438030116241185033365 7068817407661698805548439)
              ·
                refine ⟨10603226111492548208322659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7068817407661698805548439 10603226111492548208322659)
                ·
                  refine ⟨15904839167238822312483989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10603226111492548208322659 15904839167238822312483989)
                  ·
                    refine ⟨745539335964319795897687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15904839167238822312483989 745539335964319795897687)
                    ·
                      rfl

theorem cell22_2177899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_2177899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177899 prefixEnd_2177899 := by exact prefixLift 2177899
  have htrace : WordTrace (prefixWord ++ tailWord_2177899) baseStart_2177899 baseEnd_2177899 := by
    simpa [prefixWord, tailWord_2177899, baseEnd_2177899] using wordTrace_append hprefix tailTrace_2177899
  have hstable : (prefixWord ++ tailWord_2177899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177899).length < 2 ^ (prefixWord ++ tailWord_2177899).sum := by decide
  have hdescent : baseEnd_2177899 < baseStart_2177899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2177976 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 5]
def baseStart_2177976 : Nat := 118140960795 + 2177976 * 2 ^ 59
def prefixEnd_2177976 : Nat := 4983230072969 + 3 ^ 40 * 2177976 * 2
def baseEnd_2177976 : Nat := 248521898212639087240817

theorem tailTrace_2177976 : CollatzResearch.WordTrace tailWord_2177976 prefixEnd_2177976 248521898212639087240817 := by
  unfold tailWord_2177976
  simp only [CollatzResearch.WordTrace]
  refine ⟨39718655378786197765984891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52958207171714930354646521 39718655378786197765984891)
  ·
    refine ⟨59577983068179296648977337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39718655378786197765984891 59577983068179296648977337)
    ·
      refine ⟨44683487301134472486733003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59577983068179296648977337 44683487301134472486733003)
      ·
        refine ⟨67025230951701708730099505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44683487301134472486733003 67025230951701708730099505)
        ·
          refine ⟨50268923213776281547574629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67025230951701708730099505 50268923213776281547574629)
          ·
            refine ⟨9425423102583052790170243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50268923213776281547574629 9425423102583052790170243)
            ·
              refine ⟨14138134653874579185255365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9425423102583052790170243 14138134653874579185255365)
              ·
                refine ⟨2650900247601483597235381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14138134653874579185255365 2650900247601483597235381)
                ·
                  refine ⟨248521898212639087240817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2650900247601483597235381 248521898212639087240817)
                  ·
                    rfl

theorem cell22_2177976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_2177976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2177976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2177976 prefixEnd_2177976 := by exact prefixLift 2177976
  have htrace : WordTrace (prefixWord ++ tailWord_2177976) baseStart_2177976 baseEnd_2177976 := by
    simpa [prefixWord, tailWord_2177976, baseEnd_2177976] using wordTrace_append hprefix tailTrace_2177976
  have hstable : (prefixWord ++ tailWord_2177976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2177976).length < 2 ^ (prefixWord ++ tailWord_2177976).sum := by decide
  have hdescent : baseEnd_2177976 < baseStart_2177976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2177976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178038 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_2178038 : Nat := 118140960795 + 2178038 * 2 ^ 59
def prefixEnd_2178038 : Nat := 4983230072969 + 3 ^ 40 * 2178038 * 2
def baseEnd_2178038 : Nat := 248528972834989922224087

theorem tailTrace_2178038 : CollatzResearch.WordTrace tailWord_2178038 prefixEnd_2178038 248528972834989922224087 := by
  unfold tailWord_2178038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4964973255209236257545423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52959714722231853413817845 4964973255209236257545423)
  ·
    refine ⟨7447459882813854386318135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4964973255209236257545423 7447459882813854386318135)
    ·
      refine ⟨11171189824220781579477203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7447459882813854386318135 11171189824220781579477203)
      ·
        refine ⟨16756784736331172369215805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11171189824220781579477203 16756784736331172369215805)
        ·
          refine ⟨6283794276124189638455927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16756784736331172369215805 6283794276124189638455927)
          ·
            refine ⟨9425691414186284457683891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6283794276124189638455927 9425691414186284457683891)
            ·
              refine ⟨14138537121279426686525837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9425691414186284457683891 14138537121279426686525837)
              ·
                refine ⟨5301951420479785007447189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14138537121279426686525837 5301951420479785007447189)
                ·
                  refine ⟨248528972834989922224087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5301951420479785007447189 248528972834989922224087)
                  ·
                    rfl

theorem cell22_2178038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_2178038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178038 prefixEnd_2178038 := by exact prefixLift 2178038
  have htrace : WordTrace (prefixWord ++ tailWord_2178038) baseStart_2178038 baseEnd_2178038 := by
    simpa [prefixWord, tailWord_2178038, baseEnd_2178038] using wordTrace_append hprefix tailTrace_2178038
  have hstable : (prefixWord ++ tailWord_2178038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178038).length < 2 ^ (prefixWord ++ tailWord_2178038).sum := by decide
  have hdescent : baseEnd_2178038 < baseStart_2178038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178096 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_2178096 : Nat := 118140960795 + 2178096 * 2 ^ 59
def prefixEnd_2178096 : Nat := 4983230072969 + 3 ^ 40 * 2178096 * 2
def baseEnd_2178096 : Nat := 745606773090276948722083

theorem tailTrace_2178096 : CollatzResearch.WordTrace tailWord_2178096 prefixEnd_2178096 745606773090276948722083 := by
  unfold tailWord_2178096
  simp only [CollatzResearch.WordTrace]
  refine ⟨39720843758568828013169071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52961125011425104017558761 39720843758568828013169071)
  ·
    refine ⟨59581265637853242019753607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39720843758568828013169071 59581265637853242019753607)
    ·
      refine ⟨89371898456779863029630411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59581265637853242019753607 89371898456779863029630411)
      ·
        refine ⟨134057847685169794544445617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89371898456779863029630411 134057847685169794544445617)
        ·
          refine ⟨100543385763877345908334213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134057847685169794544445617 100543385763877345908334213)
          ·
            refine ⟨18851884830727002357812665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100543385763877345908334213 18851884830727002357812665)
            ·
              refine ⟨14138913623045251768359499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18851884830727002357812665 14138913623045251768359499)
              ·
                refine ⟨21208370434567877652539249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14138913623045251768359499 21208370434567877652539249)
                ·
                  refine ⟨15906277825925908239404437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21208370434567877652539249 15906277825925908239404437)
                  ·
                    refine ⟨745606773090276948722083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15906277825925908239404437 745606773090276948722083)
                    ·
                      rfl

theorem cell22_2178096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_2178096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178096 prefixEnd_2178096 := by exact prefixLift 2178096
  have htrace : WordTrace (prefixWord ++ tailWord_2178096) baseStart_2178096 baseEnd_2178096 := by
    simpa [prefixWord, tailWord_2178096, baseEnd_2178096] using wordTrace_append hprefix tailTrace_2178096
  have hstable : (prefixWord ++ tailWord_2178096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178096).length < 2 ^ (prefixWord ++ tailWord_2178096).sum := by decide
  have hdescent : baseEnd_2178096 < baseStart_2178096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178100 : List Nat := [2, 5, 1, 2, 1, 2, 2, 7]
def baseStart_2178100 : Nat := 118140960795 + 2178100 * 2 ^ 59
def prefixEnd_2178100 : Nat := 4983230072969 + 3 ^ 40 * 2178100 * 2
def baseEnd_2178100 : Nat := 82845349152446919069119

theorem tailTrace_2178100 : CollatzResearch.WordTrace tailWord_2178100 prefixEnd_2178100 82845349152446919069119 := by
  unfold tailWord_2178100
  simp only [CollatzResearch.WordTrace]
  refine ⟨39720916704561582354741877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52961222272748776472989169 39720916704561582354741877)
  ·
    refine ⟨3723835941052648345757051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39720916704561582354741877 3723835941052648345757051)
    ·
      refine ⟨5585753911578972518635577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3723835941052648345757051 5585753911578972518635577)
      ·
        refine ⟨4189315433684229388976683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5585753911578972518635577 4189315433684229388976683)
        ·
          refine ⟨6283973150526344083465025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189315433684229388976683 6283973150526344083465025)
          ·
            refine ⟨4712979862894758062598769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6283973150526344083465025 4712979862894758062598769)
            ·
              refine ⟨3534734897171068546949077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4712979862894758062598769 3534734897171068546949077)
              ·
                refine ⟨82845349152446919069119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3534734897171068546949077 82845349152446919069119)
                ·
                  rfl

theorem cell22_2178100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 7].length) (baseStart_2178100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178100 prefixEnd_2178100 := by exact prefixLift 2178100
  have htrace : WordTrace (prefixWord ++ tailWord_2178100) baseStart_2178100 baseEnd_2178100 := by
    simpa [prefixWord, tailWord_2178100, baseEnd_2178100] using wordTrace_append hprefix tailTrace_2178100
  have hstable : (prefixWord ++ tailWord_2178100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178100).length < 2 ^ (prefixWord ++ tailWord_2178100).sum := by decide
  have hdescent : baseEnd_2178100 < baseStart_2178100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178173 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 6]
def baseStart_2178173 : Nat := 118140960795 + 2178173 * 2 ^ 59
def prefixEnd_2178173 : Nat := 4983230072969 + 3 ^ 40 * 2178173 * 2
def baseEnd_2178173 : Nat := 248544377254624804848949

theorem tailTrace_2178173 : CollatzResearch.WordTrace tailWord_2178173 prefixEnd_2178173 248544377254624804848949 := by
  unfold tailWord_2178173
  simp only [CollatzResearch.WordTrace]
  refine ⟨79444495937858698176891173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52962997291905798784594115 79444495937858698176891173)
  ·
    refine ⟨14895842988348505908167095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79444495937858698176891173 14895842988348505908167095)
    ·
      refine ⟨22343764482522758862250643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14895842988348505908167095 22343764482522758862250643)
      ·
        refine ⟨33515646723784138293375965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22343764482522758862250643 33515646723784138293375965)
        ·
          refine ⟨12568367521419051860015987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33515646723784138293375965 12568367521419051860015987)
          ·
            refine ⟨18852551282128577790023981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12568367521419051860015987 18852551282128577790023981)
            ·
              refine ⟨7069706730798216671258993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18852551282128577790023981 7069706730798216671258993)
              ·
                refine ⟨5302280048098662503444245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7069706730798216671258993 5302280048098662503444245)
                ·
                  refine ⟨248544377254624804848949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5302280048098662503444245 248544377254624804848949)
                  ·
                    rfl

theorem cell22_2178173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_2178173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178173 prefixEnd_2178173 := by exact prefixLift 2178173
  have htrace : WordTrace (prefixWord ++ tailWord_2178173) baseStart_2178173 baseEnd_2178173 := by
    simpa [prefixWord, tailWord_2178173, baseEnd_2178173] using wordTrace_append hprefix tailTrace_2178173
  have hstable : (prefixWord ++ tailWord_2178173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178173).length < 2 ^ (prefixWord ++ tailWord_2178173).sum := by decide
  have hdescent : baseEnd_2178173 < baseStart_2178173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178205 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_2178205 : Nat := 118140960795 + 2178205 * 2 ^ 59
def prefixEnd_2178205 : Nat := 4983230072969 + 3 ^ 40 * 2178205 * 2
def baseEnd_2178205 : Nat := 745644086017836997746749

theorem tailTrace_2178205 : CollatzResearch.WordTrace tailWord_2178205 prefixEnd_2178205 745644086017836997746749 := by
  unfold tailWord_2178205
  simp only [CollatzResearch.WordTrace]
  refine ⟨79445663073742767642056069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52963775382495178428037379 79445663073742767642056069)
  ·
    refine ⟨14896061826326768932885513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79445663073742767642056069 14896061826326768932885513)
    ·
      refine ⟨11172046369745076699664135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14896061826326768932885513 11172046369745076699664135)
      ·
        refine ⟨16758069554617615049496203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11172046369745076699664135 16758069554617615049496203)
        ·
          refine ⟨25137104331926422574244305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16758069554617615049496203 25137104331926422574244305)
          ·
            refine ⟨18852828248944816930683229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25137104331926422574244305 18852828248944816930683229)
            ·
              refine ⟨7069810593354306349006211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18852828248944816930683229 7069810593354306349006211)
              ·
                refine ⟨10604715890031459523509317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7069810593354306349006211 10604715890031459523509317)
                ·
                  refine ⟨1988384229380898660657997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10604715890031459523509317 1988384229380898660657997)
                  ·
                    refine ⟨745644086017836997746749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1988384229380898660657997 745644086017836997746749)
                    ·
                      rfl

theorem cell22_2178205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_2178205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178205 prefixEnd_2178205 := by exact prefixLift 2178205
  have htrace : WordTrace (prefixWord ++ tailWord_2178205) baseStart_2178205 baseEnd_2178205 := by
    simpa [prefixWord, tailWord_2178205, baseEnd_2178205] using wordTrace_append hprefix tailTrace_2178205
  have hstable : (prefixWord ++ tailWord_2178205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178205).length < 2 ^ (prefixWord ++ tailWord_2178205).sum := by decide
  have hdescent : baseEnd_2178205 < baseStart_2178205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178263 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 7]
def baseStart_2178263 : Nat := 118140960795 + 2178263 * 2 ^ 59
def prefixEnd_2178263 : Nat := 4983230072969 + 3 ^ 40 * 2178263 * 2
def baseEnd_2178263 : Nat := 248554646867714726598857

theorem tailTrace_2178263 : CollatzResearch.WordTrace tailWord_2178263 prefixEnd_2178263 248554646867714726598857 := by
  unfold tailWord_2178263
  simp only [CollatzResearch.WordTrace]
  refine ⟨79447778507532643547667443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52965185671688429031778295 79447778507532643547667443)
  ·
    refine ⟨119171667761298965321501165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79447778507532643547667443 119171667761298965321501165)
    ·
      refine ⟨44689375410487111995562937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119171667761298965321501165 44689375410487111995562937)
      ·
        refine ⟨33517031557865333996672203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44689375410487111995562937 33517031557865333996672203)
        ·
          refine ⟨50275547336798000995008305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33517031557865333996672203 50275547336798000995008305)
          ·
            refine ⟨37706660502598500746256229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50275547336798000995008305 37706660502598500746256229)
            ·
              refine ⟨7069998844237218889923043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37706660502598500746256229 7069998844237218889923043)
              ·
                refine ⟨10604998266355828334884565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7069998844237218889923043 10604998266355828334884565)
                ·
                  refine ⟨248554646867714726598857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10604998266355828334884565 248554646867714726598857)
                  ·
                    rfl

theorem cell22_2178263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 7].length) (baseStart_2178263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178263 prefixEnd_2178263 := by exact prefixLift 2178263
  have htrace : WordTrace (prefixWord ++ tailWord_2178263) baseStart_2178263 baseEnd_2178263 := by
    simpa [prefixWord, tailWord_2178263, baseEnd_2178263] using wordTrace_append hprefix tailTrace_2178263
  have hstable : (prefixWord ++ tailWord_2178263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178263).length < 2 ^ (prefixWord ++ tailWord_2178263).sum := by decide
  have hdescent : baseEnd_2178263 < baseStart_2178263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178280 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 5]
def baseStart_2178280 : Nat := 118140960795 + 2178280 * 2 ^ 59
def prefixEnd_2178280 : Nat := 4983230072969 + 3 ^ 40 * 2178280 * 2
def baseEnd_2178280 : Nat := 248556586683520600707173

theorem tailTrace_2178280 : CollatzResearch.WordTrace tailWord_2178280 prefixEnd_2178280 248556586683520600707173 := by
  unfold tailWord_2178280
  simp only [CollatzResearch.WordTrace]
  refine ⟨39724199274235527725518147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52965599032314036967357529 39724199274235527725518147)
  ·
    refine ⟨59586298911353291588277221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39724199274235527725518147 59586298911353291588277221)
    ·
      refine ⟨11172431045878742172801979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59586298911353291588277221 11172431045878742172801979)
      ·
        refine ⟨16758646568818113259202969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11172431045878742172801979 16758646568818113259202969)
        ·
          refine ⟨12568984926613584944402227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16758646568818113259202969 12568984926613584944402227)
          ·
            refine ⟨18853477389920377416603341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12568984926613584944402227 18853477389920377416603341)
            ·
              refine ⟨7070054021220141531226253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18853477389920377416603341 7070054021220141531226253)
              ·
                refine ⟨2651270257957553074209845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7070054021220141531226253 2651270257957553074209845)
                ·
                  refine ⟨248556586683520600707173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2651270257957553074209845 248556586683520600707173)
                  ·
                    rfl

theorem cell22_2178280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_2178280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178280 prefixEnd_2178280 := by exact prefixLift 2178280
  have htrace : WordTrace (prefixWord ++ tailWord_2178280) baseStart_2178280 baseEnd_2178280 := by
    simpa [prefixWord, tailWord_2178280, baseEnd_2178280] using wordTrace_append hprefix tailTrace_2178280
  have hstable : (prefixWord ++ tailWord_2178280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178280).length < 2 ^ (prefixWord ++ tailWord_2178280).sum := by decide
  have hdescent : baseEnd_2178280 < baseStart_2178280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178355 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 1, 6]
def baseStart_2178355 : Nat := 118140960795 + 2178355 * 2 ^ 59
def prefixEnd_2178355 : Nat := 4983230072969 + 3 ^ 40 * 2178355 * 2
def baseEnd_2178355 : Nat := 745695434083286606496289

theorem tailTrace_2178355 : CollatzResearch.WordTrace tailWord_2178355 prefixEnd_2178355 745695434083286606496289 := by
  unfold tailWord_2178355
  simp only [CollatzResearch.WordTrace]
  refine ⟨79451134023199343260016519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52967422682132895506677679 79451134023199343260016519)
  ·
    refine ⟨119176701034799014890024779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79451134023199343260016519 119176701034799014890024779)
    ·
      refine ⟨178765051552198522335037169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119176701034799014890024779 178765051552198522335037169)
      ·
        refine ⟨134073788664148891751277877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178765051552198522335037169 134073788664148891751277877)
        ·
          refine ⟨12569417687263958601682301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134073788664148891751277877 12569417687263958601682301)
          ·
            refine ⟨4713531632723984475630863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12569417687263958601682301 4713531632723984475630863)
            ·
              refine ⟨7070297449085976713446295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4713531632723984475630863 7070297449085976713446295)
              ·
                refine ⟨10605446173628965070169443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7070297449085976713446295 10605446173628965070169443)
                ·
                  refine ⟨15908169260443447605254165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10605446173628965070169443 15908169260443447605254165)
                  ·
                    refine ⟨745695434083286606496289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15908169260443447605254165 745695434083286606496289)
                    ·
                      rfl

theorem cell22_2178355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_2178355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178355 prefixEnd_2178355 := by exact prefixLift 2178355
  have htrace : WordTrace (prefixWord ++ tailWord_2178355) baseStart_2178355 baseEnd_2178355 := by
    simpa [prefixWord, tailWord_2178355, baseEnd_2178355] using wordTrace_append hprefix tailTrace_2178355
  have hstable : (prefixWord ++ tailWord_2178355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178355).length < 2 ^ (prefixWord ++ tailWord_2178355).sum := by decide
  have hdescent : baseEnd_2178355 < baseStart_2178355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178361 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 1, 4]
def baseStart_2178361 : Nat := 118140960795 + 2178361 * 2 ^ 59
def prefixEnd_2178361 : Nat := 4983230072969 + 3 ^ 40 * 2178361 * 2
def baseEnd_2178361 : Nat := 745697488005904590846271

theorem tailTrace_2178361 : CollatzResearch.WordTrace tailWord_2178361 prefixEnd_2178361 745697488005904590846271 := by
  unfold tailWord_2178361
  simp only [CollatzResearch.WordTrace]
  refine ⟨79451352861177606284734937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52967568574118404189823291 79451352861177606284734937)
  ·
    refine ⟨59588514645883204713551203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79451352861177606284734937 59588514645883204713551203)
    ·
      refine ⟨89382771968824807070326805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59588514645883204713551203 89382771968824807070326805)
      ·
        refine ⟨4189817436038662831421569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89382771968824807070326805 4189817436038662831421569)
        ·
          refine ⟨3142363077028997123566177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4189817436038662831421569 3142363077028997123566177)
          ·
            refine ⟨2356772307771747842674633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3142363077028997123566177 2356772307771747842674633)
            ·
              refine ⟨1767579230828810882005975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2356772307771747842674633 1767579230828810882005975)
              ·
                refine ⟨2651368846243216323008963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767579230828810882005975 2651368846243216323008963)
                ·
                  refine ⟨3977053269364824484513445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651368846243216323008963 3977053269364824484513445)
                  ·
                    refine ⟨745697488005904590846271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3977053269364824484513445 745697488005904590846271)
                    ·
                      rfl

theorem cell22_2178361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 1, 4].length) (baseStart_2178361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178361 prefixEnd_2178361 := by exact prefixLift 2178361
  have htrace : WordTrace (prefixWord ++ tailWord_2178361) baseStart_2178361 baseEnd_2178361 := by
    simpa [prefixWord, tailWord_2178361, baseEnd_2178361] using wordTrace_append hprefix tailTrace_2178361
  have hstable : (prefixWord ++ tailWord_2178361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178361).length < 2 ^ (prefixWord ++ tailWord_2178361).sum := by decide
  have hdescent : baseEnd_2178361 < baseStart_2178361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178490 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_2178490 : Nat := 118140960795 + 2178490 * 2 ^ 59
def prefixEnd_2178490 : Nat := 4983230072969 + 3 ^ 40 * 2178490 * 2
def baseEnd_2178490 : Nat := 745741647342191254370875

theorem tailTrace_2178490 : CollatzResearch.WordTrace tailWord_2178490 prefixEnd_2178490 745741647342191254370875 := by
  unfold tailWord_2178490
  simp only [CollatzResearch.WordTrace]
  refine ⟨19864014469427565329045231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52970705251806840877453949 19864014469427565329045231)
  ·
    refine ⟨29796021704141347993567847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19864014469427565329045231 29796021704141347993567847)
    ·
      refine ⟨44694032556212021990351771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29796021704141347993567847 44694032556212021990351771)
      ·
        refine ⟨67041048834318032985527657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44694032556212021990351771 67041048834318032985527657)
        ·
          refine ⟨50280786625738524739145743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67041048834318032985527657 50280786625738524739145743)
          ·
            refine ⟨75421179938607787108718615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50280786625738524739145743 75421179938607787108718615)
            ·
              refine ⟨113131769907911680663077923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75421179938607787108718615 113131769907911680663077923)
              ·
                refine ⟨169697654861867520994616885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113131769907911680663077923 169697654861867520994616885)
                ·
                  refine ⟨15909155143300080093245333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169697654861867520994616885 15909155143300080093245333)
                  ·
                    refine ⟨745741647342191254370875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15909155143300080093245333 745741647342191254370875)
                    ·
                      rfl

theorem cell22_2178490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_2178490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178490 prefixEnd_2178490 := by exact prefixLift 2178490
  have htrace : WordTrace (prefixWord ++ tailWord_2178490) baseStart_2178490 baseEnd_2178490 := by
    simpa [prefixWord, tailWord_2178490, baseEnd_2178490] using wordTrace_append hprefix tailTrace_2178490
  have hstable : (prefixWord ++ tailWord_2178490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178490).length < 2 ^ (prefixWord ++ tailWord_2178490).sum := by decide
  have hdescent : baseEnd_2178490 < baseStart_2178490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178554 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_2178554 : Nat := 118140960795 + 2178554 * 2 ^ 59
def prefixEnd_2178554 : Nat := 4983230072969 + 3 ^ 40 * 2178554 * 2
def baseEnd_2178554 : Nat := 745763555850116420770679

theorem tailTrace_2178554 : CollatzResearch.WordTrace tailWord_2178554 prefixEnd_2178554 745763555850116420770679 := by
  unfold tailWord_2178554
  simp only [CollatzResearch.WordTrace]
  refine ⟨19864598037369600061627679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52972261432985600164340477 19864598037369600061627679)
  ·
    refine ⟨29796897056054400092441519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19864598037369600061627679 29796897056054400092441519)
    ·
      refine ⟨44695345584081600138662279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29796897056054400092441519 44695345584081600138662279)
      ·
        refine ⟨67043018376122400207993419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44695345584081600138662279 67043018376122400207993419)
        ·
          refine ⟨100564527564183600311990129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67043018376122400207993419 100564527564183600311990129)
          ·
            refine ⟨75423395673137700233992597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100564527564183600311990129 75423395673137700233992597)
            ·
              refine ⟨3535471672178329698468403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75423395673137700233992597 3535471672178329698468403)
              ·
                refine ⟨5303207508267494547702605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535471672178329698468403 5303207508267494547702605)
                ·
                  refine ⟨1988702815600310455388477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5303207508267494547702605 1988702815600310455388477)
                  ·
                    refine ⟨745763555850116420770679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1988702815600310455388477 745763555850116420770679)
                    ·
                      rfl

theorem cell22_2178554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_2178554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178554 prefixEnd_2178554 := by exact prefixLift 2178554
  have htrace : WordTrace (prefixWord ++ tailWord_2178554) baseStart_2178554 baseEnd_2178554 := by
    simpa [prefixWord, tailWord_2178554, baseEnd_2178554] using wordTrace_append hprefix tailTrace_2178554
  have hstable : (prefixWord ++ tailWord_2178554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178554).length < 2 ^ (prefixWord ++ tailWord_2178554).sum := by decide
  have hdescent : baseEnd_2178554 < baseStart_2178554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178590 : List Nat := [4, 3, 3, 1, 2, 1, 8]
def baseStart_2178590 : Nat := 118140960795 + 2178590 * 2 ^ 59
def prefixEnd_2178590 : Nat := 4983230072969 + 3 ^ 40 * 2178590 * 2
def baseEnd_2178590 : Nat := 27621328866141641735947

theorem tailTrace_2178590 : CollatzResearch.WordTrace tailWord_2178590 prefixEnd_2178590 27621328866141641735947 := by
  unfold tailWord_2178590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9932463147168497299352653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52973136784898652263214149 9932463147168497299352653)
  ·
    refine ⟨3724673680188186487257245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9932463147168497299352653 3724673680188186487257245)
    ·
      refine ⟨1396752630070569932721467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3724673680188186487257245 1396752630070569932721467)
      ·
        refine ⟨2095128945105854899082201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396752630070569932721467 2095128945105854899082201)
        ·
          refine ⟨1571346708829391174311651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2095128945105854899082201 1571346708829391174311651)
          ·
            refine ⟨2357020063244086761467477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571346708829391174311651 2357020063244086761467477)
            ·
              refine ⟨27621328866141641735947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2357020063244086761467477 27621328866141641735947)
              ·
                rfl

theorem cell22_2178590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 8].length) (baseStart_2178590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178590 prefixEnd_2178590 := by exact prefixLift 2178590
  have htrace : WordTrace (prefixWord ++ tailWord_2178590) baseStart_2178590 baseEnd_2178590 := by
    simpa [prefixWord, tailWord_2178590, baseEnd_2178590] using wordTrace_append hprefix tailTrace_2178590
  have hstable : (prefixWord ++ tailWord_2178590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178590).length < 2 ^ (prefixWord ++ tailWord_2178590).sum := by decide
  have hdescent : baseEnd_2178590 < baseStart_2178590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178597 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_2178597 : Nat := 118140960795 + 2178597 * 2 ^ 59
def prefixEnd_2178597 : Nat := 4983230072969 + 3 ^ 40 * 2178597 * 2
def baseEnd_2178597 : Nat := 745778275628878641945547

theorem tailTrace_2178597 : CollatzResearch.WordTrace tailWord_2178597 prefixEnd_2178597 745778275628878641945547 := by
  unfold tailWord_2178597
  simp only [CollatzResearch.WordTrace]
  refine ⟨79459960488322618590326045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52973306992215079060217363 79459960488322618590326045)
  ·
    refine ⟨29797485183120981971372267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79459960488322618590326045 29797485183120981971372267)
    ·
      refine ⟨44696227774681472957058401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29797485183120981971372267 44696227774681472957058401)
      ·
        refine ⟨33522170831011104717793801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44696227774681472957058401 33522170831011104717793801)
        ·
          refine ⟨25141628123258328538345351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33522170831011104717793801 25141628123258328538345351)
          ·
            refine ⟨37712442184887492807518027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25141628123258328538345351 37712442184887492807518027)
            ·
              refine ⟨56568663277331239211277041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37712442184887492807518027 56568663277331239211277041)
              ·
                refine ⟨42426497457998429408457781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56568663277331239211277041 42426497457998429408457781)
                ·
                  refine ⟨3977484136687352757042917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42426497457998429408457781 3977484136687352757042917)
                  ·
                    refine ⟨745778275628878641945547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3977484136687352757042917 745778275628878641945547)
                    ·
                      rfl

theorem cell22_2178597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_2178597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178597 prefixEnd_2178597 := by exact prefixLift 2178597
  have htrace : WordTrace (prefixWord ++ tailWord_2178597) baseStart_2178597 baseEnd_2178597 := by
    simpa [prefixWord, tailWord_2178597, baseEnd_2178597] using wordTrace_append hprefix tailTrace_2178597
  have hstable : (prefixWord ++ tailWord_2178597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178597).length < 2 ^ (prefixWord ++ tailWord_2178597).sum := by decide
  have hdescent : baseEnd_2178597 < baseStart_2178597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178644 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2178644 : Nat := 118140960795 + 2178644 * 2 ^ 59
def prefixEnd_2178644 : Nat := 4983230072969 + 3 ^ 40 * 2178644 * 2
def baseEnd_2178644 : Nat := 745794364689386186020403

theorem tailTrace_2178644 : CollatzResearch.WordTrace tailWord_2178644 prefixEnd_2178644 745794364689386186020403 := by
  unfold tailWord_2178644
  simp only [CollatzResearch.WordTrace]
  refine ⟨39730837359576172808643493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52974449812768230411524657 39730837359576172808643493)
  ·
    refine ⟨7449532004920532401620655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39730837359576172808643493 7449532004920532401620655)
    ·
      refine ⟨11174298007380798602430983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7449532004920532401620655 11174298007380798602430983)
      ·
        refine ⟨16761447011071197903646475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11174298007380798602430983 16761447011071197903646475)
        ·
          refine ⟨25142170516606796855469713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16761447011071197903646475 25142170516606796855469713)
          ·
            refine ⟨18856627887455097641602285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25142170516606796855469713 18856627887455097641602285)
            ·
              refine ⟨7071235457795661615600857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18856627887455097641602285 7071235457795661615600857)
              ·
                refine ⟨5303426593346746211700643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7071235457795661615600857 5303426593346746211700643)
                ·
                  refine ⟨7955139890020119317550965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5303426593346746211700643 7955139890020119317550965)
                  ·
                    refine ⟨745794364689386186020403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7955139890020119317550965 745794364689386186020403)
                    ·
                      rfl

theorem cell22_2178644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2178644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178644 prefixEnd_2178644 := by exact prefixLift 2178644
  have htrace : WordTrace (prefixWord ++ tailWord_2178644) baseStart_2178644 baseEnd_2178644 := by
    simpa [prefixWord, tailWord_2178644, baseEnd_2178644] using wordTrace_append hprefix tailTrace_2178644
  have hstable : (prefixWord ++ tailWord_2178644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178644).length < 2 ^ (prefixWord ++ tailWord_2178644).sum := by decide
  have hdescent : baseEnd_2178644 < baseStart_2178644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178659 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 2, 4]
def baseStart_2178659 : Nat := 118140960795 + 2178659 * 2 ^ 59
def prefixEnd_2178659 : Nat := 4983230072969 + 3 ^ 40 * 2178659 * 2
def baseEnd_2178659 : Nat := 745799499495931146895357

theorem tailTrace_2178659 : CollatzResearch.WordTrace tailWord_2178659 prefixEnd_2178659 745799499495931146895357 := by
  unfold tailWord_2178659
  simp only [CollatzResearch.WordTrace]
  refine ⟨79462221814098003179083031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52974814542732002119388687 79462221814098003179083031)
  ·
    refine ⟨119193332721147004768624547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79462221814098003179083031 119193332721147004768624547)
    ·
      refine ⟨178789999081720507152936821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119193332721147004768624547 178789999081720507152936821)
      ·
        refine ⟨16761562413911297545587827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178789999081720507152936821 16761562413911297545587827)
        ·
          refine ⟨25142343620866946318381741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16761562413911297545587827 25142343620866946318381741)
          ·
            refine ⟨9428378857825104869393153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25142343620866946318381741 9428378857825104869393153)
            ·
              refine ⟨7071284143368828652044865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9428378857825104869393153 7071284143368828652044865)
              ·
                refine ⟨5303463107526621489033649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7071284143368828652044865 5303463107526621489033649)
                ·
                  refine ⟨3977597330644966116775237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5303463107526621489033649 3977597330644966116775237)
                  ·
                    refine ⟨745799499495931146895357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3977597330644966116775237 745799499495931146895357)
                    ·
                      rfl

theorem cell22_2178659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 4].length) (baseStart_2178659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178659 prefixEnd_2178659 := by exact prefixLift 2178659
  have htrace : WordTrace (prefixWord ++ tailWord_2178659) baseStart_2178659 baseEnd_2178659 := by
    simpa [prefixWord, tailWord_2178659, baseEnd_2178659] using wordTrace_append hprefix tailTrace_2178659
  have hstable : (prefixWord ++ tailWord_2178659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178659).length < 2 ^ (prefixWord ++ tailWord_2178659).sum := by decide
  have hdescent : baseEnd_2178659 < baseStart_2178659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178661 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 2, 3]
def baseStart_2178661 : Nat := 118140960795 + 2178661 * 2 ^ 59
def prefixEnd_2178661 : Nat := 4983230072969 + 3 ^ 40 * 2178661 * 2
def baseEnd_2178661 : Nat := 745800184136803808345351

theorem tailTrace_2178661 : CollatzResearch.WordTrace tailWord_2178661 prefixEnd_2178661 745800184136803808345351 := by
  unfold tailWord_2178661
  simp only [CollatzResearch.WordTrace]
  refine ⟨79462294760090757520655837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52974863173393838347103891 79462294760090757520655837)
  ·
    refine ⟨29798360535034034070245939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79462294760090757520655837 29798360535034034070245939)
    ·
      refine ⟨44697540802551051105368909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29798360535034034070245939 44697540802551051105368909)
      ·
        refine ⟨16761577800956644164513341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44697540802551051105368909 16761577800956644164513341)
        ·
          refine ⟨6285591675358741561692503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16761577800956644164513341 6285591675358741561692503)
          ·
            refine ⟨9428387513038112342538755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6285591675358741561692503 9428387513038112342538755)
            ·
              refine ⟨14142581269557168513808133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9428387513038112342538755 14142581269557168513808133)
              ·
                refine ⟨2651733988041969096339025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14142581269557168513808133 2651733988041969096339025)
                ·
                  refine ⟨1988800491031476822254269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2651733988041969096339025 1988800491031476822254269)
                  ·
                    refine ⟨745800184136803808345351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1988800491031476822254269 745800184136803808345351)
                    ·
                      rfl

theorem cell22_2178661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_2178661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178661 prefixEnd_2178661 := by exact prefixLift 2178661
  have htrace : WordTrace (prefixWord ++ tailWord_2178661) baseStart_2178661 baseEnd_2178661 := by
    simpa [prefixWord, tailWord_2178661, baseEnd_2178661] using wordTrace_append hprefix tailTrace_2178661
  have hstable : (prefixWord ++ tailWord_2178661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178661).length < 2 ^ (prefixWord ++ tailWord_2178661).sum := by decide
  have hdescent : baseEnd_2178661 < baseStart_2178661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178674 : List Nat := [3, 2, 1, 2, 3, 1, 3, 7]
def baseStart_2178674 : Nat := 118140960795 + 2178674 * 2 ^ 59
def prefixEnd_2178674 : Nat := 4983230072969 + 3 ^ 40 * 2178674 * 2
def baseEnd_2178674 : Nat := 82867181589164011974479

theorem tailTrace_2178674 : CollatzResearch.WordTrace tailWord_2178674 prefixEnd_2178674 82867181589164011974479 := by
  unfold tailWord_2178674
  simp only [CollatzResearch.WordTrace]
  refine ⟨19865692227260915185219769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52975179272695773827252717 19865692227260915185219769)
  ·
    refine ⟨14899269170445686388914827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19865692227260915185219769 14899269170445686388914827)
    ·
      refine ⟨22348903755668529583372241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14899269170445686388914827 22348903755668529583372241)
      ·
        refine ⟨16761677816751397187529181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22348903755668529583372241 16761677816751397187529181)
        ·
          refine ⟨6285629181281773945323443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16761677816751397187529181 6285629181281773945323443)
          ·
            refine ⟨9428443771922660917985165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6285629181281773945323443 9428443771922660917985165)
            ·
              refine ⟨3535666414470997844244437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9428443771922660917985165 3535666414470997844244437)
              ·
                refine ⟨82867181589164011974479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3535666414470997844244437 82867181589164011974479)
                ·
                  rfl

theorem cell22_2178674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_2178674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178674 prefixEnd_2178674 := by exact prefixLift 2178674
  have htrace : WordTrace (prefixWord ++ tailWord_2178674) baseStart_2178674 baseEnd_2178674 := by
    simpa [prefixWord, tailWord_2178674, baseEnd_2178674] using wordTrace_append hprefix tailTrace_2178674
  have hstable : (prefixWord ++ tailWord_2178674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178674).length < 2 ^ (prefixWord ++ tailWord_2178674).sum := by decide
  have hdescent : baseEnd_2178674 < baseStart_2178674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178678 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_2178678 : Nat := 118140960795 + 2178678 * 2 ^ 59
def prefixEnd_2178678 : Nat := 4983230072969 + 3 ^ 40 * 2178678 * 2
def baseEnd_2178678 : Nat := 745806003584221430670299

theorem tailTrace_2178678 : CollatzResearch.WordTrace tailWord_2178678 prefixEnd_2178678 745806003584221430670299 := by
  unfold tailWord_2178678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966432175064323089001543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52975276534019446282683125 4966432175064323089001543)
  ·
    refine ⟨7449648262596484633502315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4966432175064323089001543 7449648262596484633502315)
    ·
      refine ⟨11174472393894726950253473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7449648262596484633502315 11174472393894726950253473)
      ·
        refine ⟨8380854295421045212690105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11174472393894726950253473 8380854295421045212690105)
        ·
          refine ⟨6285640721565783909517579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8380854295421045212690105 6285640721565783909517579)
          ·
            refine ⟨9428461082348675864276369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6285640721565783909517579 9428461082348675864276369)
            ·
              refine ⟨7071345811761506898207277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9428461082348675864276369 7071345811761506898207277)
              ·
                refine ⟨2651754679410565086827729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7071345811761506898207277 2651754679410565086827729)
                ·
                  refine ⟨1988816009557923815120797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2651754679410565086827729 1988816009557923815120797)
                  ·
                    refine ⟨745806003584221430670299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1988816009557923815120797 745806003584221430670299)
                    ·
                      rfl

theorem cell22_2178678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_2178678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178678 prefixEnd_2178678 := by exact prefixLift 2178678
  have htrace : WordTrace (prefixWord ++ tailWord_2178678) baseStart_2178678 baseEnd_2178678 := by
    simpa [prefixWord, tailWord_2178678, baseEnd_2178678] using wordTrace_append hprefix tailTrace_2178678
  have hstable : (prefixWord ++ tailWord_2178678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178678).length < 2 ^ (prefixWord ++ tailWord_2178678).sum := by decide
  have hdescent : baseEnd_2178678 < baseStart_2178678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178766 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2178766 : Nat := 118140960795 + 2178766 * 2 ^ 59
def prefixEnd_2178766 : Nat := 4983230072969 + 3 ^ 40 * 2178766 * 2
def baseEnd_2178766 : Nat := 745836127782618534470029

theorem tailTrace_2178766 : CollatzResearch.WordTrace tailWord_2178766 prefixEnd_2178766 745836127782618534470029 := by
  unfold tailWord_2178766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9933265553088795056653519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52977416283140240302152101 9933265553088795056653519)
  ·
    refine ⟨14899898329633192584980279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9933265553088795056653519 14899898329633192584980279)
    ·
      refine ⟨22349847494449788877470419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14899898329633192584980279 22349847494449788877470419)
      ·
        refine ⟨33524771241674683316205629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22349847494449788877470419 33524771241674683316205629)
        ·
          refine ⟨12571789215628006243577111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33524771241674683316205629 12571789215628006243577111)
          ·
            refine ⟨18857683823442009365365667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12571789215628006243577111 18857683823442009365365667)
            ·
              refine ⟨28286525735163014048048501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18857683823442009365365667 28286525735163014048048501)
              ·
                refine ⟨2651861787671532567004547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28286525735163014048048501 2651861787671532567004547)
                ·
                  refine ⟨3977792681507298850506821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2651861787671532567004547 3977792681507298850506821)
                  ·
                    refine ⟨745836127782618534470029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3977792681507298850506821 745836127782618534470029)
                    ·
                      rfl

theorem cell22_2178766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2178766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178766 prefixEnd_2178766 := by exact prefixLift 2178766
  have htrace : WordTrace (prefixWord ++ tailWord_2178766) baseStart_2178766 baseEnd_2178766 := by
    simpa [prefixWord, tailWord_2178766, baseEnd_2178766] using wordTrace_append hprefix tailTrace_2178766
  have hstable : (prefixWord ++ tailWord_2178766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178766).length < 2 ^ (prefixWord ++ tailWord_2178766).sum := by decide
  have hdescent : baseEnd_2178766 < baseStart_2178766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178774 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2178774 : Nat := 118140960795 + 2178774 * 2 ^ 59
def prefixEnd_2178774 : Nat := 4983230072969 + 3 ^ 40 * 2178774 * 2
def baseEnd_2178774 : Nat := 745838866346109180270005

theorem tailTrace_2178774 : CollatzResearch.WordTrace tailWord_2178774 prefixEnd_2178774 745838866346109180270005 := by
  unfold tailWord_2178774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966651013042586113719961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52977610805787585213012917 4966651013042586113719961)
  ·
    refine ⟨3724988259781939585289971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4966651013042586113719961 3724988259781939585289971)
    ·
      refine ⟨5587482389672909377934957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3724988259781939585289971 5587482389672909377934957)
      ·
        refine ⟨2095305896127341016725609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5587482389672909377934957 2095305896127341016725609)
        ·
          refine ⟨1571479422095505762544207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2095305896127341016725609 1571479422095505762544207)
          ·
            refine ⟨2357219133143258643816311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571479422095505762544207 2357219133143258643816311)
            ·
              refine ⟨3535828699714887965724467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357219133143258643816311 3535828699714887965724467)
              ·
                refine ⟨5303743049572331948586701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535828699714887965724467 5303743049572331948586701)
                ·
                  refine ⟨1988903643589624480720013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5303743049572331948586701 1988903643589624480720013)
                  ·
                    refine ⟨745838866346109180270005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1988903643589624480720013 745838866346109180270005)
                    ·
                      rfl

theorem cell22_2178774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2178774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178774 prefixEnd_2178774 := by exact prefixLift 2178774
  have htrace : WordTrace (prefixWord ++ tailWord_2178774) baseStart_2178774 baseEnd_2178774 := by
    simpa [prefixWord, tailWord_2178774, baseEnd_2178774] using wordTrace_append hprefix tailTrace_2178774
  have hstable : (prefixWord ++ tailWord_2178774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178774).length < 2 ^ (prefixWord ++ tailWord_2178774).sum := by decide
  have hdescent : baseEnd_2178774 < baseStart_2178774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178794 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2178794 : Nat := 118140960795 + 2178794 * 2 ^ 59
def prefixEnd_2178794 : Nat := 4983230072969 + 3 ^ 40 * 2178794 * 2
def baseEnd_2178794 : Nat := 745845712754835794769943

theorem tailTrace_2178794 : CollatzResearch.WordTrace tailWord_2178794 prefixEnd_2178794 745845712754835794769943 := by
  unfold tailWord_2178794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19866786417152230308811859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52978097112405947490164957 19866786417152230308811859)
  ·
    refine ⟨29800179625728345463217789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19866786417152230308811859 29800179625728345463217789)
    ·
      refine ⟨11175067359648129548706671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29800179625728345463217789 11175067359648129548706671)
      ·
        refine ⟨16762601039472194323060007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11175067359648129548706671 16762601039472194323060007)
        ·
          refine ⟨25143901559208291484590011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16762601039472194323060007 25143901559208291484590011)
          ·
            refine ⟨37715852338812437226885017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25143901559208291484590011 37715852338812437226885017)
            ·
              refine ⟨28286889254109327920163763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37715852338812437226885017 28286889254109327920163763)
              ·
                refine ⟨42430333881163991880245645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28286889254109327920163763 42430333881163991880245645)
                ·
                  refine ⟨15911375205436496955092117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42430333881163991880245645 15911375205436496955092117)
                  ·
                    refine ⟨745845712754835794769943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15911375205436496955092117 745845712754835794769943)
                    ·
                      rfl

theorem cell22_2178794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2178794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178794 prefixEnd_2178794 := by exact prefixLift 2178794
  have htrace : WordTrace (prefixWord ++ tailWord_2178794) baseStart_2178794 baseEnd_2178794 := by
    simpa [prefixWord, tailWord_2178794, baseEnd_2178794] using wordTrace_append hprefix tailTrace_2178794
  have hstable : (prefixWord ++ tailWord_2178794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178794).length < 2 ^ (prefixWord ++ tailWord_2178794).sum := by decide
  have hdescent : baseEnd_2178794 < baseStart_2178794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178862 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2178862 : Nat := 118140960795 + 2178862 * 2 ^ 59
def prefixEnd_2178862 : Nat := 4983230072969 + 3 ^ 40 * 2178862 * 2
def baseEnd_2178862 : Nat := 745868990544506284069735

theorem tailTrace_2178862 : CollatzResearch.WordTrace tailWord_2178862 prefixEnd_2178862 745868990544506284069735 := by
  unfold tailWord_2178862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9933703229045321106090355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52979750554908379232481893 9933703229045321106090355)
  ·
    refine ⟨14900554843567981659135533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9933703229045321106090355 14900554843567981659135533)
    ·
      refine ⟨5587708066337993122175825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14900554843567981659135533 5587708066337993122175825)
      ·
        refine ⟨4190781049753494841631869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5587708066337993122175825 4190781049753494841631869)
        ·
          refine ⟨1571542893657560565611951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4190781049753494841631869 1571542893657560565611951)
          ·
            refine ⟨2357314340486340848417927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571542893657560565611951 2357314340486340848417927)
            ·
              refine ⟨3535971510729511272626891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357314340486340848417927 3535971510729511272626891)
              ·
                refine ⟨5303957266094266908940337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535971510729511272626891 5303957266094266908940337)
                ·
                  refine ⟨3977967949570700181705253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5303957266094266908940337 3977967949570700181705253)
                  ·
                    refine ⟨745868990544506284069735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3977967949570700181705253 745868990544506284069735)
                    ·
                      rfl

theorem cell22_2178862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2178862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178862 prefixEnd_2178862 := by exact prefixLift 2178862
  have htrace : WordTrace (prefixWord ++ tailWord_2178862) baseStart_2178862 baseEnd_2178862 := by
    simpa [prefixWord, tailWord_2178862, baseEnd_2178862] using wordTrace_append hprefix tailTrace_2178862
  have hstable : (prefixWord ++ tailWord_2178862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178862).length < 2 ^ (prefixWord ++ tailWord_2178862).sum := by decide
  have hdescent : baseEnd_2178862 < baseStart_2178862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178888 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 5]
def baseStart_2178888 : Nat := 118140960795 + 2178888 * 2 ^ 59
def prefixEnd_2178888 : Nat := 4983230072969 + 3 ^ 40 * 2178888 * 2
def baseEnd_2178888 : Nat := 248625963625283627639885

theorem tailTrace_2178888 : CollatzResearch.WordTrace tailWord_2178888 prefixEnd_2178888 248625963625283627639885 := by
  unfold tailWord_2178888
  simp only [CollatzResearch.WordTrace]
  refine ⟨39735287065134187644584659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52980382753512250192779545 39735287065134187644584659)
  ·
    refine ⟨59602930597701281466876989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39735287065134187644584659 59602930597701281466876989)
    ·
      refine ⟨22351098974137980550078871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59602930597701281466876989 22351098974137980550078871)
      ·
        refine ⟨33526648461206970825118307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22351098974137980550078871 33526648461206970825118307)
        ·
          refine ⟨50289972691810456237677461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33526648461206970825118307 50289972691810456237677461)
          ·
            refine ⟨2357342469928615136141131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50289972691810456237677461 2357342469928615136141131)
            ·
              refine ⟨3536013704892922704211697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357342469928615136141131 3536013704892922704211697)
              ·
                refine ⟨2652010278669692028158773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3536013704892922704211697 2652010278669692028158773)
                ·
                  refine ⟨248625963625283627639885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2652010278669692028158773 248625963625283627639885)
                  ·
                    rfl

theorem cell22_2178888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_2178888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178888 prefixEnd_2178888 := by exact prefixLift 2178888
  have htrace : WordTrace (prefixWord ++ tailWord_2178888) baseStart_2178888 baseEnd_2178888 := by
    simpa [prefixWord, tailWord_2178888, baseEnd_2178888] using wordTrace_append hprefix tailTrace_2178888
  have hstable : (prefixWord ++ tailWord_2178888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178888).length < 2 ^ (prefixWord ++ tailWord_2178888).sum := by decide
  have hdescent : baseEnd_2178888 < baseStart_2178888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2178948 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_2178948 : Nat := 118140960795 + 2178948 * 2 ^ 59
def prefixEnd_2178948 : Nat := 4983230072969 + 3 ^ 40 * 2178948 * 2
def baseEnd_2178948 : Nat := 745898430102030726419471

theorem tailTrace_2178948 : CollatzResearch.WordTrace tailWord_2178948 prefixEnd_2178948 745898430102030726419471 := by
  unfold tailWord_2178948
  simp only [CollatzResearch.WordTrace]
  refine ⟨39736381255025502768176749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52981841673367337024235665 39736381255025502768176749)
  ·
    refine ⟨14901142970634563538066281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39736381255025502768176749 14901142970634563538066281)
    ·
      refine ⟨11175857227975922653549711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14901142970634563538066281 11175857227975922653549711)
      ·
        refine ⟨16763785841963883980324567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11175857227975922653549711 16763785841963883980324567)
        ·
          refine ⟨25145678762945825970486851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16763785841963883980324567 25145678762945825970486851)
          ·
            refine ⟨37718518144418738955730277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25145678762945825970486851 37718518144418738955730277)
            ·
              refine ⟨7072222152078513554199427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37718518144418738955730277 7072222152078513554199427)
              ·
                refine ⟨10608333228117770331299141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7072222152078513554199427 10608333228117770331299141)
                ·
                  refine ⟨1989062480272081937118589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10608333228117770331299141 1989062480272081937118589)
                  ·
                    refine ⟨745898430102030726419471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989062480272081937118589 745898430102030726419471)
                    ·
                      rfl

theorem cell22_2178948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_2178948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2178948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2178948 prefixEnd_2178948 := by exact prefixLift 2178948
  have htrace : WordTrace (prefixWord ++ tailWord_2178948) baseStart_2178948 baseEnd_2178948 := by
    simpa [prefixWord, tailWord_2178948, baseEnd_2178948] using wordTrace_append hprefix tailTrace_2178948
  have hstable : (prefixWord ++ tailWord_2178948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2178948).length < 2 ^ (prefixWord ++ tailWord_2178948).sum := by decide
  have hdescent : baseEnd_2178948 < baseStart_2178948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2178948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179057 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 5]
def baseStart_2179057 : Nat := 118140960795 + 2179057 * 2 ^ 59
def prefixEnd_2179057 : Nat := 4983230072969 + 3 ^ 40 * 2179057 * 2
def baseEnd_2179057 : Nat := 248645247676530258481379

theorem tailTrace_2179057 : CollatzResearch.WordTrace tailWord_2179057 prefixEnd_2179057 248645247676530258481379 := by
  unfold tailWord_2179057
  simp only [CollatzResearch.WordTrace]
  refine ⟨79476738066656117152071425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52984492044437411434714283 79476738066656117152071425)
  ·
    refine ⟨59607553549992087864053569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79476738066656117152071425 59607553549992087864053569)
    ·
      refine ⟨44705665162494065898040177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59607553549992087864053569 44705665162494065898040177)
      ·
        refine ⟨33529248871870549423530133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44705665162494065898040177 33529248871870549423530133)
        ·
          refine ⟨1571683540868932004227975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33529248871870549423530133 1571683540868932004227975)
          ·
            refine ⟨2357525311303398006341963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571683540868932004227975 2357525311303398006341963)
            ·
              refine ⟨3536287966955097009512945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2357525311303398006341963 3536287966955097009512945)
              ·
                refine ⟨2652215975216322757134709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3536287966955097009512945 2652215975216322757134709)
                ·
                  refine ⟨248645247676530258481379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2652215975216322757134709 248645247676530258481379)
                  ·
                    rfl

theorem cell22_2179057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_2179057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179057 prefixEnd_2179057 := by exact prefixLift 2179057
  have htrace : WordTrace (prefixWord ++ tailWord_2179057) baseStart_2179057 baseEnd_2179057 := by
    simpa [prefixWord, tailWord_2179057, baseEnd_2179057] using wordTrace_append hprefix tailTrace_2179057
  have hstable : (prefixWord ++ tailWord_2179057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179057).length < 2 ^ (prefixWord ++ tailWord_2179057).sum := by decide
  have hdescent : baseEnd_2179057 < baseStart_2179057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179066 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_2179066 : Nat := 118140960795 + 2179066 * 2 ^ 59
def prefixEnd_2179066 : Nat := 4983230072969 + 3 ^ 40 * 2179066 * 2
def baseEnd_2179066 : Nat := 745938823913517751969109

theorem tailTrace_2179066 : CollatzResearch.WordTrace tailWord_2179066 prefixEnd_2179066 745938823913517751969109 := by
  unfold tailWord_2179066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19869266580905877922287263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52984710882415674459432701 19869266580905877922287263)
  ·
    refine ⟨29803899871358816883430895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19869266580905877922287263 29803899871358816883430895)
    ·
      refine ⟨44705849807038225325146343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29803899871358816883430895 44705849807038225325146343)
      ·
        refine ⟨67058774710557337987719515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44705849807038225325146343 67058774710557337987719515)
        ·
          refine ⟨100588162065836006981579273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67058774710557337987719515 100588162065836006981579273)
          ·
            refine ⟨75441121549377005236184455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100588162065836006981579273 75441121549377005236184455)
            ·
              refine ⟨113161682324065507854276683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75441121549377005236184455 113161682324065507854276683)
              ·
                refine ⟨169742523486098261781415025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113161682324065507854276683 169742523486098261781415025)
                ·
                  refine ⟨127306892614573696336061269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169742523486098261781415025 127306892614573696336061269)
                  ·
                    refine ⟨745938823913517751969109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127306892614573696336061269 745938823913517751969109)
                    ·
                      rfl

theorem cell22_2179066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_2179066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179066 prefixEnd_2179066 := by exact prefixLift 2179066
  have htrace : WordTrace (prefixWord ++ tailWord_2179066) baseStart_2179066 baseEnd_2179066 := by
    simpa [prefixWord, tailWord_2179066, baseEnd_2179066] using wordTrace_append hprefix tailTrace_2179066
  have hstable : (prefixWord ++ tailWord_2179066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179066).length < 2 ^ (prefixWord ++ tailWord_2179066).sum := by decide
  have hdescent : baseEnd_2179066 < baseStart_2179066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179068 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 6]
def baseStart_2179068 : Nat := 118140960795 + 2179068 * 2 ^ 59
def prefixEnd_2179068 : Nat := 4983230072969 + 3 ^ 40 * 2179068 * 2
def baseEnd_2179068 : Nat := 248646502851463471139701

theorem tailTrace_2179068 : CollatzResearch.WordTrace tailWord_2179068 prefixEnd_2179068 248646502851463471139701 := by
  unfold tailWord_2179068
  simp only [CollatzResearch.WordTrace]
  refine ⟨39738569634808133015360929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52984759513077510687147905 39738569634808133015360929)
  ·
    refine ⟨29803927226106099761520697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39738569634808133015360929 29803927226106099761520697)
    ·
      refine ⟨22352945419579574821140523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29803927226106099761520697 22352945419579574821140523)
      ·
        refine ⟨33529418129369362231710785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22352945419579574821140523 33529418129369362231710785)
        ·
          refine ⟨25147063597027021673783089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33529418129369362231710785 25147063597027021673783089)
          ·
            refine ⟨18860297697770266255337317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25147063597027021673783089 18860297697770266255337317)
            ·
              refine ⟨3536305818331924922875747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18860297697770266255337317 3536305818331924922875747)
              ·
                refine ⟨5304458727497887384313621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3536305818331924922875747 5304458727497887384313621)
                ·
                  refine ⟨248646502851463471139701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5304458727497887384313621 248646502851463471139701)
                  ·
                    rfl

theorem cell22_2179068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_2179068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179068 prefixEnd_2179068 := by exact prefixLift 2179068
  have htrace : WordTrace (prefixWord ++ tailWord_2179068) baseStart_2179068 baseEnd_2179068 := by
    simpa [prefixWord, tailWord_2179068, baseEnd_2179068] using wordTrace_append hprefix tailTrace_2179068
  have hstable : (prefixWord ++ tailWord_2179068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179068).length < 2 ^ (prefixWord ++ tailWord_2179068).sum := by decide
  have hdescent : baseEnd_2179068 < baseStart_2179068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179098 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_2179098 : Nat := 118140960795 + 2179098 * 2 ^ 59
def prefixEnd_2179098 : Nat := 4983230072969 + 3 ^ 40 * 2179098 * 2
def baseEnd_2179098 : Nat := 745949778167480335169011

theorem tailTrace_2179098 : CollatzResearch.WordTrace tailWord_2179098 prefixEnd_2179098 745949778167480335169011 := by
  unfold tailWord_2179098
  simp only [CollatzResearch.WordTrace]
  refine ⟨19869558364876895288578487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52985488973005054102875965 19869558364876895288578487)
  ·
    refine ⟨29804337547315342932867731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19869558364876895288578487 29804337547315342932867731)
    ·
      refine ⟨44706506320973014399301597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29804337547315342932867731 44706506320973014399301597)
      ·
        refine ⟨16764939870364880399738099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44706506320973014399301597 16764939870364880399738099)
        ·
          refine ⟨25147409805547320599607149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16764939870364880399738099 25147409805547320599607149)
          ·
            refine ⟨9430278677080245224852681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25147409805547320599607149 9430278677080245224852681)
            ·
              refine ⟨7072709007810183918639511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9430278677080245224852681 7072709007810183918639511)
              ·
                refine ⟨10609063511715275877959267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7072709007810183918639511 10609063511715275877959267)
                ·
                  refine ⟨15913595267572913816938901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10609063511715275877959267 15913595267572913816938901)
                  ·
                    refine ⟨745949778167480335169011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15913595267572913816938901 745949778167480335169011)
                    ·
                      rfl

theorem cell22_2179098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_2179098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179098 prefixEnd_2179098 := by exact prefixLift 2179098
  have htrace : WordTrace (prefixWord ++ tailWord_2179098) baseStart_2179098 baseEnd_2179098 := by
    simpa [prefixWord, tailWord_2179098, baseEnd_2179098] using wordTrace_append hprefix tailTrace_2179098
  have hstable : (prefixWord ++ tailWord_2179098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179098).length < 2 ^ (prefixWord ++ tailWord_2179098).sum := by decide
  have hdescent : baseEnd_2179098 < baseStart_2179098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179100 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_2179100 : Nat := 118140960795 + 2179100 * 2 ^ 59
def prefixEnd_2179100 : Nat := 4983230072969 + 3 ^ 40 * 2179100 * 2
def baseEnd_2179100 : Nat := 745950462808352996619005

theorem tailTrace_2179100 : CollatzResearch.WordTrace tailWord_2179100 prefixEnd_2179100 745950462808352996619005 := by
  unfold tailWord_2179100
  simp only [CollatzResearch.WordTrace]
  refine ⟨39739153202750167747943377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52985537603666890330591169 39739153202750167747943377)
  ·
    refine ⟨29804364902062625810957533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39739153202750167747943377 29804364902062625810957533)
    ·
      refine ⟨11176636838273484679109075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29804364902062625810957533 11176636838273484679109075)
      ·
        refine ⟨16764955257410227018663613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11176636838273484679109075 16764955257410227018663613)
        ·
          refine ⟨6286858221528835131998855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16764955257410227018663613 6286858221528835131998855)
          ·
            refine ⟨9430287332293252697998283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6286858221528835131998855 9430287332293252697998283)
            ·
              refine ⟨14145430998439879046997425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9430287332293252697998283 14145430998439879046997425)
              ·
                refine ⟨10609073248829909285248069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14145430998439879046997425 10609073248829909285248069)
                ·
                  refine ⟨1989201234155607990984013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10609073248829909285248069 1989201234155607990984013)
                  ·
                    refine ⟨745950462808352996619005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989201234155607990984013 745950462808352996619005)
                    ·
                      rfl

theorem cell22_2179100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_2179100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179100 prefixEnd_2179100 := by exact prefixLift 2179100
  have htrace : WordTrace (prefixWord ++ tailWord_2179100) baseStart_2179100 baseEnd_2179100 := by
    simpa [prefixWord, tailWord_2179100, baseEnd_2179100] using wordTrace_append hprefix tailTrace_2179100
  have hstable : (prefixWord ++ tailWord_2179100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179100).length < 2 ^ (prefixWord ++ tailWord_2179100).sum := by decide
  have hdescent : baseEnd_2179100 < baseStart_2179100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179134 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_2179134 : Nat := 118140960795 + 2179134 * 2 ^ 59
def prefixEnd_2179134 : Nat := 4983230072969 + 3 ^ 40 * 2179134 * 2
def baseEnd_2179134 : Nat := 745962101703188241268901

theorem tailTrace_2179134 : CollatzResearch.WordTrace tailWord_2179134 prefixEnd_2179134 745962101703188241268901 := by
  unfold tailWord_2179134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9934943310922144912828057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52986364324918106201749637 9934943310922144912828057)
  ·
    refine ⟨7451207483191608684621043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9934943310922144912828057 7451207483191608684621043)
    ·
      refine ⟨11176811224787413026931565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7451207483191608684621043 11176811224787413026931565)
      ·
        refine ⟨4191304209295279885099337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11176811224787413026931565 4191304209295279885099337)
        ·
          refine ⟨3143478156971459913824503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4191304209295279885099337 3143478156971459913824503)
          ·
            refine ⟨4715217235457189870736755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143478156971459913824503 4715217235457189870736755)
            ·
              refine ⟨7072825853185784806105133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4715217235457189870736755 7072825853185784806105133)
              ·
                refine ⟨2652309694944669302289425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7072825853185784806105133 2652309694944669302289425)
                ·
                  refine ⟨1989232271208501976717069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2652309694944669302289425 1989232271208501976717069)
                  ·
                    refine ⟨745962101703188241268901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989232271208501976717069 745962101703188241268901)
                    ·
                      rfl

theorem cell22_2179134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_2179134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179134 prefixEnd_2179134 := by exact prefixLift 2179134
  have htrace : WordTrace (prefixWord ++ tailWord_2179134) baseStart_2179134 baseEnd_2179134 := by
    simpa [prefixWord, tailWord_2179134, baseEnd_2179134] using wordTrace_append hprefix tailTrace_2179134
  have hstable : (prefixWord ++ tailWord_2179134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179134).length < 2 ^ (prefixWord ++ tailWord_2179134).sum := by decide
  have hdescent : baseEnd_2179134 < baseStart_2179134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179162 : List Nat := [3, 1, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_2179162 : Nat := 118140960795 + 2179162 * 2 ^ 59
def prefixEnd_2179162 : Nat := 4983230072969 + 3 ^ 40 * 2179162 * 2
def baseEnd_2179162 : Nat := 745971686675405501568815

theorem tailTrace_2179162 : CollatzResearch.WordTrace tailWord_2179162 prefixEnd_2179162 745971686675405501568815 := by
  unfold tailWord_2179162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19870141932818930021160935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52987045154183813389762493 19870141932818930021160935)
  ·
    refine ⟨29805212899228395031741403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19870141932818930021160935 29805212899228395031741403)
    ·
      refine ⟨44707819348842592547612105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29805212899228395031741403 44707819348842592547612105)
      ·
        refine ⟨33530864511631944410709079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44707819348842592547612105 33530864511631944410709079)
        ·
          refine ⟨50296296767447916616063619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33530864511631944410709079 50296296767447916616063619)
          ·
            refine ⟨75444445151171874924095429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50296296767447916616063619 75444445151171874924095429)
            ·
              refine ⟨14145833465844726548267893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75444445151171874924095429 14145833465844726548267893)
              ·
                refine ⟨1326171887422943113900115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14145833465844726548267893 1326171887422943113900115)
                ·
                  refine ⟨1989257831134414670850173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326171887422943113900115 1989257831134414670850173)
                  ·
                    refine ⟨745971686675405501568815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989257831134414670850173 745971686675405501568815)
                    ·
                      rfl

theorem cell22_2179162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_2179162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179162 prefixEnd_2179162 := by exact prefixLift 2179162
  have htrace : WordTrace (prefixWord ++ tailWord_2179162) baseStart_2179162 baseEnd_2179162 := by
    simpa [prefixWord, tailWord_2179162, baseEnd_2179162] using wordTrace_append hprefix tailTrace_2179162
  have hstable : (prefixWord ++ tailWord_2179162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179162).length < 2 ^ (prefixWord ++ tailWord_2179162).sum := by decide
  have hdescent : baseEnd_2179162 < baseStart_2179162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179175 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 5]
def baseStart_2179175 : Nat := 118140960795 + 2179175 * 2 ^ 59
def prefixEnd_2179175 : Nat := 4983230072969 + 3 ^ 40 * 2179175 * 2
def baseEnd_2179175 : Nat := 248658712280359266997925

theorem tailTrace_2179175 : CollatzResearch.WordTrace tailWord_2179175 prefixEnd_2179175 248658712280359266997925 := by
  unfold tailWord_2179175
  simp only [CollatzResearch.WordTrace]
  refine ⟨79481041880228623304866979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52987361253485748869911319 79481041880228623304866979)
  ·
    refine ⟨119221562820342934957300469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79481041880228623304866979 119221562820342934957300469)
    ·
      refine ⟨11177021514407150152246919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119221562820342934957300469 11177021514407150152246919)
      ·
        refine ⟨16765532271610725228370379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11177021514407150152246919 16765532271610725228370379)
        ·
          refine ⟨25148298407416087842555569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16765532271610725228370379 25148298407416087842555569)
          ·
            refine ⟨18861223805562065881916677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25148298407416087842555569 18861223805562065881916677)
            ·
              refine ⟨3536479463542887352859377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18861223805562065881916677 3536479463542887352859377)
              ·
                refine ⟨2652359597657165514644533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3536479463542887352859377 2652359597657165514644533)
                ·
                  refine ⟨248658712280359266997925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2652359597657165514644533 248658712280359266997925)
                  ·
                    rfl

theorem cell22_2179175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 5].length) (baseStart_2179175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179175 prefixEnd_2179175 := by exact prefixLift 2179175
  have htrace : WordTrace (prefixWord ++ tailWord_2179175) baseStart_2179175 baseEnd_2179175 := by
    simpa [prefixWord, tailWord_2179175, baseEnd_2179175] using wordTrace_append hprefix tailTrace_2179175
  have hstable : (prefixWord ++ tailWord_2179175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179175).length < 2 ^ (prefixWord ++ tailWord_2179175).sum := by decide
  have hdescent : baseEnd_2179175 < baseStart_2179175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179190 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2179190 : Nat := 118140960795 + 2179190 * 2 ^ 59
def prefixEnd_2179190 : Nat := 4983230072969 + 3 ^ 40 * 2179190 * 2
def baseEnd_2179190 : Nat := 745981271647622761868729

theorem tailTrace_2179190 : CollatzResearch.WordTrace tailWord_2179190 prefixEnd_2179190 745981271647622761868729 := by
  unfold tailWord_2179190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4967599310948392554166439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52987725983449520577775349 4967599310948392554166439)
  ·
    refine ⟨7451398966422588831249659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4967599310948392554166439 7451398966422588831249659)
    ·
      refine ⟨11177098449633883246874489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7451398966422588831249659 11177098449633883246874489)
      ·
        refine ⟨8382823837225412435155867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11177098449633883246874489 8382823837225412435155867)
        ·
          refine ⟨12574235755838118652733801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8382823837225412435155867 12574235755838118652733801)
          ·
            refine ⟨9430676816878588989550351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12574235755838118652733801 9430676816878588989550351)
            ·
              refine ⟨14146015225317883484325527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9430676816878588989550351 14146015225317883484325527)
              ·
                refine ⟨21219022837976825226488291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14146015225317883484325527 21219022837976825226488291)
                ·
                  refine ⟨31828534256965237839732437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21219022837976825226488291 31828534256965237839732437)
                  ·
                    refine ⟨745981271647622761868729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31828534256965237839732437 745981271647622761868729)
                    ·
                      rfl

theorem cell22_2179190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2179190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179190 prefixEnd_2179190 := by exact prefixLift 2179190
  have htrace : WordTrace (prefixWord ++ tailWord_2179190) baseStart_2179190 baseEnd_2179190 := by
    simpa [prefixWord, tailWord_2179190, baseEnd_2179190] using wordTrace_append hprefix tailTrace_2179190
  have hstable : (prefixWord ++ tailWord_2179190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179190).length < 2 ^ (prefixWord ++ tailWord_2179190).sum := by decide
  have hdescent : baseEnd_2179190 < baseStart_2179190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179203 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 8]
def baseStart_2179203 : Nat := 118140960795 + 2179203 * 2 ^ 59
def prefixEnd_2179203 : Nat := 4983230072969 + 3 ^ 40 * 2179203 * 2
def baseEnd_2179203 : Nat := 248661907271098353764563

theorem tailTrace_2179203 : CollatzResearch.WordTrace tailWord_2179203 prefixEnd_2179203 248661907271098353764563 := by
  unfold tailWord_2179203
  simp only [CollatzResearch.WordTrace]
  refine ⟨79482063124127184086886263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52988042082751456057924175 79482063124127184086886263)
  ·
    refine ⟨119223094686190776130329395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79482063124127184086886263 119223094686190776130329395)
    ·
      refine ⟨178834642029286164195494093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119223094686190776130329395 178834642029286164195494093)
      ·
        refine ⟨67062990760982311573310285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178834642029286164195494093 67062990760982311573310285)
        ·
          refine ⟨25148621535368366839991357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67062990760982311573310285 25148621535368366839991357)
          ·
            refine ⟨9430733075763137564996759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25148621535368366839991357 9430733075763137564996759)
            ·
              refine ⟨14146099613644706347495139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9430733075763137564996759 14146099613644706347495139)
              ·
                refine ⟨21219149420467059521242709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14146099613644706347495139 21219149420467059521242709)
                ·
                  refine ⟨248661907271098353764563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21219149420467059521242709 248661907271098353764563)
                  ·
                    rfl

theorem cell22_2179203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 8].length) (baseStart_2179203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179203 prefixEnd_2179203 := by exact prefixLift 2179203
  have htrace : WordTrace (prefixWord ++ tailWord_2179203) baseStart_2179203 baseEnd_2179203 := by
    simpa [prefixWord, tailWord_2179203, baseEnd_2179203] using wordTrace_append hprefix tailTrace_2179203
  have hstable : (prefixWord ++ tailWord_2179203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179203).length < 2 ^ (prefixWord ++ tailWord_2179203).sum := by decide
  have hdescent : baseEnd_2179203 < baseStart_2179203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179205 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_2179205 : Nat := 118140960795 + 2179205 * 2 ^ 59
def prefixEnd_2179205 : Nat := 4983230072969 + 3 ^ 40 * 2179205 * 2
def baseEnd_2179205 : Nat := 745986406454167722743683

theorem tailTrace_2179205 : CollatzResearch.WordTrace tailWord_2179205 prefixEnd_2179205 745986406454167722743683 := by
  unfold tailWord_2179205
  simp only [CollatzResearch.WordTrace]
  refine ⟨79482136070119938428459069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52988090713413292285639379 79482136070119938428459069)
  ·
    refine ⟨29805801026294976910672151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79482136070119938428459069 29805801026294976910672151)
    ·
      refine ⟨44708701539442465366008227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29805801026294976910672151 44708701539442465366008227)
      ·
        refine ⟨67063052309163698049012341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44708701539442465366008227 67063052309163698049012341)
        ·
          refine ⟨6287161153984096692094907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67063052309163698049012341 6287161153984096692094907)
          ·
            refine ⟨9430741730976145038142361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6287161153984096692094907 9430741730976145038142361)
            ·
              refine ⟨7073056298232108778606771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9430741730976145038142361 7073056298232108778606771)
              ·
                refine ⟨10609584447348163167910157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7073056298232108778606771 10609584447348163167910157)
                ·
                  refine ⟨3978594167755561187966309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10609584447348163167910157 3978594167755561187966309)
                  ·
                    refine ⟨745986406454167722743683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3978594167755561187966309 745986406454167722743683)
                    ·
                      rfl

theorem cell22_2179205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_2179205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179205 prefixEnd_2179205 := by exact prefixLift 2179205
  have htrace : WordTrace (prefixWord ++ tailWord_2179205) baseStart_2179205 baseEnd_2179205 := by
    simpa [prefixWord, tailWord_2179205, baseEnd_2179205] using wordTrace_append hprefix tailTrace_2179205
  have hstable : (prefixWord ++ tailWord_2179205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179205).length < 2 ^ (prefixWord ++ tailWord_2179205).sum := by decide
  have hdescent : baseEnd_2179205 < baseStart_2179205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179263 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 9]
def baseStart_2179263 : Nat := 118140960795 + 2179263 * 2 ^ 59
def prefixEnd_2179263 : Nat := 4983230072969 + 3 ^ 40 * 2179263 * 2
def baseEnd_2179263 : Nat := 746006261039474904793505

theorem tailTrace_2179263 : CollatzResearch.WordTrace tailWord_2179263 prefixEnd_2179263 746006261039474904793505 := by
  unfold tailWord_2179263
  simp only [CollatzResearch.WordTrace]
  refine ⟨79484251503909814334070443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52989501002606542889380295 79484251503909814334070443)
  ·
    refine ⟨119226377255864721501105665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79484251503909814334070443 119226377255864721501105665)
    ·
      refine ⟨89419782941898541125829249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119226377255864721501105665 89419782941898541125829249)
      ·
        refine ⟨67064837206423905844371937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89419782941898541125829249 67064837206423905844371937)
        ·
          refine ⟨50298627904817929383278953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67064837206423905844371937 50298627904817929383278953)
          ·
            refine ⟨37723970928613447037459215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50298627904817929383278953 37723970928613447037459215)
            ·
              refine ⟨56585956392920170556188823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37723970928613447037459215 56585956392920170556188823)
              ·
                refine ⟨84878934589380255834283235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56585956392920170556188823 84878934589380255834283235)
                ·
                  refine ⟨127318401884070383751424853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84878934589380255834283235 127318401884070383751424853)
                  ·
                    refine ⟨746006261039474904793505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127318401884070383751424853 746006261039474904793505)
                    ·
                      rfl

theorem cell22_2179263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_2179263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179263 prefixEnd_2179263 := by exact prefixLift 2179263
  have htrace : WordTrace (prefixWord ++ tailWord_2179263) baseStart_2179263 baseEnd_2179263 := by
    simpa [prefixWord, tailWord_2179263, baseEnd_2179263] using wordTrace_append hprefix tailTrace_2179263
  have hstable : (prefixWord ++ tailWord_2179263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179263).length < 2 ^ (prefixWord ++ tailWord_2179263).sum := by decide
  have hdescent : baseEnd_2179263 < baseStart_2179263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179434 : List Nat := [3, 1, 3, 3, 1, 1, 4, 6]
def baseStart_2179434 : Nat := 118140960795 + 2179434 * 2 ^ 59
def prefixEnd_2179434 : Nat := 4983230072969 + 3 ^ 40 * 2179434 * 2
def baseEnd_2179434 : Nat := 82896088648231939863109

theorem tailTrace_2179434 : CollatzResearch.WordTrace tailWord_2179434 prefixEnd_2179434 82896088648231939863109 := by
  unfold tailWord_2179434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19872622096572577634636339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52993658924193540359030237 19872622096572577634636339)
  ·
    refine ⟨29808933144858866451954509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19872622096572577634636339 29808933144858866451954509)
    ·
      refine ⟨11178349929322074919482941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29808933144858866451954509 11178349929322074919482941)
      ·
        refine ⟨4191881223495778094806103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11178349929322074919482941 4191881223495778094806103)
        ·
          refine ⟨6287821835243667142209155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191881223495778094806103 6287821835243667142209155)
          ·
            refine ⟨9431732752865500713313733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6287821835243667142209155 9431732752865500713313733)
            ·
              refine ⟨1768449891162281383746325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9431732752865500713313733 1768449891162281383746325)
              ·
                refine ⟨82896088648231939863109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1768449891162281383746325 82896088648231939863109)
                ·
                  rfl

theorem cell22_2179434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_2179434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179434 prefixEnd_2179434 := by exact prefixLift 2179434
  have htrace : WordTrace (prefixWord ++ tailWord_2179434) baseStart_2179434 baseEnd_2179434 := by
    simpa [prefixWord, tailWord_2179434, baseEnd_2179434] using wordTrace_append hprefix tailTrace_2179434
  have hstable : (prefixWord ++ tailWord_2179434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179434).length < 2 ^ (prefixWord ++ tailWord_2179434).sum := by decide
  have hdescent : baseEnd_2179434 < baseStart_2179434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179479 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 5]
def baseStart_2179479 : Nat := 118140960795 + 2179479 * 2 ^ 59
def prefixEnd_2179479 : Nat := 4983230072969 + 3 ^ 40 * 2179479 * 2
def baseEnd_2179479 : Nat := 248693400751240780464281

theorem tailTrace_2179479 : CollatzResearch.WordTrace tailWord_2179479 prefixEnd_2179479 248693400751240780464281 := by
  unfold tailWord_2179479
  simp only [CollatzResearch.WordTrace]
  refine ⟨79492129671127283223933491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52994753114084855482622327 79492129671127283223933491)
  ·
    refine ⟨119238194506690924835900237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79492129671127283223933491 119238194506690924835900237)
    ·
      refine ⟨44714322940009096813462589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119238194506690924835900237 44714322940009096813462589)
      ·
        refine ⟨16767871102503411305048471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44714322940009096813462589 16767871102503411305048471)
        ·
          refine ⟨25151806653755116957572707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16767871102503411305048471 25151806653755116957572707)
          ·
            refine ⟨37727709980632675436359061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25151806653755116957572707 37727709980632675436359061)
            ·
              refine ⟨1768486405342156661079331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37727709980632675436359061 1768486405342156661079331)
              ·
                refine ⟨2652729608013234991618997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768486405342156661079331 2652729608013234991618997)
                ·
                  refine ⟨248693400751240780464281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2652729608013234991618997 248693400751240780464281)
                  ·
                    rfl

theorem cell22_2179479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 5].length) (baseStart_2179479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179479 prefixEnd_2179479 := by exact prefixLift 2179479
  have htrace : WordTrace (prefixWord ++ tailWord_2179479) baseStart_2179479 baseEnd_2179479 := by
    simpa [prefixWord, tailWord_2179479, baseEnd_2179479] using wordTrace_append hprefix tailTrace_2179479
  have hstable : (prefixWord ++ tailWord_2179479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179479).length < 2 ^ (prefixWord ++ tailWord_2179479).sum := by decide
  have hdescent : baseEnd_2179479 < baseStart_2179479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179537 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_2179537 : Nat := 118140960795 + 2179537 * 2 ^ 59
def prefixEnd_2179537 : Nat := 4983230072969 + 3 ^ 40 * 2179537 * 2
def baseEnd_2179537 : Nat := 746100056839029523442665

theorem tailTrace_2179537 : CollatzResearch.WordTrace tailWord_2179537 prefixEnd_2179537 746100056839029523442665 := by
  unfold tailWord_2179537
  simp only [CollatzResearch.WordTrace]
  refine ⟨79494245104917159129544865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52996163403278106086363243 79494245104917159129544865)
  ·
    refine ⟨59620683828687869347158649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79494245104917159129544865 59620683828687869347158649)
    ·
      refine ⟨44715512871515902010368987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59620683828687869347158649 44715512871515902010368987)
      ·
        refine ⟨67073269307273853015553481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44715512871515902010368987 67073269307273853015553481)
        ·
          refine ⟨50304951980455389761665111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67073269307273853015553481 50304951980455389761665111)
          ·
            refine ⟨75457427970683084642497667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50304951980455389761665111 75457427970683084642497667)
            ·
              refine ⟨113186141956024626963746501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75457427970683084642497667 113186141956024626963746501)
              ·
                refine ⟨21222401616754617555702469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113186141956024626963746501 21222401616754617555702469)
                ·
                  refine ⟨3979200303141490791694213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21222401616754617555702469 3979200303141490791694213)
                  ·
                    refine ⟨746100056839029523442665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3979200303141490791694213 746100056839029523442665)
                    ·
                      rfl

theorem cell22_2179537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_2179537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179537 prefixEnd_2179537 := by exact prefixLift 2179537
  have htrace : WordTrace (prefixWord ++ tailWord_2179537) baseStart_2179537 baseEnd_2179537 := by
    simpa [prefixWord, tailWord_2179537, baseEnd_2179537] using wordTrace_append hprefix tailTrace_2179537
  have hstable : (prefixWord ++ tailWord_2179537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179537).length < 2 ^ (prefixWord ++ tailWord_2179537).sum := by decide
  have hdescent : baseEnd_2179537 < baseStart_2179537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179573 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2179573 : Nat := 118140960795 + 2179573 * 2 ^ 59
def prefixEnd_2179573 : Nat := 4983230072969 + 3 ^ 40 * 2179573 * 2
def baseEnd_2179573 : Nat := 746112380374737429542555

theorem tailTrace_2179573 : CollatzResearch.WordTrace tailWord_2179573 prefixEnd_2179573 746112380374737429542555 := by
  unfold tailWord_2179573
  simp only [CollatzResearch.WordTrace]
  refine ⟨79495558132786737277855373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52997038755191158185236915 79495558132786737277855373)
  ·
    refine ⟨29810834299795026479195765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79495558132786737277855373 29810834299795026479195765)
    ·
      refine ⟨2794765715605783732424603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29810834299795026479195765 2794765715605783732424603)
      ·
        refine ⟨4192148573408675598636905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794765715605783732424603 4192148573408675598636905)
        ·
          refine ⟨3144111430056506698977679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4192148573408675598636905 3144111430056506698977679)
          ·
            refine ⟨4716167145084760048466519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144111430056506698977679 4716167145084760048466519)
            ·
              refine ⟨7074250717627140072699779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716167145084760048466519 7074250717627140072699779)
              ·
                refine ⟨10611376076440710109049669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7074250717627140072699779 10611376076440710109049669)
                ·
                  refine ⟨1989633014332633145446813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10611376076440710109049669 1989633014332633145446813)
                  ·
                    refine ⟨746112380374737429542555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989633014332633145446813 746112380374737429542555)
                    ·
                      rfl

theorem cell22_2179573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2179573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179573 prefixEnd_2179573 := by exact prefixLift 2179573
  have htrace : WordTrace (prefixWord ++ tailWord_2179573) baseStart_2179573 baseEnd_2179573 := by
    simpa [prefixWord, tailWord_2179573, baseEnd_2179573] using wordTrace_append hprefix tailTrace_2179573
  have hstable : (prefixWord ++ tailWord_2179573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179573).length < 2 ^ (prefixWord ++ tailWord_2179573).sum := by decide
  have hdescent : baseEnd_2179573 < baseStart_2179573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179590 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2179590 : Nat := 118140960795 + 2179590 * 2 ^ 59
def prefixEnd_2179590 : Nat := 4983230072969 + 3 ^ 40 * 2179590 * 2
def baseEnd_2179590 : Nat := 746118199822155051867503

theorem tailTrace_2179590 : CollatzResearch.WordTrace tailWord_2179590 prefixEnd_2179590 746118199822155051867503 := by
  unfold tailWord_2179590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484255567928910911913257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52997452115816766120816149 2484255567928910911913257)
  ·
    refine ⟨1863191675946683183934943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2484255567928910911913257 1863191675946683183934943)
    ·
      refine ⟨2794787513920024775902415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1863191675946683183934943 2794787513920024775902415)
      ·
        refine ⟨4192181270880037163853623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794787513920024775902415 4192181270880037163853623)
        ·
          refine ⟨6288271906320055745780435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192181270880037163853623 6288271906320055745780435)
          ·
            refine ⟨9432407859480083618670653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6288271906320055745780435 9432407859480083618670653)
            ·
              refine ⟨3537152947305031357001495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9432407859480083618670653 3537152947305031357001495)
              ·
                refine ⟨5305729420957547035502243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3537152947305031357001495 5305729420957547035502243)
                ·
                  refine ⟨7958594131436320553253365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5305729420957547035502243 7958594131436320553253365)
                  ·
                    refine ⟨746118199822155051867503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7958594131436320553253365 746118199822155051867503)
                    ·
                      rfl

theorem cell22_2179590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2179590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179590 prefixEnd_2179590 := by exact prefixLift 2179590
  have htrace : WordTrace (prefixWord ++ tailWord_2179590) baseStart_2179590 baseEnd_2179590 := by
    simpa [prefixWord, tailWord_2179590, baseEnd_2179590] using wordTrace_append hprefix tailTrace_2179590
  have hstable : (prefixWord ++ tailWord_2179590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179590).length < 2 ^ (prefixWord ++ tailWord_2179590).sum := by decide
  have hdescent : baseEnd_2179590 < baseStart_2179590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179693 : List Nat := [1, 5, 1, 1, 3, 2, 1, 4, 4]
def baseStart_2179693 : Nat := 118140960795 + 2179693 * 2 ^ 59
def prefixEnd_2179693 : Nat := 4983230072969 + 3 ^ 40 * 2179693 * 2
def baseEnd_2179693 : Nat := 248717819609032372180729

theorem tailTrace_2179693 : CollatzResearch.WordTrace tailWord_2179693 prefixEnd_2179693 248717819609032372180729 := by
  unfold tailWord_2179693
  simp only [CollatzResearch.WordTrace]
  refine ⟨79499934892351997772223733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52999956594901331848149155 79499934892351997772223733)
  ·
    refine ⟨7453118896157999791145975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79499934892351997772223733 7453118896157999791145975)
    ·
      refine ⟨11179678344236999686718963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7453118896157999791145975 11179678344236999686718963)
      ·
        refine ⟨16769517516355499530078445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11179678344236999686718963 16769517516355499530078445)
        ·
          refine ⟨6288569068633312323779417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16769517516355499530078445 6288569068633312323779417)
          ·
            refine ⟨4716426801474984242834563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6288569068633312323779417 4716426801474984242834563)
            ·
              refine ⟨7074640202212476364251845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4716426801474984242834563 7074640202212476364251845)
              ·
                refine ⟨1326495037914839318297221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7074640202212476364251845 1326495037914839318297221)
                ·
                  refine ⟨248717819609032372180729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1326495037914839318297221 248717819609032372180729)
                  ·
                    rfl

theorem cell22_2179693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_2179693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179693 prefixEnd_2179693 := by exact prefixLift 2179693
  have htrace : WordTrace (prefixWord ++ tailWord_2179693) baseStart_2179693 baseEnd_2179693 := by
    simpa [prefixWord, tailWord_2179693, baseEnd_2179693] using wordTrace_append hprefix tailTrace_2179693
  have hstable : (prefixWord ++ tailWord_2179693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179693).length < 2 ^ (prefixWord ++ tailWord_2179693).sum := by decide
  have hdescent : baseEnd_2179693 < baseStart_2179693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179736 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 5, 3]
def baseStart_2179736 : Nat := 118140960795 + 2179736 * 2 ^ 59
def prefixEnd_2179736 : Nat := 4983230072969 + 3 ^ 40 * 2179736 * 2
def baseEnd_2179736 : Nat := 746168178605859337717055

theorem tailTrace_2179736 : CollatzResearch.WordTrace tailWord_2179736 prefixEnd_2179736 746168178605859337717055 := by
  unfold tailWord_2179736
  simp only [CollatzResearch.WordTrace]
  refine ⟨39750751615598108058019531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53001002154130810744026041 39750751615598108058019531)
  ·
    refine ⟨59626127423397162087029297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39750751615598108058019531 59626127423397162087029297)
    ·
      refine ⟨44719595567547871565271973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59626127423397162087029297 44719595567547871565271973)
      ·
        refine ⟨8384924168915225918488495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44719595567547871565271973 8384924168915225918488495)
        ·
          refine ⟨12577386253372838877732743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8384924168915225918488495 12577386253372838877732743)
          ·
            refine ⟨18866079380059258316599115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12577386253372838877732743 18866079380059258316599115)
            ·
              refine ⟨28299119070088887474898673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18866079380059258316599115 28299119070088887474898673)
              ·
                refine ⟨21224339302566665606174005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28299119070088887474898673 21224339302566665606174005)
                ·
                  refine ⟨1989781809615624900578813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21224339302566665606174005 1989781809615624900578813)
                  ·
                    refine ⟨746168178605859337717055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989781809615624900578813 746168178605859337717055)
                    ·
                      rfl

theorem cell22_2179736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_2179736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179736 prefixEnd_2179736 := by exact prefixLift 2179736
  have htrace : WordTrace (prefixWord ++ tailWord_2179736) baseStart_2179736 baseEnd_2179736 := by
    simpa [prefixWord, tailWord_2179736, baseEnd_2179736] using wordTrace_append hprefix tailTrace_2179736
  have hstable : (prefixWord ++ tailWord_2179736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179736).length < 2 ^ (prefixWord ++ tailWord_2179736).sum := by decide
  have hdescent : baseEnd_2179736 < baseStart_2179736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179804 : List Nat := [2, 2, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2179804 : Nat := 118140960795 + 2179804 * 2 ^ 59
def prefixEnd_2179804 : Nat := 4983230072969 + 3 ^ 40 * 2179804 * 2
def baseEnd_2179804 : Nat := 746191456395529827016847

theorem tailTrace_2179804 : CollatzResearch.WordTrace tailWord_2179804 prefixEnd_2179804 746191456395529827016847 := by
  unfold tailWord_2179804
  simp only [CollatzResearch.WordTrace]
  refine ⟨39751991697474931864757233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53002655596633242486342977 39751991697474931864757233)
  ·
    refine ⟨29813993773106198898567925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39751991697474931864757233 29813993773106198898567925)
    ·
      refine ⟨2795061916228706146740743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29813993773106198898567925 2795061916228706146740743)
      ·
        refine ⟨4192592874343059220111115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2795061916228706146740743 4192592874343059220111115)
        ·
          refine ⟨6288889311514588830166673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192592874343059220111115 6288889311514588830166673)
          ·
            refine ⟨4716666983635941622625005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6288889311514588830166673 4716666983635941622625005)
            ·
              refine ⟨1768750118863478108484377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4716666983635941622625005 1768750118863478108484377)
              ·
                refine ⟨1326562589147608581363283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1768750118863478108484377 1326562589147608581363283)
                ·
                  refine ⟨1989843883721412872044925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326562589147608581363283 1989843883721412872044925)
                  ·
                    refine ⟨746191456395529827016847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989843883721412872044925 746191456395529827016847)
                    ·
                      rfl

theorem cell22_2179804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2179804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179804 prefixEnd_2179804 := by exact prefixLift 2179804
  have htrace : WordTrace (prefixWord ++ tailWord_2179804) baseStart_2179804 baseEnd_2179804 := by
    simpa [prefixWord, tailWord_2179804, baseEnd_2179804] using wordTrace_append hprefix tailTrace_2179804
  have hstable : (prefixWord ++ tailWord_2179804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179804).length < 2 ^ (prefixWord ++ tailWord_2179804).sum := by decide
  have hdescent : baseEnd_2179804 < baseStart_2179804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2179892 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2179892 : Nat := 118140960795 + 2179892 * 2 ^ 59
def prefixEnd_2179892 : Nat := 4983230072969 + 3 ^ 40 * 2179892 * 2
def baseEnd_2179892 : Nat := 746221580593926930816577

theorem tailTrace_2179892 : CollatzResearch.WordTrace tailWord_2179892 prefixEnd_2179892 746221580593926930816577 := by
  unfold tailWord_2179892
  simp only [CollatzResearch.WordTrace]
  refine ⟨39753596509315527379358965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53004795345754036505811953 39753596509315527379358965)
  ·
    refine ⟨3726899672748330691814903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39753596509315527379358965 3726899672748330691814903)
    ·
      refine ⟨5590349509122496037722355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726899672748330691814903 5590349509122496037722355)
      ·
        refine ⟨8385524263683744056583533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5590349509122496037722355 8385524263683744056583533)
        ·
          refine ⟨3144571598881404021218825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8385524263683744056583533 3144571598881404021218825)
          ·
            refine ⟨2358428699161053015914119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3144571598881404021218825 2358428699161053015914119)
            ·
              refine ⟨3537643048741579523871179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358428699161053015914119 3537643048741579523871179)
              ·
                refine ⟨5306464573112369285806769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3537643048741579523871179 5306464573112369285806769)
                ·
                  refine ⟨3979848429834276964355077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5306464573112369285806769 3979848429834276964355077)
                  ·
                    refine ⟨746221580593926930816577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3979848429834276964355077 746221580593926930816577)
                    ·
                      rfl

theorem cell22_2179892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2179892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2179892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2179892 prefixEnd_2179892 := by exact prefixLift 2179892
  have htrace : WordTrace (prefixWord ++ tailWord_2179892) baseStart_2179892 baseEnd_2179892 := by
    simpa [prefixWord, tailWord_2179892, baseEnd_2179892] using wordTrace_append hprefix tailTrace_2179892
  have hstable : (prefixWord ++ tailWord_2179892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2179892).length < 2 ^ (prefixWord ++ tailWord_2179892).sum := by decide
  have hdescent : baseEnd_2179892 < baseStart_2179892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2179892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180074 : List Nat := [3, 1, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_2180074 : Nat := 118140960795 + 2180074 * 2 ^ 59
def prefixEnd_2180074 : Nat := 4983230072969 + 3 ^ 40 * 2180074 * 2
def baseEnd_2180074 : Nat := 746283882913339122766019

theorem tailTrace_2180074 : CollatzResearch.WordTrace tailWord_2180074 prefixEnd_2180074 746283882913339122766019 := by
  unfold tailWord_2180074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19878457775992924960460819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53009220735981133227895517 19878457775992924960460819)
  ·
    refine ⟨29817686663989387440691229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19878457775992924960460819 29817686663989387440691229)
    ·
      refine ⟨11181632498996020290259211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29817686663989387440691229 11181632498996020290259211)
      ·
        refine ⟨16772448748494030435388817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11181632498996020290259211 16772448748494030435388817)
        ·
          refine ⟨12579336561370522826541613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16772448748494030435388817 12579336561370522826541613)
          ·
            refine ⟨4717251210513946059953105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12579336561370522826541613 4717251210513946059953105)
            ·
              refine ⟨3537938407885459544964829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4717251210513946059953105 3537938407885459544964829)
              ·
                refine ⟨1326726902957047329361811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3537938407885459544964829 1326726902957047329361811)
                ·
                  refine ⟨1990090354435570994042717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326726902957047329361811 1990090354435570994042717)
                  ·
                    refine ⟨746283882913339122766019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990090354435570994042717 746283882913339122766019)
                    ·
                      rfl

theorem cell22_2180074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_2180074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180074 prefixEnd_2180074 := by exact prefixLift 2180074
  have htrace : WordTrace (prefixWord ++ tailWord_2180074) baseStart_2180074 baseEnd_2180074 := by
    simpa [prefixWord, tailWord_2180074, baseEnd_2180074] using wordTrace_append hprefix tailTrace_2180074
  have hstable : (prefixWord ++ tailWord_2180074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180074).length < 2 ^ (prefixWord ++ tailWord_2180074).sum := by decide
  have hdescent : baseEnd_2180074 < baseStart_2180074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180117 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_2180117 : Nat := 118140960795 + 2180117 * 2 ^ 59
def prefixEnd_2180117 : Nat := 4983230072969 + 3 ^ 40 * 2180117 * 2
def baseEnd_2180117 : Nat := 746298602692101343940887

theorem tailTrace_2180117 : CollatzResearch.WordTrace tailWord_2180117 prefixEnd_2180117 746298602692101343940887 := by
  unfold tailWord_2180117
  simp only [CollatzResearch.WordTrace]
  refine ⟨79515399442815918185658605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53010266295210612123772403 79515399442815918185658605)
  ·
    refine ⟨29818274791055969319621977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79515399442815918185658605 29818274791055969319621977)
    ·
      refine ⟨22363706093291976989716483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29818274791055969319621977 22363706093291976989716483)
      ·
        refine ⟨33545559139937965484574725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22363706093291976989716483 33545559139937965484574725)
        ·
          refine ⟨6289792338738368528357761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33545559139937965484574725 6289792338738368528357761)
          ·
            refine ⟨4717344254053776396268321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6289792338738368528357761 4717344254053776396268321)
            ·
              refine ⟨3538008190540332297201241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4717344254053776396268321 3538008190540332297201241)
              ·
                refine ⟨2653506142905249222900931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3538008190540332297201241 2653506142905249222900931)
                ·
                  refine ⟨3980259214357873834351397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2653506142905249222900931 3980259214357873834351397)
                  ·
                    refine ⟨746298602692101343940887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3980259214357873834351397 746298602692101343940887)
                    ·
                      rfl

theorem cell22_2180117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_2180117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180117 prefixEnd_2180117 := by exact prefixLift 2180117
  have htrace : WordTrace (prefixWord ++ tailWord_2180117) baseStart_2180117 baseEnd_2180117 := by
    simpa [prefixWord, tailWord_2180117, baseEnd_2180117] using wordTrace_append hprefix tailTrace_2180117
  have hstable : (prefixWord ++ tailWord_2180117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180117).length < 2 ^ (prefixWord ++ tailWord_2180117).sum := by decide
  have hdescent : baseEnd_2180117 < baseStart_2180117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180145 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_2180145 : Nat := 118140960795 + 2180145 * 2 ^ 59
def prefixEnd_2180145 : Nat := 4983230072969 + 3 ^ 40 * 2180145 * 2
def baseEnd_2180145 : Nat := 746308187664318604240801

theorem tailTrace_2180145 : CollatzResearch.WordTrace tailWord_2180145 prefixEnd_2180145 746308187664318604240801 := by
  unfold tailWord_2180145
  simp only [CollatzResearch.WordTrace]
  refine ⟨79516420686714478967677889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53010947124476319311785259 79516420686714478967677889)
  ·
    refine ⟨59637315515035859225758417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79516420686714478967677889 59637315515035859225758417)
    ·
      refine ⟨44727986636276894419318813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59637315515035859225758417 44727986636276894419318813)
      ·
        refine ⟨16772994988603835407244555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44727986636276894419318813 16772994988603835407244555)
        ·
          refine ⟨25159492482905753110866833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16772994988603835407244555 25159492482905753110866833)
          ·
            refine ⟨18869619362179314833150125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25159492482905753110866833 18869619362179314833150125)
            ·
              refine ⟨7076107260817243062431297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18869619362179314833150125 7076107260817243062431297)
              ·
                refine ⟨5307080445612932296823473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7076107260817243062431297 5307080445612932296823473)
                ·
                  refine ⟨3980310334209699222617605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5307080445612932296823473 3980310334209699222617605)
                  ·
                    refine ⟨746308187664318604240801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3980310334209699222617605 746308187664318604240801)
                    ·
                      rfl

theorem cell22_2180145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_2180145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180145 prefixEnd_2180145 := by exact prefixLift 2180145
  have htrace : WordTrace (prefixWord ++ tailWord_2180145) baseStart_2180145 baseEnd_2180145 := by
    simpa [prefixWord, tailWord_2180145, baseEnd_2180145] using wordTrace_append hprefix tailTrace_2180145
  have hstable : (prefixWord ++ tailWord_2180145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180145).length < 2 ^ (prefixWord ++ tailWord_2180145).sum := by decide
  have hdescent : baseEnd_2180145 < baseStart_2180145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180203 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 5, 7]
def baseStart_2180203 : Nat := 118140960795 + 2180203 * 2 ^ 59
def prefixEnd_2180203 : Nat := 4983230072969 + 3 ^ 40 * 2180203 * 2
def baseEnd_2180203 : Nat := 746328042249625786290623

theorem tailTrace_2180203 : CollatzResearch.WordTrace tailWord_2180203 prefixEnd_2180203 746328042249625786290623 := by
  unfold tailWord_2180203
  simp only [CollatzResearch.WordTrace]
  refine ⟨79518536120504354873289263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53012357413669569915526175 79518536120504354873289263)
  ·
    refine ⟨119277804180756532309933895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79518536120504354873289263 119277804180756532309933895)
    ·
      refine ⟨178916706271134798464900843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119277804180756532309933895 178916706271134798464900843)
      ·
        refine ⟨268375059406702197697351265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178916706271134798464900843 268375059406702197697351265)
        ·
          refine ⟨201281294555026648273013449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268375059406702197697351265 201281294555026648273013449)
          ·
            refine ⟨150960970916269986204760087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201281294555026648273013449 150960970916269986204760087)
            ·
              refine ⟨226441456374404979307140131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150960970916269986204760087 226441456374404979307140131)
              ·
                refine ⟨339662184561607468960710197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226441456374404979307140131 339662184561607468960710197)
                ·
                  refine ⟨31843329802650700215066581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 339662184561607468960710197 31843329802650700215066581)
                  ·
                    refine ⟨746328042249625786290623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31843329802650700215066581 746328042249625786290623)
                    ·
                      rfl

theorem cell22_2180203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_2180203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180203 prefixEnd_2180203 := by exact prefixLift 2180203
  have htrace : WordTrace (prefixWord ++ tailWord_2180203) baseStart_2180203 baseEnd_2180203 := by
    simpa [prefixWord, tailWord_2180203, baseEnd_2180203] using wordTrace_append hprefix tailTrace_2180203
  have hstable : (prefixWord ++ tailWord_2180203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180203).length < 2 ^ (prefixWord ++ tailWord_2180203).sum := by decide
  have hdescent : baseEnd_2180203 < baseStart_2180203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180220 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_2180220 : Nat := 118140960795 + 2180220 * 2 ^ 59
def prefixEnd_2180220 : Nat := 4983230072969 + 3 ^ 40 * 2180220 * 2
def baseEnd_2180220 : Nat := 746333861697043408615571

theorem tailTrace_2180220 : CollatzResearch.WordTrace tailWord_2180220 prefixEnd_2180220 746333861697043408615571 := by
  unfold tailWord_2180220
  simp only [CollatzResearch.WordTrace]
  refine ⟨39759578080721383388329057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53012770774295177851105409 39759578080721383388329057)
  ·
    refine ⟨29819683560541037541246793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39759578080721383388329057 29819683560541037541246793)
    ·
      refine ⟨22364762670405778155935095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29819683560541037541246793 22364762670405778155935095)
      ·
        refine ⟨33547144005608667233902643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22364762670405778155935095 33547144005608667233902643)
        ·
          refine ⟨50320716008413000850853965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33547144005608667233902643 50320716008413000850853965)
          ·
            refine ⟨18870268503154875319070237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50320716008413000850853965 18870268503154875319070237)
            ·
              refine ⟨7076350688683078244651339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18870268503154875319070237 7076350688683078244651339)
              ·
                refine ⟨10614526033024617366977009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7076350688683078244651339 10614526033024617366977009)
                ·
                  refine ⟨7960894524768463025232757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10614526033024617366977009 7960894524768463025232757)
                  ·
                    refine ⟨746333861697043408615571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7960894524768463025232757 746333861697043408615571)
                    ·
                      rfl

theorem cell22_2180220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_2180220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180220 prefixEnd_2180220 := by exact prefixLift 2180220
  have htrace : WordTrace (prefixWord ++ tailWord_2180220) baseStart_2180220 baseEnd_2180220 := by
    simpa [prefixWord, tailWord_2180220, baseEnd_2180220] using wordTrace_append hprefix tailTrace_2180220
  have hstable : (prefixWord ++ tailWord_2180220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180220).length < 2 ^ (prefixWord ++ tailWord_2180220).sum := by decide
  have hdescent : baseEnd_2180220 < baseStart_2180220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180280 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_2180280 : Nat := 118140960795 + 2180280 * 2 ^ 59
def prefixEnd_2180280 : Nat := 4983230072969 + 3 ^ 40 * 2180280 * 2
def baseEnd_2180280 : Nat := 746354400923223252115387

theorem tailTrace_2180280 : CollatzResearch.WordTrace tailWord_2180280 prefixEnd_2180280 746354400923223252115387 := by
  unfold tailWord_2180280
  simp only [CollatzResearch.WordTrace]
  refine ⟨39760672270612698511921147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53014229694150264682561529 39760672270612698511921147)
  ·
    refine ⟨59641008405919047767881721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39760672270612698511921147 59641008405919047767881721)
    ·
      refine ⟨44730756304439285825911291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59641008405919047767881721 44730756304439285825911291)
      ·
        refine ⟨67096134456658928738866937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44730756304439285825911291 67096134456658928738866937)
        ·
          refine ⟨50322100842494196554150203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67096134456658928738866937 50322100842494196554150203)
          ·
            refine ⟨75483151263741294831225305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50322100842494196554150203 75483151263741294831225305)
            ·
              refine ⟨56612363447805971123418979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75483151263741294831225305 56612363447805971123418979)
              ·
                refine ⟨84918545171708956685128469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56612363447805971123418979 84918545171708956685128469)
                ·
                  refine ⟨3980556804923857344615397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84918545171708956685128469 3980556804923857344615397)
                  ·
                    refine ⟨746354400923223252115387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3980556804923857344615397 746354400923223252115387)
                    ·
                      rfl

theorem cell22_2180280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_2180280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180280 prefixEnd_2180280 := by exact prefixLift 2180280
  have htrace : WordTrace (prefixWord ++ tailWord_2180280) baseStart_2180280 baseEnd_2180280 := by
    simpa [prefixWord, tailWord_2180280, baseEnd_2180280] using wordTrace_append hprefix tailTrace_2180280
  have hstable : (prefixWord ++ tailWord_2180280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180280).length < 2 ^ (prefixWord ++ tailWord_2180280).sum := by decide
  have hdescent : baseEnd_2180280 < baseStart_2180280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180294 : List Nat := [6, 1, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2180294 : Nat := 118140960795 + 2180294 * 2 ^ 59
def prefixEnd_2180294 : Nat := 4983230072969 + 3 ^ 40 * 2180294 * 2
def baseEnd_2180294 : Nat := 746359193409331882265345

theorem tailTrace_2180294 : CollatzResearch.WordTrace tailWord_2180294 prefixEnd_2180294 746359193409331882265345 := by
  unfold tailWord_2180294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485057973849208669214123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53014570108783118276567957 2485057973849208669214123)
  ·
    refine ⟨3727586960773813003821185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2485057973849208669214123 3727586960773813003821185)
    ·
      refine ⟨2795690220580359752865889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3727586960773813003821185 2795690220580359752865889)
      ·
        refine ⟨2096767665435269814649417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2795690220580359752865889 2096767665435269814649417)
        ·
          refine ⟨1572575749076452360987063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2096767665435269814649417 1572575749076452360987063)
          ·
            refine ⟨2358863623614678541480595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572575749076452360987063 2358863623614678541480595)
            ·
              refine ⟨3538295435422017812220893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358863623614678541480595 3538295435422017812220893)
              ·
                refine ⟨1326860788283256679582835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3538295435422017812220893 1326860788283256679582835)
                ·
                  refine ⟨1990291182424885019374253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326860788283256679582835 1990291182424885019374253)
                  ·
                    refine ⟨746359193409331882265345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990291182424885019374253 746359193409331882265345)
                    ·
                      rfl

theorem cell22_2180294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2180294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180294 prefixEnd_2180294 := by exact prefixLift 2180294
  have htrace : WordTrace (prefixWord ++ tailWord_2180294) baseStart_2180294 baseEnd_2180294 := by
    simpa [prefixWord, tailWord_2180294, baseEnd_2180294] using wordTrace_append hprefix tailTrace_2180294
  have hstable : (prefixWord ++ tailWord_2180294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180294).length < 2 ^ (prefixWord ++ tailWord_2180294).sum := by decide
  have hdescent : baseEnd_2180294 < baseStart_2180294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180312 : List Nat := [2, 1, 2, 2, 5, 2, 8]
def baseStart_2180312 : Nat := 118140960795 + 2180312 * 2 ^ 59
def prefixEnd_2180312 : Nat := 4983230072969 + 3 ^ 40 * 2180312 * 2
def baseEnd_2180312 : Nat := 27643161302858734641307

theorem tailTrace_2180312 : CollatzResearch.WordTrace tailWord_2180312 prefixEnd_2180312 27643161302858734641307 := by
  unfold tailWord_2180312
  simp only [CollatzResearch.WordTrace]
  refine ⟨39761255838554733244503595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53015007784739644326004793 39761255838554733244503595)
  ·
    refine ⟨59641883757832099866755393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39761255838554733244503595 59641883757832099866755393)
    ·
      refine ⟨44731412818374074900066545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59641883757832099866755393 44731412818374074900066545)
      ·
        refine ⟨33548559613780556175049909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44731412818374074900066545 33548559613780556175049909)
        ·
          refine ⟨3145177463791927141410929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33548559613780556175049909 3145177463791927141410929)
          ·
            refine ⟨2358883097843945356058197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3145177463791927141410929 2358883097843945356058197)
            ·
              refine ⟨27643161302858734641307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2358883097843945356058197 27643161302858734641307)
              ·
                rfl

theorem cell22_2180312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 8].length) (baseStart_2180312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180312 prefixEnd_2180312 := by exact prefixLift 2180312
  have htrace : WordTrace (prefixWord ++ tailWord_2180312) baseStart_2180312 baseEnd_2180312 := by
    simpa [prefixWord, tailWord_2180312, baseEnd_2180312] using wordTrace_append hprefix tailTrace_2180312
  have hstable : (prefixWord ++ tailWord_2180312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180312).length < 2 ^ (prefixWord ++ tailWord_2180312).sum := by decide
  have hdescent : baseEnd_2180312 < baseStart_2180312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180333 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_2180333 : Nat := 118140960795 + 2180333 * 2 ^ 59
def prefixEnd_2180333 : Nat := 4983230072969 + 3 ^ 40 * 2180333 * 2
def baseEnd_2180333 : Nat := 746372543906348780540225

theorem tailTrace_2180333 : CollatzResearch.WordTrace tailWord_2180333 prefixEnd_2180333 746372543906348780540225 := by
  unfold tailWord_2180333
  simp only [CollatzResearch.WordTrace]
  refine ⟨79523277610033387075521653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53015518406688924717014435 79523277610033387075521653)
  ·
    refine ⟨7455307275940630038330155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79523277610033387075521653 7455307275940630038330155)
    ·
      refine ⟨11182960913910945057495233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7455307275940630038330155 11182960913910945057495233)
      ·
        refine ⟨8387220685433208793121425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11182960913910945057495233 8387220685433208793121425)
        ·
          refine ⟨6290415514074906594841069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8387220685433208793121425 6290415514074906594841069)
          ·
            refine ⟨2358905817778089973065401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6290415514074906594841069 2358905817778089973065401)
            ·
              refine ⟨1769179363333567479799051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2358905817778089973065401 1769179363333567479799051)
              ·
                refine ⟨2653769045000351219698577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769179363333567479799051 2653769045000351219698577)
                ·
                  refine ⟨1990326783750263414773933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2653769045000351219698577 1990326783750263414773933)
                  ·
                    refine ⟨746372543906348780540225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990326783750263414773933 746372543906348780540225)
                    ·
                      rfl

theorem cell22_2180333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_2180333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180333 prefixEnd_2180333 := by exact prefixLift 2180333
  have htrace : WordTrace (prefixWord ++ tailWord_2180333) baseStart_2180333 baseEnd_2180333 := by
    simpa [prefixWord, tailWord_2180333, baseEnd_2180333] using wordTrace_append hprefix tailTrace_2180333
  have hstable : (prefixWord ++ tailWord_2180333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180333).length < 2 ^ (prefixWord ++ tailWord_2180333).sum := by decide
  have hdescent : baseEnd_2180333 < baseStart_2180333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180378 : List Nat := [3, 1, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_2180378 : Nat := 118140960795 + 2180378 * 2 ^ 59
def prefixEnd_2180378 : Nat := 4983230072969 + 3 ^ 40 * 2180378 * 2
def baseEnd_2180378 : Nat := 746387948325983663165087

theorem tailTrace_2180378 : CollatzResearch.WordTrace tailWord_2180378 prefixEnd_2180378 746387948325983663165087 := by
  unfold tailWord_2180378
  simp only [CollatzResearch.WordTrace]
  refine ⟨19881229723717589940227447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53016612596580239840606525 19881229723717589940227447)
  ·
    refine ⟨29821844585576384910341171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19881229723717589940227447 29821844585576384910341171)
    ·
      refine ⟨44732766878364577365511757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29821844585576384910341171 44732766878364577365511757)
      ·
        refine ⟨16774787579386716512066909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44732766878364577365511757 16774787579386716512066909)
        ·
          refine ⟨6290545342270018692025091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16774787579386716512066909 6290545342270018692025091)
          ·
            refine ⟨9435818013405028038037637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6290545342270018692025091 9435818013405028038037637)
            ·
              refine ⟨1769215877513442757132057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9435818013405028038037637 1769215877513442757132057)
              ·
                refine ⟨1326911908135082067849043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1769215877513442757132057 1326911908135082067849043)
                ·
                  refine ⟨1990367862202623101773565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1326911908135082067849043 1990367862202623101773565)
                  ·
                    refine ⟨746387948325983663165087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990367862202623101773565 746387948325983663165087)
                    ·
                      rfl

theorem cell22_2180378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_2180378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180378 prefixEnd_2180378 := by exact prefixLift 2180378
  have htrace : WordTrace (prefixWord ++ tailWord_2180378) baseStart_2180378 baseEnd_2180378 := by
    simpa [prefixWord, tailWord_2180378, baseEnd_2180378] using wordTrace_append hprefix tailTrace_2180378
  have hstable : (prefixWord ++ tailWord_2180378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180378).length < 2 ^ (prefixWord ++ tailWord_2180378).sum := by decide
  have hdescent : baseEnd_2180378 < baseStart_2180378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180387 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 3, 4]
def baseStart_2180387 : Nat := 118140960795 + 2180387 * 2 ^ 59
def prefixEnd_2180387 : Nat := 4983230072969 + 3 ^ 40 * 2180387 * 2
def baseEnd_2180387 : Nat := 746391029209910639690059

theorem tailTrace_2180387 : CollatzResearch.WordTrace tailWord_2180387 prefixEnd_2180387 746391029209910639690059 := by
  unfold tailWord_2180387
  simp only [CollatzResearch.WordTrace]
  refine ⟨79525247151837754297987415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53016831434558502865324943 79525247151837754297987415)
  ·
    refine ⟨119287870727756631446981123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79525247151837754297987415 119287870727756631446981123)
    ·
      refine ⟨178931806091634947170471685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119287870727756631446981123 178931806091634947170471685)
      ·
        refine ⟨33549713642181552594463441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178931806091634947170471685 33549713642181552594463441)
        ·
          refine ⟨25162285231636164445847581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33549713642181552594463441 25162285231636164445847581)
          ·
            refine ⟨9435856961863561667192843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25162285231636164445847581 9435856961863561667192843)
            ·
              refine ⟨14153785442795342500789265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9435856961863561667192843 14153785442795342500789265)
              ·
                refine ⟨10615339082096506875591949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14153785442795342500789265 10615339082096506875591949)
                ·
                  refine ⟨3980752155786190078346981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10615339082096506875591949 3980752155786190078346981)
                  ·
                    refine ⟨746391029209910639690059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3980752155786190078346981 746391029209910639690059)
                    ·
                      rfl

theorem cell22_2180387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 4].length) (baseStart_2180387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180387 prefixEnd_2180387 := by exact prefixLift 2180387
  have htrace : WordTrace (prefixWord ++ tailWord_2180387) baseStart_2180387 baseEnd_2180387 := by
    simpa [prefixWord, tailWord_2180387, baseEnd_2180387] using wordTrace_append hprefix tailTrace_2180387
  have hstable : (prefixWord ++ tailWord_2180387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180387).length < 2 ^ (prefixWord ++ tailWord_2180387).sum := by decide
  have hdescent : baseEnd_2180387 < baseStart_2180387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180402 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_2180402 : Nat := 118140960795 + 2180402 * 2 ^ 59
def prefixEnd_2180402 : Nat := 4983230072969 + 3 ^ 40 * 2180402 * 2
def baseEnd_2180402 : Nat := 248798721338818533521671

theorem tailTrace_2180402 : CollatzResearch.WordTrace tailWord_2180402 prefixEnd_2180402 248798721338818533521671 := by
  unfold tailWord_2180402
  simp only [CollatzResearch.WordTrace]
  refine ⟨19881448561695852964945865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53017196164522274573188973 19881448561695852964945865)
  ·
    refine ⟨14911086421271889723709399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19881448561695852964945865 14911086421271889723709399)
    ·
      refine ⟨22366629631907834585564099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14911086421271889723709399 22366629631907834585564099)
      ·
        refine ⟨33549944447861751878346149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22366629631907834585564099 33549944447861751878346149)
        ·
          refine ⟨6290614583974078477189903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33549944447861751878346149 6290614583974078477189903)
          ·
            refine ⟨9435921875961117715784855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6290614583974078477189903 9435921875961117715784855)
            ·
              refine ⟨14153882813941676573677283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9435921875961117715784855 14153882813941676573677283)
              ·
                refine ⟨21230824220912514860515925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14153882813941676573677283 21230824220912514860515925)
                ·
                  refine ⟨248798721338818533521671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21230824220912514860515925 248798721338818533521671)
                  ·
                    rfl

theorem cell22_2180402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_2180402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180402 prefixEnd_2180402 := by exact prefixLift 2180402
  have htrace : WordTrace (prefixWord ++ tailWord_2180402) baseStart_2180402 baseEnd_2180402 := by
    simpa [prefixWord, tailWord_2180402, baseEnd_2180402] using wordTrace_append hprefix tailTrace_2180402
  have hstable : (prefixWord ++ tailWord_2180402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180402).length < 2 ^ (prefixWord ++ tailWord_2180402).sum := by decide
  have hdescent : baseEnd_2180402 < baseStart_2180402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180404 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2180404 : Nat := 118140960795 + 2180404 * 2 ^ 59
def prefixEnd_2180404 : Nat := 4983230072969 + 3 ^ 40 * 2180404 * 2
def baseEnd_2180404 : Nat := 746396848657328262015007

theorem tailTrace_2180404 : CollatzResearch.WordTrace tailWord_2180404 prefixEnd_2180404 746396848657328262015007 := by
  unfold tailWord_2180404
  simp only [CollatzResearch.WordTrace]
  refine ⟨39762933596388083100678133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53017244795184110800904177 39762933596388083100678133)
  ·
    refine ⟨3727775024661382790688575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39762933596388083100678133 3727775024661382790688575)
    ·
      refine ⟨5591662536992074186032863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3727775024661382790688575 5591662536992074186032863)
      ·
        refine ⟨8387493805488111279049295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5591662536992074186032863 8387493805488111279049295)
        ·
          refine ⟨12581240708232166918573943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8387493805488111279049295 12581240708232166918573943)
          ·
            refine ⟨18871861062348250377860915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12581240708232166918573943 18871861062348250377860915)
            ·
              refine ⟨28307791593522375566791373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18871861062348250377860915 28307791593522375566791373)
              ·
                refine ⟨10615421847570890837546765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28307791593522375566791373 10615421847570890837546765)
                ·
                  refine ⟨3980783192839084064080037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10615421847570890837546765 3980783192839084064080037)
                  ·
                    refine ⟨746396848657328262015007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3980783192839084064080037 746396848657328262015007)
                    ·
                      rfl

theorem cell22_2180404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2180404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180404 prefixEnd_2180404 := by exact prefixLift 2180404
  have htrace : WordTrace (prefixWord ++ tailWord_2180404) baseStart_2180404 baseEnd_2180404 := by
    simpa [prefixWord, tailWord_2180404, baseEnd_2180404] using wordTrace_append hprefix tailTrace_2180404
  have hstable : (prefixWord ++ tailWord_2180404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180404).length < 2 ^ (prefixWord ++ tailWord_2180404).sum := by decide
  have hdescent : baseEnd_2180404 < baseStart_2180404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180432 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_2180432 : Nat := 118140960795 + 2180432 * 2 ^ 59
def prefixEnd_2180432 : Nat := 4983230072969 + 3 ^ 40 * 2180432 * 2
def baseEnd_2180432 : Nat := 746406433629545522314921

theorem tailTrace_2180432 : CollatzResearch.WordTrace tailWord_2180432 prefixEnd_2180432 746406433629545522314921 := by
  unfold tailWord_2180432
  simp only [CollatzResearch.WordTrace]
  refine ⟨39763444218337363491687775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53017925624449817988917033 39763444218337363491687775)
  ·
    refine ⟨59645166327506045237531663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39763444218337363491687775 59645166327506045237531663)
    ·
      refine ⟨89467749491259067856297495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59645166327506045237531663 89467749491259067856297495)
      ·
        refine ⟨134201624236888601784446243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89467749491259067856297495 134201624236888601784446243)
        ·
          refine ⟨201302436355332902676669365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134201624236888601784446243 201302436355332902676669365)
          ·
            refine ⟨18872103408312459625937753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201302436355332902676669365 18872103408312459625937753)
            ·
              refine ⟨14154077556234344719453315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18872103408312459625937753 14154077556234344719453315)
              ·
                refine ⟨21231116334351517079179973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14154077556234344719453315 21231116334351517079179973)
                ·
                  refine ⟨3980834312690909452346245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21231116334351517079179973 3980834312690909452346245)
                  ·
                    refine ⟨746406433629545522314921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3980834312690909452346245 746406433629545522314921)
                    ·
                      rfl

theorem cell22_2180432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_2180432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180432 prefixEnd_2180432 := by exact prefixLift 2180432
  have htrace : WordTrace (prefixWord ++ tailWord_2180432) baseStart_2180432 baseEnd_2180432 := by
    simpa [prefixWord, tailWord_2180432, baseEnd_2180432] using wordTrace_append hprefix tailTrace_2180432
  have hstable : (prefixWord ++ tailWord_2180432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180432).length < 2 ^ (prefixWord ++ tailWord_2180432).sum := by decide
  have hdescent : baseEnd_2180432 < baseStart_2180432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180481 : List Nat := [1, 2, 4, 3, 3, 1, 8]
def baseStart_2180481 : Nat := 118140960795 + 2180481 * 2 ^ 59
def prefixEnd_2180481 : Nat := 4983230072969 + 3 ^ 40 * 2180481 * 2
def baseEnd_2180481 : Nat := 27645303975219471401473

theorem tailTrace_2180481 : CollatzResearch.WordTrace tailWord_2180481 prefixEnd_2180481 27645303975219471401473 := by
  unfold tailWord_2180481
  simp only [CollatzResearch.WordTrace]
  refine ⟨79528675613497208351909297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53019117075664805567939531 79528675613497208351909297)
  ·
    refine ⟨59646506710122906263931973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79528675613497208351909297 59646506710122906263931973)
    ·
      refine ⟨11183720008148044924487245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59646506710122906263931973 11183720008148044924487245)
      ·
        refine ⟨4193895003055516846682717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11183720008148044924487245 4193895003055516846682717)
        ·
          refine ⟨1572710626145818817506019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4193895003055516846682717 1572710626145818817506019)
          ·
            refine ⟨2359065939218728226259029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572710626145818817506019 2359065939218728226259029)
            ·
              refine ⟨27645303975219471401473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2359065939218728226259029 27645303975219471401473)
              ·
                rfl

theorem cell22_2180481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 8].length) (baseStart_2180481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180481 prefixEnd_2180481 := by exact prefixLift 2180481
  have htrace : WordTrace (prefixWord ++ tailWord_2180481) baseStart_2180481 baseEnd_2180481 := by
    simpa [prefixWord, tailWord_2180481, baseEnd_2180481] using wordTrace_append hprefix tailTrace_2180481
  have hstable : (prefixWord ++ tailWord_2180481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180481).length < 2 ^ (prefixWord ++ tailWord_2180481).sum := by decide
  have hdescent : baseEnd_2180481 < baseStart_2180481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180492 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 7]
def baseStart_2180492 : Nat := 118140960795 + 2180492 * 2 ^ 59
def prefixEnd_2180492 : Nat := 4983230072969 + 3 ^ 40 * 2180492 * 2
def baseEnd_2180492 : Nat := 248808990951908455271579

theorem tailTrace_2180492 : CollatzResearch.WordTrace tailWord_2180492 prefixEnd_2180492 248808990951908455271579 := by
  unfold tailWord_2180492
  simp only [CollatzResearch.WordTrace]
  refine ⟨39764538408228678615279865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53019384544304904820373153 39764538408228678615279865)
  ·
    refine ⟨29823403806171508961459899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39764538408228678615279865 29823403806171508961459899)
    ·
      refine ⟨44735105709257263442189849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29823403806171508961459899 44735105709257263442189849)
      ·
        refine ⟨33551329281942947581642387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44735105709257263442189849 33551329281942947581642387)
        ·
          refine ⟨50326993922914421372463581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33551329281942947581642387 50326993922914421372463581)
          ·
            refine ⟨18872622721092908014673843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50326993922914421372463581 18872622721092908014673843)
            ·
              refine ⟨28308934081639362022010765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18872622721092908014673843 28308934081639362022010765)
              ·
                refine ⟨10615850280614760758254037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28308934081639362022010765 10615850280614760758254037)
                ·
                  refine ⟨248808990951908455271579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10615850280614760758254037 248808990951908455271579)
                  ·
                    rfl

theorem cell22_2180492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_2180492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180492 prefixEnd_2180492 := by exact prefixLift 2180492
  have htrace : WordTrace (prefixWord ++ tailWord_2180492) baseStart_2180492 baseEnd_2180492 := by
    simpa [prefixWord, tailWord_2180492, baseEnd_2180492] using wordTrace_append hprefix tailTrace_2180492
  have hstable : (prefixWord ++ tailWord_2180492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180492).length < 2 ^ (prefixWord ++ tailWord_2180492).sum := by decide
  have hdescent : baseEnd_2180492 < baseStart_2180492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180569 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_2180569 : Nat := 118140960795 + 2180569 * 2 ^ 59
def prefixEnd_2180569 : Nat := 4983230072969 + 3 ^ 40 * 2180569 * 2
def baseEnd_2180569 : Nat := 746453331529322831639501

theorem tailTrace_2180569 : CollatzResearch.WordTrace tailWord_2180569 prefixEnd_2180569 746453331529322831639501 := by
  unfold tailWord_2180569
  simp only [CollatzResearch.WordTrace]
  refine ⟨79531885237178399381112761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53021256824785599587408507 79531885237178399381112761)
  ·
    refine ⟨59648913927883799535834571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79531885237178399381112761 59648913927883799535834571)
    ·
      refine ⟨89473370891825699303751857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59648913927883799535834571 89473370891825699303751857)
      ·
        refine ⟨67105028168869274477813893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89473370891825699303751857 67105028168869274477813893)
        ·
          refine ⟨12582192781662988964590105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67105028168869274477813893 12582192781662988964590105)
          ·
            refine ⟨9436644586247241723442579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12582192781662988964590105 9436644586247241723442579)
            ·
              refine ⟨14154966879370862585163869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9436644586247241723442579 14154966879370862585163869)
              ·
                refine ⟨5308112579764073469436451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14154966879370862585163869 5308112579764073469436451)
                ·
                  refine ⟨7962168869646110204154677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5308112579764073469436451 7962168869646110204154677)
                  ·
                    refine ⟨746453331529322831639501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7962168869646110204154677 746453331529322831639501)
                    ·
                      rfl

theorem cell22_2180569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_2180569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180569 prefixEnd_2180569 := by exact prefixLift 2180569
  have htrace : WordTrace (prefixWord ++ tailWord_2180569) baseStart_2180569 baseEnd_2180569 := by
    simpa [prefixWord, tailWord_2180569, baseEnd_2180569] using wordTrace_append hprefix tailTrace_2180569
  have hstable : (prefixWord ++ tailWord_2180569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180569).length < 2 ^ (prefixWord ++ tailWord_2180569).sum := by decide
  have hdescent : baseEnd_2180569 < baseStart_2180569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180584 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2180584 : Nat := 118140960795 + 2180584 * 2 ^ 59
def prefixEnd_2180584 : Nat := 4983230072969 + 3 ^ 40 * 2180584 * 2
def baseEnd_2180584 : Nat := 746458466335867792514455

theorem tailTrace_2180584 : CollatzResearch.WordTrace tailWord_2180584 prefixEnd_2180584 746458466335867792514455 := by
  unfold tailWord_2180584
  simp only [CollatzResearch.WordTrace]
  refine ⟨39766216166062028471454403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53021621554749371295272537 39766216166062028471454403)
  ·
    refine ⟨59649324249093042707181605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39766216166062028471454403 59649324249093042707181605)
    ·
      refine ⟨11184248296704945507596551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59649324249093042707181605 11184248296704945507596551)
      ·
        refine ⟨16776372445057418261394827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11184248296704945507596551 16776372445057418261394827)
        ·
          refine ⟨25164558667586127392092241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16776372445057418261394827 25164558667586127392092241)
          ·
            refine ⟨18873419000689595544069181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25164558667586127392092241 18873419000689595544069181)
            ·
              refine ⟨7077532125258598329025943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18873419000689595544069181 7077532125258598329025943)
              ·
                refine ⟨10616298187887897493538915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7077532125258598329025943 10616298187887897493538915)
                ·
                  refine ⟨15924447281831846240308373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10616298187887897493538915 15924447281831846240308373)
                  ·
                    refine ⟨746458466335867792514455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15924447281831846240308373 746458466335867792514455)
                    ·
                      rfl

theorem cell22_2180584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2180584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180584 prefixEnd_2180584 := by exact prefixLift 2180584
  have htrace : WordTrace (prefixWord ++ tailWord_2180584) baseStart_2180584 baseEnd_2180584 := by
    simpa [prefixWord, tailWord_2180584, baseEnd_2180584] using wordTrace_append hprefix tailTrace_2180584
  have hstable : (prefixWord ++ tailWord_2180584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180584).length < 2 ^ (prefixWord ++ tailWord_2180584).sum := by decide
  have hdescent : baseEnd_2180584 < baseStart_2180584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180620 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_2180620 : Nat := 118140960795 + 2180620 * 2 ^ 59
def prefixEnd_2180620 : Nat := 4983230072969 + 3 ^ 40 * 2180620 * 2
def baseEnd_2180620 : Nat := 746470789871575698614345

theorem tailTrace_2180620 : CollatzResearch.WordTrace tailWord_2180620 prefixEnd_2180620 746470789871575698614345 := by
  unfold tailWord_2180620
  simp only [CollatzResearch.WordTrace]
  refine ⟨39766872679996817545609657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53022496906662423394146209 39766872679996817545609657)
  ·
    refine ⟨29825154509997613159207243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39766872679996817545609657 29825154509997613159207243)
    ·
      refine ⟨44737731764996419738810865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29825154509997613159207243 44737731764996419738810865)
      ·
        refine ⟨33553298823747314804108149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44737731764996419738810865 33553298823747314804108149)
        ·
          refine ⟨3145621764726310762885139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33553298823747314804108149 3145621764726310762885139)
          ·
            refine ⟨4718432647089466144327709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145621764726310762885139 4718432647089466144327709)
            ·
              refine ⟨1769412242658549804122891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4718432647089466144327709 1769412242658549804122891)
              ·
                refine ⟨2654118363987824706184337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769412242658549804122891 2654118363987824706184337)
                ·
                  refine ⟨1990588772990868529638253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2654118363987824706184337 1990588772990868529638253)
                  ·
                    refine ⟨746470789871575698614345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990588772990868529638253 746470789871575698614345)
                    ·
                      rfl

theorem cell22_2180620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_2180620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180620 prefixEnd_2180620 := by exact prefixLift 2180620
  have htrace : WordTrace (prefixWord ++ tailWord_2180620) baseStart_2180620 baseEnd_2180620 := by
    simpa [prefixWord, tailWord_2180620, baseEnd_2180620] using wordTrace_append hprefix tailTrace_2180620
  have hstable : (prefixWord ++ tailWord_2180620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180620).length < 2 ^ (prefixWord ++ tailWord_2180620).sum := by decide
  have hdescent : baseEnd_2180620 < baseStart_2180620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180689 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 8]
def baseStart_2180689 : Nat := 118140960795 + 2180689 * 2 ^ 59
def prefixEnd_2180689 : Nat := 4983230072969 + 3 ^ 40 * 2180689 * 2
def baseEnd_2180689 : Nat := 248831469993894172879711

theorem tailTrace_2180689 : CollatzResearch.WordTrace tailWord_2180689 prefixEnd_2180689 248831469993894172879711 := by
  unfold tailWord_2180689
  simp only [CollatzResearch.WordTrace]
  refine ⟨79536261996743659875481121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53024174664495773250320747 79536261996743659875481121)
  ·
    refine ⟨59652196497557744906610841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79536261996743659875481121 59652196497557744906610841)
    ·
      refine ⟨44739147373168308679958131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59652196497557744906610841 44739147373168308679958131)
      ·
        refine ⟨67108721059752463019937197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44739147373168308679958131 67108721059752463019937197)
        ·
          refine ⟨25165770397407173632476449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67108721059752463019937197 25165770397407173632476449)
          ·
            refine ⟨18874327798055380224357337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25165770397407173632476449 18874327798055380224357337)
            ·
              refine ⟨14155745848541535168268003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18874327798055380224357337 14155745848541535168268003)
              ·
                refine ⟨21233618772812302752402005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14155745848541535168268003 21233618772812302752402005)
                ·
                  refine ⟨248831469993894172879711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21233618772812302752402005 248831469993894172879711)
                  ·
                    rfl

theorem cell22_2180689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_2180689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180689 prefixEnd_2180689 := by exact prefixLift 2180689
  have htrace : WordTrace (prefixWord ++ tailWord_2180689) baseStart_2180689 baseEnd_2180689 := by
    simpa [prefixWord, tailWord_2180689, baseEnd_2180689] using wordTrace_append hprefix tailTrace_2180689
  have hstable : (prefixWord ++ tailWord_2180689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180689).length < 2 ^ (prefixWord ++ tailWord_2180689).sum := by decide
  have hdescent : baseEnd_2180689 < baseStart_2180689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180719 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 3, 6]
def baseStart_2180719 : Nat := 118140960795 + 2180719 * 2 ^ 59
def prefixEnd_2180719 : Nat := 4983230072969 + 3 ^ 40 * 2180719 * 2
def baseEnd_2180719 : Nat := 746504679594772440389041

theorem tailTrace_2180719 : CollatzResearch.WordTrace tailWord_2180719 prefixEnd_2180719 746504679594772440389041 := by
  unfold tailWord_2180719
  simp only [CollatzResearch.WordTrace]
  refine ⟨79537356186634974999073211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53024904124423316666048807 79537356186634974999073211)
  ·
    refine ⟨119306034279952462498609817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79537356186634974999073211 119306034279952462498609817)
    ·
      refine ⟨89479525709964346873957363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119306034279952462498609817 89479525709964346873957363)
      ·
        refine ⟨134219288564946520310936045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89479525709964346873957363 134219288564946520310936045)
        ·
          refine ⟨50332233211854945116601017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134219288564946520310936045 50332233211854945116601017)
          ·
            refine ⟨37749174908891208837450763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50332233211854945116601017 37749174908891208837450763)
            ·
              refine ⟨56623762363336813256176145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37749174908891208837450763 56623762363336813256176145)
              ·
                refine ⟨42467821772502609942132109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56623762363336813256176145 42467821772502609942132109)
                ·
                  refine ⟨15925433164688478728299541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42467821772502609942132109 15925433164688478728299541)
                  ·
                    refine ⟨746504679594772440389041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15925433164688478728299541 746504679594772440389041)
                    ·
                      rfl

theorem cell22_2180719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_2180719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180719 prefixEnd_2180719 := by exact prefixLift 2180719
  have htrace : WordTrace (prefixWord ++ tailWord_2180719) baseStart_2180719 baseEnd_2180719 := by
    simpa [prefixWord, tailWord_2180719, baseEnd_2180719] using wordTrace_append hprefix tailTrace_2180719
  have hstable : (prefixWord ++ tailWord_2180719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180719).length < 2 ^ (prefixWord ++ tailWord_2180719).sum := by decide
  have hdescent : baseEnd_2180719 < baseStart_2180719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180721 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 4, 3]
def baseStart_2180721 : Nat := 118140960795 + 2180721 * 2 ^ 59
def prefixEnd_2180721 : Nat := 4983230072969 + 3 ^ 40 * 2180721 * 2
def baseEnd_2180721 : Nat := 746505364235645101839035

theorem tailTrace_2180721 : CollatzResearch.WordTrace tailWord_2180721 prefixEnd_2180721 746505364235645101839035 := by
  unfold tailWord_2180721
  simp only [CollatzResearch.WordTrace]
  refine ⟨79537429132627729340646017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53024952755085152893764011 79537429132627729340646017)
  ·
    refine ⟨59653071849470797005484513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79537429132627729340646017 59653071849470797005484513)
    ·
      refine ⟨44739803887103097754113385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59653071849470797005484513 44739803887103097754113385)
      ·
        refine ⟨33554852915327323315585039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44739803887103097754113385 33554852915327323315585039)
        ·
          refine ⟨50332279372990984973377559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33554852915327323315585039 50332279372990984973377559)
          ·
            refine ⟨75498419059486477460066339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50332279372990984973377559 75498419059486477460066339)
            ·
              refine ⟨113247628589229716190099509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75498419059486477460066339 113247628589229716190099509)
              ·
                refine ⟨10616965180240285892821829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113247628589229716190099509 10616965180240285892821829)
                ·
                  refine ⟨1990680971295053604904093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10616965180240285892821829 1990680971295053604904093)
                  ·
                    refine ⟨746505364235645101839035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990680971295053604904093 746505364235645101839035)
                    ·
                      rfl

theorem cell22_2180721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_2180721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180721 prefixEnd_2180721 := by exact prefixLift 2180721
  have htrace : WordTrace (prefixWord ++ tailWord_2180721) baseStart_2180721 baseEnd_2180721 := by
    simpa [prefixWord, tailWord_2180721, baseEnd_2180721] using wordTrace_append hprefix tailTrace_2180721
  have hstable : (prefixWord ++ tailWord_2180721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180721).length < 2 ^ (prefixWord ++ tailWord_2180721).sum := by decide
  have hdescent : baseEnd_2180721 < baseStart_2180721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180783 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 3, 3]
def baseStart_2180783 : Nat := 118140960795 + 2180783 * 2 ^ 59
def prefixEnd_2180783 : Nat := 4983230072969 + 3 ^ 40 * 2180783 * 2
def baseEnd_2180783 : Nat := 746526588102697606788845

theorem tailTrace_2180783 : CollatzResearch.WordTrace tailWord_2180783 prefixEnd_2180783 746526588102697606788845 := by
  unfold tailWord_2180783
  simp only [CollatzResearch.WordTrace]
  refine ⟨79539690458403113929403003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53026460305602075952935335 79539690458403113929403003)
  ·
    refine ⟨119309535687604670894104505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79539690458403113929403003 119309535687604670894104505)
    ·
      refine ⟨89482151765703503170578379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119309535687604670894104505 89482151765703503170578379)
      ·
        refine ⟨134223227648555254755867569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89482151765703503170578379 134223227648555254755867569)
        ·
          refine ⟨100667420736416441066900677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134223227648555254755867569 100667420736416441066900677)
          ·
            refine ⟨18875141388078082700043877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100667420736416441066900677 18875141388078082700043877)
            ·
              refine ⟨3539089010264640506258227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18875141388078082700043877 3539089010264640506258227)
              ·
                refine ⟨5308633515396960759387341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3539089010264640506258227 5308633515396960759387341)
                ·
                  refine ⟨1990737568273860284770253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5308633515396960759387341 1990737568273860284770253)
                  ·
                    refine ⟨746526588102697606788845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990737568273860284770253 746526588102697606788845)
                    ·
                      rfl

theorem cell22_2180783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_2180783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180783 prefixEnd_2180783 := by exact prefixLift 2180783
  have htrace : WordTrace (prefixWord ++ tailWord_2180783) baseStart_2180783 baseEnd_2180783 := by
    simpa [prefixWord, tailWord_2180783, baseEnd_2180783] using wordTrace_append hprefix tailTrace_2180783
  have hstable : (prefixWord ++ tailWord_2180783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180783).length < 2 ^ (prefixWord ++ tailWord_2180783).sum := by decide
  have hdescent : baseEnd_2180783 < baseStart_2180783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180802 : List Nat := [3, 5, 1, 2, 1, 1, 1, 8]
def baseStart_2180802 : Nat := 118140960795 + 2180802 * 2 ^ 59
def prefixEnd_2180802 : Nat := 4983230072969 + 3 ^ 40 * 2180802 * 2
def baseEnd_2180802 : Nat := 82948121354554210062643

theorem tailTrace_2180802 : CollatzResearch.WordTrace tailWord_2180802 prefixEnd_2180802 82948121354554210062643 := by
  unfold tailWord_2180802
  simp only [CollatzResearch.WordTrace]
  refine ⟨19885095861333570043586165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53026922296889520116229773 19885095861333570043586165)
  ·
    refine ⟨1864227737000022191586203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19885095861333570043586165 1864227737000022191586203)
    ·
      refine ⟨2796341605500033287379305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1864227737000022191586203 2796341605500033287379305)
      ·
        refine ⟨2097256204125024965534479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2796341605500033287379305 2097256204125024965534479)
        ·
          refine ⟨3145884306187537448301719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097256204125024965534479 3145884306187537448301719)
          ·
            refine ⟨4718826459281306172452579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145884306187537448301719 4718826459281306172452579)
            ·
              refine ⟨7078239688921959258678869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4718826459281306172452579 7078239688921959258678869)
              ·
                refine ⟨82948121354554210062643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7078239688921959258678869 82948121354554210062643)
                ·
                  rfl

theorem cell22_2180802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_2180802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180802 prefixEnd_2180802 := by exact prefixLift 2180802
  have htrace : WordTrace (prefixWord ++ tailWord_2180802) baseStart_2180802 baseEnd_2180802 := by
    simpa [prefixWord, tailWord_2180802, baseEnd_2180802] using wordTrace_append hprefix tailTrace_2180802
  have hstable : (prefixWord ++ tailWord_2180802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180802).length < 2 ^ (prefixWord ++ tailWord_2180802).sum := by decide
  have hdescent : baseEnd_2180802 < baseStart_2180802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180817 : List Nat := [1, 2, 2, 1, 2, 6, 1, 3, 1, 3]
def baseStart_2180817 : Nat := 118140960795 + 2180817 * 2 ^ 59
def prefixEnd_2180817 : Nat := 4983230072969 + 3 ^ 40 * 2180817 * 2
def baseEnd_2180817 : Nat := 746538226997532851438741

theorem tailTrace_2180817 : CollatzResearch.WordTrace tailWord_2180817 prefixEnd_2180817 746538226997532851438741 := by
  unfold tailWord_2180817
  simp only [CollatzResearch.WordTrace]
  refine ⟨79540930540279937736140705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53027287026853291824093803 79540930540279937736140705)
  ·
    refine ⟨59655697905209953302105529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79540930540279937736140705 59655697905209953302105529)
    ·
      refine ⟨44741773428907464976579147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59655697905209953302105529 44741773428907464976579147)
      ·
        refine ⟨67112660143361197464868721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44741773428907464976579147 67112660143361197464868721)
        ·
          refine ⟨50334495107520898098651541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67112660143361197464868721 50334495107520898098651541)
          ·
            refine ⟨2359429458165042098374291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50334495107520898098651541 2359429458165042098374291)
            ·
              refine ⟨3539144187247563147561437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359429458165042098374291 3539144187247563147561437)
              ·
                refine ⟨1327179070217836180335539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3539144187247563147561437 1327179070217836180335539)
                ·
                  refine ⟨1990768605326754270503309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327179070217836180335539 1990768605326754270503309)
                  ·
                    refine ⟨746538226997532851438741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990768605326754270503309 746538226997532851438741)
                    ·
                      rfl

theorem cell22_2180817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_2180817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180817 prefixEnd_2180817 := by exact prefixLift 2180817
  have htrace : WordTrace (prefixWord ++ tailWord_2180817) baseStart_2180817 baseEnd_2180817 := by
    simpa [prefixWord, tailWord_2180817, baseEnd_2180817] using wordTrace_append hprefix tailTrace_2180817
  have hstable : (prefixWord ++ tailWord_2180817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180817).length < 2 ^ (prefixWord ++ tailWord_2180817).sum := by decide
  have hdescent : baseEnd_2180817 < baseStart_2180817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180888 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_2180888 : Nat := 118140960795 + 2180888 * 2 ^ 59
def prefixEnd_2180888 : Nat := 4983230072969 + 3 ^ 40 * 2180888 * 2
def baseEnd_2180888 : Nat := 746562531748512332913523

theorem tailTrace_2180888 : CollatzResearch.WordTrace tailWord_2180888 prefixEnd_2180888 746562531748512332913523 := by
  unfold tailWord_2180888
  simp only [CollatzResearch.WordTrace]
  refine ⟨39771760061511358430987659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53029013415348477907983545 39771760061511358430987659)
  ·
    refine ⟨59657640092267037646481489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39771760061511358430987659 59657640092267037646481489)
    ·
      refine ⟨44743230069200278234861117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59657640092267037646481489 44743230069200278234861117)
      ·
        refine ⟨16778711275950104338072919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44743230069200278234861117 16778711275950104338072919)
        ·
          refine ⟨25168066913925156507109379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16778711275950104338072919 25168066913925156507109379)
          ·
            refine ⟨37752100370887734760664069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25168066913925156507109379 37752100370887734760664069)
            ·
              refine ⟨7078518819541450267624513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37752100370887734760664069 7078518819541450267624513)
              ·
                refine ⟨5308889114656087700718385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7078518819541450267624513 5308889114656087700718385)
                ·
                  refine ⟨3981666835992065775538789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5308889114656087700718385 3981666835992065775538789)
                  ·
                    refine ⟨746562531748512332913523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3981666835992065775538789 746562531748512332913523)
                    ·
                      rfl

theorem cell22_2180888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_2180888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180888 prefixEnd_2180888 := by exact prefixLift 2180888
  have htrace : WordTrace (prefixWord ++ tailWord_2180888) baseStart_2180888 baseEnd_2180888 := by
    simpa [prefixWord, tailWord_2180888, baseEnd_2180888] using wordTrace_append hprefix tailTrace_2180888
  have hstable : (prefixWord ++ tailWord_2180888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180888).length < 2 ^ (prefixWord ++ tailWord_2180888).sum := by decide
  have hdescent : baseEnd_2180888 < baseStart_2180888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180890 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_2180890 : Nat := 118140960795 + 2180890 * 2 ^ 59
def prefixEnd_2180890 : Nat := 4983230072969 + 3 ^ 40 * 2180890 * 2
def baseEnd_2180890 : Nat := 746563216389384994363517

theorem tailTrace_2180890 : CollatzResearch.WordTrace tailWord_2180890 prefixEnd_2180890 746563216389384994363517 := by
  unfold tailWord_2180890
  simp only [CollatzResearch.WordTrace]
  refine ⟨19885898267253867800887031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53029062046010314135698749 19885898267253867800887031)
  ·
    refine ⟨29828847400880801701330547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19885898267253867800887031 29828847400880801701330547)
    ·
      refine ⟨44743271101321202551995821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29828847400880801701330547 44743271101321202551995821)
      ·
        refine ⟨16778726662995450956998433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44743271101321202551995821 16778726662995450956998433)
        ·
          refine ⟨12584044997246588217748825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16778726662995450956998433 12584044997246588217748825)
          ·
            refine ⟨9438033747934941163311619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12584044997246588217748825 9438033747934941163311619)
            ·
              refine ⟨14157050621902411744967429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9438033747934941163311619 14157050621902411744967429)
              ·
                refine ⟨2654446991606702202181393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14157050621902411744967429 2654446991606702202181393)
                ·
                  refine ⟨1990835243705026651636045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2654446991606702202181393 1990835243705026651636045)
                  ·
                    refine ⟨746563216389384994363517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1990835243705026651636045 746563216389384994363517)
                    ·
                      rfl

theorem cell22_2180890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_2180890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180890 prefixEnd_2180890 := by exact prefixLift 2180890
  have htrace : WordTrace (prefixWord ++ tailWord_2180890) baseStart_2180890 baseEnd_2180890 := by
    simpa [prefixWord, tailWord_2180890, baseEnd_2180890] using wordTrace_append hprefix tailTrace_2180890
  have hstable : (prefixWord ++ tailWord_2180890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180890).length < 2 ^ (prefixWord ++ tailWord_2180890).sum := by decide
  have hdescent : baseEnd_2180890 < baseStart_2180890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2180995 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 1, 4]
def baseStart_2180995 : Nat := 118140960795 + 2180995 * 2 ^ 59
def prefixEnd_2180995 : Nat := 4983230072969 + 3 ^ 40 * 2180995 * 2
def baseEnd_2180995 : Nat := 746599160035199720488195

theorem tailTrace_2180995 : CollatzResearch.WordTrace tailWord_2180995 prefixEnd_2180995 746599160035199720488195 := by
  unfold tailWord_2180995
  simp only [CollatzResearch.WordTrace]
  refine ⟨79547422733635074136120439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53031615155756716090746959 79547422733635074136120439)
  ·
    refine ⟨119321134100452611204180659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79547422733635074136120439 119321134100452611204180659)
    ·
      refine ⟨178981701150678916806270989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119321134100452611204180659 178981701150678916806270989)
      ·
        refine ⟨67118137931504593802351621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178981701150678916806270989 67118137931504593802351621)
        ·
          refine ⟨12584650862157111337940929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67118137931504593802351621 12584650862157111337940929)
          ·
            refine ⟨9438488146617833503455697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12584650862157111337940929 9438488146617833503455697)
            ·
              refine ⟨7078866109963375127591773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9438488146617833503455697 7078866109963375127591773)
              ·
                refine ⟨2654574791236265672846915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7078866109963375127591773 2654574791236265672846915)
                ·
                  refine ⟨3981862186854398509270373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654574791236265672846915 3981862186854398509270373)
                  ·
                    refine ⟨746599160035199720488195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3981862186854398509270373 746599160035199720488195)
                    ·
                      rfl

theorem cell22_2180995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 4].length) (baseStart_2180995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2180995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2180995 prefixEnd_2180995 := by exact prefixLift 2180995
  have htrace : WordTrace (prefixWord ++ tailWord_2180995) baseStart_2180995 baseEnd_2180995 := by
    simpa [prefixWord, tailWord_2180995, baseEnd_2180995] using wordTrace_append hprefix tailTrace_2180995
  have hstable : (prefixWord ++ tailWord_2180995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2180995).length < 2 ^ (prefixWord ++ tailWord_2180995).sum := by decide
  have hdescent : baseEnd_2180995 < baseStart_2180995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2180995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181016 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 5]
def baseStart_2181016 : Nat := 118140960795 + 2181016 * 2 ^ 59
def prefixEnd_2181016 : Nat := 4983230072969 + 3 ^ 40 * 2181016 * 2
def baseEnd_2181016 : Nat := 248868782921454221904377

theorem tailTrace_2181016 : CollatzResearch.WordTrace tailWord_2181016 prefixEnd_2181016 248868782921454221904377 := by
  unfold tailWord_2181016
  simp only [CollatzResearch.WordTrace]
  refine ⟨39774094333279497361317451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53032125777705996481756601 39774094333279497361317451)
  ·
    refine ⟨59661141499919246041976177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39774094333279497361317451 59661141499919246041976177)
    ·
      refine ⟨44745856124939434531482133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59661141499919246041976177 44745856124939434531482133)
      ·
        refine ⟨2097462005856535993663225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44745856124939434531482133 2097462005856535993663225)
        ·
          refine ⟨1573096504392401995247419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2097462005856535993663225 1573096504392401995247419)
          ·
            refine ⟨2359644756588602992871129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573096504392401995247419 2359644756588602992871129)
            ·
              refine ⟨1769733567441452244653347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2359644756588602992871129 1769733567441452244653347)
              ·
                refine ⟨2654600351162178366980021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769733567441452244653347 2654600351162178366980021)
                ·
                  refine ⟨248868782921454221904377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2654600351162178366980021 248868782921454221904377)
                  ·
                    rfl

theorem cell22_2181016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_2181016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181016 prefixEnd_2181016 := by exact prefixLift 2181016
  have htrace : WordTrace (prefixWord ++ tailWord_2181016) baseStart_2181016 baseEnd_2181016 := by
    simpa [prefixWord, tailWord_2181016, baseEnd_2181016] using wordTrace_append hprefix tailTrace_2181016
  have hstable : (prefixWord ++ tailWord_2181016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181016).length < 2 ^ (prefixWord ++ tailWord_2181016).sum := by decide
  have hdescent : baseEnd_2181016 < baseStart_2181016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181087 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 3, 3]
def baseStart_2181087 : Nat := 118140960795 + 2181087 * 2 ^ 59
def prefixEnd_2181087 : Nat := 4983230072969 + 3 ^ 40 * 2181087 * 2
def baseEnd_2181087 : Nat := 746630653515342147187913

theorem tailTrace_2181087 : CollatzResearch.WordTrace tailWord_2181087 prefixEnd_2181087 746630653515342147187913 := by
  unfold tailWord_2181087
  simp only [CollatzResearch.WordTrace]
  refine ⟨79550778249301773848469515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53033852166201182565646343 79550778249301773848469515)
  ·
    refine ⟨119326167373952660772704273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79550778249301773848469515 119326167373952660772704273)
    ·
      refine ⟨89494625530464495579528205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119326167373952660772704273 89494625530464495579528205)
      ·
        refine ⟨33560484573924185842323077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89494625530464495579528205 33560484573924185842323077)
        ·
          refine ⟨6292590857610784845435577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33560484573924185842323077 6292590857610784845435577)
          ·
            refine ⟨4719443143208088634076683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6292590857610784845435577 4719443143208088634076683)
            ·
              refine ⟨7079164714812132951115025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4719443143208088634076683 7079164714812132951115025)
              ·
                refine ⟨5309373536109099713336269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7079164714812132951115025 5309373536109099713336269)
                ·
                  refine ⟨1991015076040912392501101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5309373536109099713336269 1991015076040912392501101)
                  ·
                    refine ⟨746630653515342147187913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1991015076040912392501101 746630653515342147187913)
                    ·
                      rfl

theorem cell22_2181087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_2181087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181087 prefixEnd_2181087 := by exact prefixLift 2181087
  have htrace : WordTrace (prefixWord ++ tailWord_2181087) baseStart_2181087 baseEnd_2181087 := by
    simpa [prefixWord, tailWord_2181087, baseEnd_2181087] using wordTrace_append hprefix tailTrace_2181087
  have hstable : (prefixWord ++ tailWord_2181087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181087).length < 2 ^ (prefixWord ++ tailWord_2181087).sum := by decide
  have hdescent : baseEnd_2181087 < baseStart_2181087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181175 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 4, 4]
def baseStart_2181175 : Nat := 118140960795 + 2181175 * 2 ^ 59
def prefixEnd_2181175 : Nat := 4983230072969 + 3 ^ 40 * 2181175 * 2
def baseEnd_2181175 : Nat := 746660777713739250987643

theorem tailTrace_2181175 : CollatzResearch.WordTrace tailWord_2181175 prefixEnd_2181175 746660777713739250987643 := by
  unfold tailWord_2181175
  simp only [CollatzResearch.WordTrace]
  refine ⟨79553987872982964877672979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53035991915321976585115319 79553987872982964877672979)
  ·
    refine ⟨119330981809474447316509469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79553987872982964877672979 119330981809474447316509469)
    ·
      refine ⟨44749118178552917743691051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119330981809474447316509469 44749118178552917743691051)
      ·
        refine ⟨67123677267829376615536577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44749118178552917743691051 67123677267829376615536577)
        ·
          refine ⟨50342757950872032461652433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67123677267829376615536577 50342757950872032461652433)
          ·
            refine ⟨37757068463154024346239325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50342757950872032461652433 37757068463154024346239325)
            ·
              refine ⟨14158900673682759129839747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37757068463154024346239325 14158900673682759129839747)
              ·
                refine ⟨21238351010524138694759621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14158900673682759129839747 21238351010524138694759621)
                ·
                  refine ⟨3982190814473276005267429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21238351010524138694759621 3982190814473276005267429)
                  ·
                    refine ⟨746660777713739250987643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3982190814473276005267429 746660777713739250987643)
                    ·
                      rfl

theorem cell22_2181175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_2181175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181175 prefixEnd_2181175 := by exact prefixLift 2181175
  have htrace : WordTrace (prefixWord ++ tailWord_2181175) baseStart_2181175 baseEnd_2181175 := by
    simpa [prefixWord, tailWord_2181175, baseEnd_2181175] using wordTrace_append hprefix tailTrace_2181175
  have hstable : (prefixWord ++ tailWord_2181175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181175).length < 2 ^ (prefixWord ++ tailWord_2181175).sum := by decide
  have hdescent : baseEnd_2181175 < baseStart_2181175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181252 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 5]
def baseStart_2181252 : Nat := 118140960795 + 2181252 * 2 ^ 59
def prefixEnd_2181252 : Nat := 4983230072969 + 3 ^ 40 * 2181252 * 2
def baseEnd_2181252 : Nat := 248895712129112238937469

theorem tailTrace_2181252 : CollatzResearch.WordTrace tailWord_2181252 prefixEnd_2181252 248895712129112238937469 := by
  unfold tailWord_2181252
  simp only [CollatzResearch.WordTrace]
  refine ⟨39778398146852003514113005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53037864195802671352150673 39778398146852003514113005)
  ·
    refine ⟨14916899305069501317792377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39778398146852003514113005 14916899305069501317792377)
    ·
      refine ⟨11187674478802125988344283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14916899305069501317792377 11187674478802125988344283)
      ·
        refine ⟨16781511718203188982516425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11187674478802125988344283 16781511718203188982516425)
        ·
          refine ⟨12586133788652391736887319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16781511718203188982516425 12586133788652391736887319)
          ·
            refine ⟨18879200682978587605330979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12586133788652391736887319 18879200682978587605330979)
            ·
              refine ⟨28318801024467881407996469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18879200682978587605330979 28318801024467881407996469)
              ·
                refine ⟨2654887596043863881999669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28318801024467881407996469 2654887596043863881999669)
                ·
                  refine ⟨248895712129112238937469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2654887596043863881999669 248895712129112238937469)
                  ·
                    rfl

theorem cell22_2181252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_2181252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181252 prefixEnd_2181252 := by exact prefixLift 2181252
  have htrace : WordTrace (prefixWord ++ tailWord_2181252) baseStart_2181252 baseEnd_2181252 := by
    simpa [prefixWord, tailWord_2181252, baseEnd_2181252] using wordTrace_append hprefix tailTrace_2181252
  have hstable : (prefixWord ++ tailWord_2181252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181252).length < 2 ^ (prefixWord ++ tailWord_2181252).sum := by decide
  have hdescent : baseEnd_2181252 < baseStart_2181252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181316 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2181316 : Nat := 118140960795 + 2181316 * 2 ^ 59
def prefixEnd_2181316 : Nat := 4983230072969 + 3 ^ 40 * 2181316 * 2
def baseEnd_2181316 : Nat := 746709044895261883212211

theorem tailTrace_2181316 : CollatzResearch.WordTrace tailWord_2181316 prefixEnd_2181316 746709044895261883212211 := by
  unfold tailWord_2181316
  simp only [CollatzResearch.WordTrace]
  refine ⟨39779565282736072979277901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53039420376981430639037201 39779565282736072979277901)
  ·
    refine ⟨14917336981026027367229213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39779565282736072979277901 14917336981026027367229213)
    ·
      refine ⟨5594001367884760262710955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14917336981026027367229213 5594001367884760262710955)
      ·
        refine ⟨8391002051827140394066433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5594001367884760262710955 8391002051827140394066433)
        ·
          refine ⟨6293251538870355295549825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8391002051827140394066433 6293251538870355295549825)
          ·
            refine ⟨4719938654152766471662369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6293251538870355295549825 4719938654152766471662369)
            ·
              refine ⟨3539953990614574853746777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4719938654152766471662369 3539953990614574853746777)
              ·
                refine ⟨2654965492960931140310083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3539953990614574853746777 2654965492960931140310083)
                ·
                  refine ⟨3982448239441396710465125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2654965492960931140310083 3982448239441396710465125)
                  ·
                    refine ⟨746709044895261883212211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3982448239441396710465125 746709044895261883212211)
                    ·
                      rfl

theorem cell22_2181316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2181316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181316 prefixEnd_2181316 := by exact prefixLift 2181316
  have htrace : WordTrace (prefixWord ++ tailWord_2181316) baseStart_2181316 baseEnd_2181316 := by
    simpa [prefixWord, tailWord_2181316, baseEnd_2181316] using wordTrace_append hprefix tailTrace_2181316
  have hstable : (prefixWord ++ tailWord_2181316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181316).length < 2 ^ (prefixWord ++ tailWord_2181316).sum := by decide
  have hdescent : baseEnd_2181316 < baseStart_2181316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181327 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 2, 4]
def baseStart_2181327 : Nat := 118140960795 + 2181327 * 2 ^ 59
def prefixEnd_2181327 : Nat := 4983230072969 + 3 ^ 40 * 2181327 * 2
def baseEnd_2181327 : Nat := 746712810420061521187177

theorem tailTrace_2181327 : CollatzResearch.WordTrace tailWord_2181327 prefixEnd_2181327 746712810420061521187177 := by
  unfold tailWord_2181327
  simp only [CollatzResearch.WordTrace]
  refine ⟨79559531768432294837206235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53039687845621529891470823 79559531768432294837206235)
  ·
    refine ⟨119339297652648442255809353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79559531768432294837206235 119339297652648442255809353)
    ·
      refine ⟨89504473239486331691857015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119339297652648442255809353 89504473239486331691857015)
      ·
        refine ⟨134256709859229497537785523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89504473239486331691857015 134256709859229497537785523)
        ·
          refine ⟨201385064788844246306678285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134256709859229497537785523 201385064788844246306678285)
          ·
            refine ⟨75519399295816592365004357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201385064788844246306678285 75519399295816592365004357)
            ·
              refine ⟨14159887367965611068438317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75519399295816592365004357 14159887367965611068438317)
              ·
                refine ⟨5309957762987104150664369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14159887367965611068438317 5309957762987104150664369)
                ·
                  refine ⟨3982468322240328112998277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5309957762987104150664369 3982468322240328112998277)
                  ·
                    refine ⟨746712810420061521187177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3982468322240328112998277 746712810420061521187177)
                    ·
                      rfl

theorem cell22_2181327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_2181327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181327 prefixEnd_2181327 := by exact prefixLift 2181327
  have htrace : WordTrace (prefixWord ++ tailWord_2181327) baseStart_2181327 baseEnd_2181327 := by
    simpa [prefixWord, tailWord_2181327, baseEnd_2181327] using wordTrace_append hprefix tailTrace_2181327
  have hstable : (prefixWord ++ tailWord_2181327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181327).length < 2 ^ (prefixWord ++ tailWord_2181327).sum := by decide
  have hdescent : baseEnd_2181327 < baseStart_2181327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181406 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2181406 : Nat := 118140960795 + 2181406 * 2 ^ 59
def prefixEnd_2181406 : Nat := 4983230072969 + 3 ^ 40 * 2181406 * 2
def baseEnd_2181406 : Nat := 746739853734531648461935

theorem tailTrace_2181406 : CollatzResearch.WordTrace tailWord_2181406 prefixEnd_2181406 746739853734531648461935 := by
  unfold tailWord_2181406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9945301641893261416166509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53041608756764060886221381 9945301641893261416166509)
  ·
    refine ⟨3729488115709973031062441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9945301641893261416166509 3729488115709973031062441)
    ·
      refine ⟨2797116086782479773296831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3729488115709973031062441 2797116086782479773296831)
      ·
        refine ⟨4195674130173719659945247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2797116086782479773296831 4195674130173719659945247)
        ·
          refine ⟨6293511195260579489917871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4195674130173719659945247 6293511195260579489917871)
          ·
            refine ⟨9440266792890869234876807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293511195260579489917871 9440266792890869234876807)
            ·
              refine ⟨14160400189336303852315211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9440266792890869234876807 14160400189336303852315211)
              ·
                refine ⟨21240600284004455778472817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14160400189336303852315211 21240600284004455778472817)
                ·
                  refine ⟨15930450213003341833854613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21240600284004455778472817 15930450213003341833854613)
                  ·
                    refine ⟨746739853734531648461935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15930450213003341833854613 746739853734531648461935)
                    ·
                      rfl

theorem cell22_2181406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2181406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181406 prefixEnd_2181406 := by exact prefixLift 2181406
  have htrace : WordTrace (prefixWord ++ tailWord_2181406) baseStart_2181406 baseEnd_2181406 := by
    simpa [prefixWord, tailWord_2181406, baseEnd_2181406] using wordTrace_append hprefix tailTrace_2181406
  have hstable : (prefixWord ++ tailWord_2181406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181406).length < 2 ^ (prefixWord ++ tailWord_2181406).sum := by decide
  have hdescent : baseEnd_2181406 < baseStart_2181406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181408 : List Nat := [2, 1, 1, 5, 2, 2, 1, 4, 1, 3]
def baseStart_2181408 : Nat := 118140960795 + 2181408 * 2 ^ 59
def prefixEnd_2181408 : Nat := 4983230072969 + 3 ^ 40 * 2181408 * 2
def baseEnd_2181408 : Nat := 746740538375404309911929

theorem tailTrace_2181408 : CollatzResearch.WordTrace tailWord_2181408 prefixEnd_2181408 746740538375404309911929 := by
  unfold tailWord_2181408
  simp only [CollatzResearch.WordTrace]
  refine ⟨39781243040569422835452439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53041657387425897113936585 39781243040569422835452439)
  ·
    refine ⟨59671864560854134253178659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39781243040569422835452439 59671864560854134253178659)
    ·
      refine ⟨89507796841281201379767989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59671864560854134253178659 89507796841281201379767989)
      ·
        refine ⟨8391355953870112629353249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89507796841281201379767989 8391355953870112629353249)
        ·
          refine ⟨6293516965402584472014937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8391355953870112629353249 6293516965402584472014937)
          ·
            refine ⟨4720137724051938354011203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6293516965402584472014937 4720137724051938354011203)
            ·
              refine ⟨7080206586077907531016805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4720137724051938354011203 7080206586077907531016805)
              ·
                refine ⟨1327538734889607662065651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7080206586077907531016805 1327538734889607662065651)
                ·
                  refine ⟨1991308102334411493098477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327538734889607662065651 1991308102334411493098477)
                  ·
                    refine ⟨746740538375404309911929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1991308102334411493098477 746740538375404309911929)
                    ·
                      rfl

theorem cell22_2181408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 3].length) (baseStart_2181408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181408 prefixEnd_2181408 := by exact prefixLift 2181408
  have htrace : WordTrace (prefixWord ++ tailWord_2181408) baseStart_2181408 baseEnd_2181408 := by
    simpa [prefixWord, tailWord_2181408, baseEnd_2181408] using wordTrace_append hprefix tailTrace_2181408
  have hstable : (prefixWord ++ tailWord_2181408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181408).length < 2 ^ (prefixWord ++ tailWord_2181408).sum := by decide
  have hdescent : baseEnd_2181408 < baseStart_2181408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181432 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 8]
def baseStart_2181432 : Nat := 118140960795 + 2181432 * 2 ^ 59
def prefixEnd_2181432 : Nat := 4983230072969 + 3 ^ 40 * 2181432 * 2
def baseEnd_2181432 : Nat := 248916251355292082437285

theorem tailTrace_2181432 : CollatzResearch.WordTrace tailWord_2181432 prefixEnd_2181432 248916251355292082437285 := by
  unfold tailWord_2181432
  simp only [CollatzResearch.WordTrace]
  refine ⟨39781680716525948884889275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53042240955367931846519033 39781680716525948884889275)
  ·
    refine ⟨59672521074788923327333913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39781680716525948884889275 59672521074788923327333913)
    ·
      refine ⟨44754390806091692495500435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59672521074788923327333913 44754390806091692495500435)
      ·
        refine ⟨67131586209137538743250653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44754390806091692495500435 67131586209137538743250653)
        ·
          refine ⟨25174344828426577028718995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67131586209137538743250653 25174344828426577028718995)
          ·
            refine ⟨37761517242639865543078493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25174344828426577028718995 37761517242639865543078493)
            ·
              refine ⟨14160568965989949578654435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37761517242639865543078493 14160568965989949578654435)
              ·
                refine ⟨21240853448984924367981653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14160568965989949578654435 21240853448984924367981653)
                ·
                  refine ⟨248916251355292082437285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21240853448984924367981653 248916251355292082437285)
                  ·
                    rfl

theorem cell22_2181432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_2181432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181432 prefixEnd_2181432 := by exact prefixLift 2181432
  have htrace : WordTrace (prefixWord ++ tailWord_2181432) baseStart_2181432 baseEnd_2181432 := by
    simpa [prefixWord, tailWord_2181432, baseEnd_2181432] using wordTrace_append hprefix tailTrace_2181432
  have hstable : (prefixWord ++ tailWord_2181432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181432).length < 2 ^ (prefixWord ++ tailWord_2181432).sum := by decide
  have hdescent : baseEnd_2181432 < baseStart_2181432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181434 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_2181434 : Nat := 118140960795 + 2181434 * 2 ^ 59
def prefixEnd_2181434 : Nat := 4983230072969 + 3 ^ 40 * 2181434 * 2
def baseEnd_2181434 : Nat := 746749438706748908761849

theorem tailTrace_2181434 : CollatzResearch.WordTrace tailWord_2181434 prefixEnd_2181434 746749438706748908761849 := by
  unfold tailWord_2181434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19890858594761163027837839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53042289586029768074234237 19890858594761163027837839)
  ·
    refine ⟨29836287892141744541756759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19890858594761163027837839 29836287892141744541756759)
    ·
      refine ⟨44754431838212616812635139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29836287892141744541756759 44754431838212616812635139)
      ·
        refine ⟨67131647757318925218952709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44754431838212616812635139 67131647757318925218952709)
        ·
          refine ⟨12587183954497298478553633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67131647757318925218952709 12587183954497298478553633)
          ·
            refine ⟨9440387965872973858915225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12587183954497298478553633 9440387965872973858915225)
            ·
              refine ⟨7080290974404730394186419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9440387965872973858915225 7080290974404730394186419)
              ·
                refine ⟨10620436461607095591279629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7080290974404730394186419 10620436461607095591279629)
                ·
                  refine ⟨3982663673102660846729861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10620436461607095591279629 3982663673102660846729861)
                  ·
                    refine ⟨746749438706748908761849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3982663673102660846729861 746749438706748908761849)
                    ·
                      rfl

theorem cell22_2181434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_2181434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181434 prefixEnd_2181434 := by exact prefixLift 2181434
  have htrace : WordTrace (prefixWord ++ tailWord_2181434) baseStart_2181434 baseEnd_2181434 := by
    simpa [prefixWord, tailWord_2181434, baseEnd_2181434] using wordTrace_append hprefix tailTrace_2181434
  have hstable : (prefixWord ++ tailWord_2181434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181434).length < 2 ^ (prefixWord ++ tailWord_2181434).sum := by decide
  have hdescent : baseEnd_2181434 < baseStart_2181434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181479 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2181479 : Nat := 118140960795 + 2181479 * 2 ^ 59
def prefixEnd_2181479 : Nat := 4983230072969 + 3 ^ 40 * 2181479 * 2
def baseEnd_2181479 : Nat := 746764843126383791386711

theorem tailTrace_2181479 : CollatzResearch.WordTrace tailWord_2181479 prefixEnd_2181479 746764843126383791386711 := by
  unfold tailWord_2181479
  simp only [CollatzResearch.WordTrace]
  refine ⟨79565075663881624796739491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53043383775921083197826327 79565075663881624796739491)
  ·
    refine ⟨119347613495822437195109237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79565075663881624796739491 119347613495822437195109237)
    ·
      refine ⟨11188838765233353487041491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119347613495822437195109237 11188838765233353487041491)
      ·
        refine ⟨16783258147850030230562237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11188838765233353487041491 16783258147850030230562237)
        ·
          refine ⟨6293721805443761336460839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16783258147850030230562237 6293721805443761336460839)
          ·
            refine ⟨9440582708165642004691259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6293721805443761336460839 9440582708165642004691259)
            ·
              refine ⟨14160874062248463007036889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9440582708165642004691259 14160874062248463007036889)
              ·
                refine ⟨10620655546686347255277667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14160874062248463007036889 10620655546686347255277667)
                ·
                  refine ⟨15930983320029520882916501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10620655546686347255277667 15930983320029520882916501)
                  ·
                    refine ⟨746764843126383791386711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15930983320029520882916501 746764843126383791386711)
                    ·
                      rfl

theorem cell22_2181479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2181479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181479 prefixEnd_2181479 := by exact prefixLift 2181479
  have htrace : WordTrace (prefixWord ++ tailWord_2181479) baseStart_2181479 baseEnd_2181479 := by
    simpa [prefixWord, tailWord_2181479, baseEnd_2181479] using wordTrace_append hprefix tailTrace_2181479
  have hstable : (prefixWord ++ tailWord_2181479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181479).length < 2 ^ (prefixWord ++ tailWord_2181479).sum := by decide
  have hdescent : baseEnd_2181479 < baseStart_2181479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181616 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 4, 3]
def baseStart_2181616 : Nat := 118140960795 + 2181616 * 2 ^ 59
def prefixEnd_2181616 : Nat := 4983230072969 + 3 ^ 40 * 2181616 * 2
def baseEnd_2181616 : Nat := 746811741026161100711291

theorem tailTrace_2181616 : CollatzResearch.WordTrace tailWord_2181616 prefixEnd_2181616 746811741026161100711291 := by
  unfold tailWord_2181616
  simp only [CollatzResearch.WordTrace]
  refine ⟨39785036232192648597238351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53046714976256864796317801 39785036232192648597238351)
  ·
    refine ⟨59677554348288972895857527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39785036232192648597238351 59677554348288972895857527)
    ·
      refine ⟨89516331522433459343786291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59677554348288972895857527 89516331522433459343786291)
      ·
        refine ⟨134274497283650189015679437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89516331522433459343786291 134274497283650189015679437)
        ·
          refine ⟨50352936481368820880879789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134274497283650189015679437 50352936481368820880879789)
          ·
            refine ⟨18882351180513307830329921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50352936481368820880879789 18882351180513307830329921)
            ·
              refine ⟨14161763385384980872747441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18882351180513307830329921 14161763385384980872747441)
              ·
                refine ⟨10621322539038735654560581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14161763385384980872747441 10621322539038735654560581)
                ·
                  refine ⟨1991497976069762935230109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10621322539038735654560581 1991497976069762935230109)
                  ·
                    refine ⟨746811741026161100711291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1991497976069762935230109 746811741026161100711291)
                    ·
                      rfl

theorem cell22_2181616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_2181616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181616 prefixEnd_2181616 := by exact prefixLift 2181616
  have htrace : WordTrace (prefixWord ++ tailWord_2181616) baseStart_2181616 baseEnd_2181616 := by
    simpa [prefixWord, tailWord_2181616, baseEnd_2181616] using wordTrace_append hprefix tailTrace_2181616
  have hstable : (prefixWord ++ tailWord_2181616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181616).length < 2 ^ (prefixWord ++ tailWord_2181616).sum := by decide
  have hdescent : baseEnd_2181616 < baseStart_2181616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181629 : List Nat := [1, 4, 1, 1, 1, 3, 11]
def baseStart_2181629 : Nat := 118140960795 + 2181629 * 2 ^ 59
def prefixEnd_2181629 : Nat := 4983230072969 + 3 ^ 40 * 2181629 * 2
def baseEnd_2181629 : Nat := 27659858933030866671713

theorem tailTrace_2181629 : CollatzResearch.WordTrace tailWord_2181629 prefixEnd_2181629 27659858933030866671713 := by
  unfold tailWord_2181629
  simp only [CollatzResearch.WordTrace]
  refine ⟨79570546613338200414699941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53047031075558800276466627 79570546613338200414699941)
  ·
    refine ⟨14919477490000912577756239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79570546613338200414699941 14919477490000912577756239)
    ·
      refine ⟨22379216235001368866634359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14919477490000912577756239 22379216235001368866634359)
      ·
        refine ⟨33568824352502053299951539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22379216235001368866634359 33568824352502053299951539)
        ·
          refine ⟨50353236528753079949927309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33568824352502053299951539 50353236528753079949927309)
          ·
            refine ⟨18882463698282404981222741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50353236528753079949927309 18882463698282404981222741)
            ·
              refine ⟨27659858933030866671713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18882463698282404981222741 27659858933030866671713)
              ·
                rfl

theorem cell22_2181629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 11].length) (baseStart_2181629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181629 prefixEnd_2181629 := by exact prefixLift 2181629
  have htrace : WordTrace (prefixWord ++ tailWord_2181629) baseStart_2181629 baseEnd_2181629 := by
    simpa [prefixWord, tailWord_2181629, baseEnd_2181629] using wordTrace_append hprefix tailTrace_2181629
  have hstable : (prefixWord ++ tailWord_2181629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181629).length < 2 ^ (prefixWord ++ tailWord_2181629).sum := by decide
  have hdescent : baseEnd_2181629 < baseStart_2181629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181633 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2181633 : Nat := 118140960795 + 2181633 * 2 ^ 59
def prefixEnd_2181633 : Nat := 4983230072969 + 3 ^ 40 * 2181633 * 2
def baseEnd_2181633 : Nat := 746817560473578723036239

theorem tailTrace_2181633 : CollatzResearch.WordTrace tailWord_2181633 prefixEnd_2181633 746817560473578723036239 := by
  unfold tailWord_2181633
  simp only [CollatzResearch.WordTrace]
  refine ⟨79570692505323709097845553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53047128336882472731897035 79570692505323709097845553)
  ·
    refine ⟨59678019378992781823384165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79570692505323709097845553 59678019378992781823384165)
    ·
      refine ⟨11189628633561146591884531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59678019378992781823384165 11189628633561146591884531)
      ·
        refine ⟨16784442950341719887826797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11189628633561146591884531 16784442950341719887826797)
        ·
          refine ⟨6294166106378144957935049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16784442950341719887826797 6294166106378144957935049)
          ·
            refine ⟨4720624579783608718451287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6294166106378144957935049 4720624579783608718451287)
            ·
              refine ⟨7080936869675413077676931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4720624579783608718451287 7080936869675413077676931)
              ·
                refine ⟨10621405304513119616515397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7080936869675413077676931 10621405304513119616515397)
                ·
                  refine ⟨1991513494596209928096637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10621405304513119616515397 1991513494596209928096637)
                  ·
                    refine ⟨746817560473578723036239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1991513494596209928096637 746817560473578723036239)
                    ·
                      rfl

theorem cell22_2181633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2181633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181633 prefixEnd_2181633 := by exact prefixLift 2181633
  have htrace : WordTrace (prefixWord ++ tailWord_2181633) baseStart_2181633 baseEnd_2181633 := by
    simpa [prefixWord, tailWord_2181633, baseEnd_2181633] using wordTrace_append hprefix tailTrace_2181633
  have hstable : (prefixWord ++ tailWord_2181633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181633).length < 2 ^ (prefixWord ++ tailWord_2181633).sum := by decide
  have hdescent : baseEnd_2181633 < baseStart_2181633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181746 : List Nat := [3, 2, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_2181746 : Nat := 118140960795 + 2181746 * 2 ^ 59
def prefixEnd_2181746 : Nat := 4983230072969 + 3 ^ 40 * 2181746 * 2
def baseEnd_2181746 : Nat := 746856242682884094960893

theorem tailTrace_2181746 : CollatzResearch.WordTrace tailWord_2181746 prefixEnd_2181746 746856242682884094960893 := by
  unfold tailWord_2181746
  simp only [CollatzResearch.WordTrace]
  refine ⟨19893703488478582349177273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53049875969276219597806061 19893703488478582349177273)
  ·
    refine ⟨14920277616358936761882955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19893703488478582349177273 14920277616358936761882955)
    ·
      refine ⟨22380416424538405142824433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14920277616358936761882955 22380416424538405142824433)
      ·
        refine ⟨16785312318403803857118325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22380416424538405142824433 16785312318403803857118325)
        ·
          refine ⟨1573623029850356611604843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16785312318403803857118325 1573623029850356611604843)
          ·
            refine ⟨2360434544775534917407265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573623029850356611604843 2360434544775534917407265)
            ·
              refine ⟨1770325908581651188055449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2360434544775534917407265 1770325908581651188055449)
              ·
                refine ⟨1327744431436238391041587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770325908581651188055449 1327744431436238391041587)
                ·
                  refine ⟨1991616647154357586562381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327744431436238391041587 1991616647154357586562381)
                  ·
                    refine ⟨746856242682884094960893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1991616647154357586562381 746856242682884094960893)
                    ·
                      rfl

theorem cell22_2181746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_2181746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181746 prefixEnd_2181746 := by exact prefixLift 2181746
  have htrace : WordTrace (prefixWord ++ tailWord_2181746) baseStart_2181746 baseEnd_2181746 := by
    simpa [prefixWord, tailWord_2181746, baseEnd_2181746] using wordTrace_append hprefix tailTrace_2181746
  have hstable : (prefixWord ++ tailWord_2181746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181746).length < 2 ^ (prefixWord ++ tailWord_2181746).sum := by decide
  have hdescent : baseEnd_2181746 < baseStart_2181746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181847 : List Nat := [1, 1, 3, 2, 1, 4, 3, 3, 1, 3]
def baseStart_2181847 : Nat := 118140960795 + 2181847 * 2 ^ 59
def prefixEnd_2181847 : Nat := 4983230072969 + 3 ^ 40 * 2181847 * 2
def baseEnd_2181847 : Nat := 746890817046953498185583

theorem tailTrace_2181847 : CollatzResearch.WordTrace tailWord_2181847 prefixEnd_2181847 746890817046953498185583 := by
  unfold tailWord_2181847
  simp only [CollatzResearch.WordTrace]
  refine ⟨79578497726548423646135795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53052331817698949097423863 79578497726548423646135795)
  ·
    refine ⟨119367746589822635469203693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79578497726548423646135795 119367746589822635469203693)
    ·
      refine ⟨44762904971183488300951385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119367746589822635469203693 44762904971183488300951385)
      ·
        refine ⟨33572178728387616225713539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44762904971183488300951385 33572178728387616225713539)
        ·
          refine ⟨50358268092581424338570309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33572178728387616225713539 50358268092581424338570309)
          ·
            refine ⟨9442175267359017063481933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50358268092581424338570309 9442175267359017063481933)
            ·
              refine ⟨3540815725259631398805725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9442175267359017063481933 3540815725259631398805725)
              ·
                refine ⟨1327805896972361774552147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3540815725259631398805725 1327805896972361774552147)
                ·
                  refine ⟨1991708845458542661828221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1327805896972361774552147 1991708845458542661828221)
                  ·
                    refine ⟨746890817046953498185583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1991708845458542661828221 746890817046953498185583)
                    ·
                      rfl

theorem cell22_2181847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_2181847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181847 prefixEnd_2181847 := by exact prefixLift 2181847
  have htrace : WordTrace (prefixWord ++ tailWord_2181847) baseStart_2181847 baseEnd_2181847 := by
    simpa [prefixWord, tailWord_2181847, baseEnd_2181847] using wordTrace_append hprefix tailTrace_2181847
  have hstable : (prefixWord ++ tailWord_2181847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181847).length < 2 ^ (prefixWord ++ tailWord_2181847).sum := by decide
  have hdescent : baseEnd_2181847 < baseStart_2181847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181864 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 3, 3]
def baseStart_2181864 : Nat := 118140960795 + 2181864 * 2 ^ 59
def prefixEnd_2181864 : Nat := 4983230072969 + 3 ^ 40 * 2181864 * 2
def baseEnd_2181864 : Nat := 746896636494371120510531

theorem tailTrace_2181864 : CollatzResearch.WordTrace tailWord_2181864 prefixEnd_2181864 746896636494371120510531 := by
  unfold tailWord_2181864
  simp only [CollatzResearch.WordTrace]
  refine ⟨39789558883743417774752323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53052745178324557033003097 39789558883743417774752323)
  ·
    refine ⟨59684338325615126662128485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39789558883743417774752323 59684338325615126662128485)
    ·
      refine ⟨11190813436052836249149091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59684338325615126662128485 11190813436052836249149091)
      ·
        refine ⟨16786220154079254373723637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11190813436052836249149091 16786220154079254373723637)
        ·
          refine ⟨1573708139444930097536591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16786220154079254373723637 1573708139444930097536591)
          ·
            refine ⟨2360562209167395146304887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573708139444930097536591 2360562209167395146304887)
            ·
              refine ⟨3540843313751092719457331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360562209167395146304887 3540843313751092719457331)
              ·
                refine ⟨5311264970626639079185997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3540843313751092719457331 5311264970626639079185997)
                ·
                  refine ⟨1991724363984989654694749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5311264970626639079185997 1991724363984989654694749)
                  ·
                    refine ⟨746896636494371120510531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1991724363984989654694749 746896636494371120510531)
                    ·
                      rfl

theorem cell22_2181864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_2181864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181864 prefixEnd_2181864 := by exact prefixLift 2181864
  have htrace : WordTrace (prefixWord ++ tailWord_2181864) baseStart_2181864 baseEnd_2181864 := by
    simpa [prefixWord, tailWord_2181864, baseEnd_2181864] using wordTrace_append hprefix tailTrace_2181864
  have hstable : (prefixWord ++ tailWord_2181864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181864).length < 2 ^ (prefixWord ++ tailWord_2181864).sum := by decide
  have hdescent : baseEnd_2181864 < baseStart_2181864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181873 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_2181873 : Nat := 118140960795 + 2181873 * 2 ^ 59
def prefixEnd_2181873 : Nat := 4983230072969 + 3 ^ 40 * 2181873 * 2
def baseEnd_2181873 : Nat := 746899717378298097035503

theorem tailTrace_2181873 : CollatzResearch.WordTrace tailWord_2181873 prefixEnd_2181873 746899717378298097035503 := by
  unfold tailWord_2181873
  simp only [CollatzResearch.WordTrace]
  refine ⟨79579446024454230086582273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53052964016302820057721515 79579446024454230086582273)
  ·
    refine ⟨59684584518340672564936705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79579446024454230086582273 59684584518340672564936705)
    ·
      refine ⟨44763438388755504423702529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59684584518340672564936705 44763438388755504423702529)
      ·
        refine ⟨33572578791566628317776897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44763438388755504423702529 33572578791566628317776897)
        ·
          refine ⟨25179434093674971238332673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33572578791566628317776897 25179434093674971238332673)
          ·
            refine ⟨18884575570256228428749505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25179434093674971238332673 18884575570256228428749505)
            ·
              refine ⟨14163431677692171321562129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18884575570256228428749505 14163431677692171321562129)
              ·
                refine ⟨10622573758269128491171597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14163431677692171321562129 10622573758269128491171597)
                ·
                  refine ⟨3983465159350923184189349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10622573758269128491171597 3983465159350923184189349)
                  ·
                    refine ⟨746899717378298097035503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3983465159350923184189349 746899717378298097035503)
                    ·
                      rfl

theorem cell22_2181873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_2181873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181873 prefixEnd_2181873 := by exact prefixLift 2181873
  have htrace : WordTrace (prefixWord ++ tailWord_2181873) baseStart_2181873 baseEnd_2181873 := by
    simpa [prefixWord, tailWord_2181873, baseEnd_2181873] using wordTrace_append hprefix tailTrace_2181873
  have hstable : (prefixWord ++ tailWord_2181873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181873).length < 2 ^ (prefixWord ++ tailWord_2181873).sum := by decide
  have hdescent : baseEnd_2181873 < baseStart_2181873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181903 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 1, 5]
def baseStart_2181903 : Nat := 118140960795 + 2181903 * 2 ^ 59
def prefixEnd_2181903 : Nat := 4983230072969 + 3 ^ 40 * 2181903 * 2
def baseEnd_2181903 : Nat := 746909986991388018785411

theorem tailTrace_2181903 : CollatzResearch.WordTrace tailWord_2181903 prefixEnd_2181903 746909986991388018785411 := by
  unfold tailWord_2181903
  simp only [CollatzResearch.WordTrace]
  refine ⟨79580540214345545210174363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53053693476230363473449575 79580540214345545210174363)
  ·
    refine ⟨119370810321518317815261545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79580540214345545210174363 119370810321518317815261545)
    ·
      refine ⟨89528107741138738361446159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119370810321518317815261545 89528107741138738361446159)
      ·
        refine ⟨134292161611708107542169239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89528107741138738361446159 134292161611708107542169239)
        ·
          refine ⟨201438242417562161313253859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134292161611708107542169239 201438242417562161313253859)
          ·
            refine ⟨302157363626343241969880789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201438242417562161313253859 302157363626343241969880789)
            ·
              refine ⟨7081813209992419733669081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 302157363626343241969880789 7081813209992419733669081)
              ·
                refine ⟨5311359907494314800251811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7081813209992419733669081 5311359907494314800251811)
                ·
                  refine ⟨7967039861241472200377717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5311359907494314800251811 7967039861241472200377717)
                  ·
                    refine ⟨746909986991388018785411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7967039861241472200377717 746909986991388018785411)
                    ·
                      rfl

theorem cell22_2181903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_2181903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181903 prefixEnd_2181903 := by exact prefixLift 2181903
  have htrace : WordTrace (prefixWord ++ tailWord_2181903) baseStart_2181903 baseEnd_2181903 := by
    simpa [prefixWord, tailWord_2181903, baseEnd_2181903] using wordTrace_append hprefix tailTrace_2181903
  have hstable : (prefixWord ++ tailWord_2181903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181903).length < 2 ^ (prefixWord ++ tailWord_2181903).sum := by decide
  have hdescent : baseEnd_2181903 < baseStart_2181903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181922 : List Nat := [3, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_2181922 : Nat := 118140960795 + 2181922 * 2 ^ 59
def prefixEnd_2181922 : Nat := 4983230072969 + 3 ^ 40 * 2181922 * 2
def baseEnd_2181922 : Nat := 248972163693226100853451

theorem tailTrace_2181922 : CollatzResearch.WordTrace tailWord_2181922 prefixEnd_2181922 248972163693226100853451 := by
  unfold tailWord_2181922
  simp only [CollatzResearch.WordTrace]
  refine ⟨19895308300319177863779005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53054155467517807636744013 19895308300319177863779005)
  ·
    refine ⟨7460740612619691698917127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19895308300319177863779005 7460740612619691698917127)
    ·
      refine ⟨11191110918929537548375691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7460740612619691698917127 11191110918929537548375691)
      ·
        refine ⟨16786666378394306322563537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11191110918929537548375691 16786666378394306322563537)
        ·
          refine ⟨12589999783795729741922653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16786666378394306322563537 12589999783795729741922653)
          ·
            refine ⟨4721249918923398653220995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12589999783795729741922653 4721249918923398653220995)
            ·
              refine ⟨7081874878385097979831493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4721249918923398653220995 7081874878385097979831493)
              ·
                refine ⟨1327851539697205871218405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7081874878385097979831493 1327851539697205871218405)
                ·
                  refine ⟨248972163693226100853451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1327851539697205871218405 248972163693226100853451)
                  ·
                    rfl

theorem cell22_2181922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_2181922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181922 prefixEnd_2181922 := by exact prefixLift 2181922
  have htrace : WordTrace (prefixWord ++ tailWord_2181922) baseStart_2181922 baseEnd_2181922 := by
    simpa [prefixWord, tailWord_2181922, baseEnd_2181922] using wordTrace_append hprefix tailTrace_2181922
  have hstable : (prefixWord ++ tailWord_2181922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181922).length < 2 ^ (prefixWord ++ tailWord_2181922).sum := by decide
  have hdescent : baseEnd_2181922 < baseStart_2181922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181956 : List Nat := [2, 3, 4, 2, 1, 1, 2, 3, 4]
def baseStart_2181956 : Nat := 118140960795 + 2181956 * 2 ^ 59
def prefixEnd_2181956 : Nat := 4983230072969 + 3 ^ 40 * 2181956 * 2
def baseEnd_2181956 : Nat := 248976043324837849070083

theorem tailTrace_2181956 : CollatzResearch.WordTrace tailWord_2181956 prefixEnd_2181956 248976043324837849070083 := by
  unfold tailWord_2181956
  simp only [CollatzResearch.WordTrace]
  refine ⟨39791236641576767630926861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53054982188769023507902481 39791236641576767630926861)
  ·
    refine ⟨14921713740591287861597573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39791236641576767630926861 14921713740591287861597573)
    ·
      refine ⟨2797821326360866474049545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14921713740591287861597573 2797821326360866474049545)
      ·
        refine ⟨2098365994770649855537159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2797821326360866474049545 2098365994770649855537159)
        ·
          refine ⟨3147548992155974783305739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098365994770649855537159 3147548992155974783305739)
          ·
            refine ⟨4721323488233962174958609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3147548992155974783305739 4721323488233962174958609)
            ·
              refine ⟨3540992616175471631218957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4721323488233962174958609 3540992616175471631218957)
              ·
                refine ⟨1327872231065801861707109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3540992616175471631218957 1327872231065801861707109)
                ·
                  refine ⟨248976043324837849070083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1327872231065801861707109 248976043324837849070083)
                  ·
                    rfl

theorem cell22_2181956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_2181956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181956 prefixEnd_2181956 := by exact prefixLift 2181956
  have htrace : WordTrace (prefixWord ++ tailWord_2181956) baseStart_2181956 baseEnd_2181956 := by
    simpa [prefixWord, tailWord_2181956, baseEnd_2181956] using wordTrace_append hprefix tailTrace_2181956
  have hstable : (prefixWord ++ tailWord_2181956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181956).length < 2 ^ (prefixWord ++ tailWord_2181956).sum := by decide
  have hdescent : baseEnd_2181956 < baseStart_2181956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181958 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2181958 : Nat := 118140960795 + 2181958 * 2 ^ 59
def prefixEnd_2181958 : Nat := 4983230072969 + 3 ^ 40 * 2181958 * 2
def baseEnd_2181958 : Nat := 746928814615386208660243

theorem tailTrace_2181958 : CollatzResearch.WordTrace tailWord_2181958 prefixEnd_2181958 746928814615386208660243 := by
  unfold tailWord_2181958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486954569660821550107079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53055030819430859735617685 2486954569660821550107079)
  ·
    refine ⟨3730431854491232325160619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2486954569660821550107079 3730431854491232325160619)
    ·
      refine ⟨5595647781736848487740929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3730431854491232325160619 5595647781736848487740929)
      ·
        refine ⟨4196735836302636365805697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5595647781736848487740929 4196735836302636365805697)
        ·
          refine ⟨3147551877226977274354273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4196735836302636365805697 3147551877226977274354273)
          ·
            refine ⟨2360663907920232955765705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147551877226977274354273 2360663907920232955765705)
            ·
              refine ⟨1770497930940174716824279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2360663907920232955765705 1770497930940174716824279)
              ·
                refine ⟨2655746896410262075236419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770497930940174716824279 2655746896410262075236419)
                ·
                  refine ⟨3983620344615393112854629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655746896410262075236419 3983620344615393112854629)
                  ·
                    refine ⟨746928814615386208660243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3983620344615393112854629 746928814615386208660243)
                    ·
                      rfl

theorem cell22_2181958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2181958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2181958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2181958 prefixEnd_2181958 := by exact prefixLift 2181958
  have htrace : WordTrace (prefixWord ++ tailWord_2181958) baseStart_2181958 baseEnd_2181958 := by
    simpa [prefixWord, tailWord_2181958, baseEnd_2181958] using wordTrace_append hprefix tailTrace_2181958
  have hstable : (prefixWord ++ tailWord_2181958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181958).length < 2 ^ (prefixWord ++ tailWord_2181958).sum := by decide
  have hdescent : baseEnd_2181958 < baseStart_2181958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182115 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 2, 6]
def baseStart_2182115 : Nat := 118140960795 + 2182115 * 2 ^ 59
def prefixEnd_2182115 : Nat := 4983230072969 + 3 ^ 40 * 2182115 * 2
def baseEnd_2182115 : Nat := 746982558923890132484761

theorem tailTrace_2182115 : CollatzResearch.WordTrace tailWord_2182115 prefixEnd_2182115 746982558923890132484761 := by
  unfold tailWord_2182115
  simp only [CollatzResearch.WordTrace]
  refine ⟨79588272489577505416891799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53058848326385003611261199 79588272489577505416891799)
  ·
    refine ⟨119382408734366258125337699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79588272489577505416891799 119382408734366258125337699)
    ·
      refine ⟨179073613101549387188006549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119382408734366258125337699 179073613101549387188006549)
      ·
        refine ⟨8394075614135127524437807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 179073613101549387188006549 8394075614135127524437807)
        ·
          refine ⟨12591113421202691286656711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8394075614135127524437807 12591113421202691286656711)
          ·
            refine ⟨18886670131804036929985067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12591113421202691286656711 18886670131804036929985067)
            ·
              refine ⟨28330005197706055394977601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18886670131804036929985067 28330005197706055394977601)
              ·
                refine ⟨21247503898279541546233201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28330005197706055394977601 21247503898279541546233201)
                ·
                  refine ⟨15935627923709656159674901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21247503898279541546233201 15935627923709656159674901)
                  ·
                    refine ⟨746982558923890132484761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15935627923709656159674901 746982558923890132484761)
                    ·
                      rfl

theorem cell22_2182115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_2182115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182115 prefixEnd_2182115 := by exact prefixLift 2182115
  have htrace : WordTrace (prefixWord ++ tailWord_2182115) baseStart_2182115 baseEnd_2182115 := by
    simpa [prefixWord, tailWord_2182115, baseEnd_2182115] using wordTrace_append hprefix tailTrace_2182115
  have hstable : (prefixWord ++ tailWord_2182115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182115).length < 2 ^ (prefixWord ++ tailWord_2182115).sum := by decide
  have hdescent : baseEnd_2182115 < baseStart_2182115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182222 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2182222 : Nat := 118140960795 + 2182222 * 2 ^ 59
def prefixEnd_2182222 : Nat := 4983230072969 + 3 ^ 40 * 2182222 * 2
def baseEnd_2182222 : Nat := 747019187210577520059433

theorem tailTrace_2182222 : CollatzResearch.WordTrace tailWord_2182222 prefixEnd_2182222 747019187210577520059433 := by
  unfold tailWord_2182222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949021887523732836379615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53061450066793241794024613 9949021887523732836379615)
  ·
    refine ⟨14923532831285599254569423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9949021887523732836379615 14923532831285599254569423)
    ·
      refine ⟨22385299246928398881854135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14923532831285599254569423 22385299246928398881854135)
      ·
        refine ⟨33577948870392598322781203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22385299246928398881854135 33577948870392598322781203)
        ·
          refine ⟨50366923305588897484171805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33577948870392598322781203 50366923305588897484171805)
          ·
            refine ⟨18887596239595836556564427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50366923305588897484171805 18887596239595836556564427)
            ·
              refine ⟨28331394359393754834846641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18887596239595836556564427 28331394359393754834846641)
              ·
                refine ⟨21248545769545316126134981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28331394359393754834846641 21248545769545316126134981)
                ·
                  refine ⟨3984102331789746773650309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21248545769545316126134981 3984102331789746773650309)
                  ·
                    refine ⟨747019187210577520059433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984102331789746773650309 747019187210577520059433)
                    ·
                      rfl

theorem cell22_2182222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2182222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182222 prefixEnd_2182222 := by exact prefixLift 2182222
  have htrace : WordTrace (prefixWord ++ tailWord_2182222) baseStart_2182222 baseEnd_2182222 := by
    simpa [prefixWord, tailWord_2182222, baseEnd_2182222] using wordTrace_append hprefix tailTrace_2182222
  have hstable : (prefixWord ++ tailWord_2182222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182222).length < 2 ^ (prefixWord ++ tailWord_2182222).sum := by decide
  have hdescent : baseEnd_2182222 < baseStart_2182222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182269 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_2182269 : Nat := 118140960795 + 2182269 * 2 ^ 59
def prefixEnd_2182269 : Nat := 4983230072969 + 3 ^ 40 * 2182269 * 2
def baseEnd_2182269 : Nat := 747035276271085064134289

theorem tailTrace_2182269 : CollatzResearch.WordTrace tailWord_2182269 prefixEnd_2182269 747035276271085064134289 := by
  unfold tailWord_2182269
  simp only [CollatzResearch.WordTrace]
  refine ⟨79593889331019589717997861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53062592887346393145331907 79593889331019589717997861)
  ·
    refine ⟨14923854249566173072124599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79593889331019589717997861 14923854249566173072124599)
    ·
      refine ⟨22385781374349259608186899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14923854249566173072124599 22385781374349259608186899)
      ·
        refine ⟨33578672061523889412280349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22385781374349259608186899 33578672061523889412280349)
        ·
          refine ⟨12592002023071458529605131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33578672061523889412280349 12592002023071458529605131)
          ·
            refine ⟨18888003034607187794407697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12592002023071458529605131 18888003034607187794407697)
            ·
              refine ⟨14166002275955390845805773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18888003034607187794407697 14166002275955390845805773)
              ·
                refine ⟨5312250853483271567177165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14166002275955390845805773 5312250853483271567177165)
                ·
                  refine ⟨1992094070056226837691437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5312250853483271567177165 1992094070056226837691437)
                  ·
                    refine ⟨747035276271085064134289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1992094070056226837691437 747035276271085064134289)
                    ·
                      rfl

theorem cell22_2182269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_2182269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182269 prefixEnd_2182269 := by exact prefixLift 2182269
  have htrace : WordTrace (prefixWord ++ tailWord_2182269) baseStart_2182269 baseEnd_2182269 := by
    simpa [prefixWord, tailWord_2182269, baseEnd_2182269] using wordTrace_append hprefix tailTrace_2182269
  have hstable : (prefixWord ++ tailWord_2182269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182269).length < 2 ^ (prefixWord ++ tailWord_2182269).sum := by decide
  have hdescent : baseEnd_2182269 < baseStart_2182269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182286 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_2182286 : Nat := 118140960795 + 2182286 * 2 ^ 59
def prefixEnd_2182286 : Nat := 4983230072969 + 3 ^ 40 * 2182286 * 2
def baseEnd_2182286 : Nat := 747041095718502686459237

theorem tailTrace_2182286 : CollatzResearch.WordTrace tailWord_2182286 prefixEnd_2182286 747041095718502686459237 := by
  unfold tailWord_2182286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949313671494750202670839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53063006247972001080911141 9949313671494750202670839)
  ·
    refine ⟨14923970507242125304006259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9949313671494750202670839 14923970507242125304006259)
    ·
      refine ⟨22385955760863187956009389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14923970507242125304006259 22385955760863187956009389)
      ·
        refine ⟨8394733410323695483503521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22385955760863187956009389 8394733410323695483503521)
        ·
          refine ⟨6296050057742771612627641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8394733410323695483503521 6296050057742771612627641)
          ·
            refine ⟨4722037543307078709470731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296050057742771612627641 4722037543307078709470731)
            ·
              refine ⟨7083056314960618064206097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722037543307078709470731 7083056314960618064206097)
              ·
                refine ⟨5312292236220463548154573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083056314960618064206097 5312292236220463548154573)
                ·
                  refine ⟨1992109588582673830557965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5312292236220463548154573 1992109588582673830557965)
                  ·
                    refine ⟨747041095718502686459237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1992109588582673830557965 747041095718502686459237)
                    ·
                      rfl

theorem cell22_2182286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_2182286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182286 prefixEnd_2182286 := by exact prefixLift 2182286
  have htrace : WordTrace (prefixWord ++ tailWord_2182286) baseStart_2182286 baseEnd_2182286 := by
    simpa [prefixWord, tailWord_2182286, baseEnd_2182286] using wordTrace_append hprefix tailTrace_2182286
  have hstable : (prefixWord ++ tailWord_2182286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182286).length < 2 ^ (prefixWord ++ tailWord_2182286).sum := by decide
  have hdescent : baseEnd_2182286 < baseStart_2182286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182346 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_2182346 : Nat := 118140960795 + 2182346 * 2 ^ 59
def prefixEnd_2182346 : Nat := 4983230072969 + 3 ^ 40 * 2182346 * 2
def baseEnd_2182346 : Nat := 747061634944682529959053

theorem tailTrace_2182346 : CollatzResearch.WordTrace tailWord_2182346 prefixEnd_2182346 747061634944682529959053 := by
  unfold tailWord_2182346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19899174437935157967137723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53064465167827087912367261 19899174437935157967137723)
  ·
    refine ⟨29848761656902736950706585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19899174437935157967137723 29848761656902736950706585)
    ·
      refine ⟨22386571242677052713029939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29848761656902736950706585 22386571242677052713029939)
      ·
        refine ⟨33579856864015579069544909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22386571242677052713029939 33579856864015579069544909)
        ·
          refine ⟨12592446324005842151079341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33579856864015579069544909 12592446324005842151079341)
          ·
            refine ⟨4722167371502190806654753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12592446324005842151079341 4722167371502190806654753)
            ·
              refine ⟨3541625528626643104991065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4722167371502190806654753 3541625528626643104991065)
              ·
                refine ⟨2656219146469982328743299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541625528626643104991065 2656219146469982328743299)
                ·
                  refine ⟨3984328719704973493114949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656219146469982328743299 3984328719704973493114949)
                  ·
                    refine ⟨747061634944682529959053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984328719704973493114949 747061634944682529959053)
                    ·
                      rfl

theorem cell22_2182346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_2182346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182346 prefixEnd_2182346 := by exact prefixLift 2182346
  have htrace : WordTrace (prefixWord ++ tailWord_2182346) baseStart_2182346 baseEnd_2182346 := by
    simpa [prefixWord, tailWord_2182346, baseEnd_2182346] using wordTrace_append hprefix tailTrace_2182346
  have hstable : (prefixWord ++ tailWord_2182346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182346).length < 2 ^ (prefixWord ++ tailWord_2182346).sum := by decide
  have hdescent : baseEnd_2182346 < baseStart_2182346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182359 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 4, 3]
def baseStart_2182359 : Nat := 118140960795 + 2182359 * 2 ^ 59
def prefixEnd_2182359 : Nat := 4983230072969 + 3 ^ 40 * 2182359 * 2
def baseEnd_2182359 : Nat := 747066085110354829384013

theorem tailTrace_2182359 : CollatzResearch.WordTrace tailWord_2182359 prefixEnd_2182359 747066085110354829384013 := by
  unfold tailWord_2182359
  simp only [CollatzResearch.WordTrace]
  refine ⟨79597171900693535088774131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53064781267129023392516087 79597171900693535088774131)
  ·
    refine ⟨119395757851040302633161197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79597171900693535088774131 119395757851040302633161197)
    ·
      refine ⟨44773409194140113487435449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119395757851040302633161197 44773409194140113487435449)
      ·
        refine ⟨33580056895605085115576587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44773409194140113487435449 33580056895605085115576587)
        ·
          refine ⟨50370085343407627673364881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33580056895605085115576587 50370085343407627673364881)
          ·
            refine ⟨37777564007555720755023661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50370085343407627673364881 37777564007555720755023661)
            ·
              refine ⟨14166586502833395283133873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37777564007555720755023661 14166586502833395283133873)
              ·
                refine ⟨10624939877125046462350405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14166586502833395283133873 10624939877125046462350405)
                ·
                  refine ⟨1992176226960946211690701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10624939877125046462350405 1992176226960946211690701)
                  ·
                    refine ⟨747066085110354829384013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1992176226960946211690701 747066085110354829384013)
                    ·
                      rfl

theorem cell22_2182359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_2182359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182359 prefixEnd_2182359 := by exact prefixLift 2182359
  have htrace : WordTrace (prefixWord ++ tailWord_2182359) baseStart_2182359 baseEnd_2182359 := by
    simpa [prefixWord, tailWord_2182359, baseEnd_2182359] using wordTrace_append hprefix tailTrace_2182359
  have hstable : (prefixWord ++ tailWord_2182359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182359).length < 2 ^ (prefixWord ++ tailWord_2182359).sum := by decide
  have hdescent : baseEnd_2182359 < baseStart_2182359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182372 : List Nat := [2, 3, 1, 1, 1, 2, 12]
def baseStart_2182372 : Nat := 118140960795 + 2182372 * 2 ^ 59
def prefixEnd_2182372 : Nat := 4983230072969 + 3 ^ 40 * 2182372 * 2
def baseEnd_2182372 : Nat := 27669279084297301066999

theorem tailTrace_2182372 : CollatzResearch.WordTrace tailWord_2182372 prefixEnd_2182372 27669279084297301066999 := by
  unfold tailWord_2182372
  simp only [CollatzResearch.WordTrace]
  refine ⟨39798823024823219154498685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53065097366430958872664913 39798823024823219154498685)
  ·
    refine ⟨14924558634308707182937007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39798823024823219154498685 14924558634308707182937007)
    ·
      refine ⟨22386837951463060774405511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14924558634308707182937007 22386837951463060774405511)
      ·
        refine ⟨33580256927194591161608267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22386837951463060774405511 33580256927194591161608267)
        ·
          refine ⟨50370385390791886742412401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33580256927194591161608267 50370385390791886742412401)
          ·
            refine ⟨37777789043093915056809301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50370385390791886742412401 37777789043093915056809301)
            ·
              refine ⟨27669279084297301066999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 37777789043093915056809301 27669279084297301066999)
              ·
                rfl

theorem cell22_2182372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 12].length) (baseStart_2182372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182372 prefixEnd_2182372 := by exact prefixLift 2182372
  have htrace : WordTrace (prefixWord ++ tailWord_2182372) baseStart_2182372 baseEnd_2182372 := by
    simpa [prefixWord, tailWord_2182372, baseEnd_2182372] using wordTrace_append hprefix tailTrace_2182372
  have hstable : (prefixWord ++ tailWord_2182372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182372).length < 2 ^ (prefixWord ++ tailWord_2182372).sum := by decide
  have hdescent : baseEnd_2182372 < baseStart_2182372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182376 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 2, 3]
def baseStart_2182376 : Nat := 118140960795 + 2182376 * 2 ^ 59
def prefixEnd_2182376 : Nat := 4983230072969 + 3 ^ 40 * 2182376 * 2
def baseEnd_2182376 : Nat := 747071904557772451708961

theorem tailTrace_2182376 : CollatzResearch.WordTrace tailWord_2182376 prefixEnd_2182376 747071904557772451708961 := by
  unfold tailWord_2182376
  simp only [CollatzResearch.WordTrace]
  refine ⟨39798895970815973496071491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53065194627754631328095321 39798895970815973496071491)
  ·
    refine ⟨59698343956223960244107237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39798895970815973496071491 59698343956223960244107237)
    ·
      refine ⟨11193439491791992545770107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59698343956223960244107237 11193439491791992545770107)
      ·
        refine ⟨16790159237687988818655161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11193439491791992545770107 16790159237687988818655161)
        ·
          refine ⟨12592619428265991613991371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16790159237687988818655161 12592619428265991613991371)
          ·
            refine ⟨18888929142398987420987057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12592619428265991613991371 18888929142398987420987057)
            ·
              refine ⟨14166696856799240565740293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18888929142398987420987057 14166696856799240565740293)
              ·
                refine ⟨2656255660649857606076305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14166696856799240565740293 2656255660649857606076305)
                ·
                  refine ⟨1992191745487393204557229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2656255660649857606076305 1992191745487393204557229)
                  ·
                    refine ⟨747071904557772451708961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1992191745487393204557229 747071904557772451708961)
                    ·
                      rfl

theorem cell22_2182376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_2182376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182376 prefixEnd_2182376 := by exact prefixLift 2182376
  have htrace : WordTrace (prefixWord ++ tailWord_2182376) baseStart_2182376 baseEnd_2182376 := by
    simpa [prefixWord, tailWord_2182376, baseEnd_2182376] using wordTrace_append hprefix tailTrace_2182376
  have hstable : (prefixWord ++ tailWord_2182376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182376).length < 2 ^ (prefixWord ++ tailWord_2182376).sum := by decide
  have hdescent : baseEnd_2182376 < baseStart_2182376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182378 : List Nat := [3, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_2182378 : Nat := 118140960795 + 2182378 * 2 ^ 59
def prefixEnd_2182378 : Nat := 4983230072969 + 3 ^ 40 * 2182378 * 2
def baseEnd_2182378 : Nat := 249024196399548371052985

theorem tailTrace_2182378 : CollatzResearch.WordTrace tailWord_2182378 prefixEnd_2182378 249024196399548371052985 := by
  unfold tailWord_2182378
  simp only [CollatzResearch.WordTrace]
  refine ⟨19899466221906175333428947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53065243258416467555810525 19899466221906175333428947)
  ·
    refine ⟨29849199332859263000143421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19899466221906175333428947 29849199332859263000143421)
    ·
      refine ⟨11193449749822223625053783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29849199332859263000143421 11193449749822223625053783)
      ·
        refine ⟨16790174624733335437580675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11193449749822223625053783 16790174624733335437580675)
        ·
          refine ⟨25185261937100003156371013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16790174624733335437580675 25185261937100003156371013)
          ·
            refine ⟨4722236613206250591819565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25185261937100003156371013 4722236613206250591819565)
            ·
              refine ⟨1770838729952343971932337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4722236613206250591819565 1770838729952343971932337)
              ·
                refine ⟨1328129047464257978949253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770838729952343971932337 1328129047464257978949253)
                ·
                  refine ⟨249024196399548371052985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328129047464257978949253 249024196399548371052985)
                  ·
                    rfl

theorem cell22_2182378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_2182378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182378 prefixEnd_2182378 := by exact prefixLift 2182378
  have htrace : WordTrace (prefixWord ++ tailWord_2182378) baseStart_2182378 baseEnd_2182378 := by
    simpa [prefixWord, tailWord_2182378, baseEnd_2182378] using wordTrace_append hprefix tailTrace_2182378
  have hstable : (prefixWord ++ tailWord_2182378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182378).length < 2 ^ (prefixWord ++ tailWord_2182378).sum := by decide
  have hdescent : baseEnd_2182378 < baseStart_2182378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182449 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_2182449 : Nat := 118140960795 + 2182449 * 2 ^ 59
def prefixEnd_2182449 : Nat := 4983230072969 + 3 ^ 40 * 2182449 * 2
def baseEnd_2182449 : Nat := 747096893949624594633737

theorem tailTrace_2182449 : CollatzResearch.WordTrace tailWord_2182449 prefixEnd_2182449 747096893949624594633737 := by
  unfold tailWord_2182449
  simp only [CollatzResearch.WordTrace]
  refine ⟨79600454470367480459550401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53066969646911653639700267 79600454470367480459550401)
  ·
    refine ⟨59700340852775610344662801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79600454470367480459550401 59700340852775610344662801)
    ·
      refine ⟨44775255639581707758497101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59700340852775610344662801 44775255639581707758497101)
      ·
        refine ⟨16790720864843140409436413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44775255639581707758497101 16790720864843140409436413)
        ·
          refine ⟨6296520324316177653538655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16790720864843140409436413 6296520324316177653538655)
          ·
            refine ⟨9444780486474266480307983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6296520324316177653538655 9444780486474266480307983)
            ·
              refine ⟨14167170729711399720461975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9444780486474266480307983 14167170729711399720461975)
              ·
                refine ⟨21250756094567099580692963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14167170729711399720461975 21250756094567099580692963)
                ·
                  refine ⟨31876134141850649371039445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21250756094567099580692963 31876134141850649371039445)
                  ·
                    refine ⟨747096893949624594633737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31876134141850649371039445 747096893949624594633737)
                    ·
                      rfl

theorem cell22_2182449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_2182449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182449 prefixEnd_2182449 := by exact prefixLift 2182449
  have htrace : WordTrace (prefixWord ++ tailWord_2182449) baseStart_2182449 baseEnd_2182449 := by
    simpa [prefixWord, tailWord_2182449, baseEnd_2182449] using wordTrace_append hprefix tailTrace_2182449
  have hstable : (prefixWord ++ tailWord_2182449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182449).length < 2 ^ (prefixWord ++ tailWord_2182449).sum := by decide
  have hdescent : baseEnd_2182449 < baseStart_2182449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182464 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_2182464 : Nat := 118140960795 + 2182464 * 2 ^ 59
def prefixEnd_2182464 : Nat := 4983230072969 + 3 ^ 40 * 2182464 * 2
def baseEnd_2182464 : Nat := 747102028756169555508691

theorem tailTrace_2182464 : CollatzResearch.WordTrace tailWord_2182464 prefixEnd_2182464 747102028756169555508691 := by
  unfold tailWord_2182464
  simp only [CollatzResearch.WordTrace]
  refine ⟨39800500782656569010673223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53067334376875425347564297 39800500782656569010673223)
  ·
    refine ⟨59700751173984853516009835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39800500782656569010673223 59700751173984853516009835)
    ·
      refine ⟨89551126760977280274014753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59700751173984853516009835 89551126760977280274014753)
      ·
        refine ⟨67163345070732960205511065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89551126760977280274014753 67163345070732960205511065)
        ·
          refine ⟨50372508803049720154133299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67163345070732960205511065 50372508803049720154133299)
          ·
            refine ⟨75558763204574580231199949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50372508803049720154133299 75558763204574580231199949)
            ·
              refine ⟨28334536201715467586699981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75558763204574580231199949 28334536201715467586699981)
              ·
                refine ⟨10625451075643300345012493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28334536201715467586699981 10625451075643300345012493)
                ·
                  refine ⟨3984544153366237629379685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10625451075643300345012493 3984544153366237629379685)
                  ·
                    refine ⟨747102028756169555508691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984544153366237629379685 747102028756169555508691)
                    ·
                      rfl

theorem cell22_2182464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_2182464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182464 prefixEnd_2182464 := by exact prefixLift 2182464
  have htrace : WordTrace (prefixWord ++ tailWord_2182464) baseStart_2182464 baseEnd_2182464 := by
    simpa [prefixWord, tailWord_2182464, baseEnd_2182464] using wordTrace_append hprefix tailTrace_2182464
  have hstable : (prefixWord ++ tailWord_2182464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182464).length < 2 ^ (prefixWord ++ tailWord_2182464).sum := by decide
  have hdescent : baseEnd_2182464 < baseStart_2182464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182481 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_2182481 : Nat := 118140960795 + 2182481 * 2 ^ 59
def prefixEnd_2182481 : Nat := 4983230072969 + 3 ^ 40 * 2182481 * 2
def baseEnd_2182481 : Nat := 747107848203587177833639

theorem tailTrace_2182481 : CollatzResearch.WordTrace tailWord_2182481 prefixEnd_2182481 747107848203587177833639 := by
  unfold tailWord_2182481
  simp only [CollatzResearch.WordTrace]
  refine ⟨79601621606251549924715297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53067747737501033283143531 79601621606251549924715297)
  ·
    refine ⟨59701216204688662443536473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79601621606251549924715297 59701216204688662443536473)
    ·
      refine ⟨44775912153516496832652355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59701216204688662443536473 44775912153516496832652355)
      ·
        refine ⟨67163868230274745248978533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44775912153516496832652355 67163868230274745248978533)
        ·
          refine ⟨12593225293176514734183475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67163868230274745248978533 12593225293176514734183475)
          ·
            refine ⟨18889837939764772101275213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12593225293176514734183475 18889837939764772101275213)
            ·
              refine ⟨7083689227411789537978205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18889837939764772101275213 7083689227411789537978205)
              ·
                refine ⟨2656383460279421076741827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7083689227411789537978205 2656383460279421076741827)
                ·
                  refine ⟨3984575190419131615112741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656383460279421076741827 3984575190419131615112741)
                  ·
                    refine ⟨747107848203587177833639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984575190419131615112741 747107848203587177833639)
                    ·
                      rfl

theorem cell22_2182481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_2182481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182481 prefixEnd_2182481 := by exact prefixLift 2182481
  have htrace : WordTrace (prefixWord ++ tailWord_2182481) baseStart_2182481 baseEnd_2182481 := by
    simpa [prefixWord, tailWord_2182481, baseEnd_2182481] using wordTrace_append hprefix tailTrace_2182481
  have hstable : (prefixWord ++ tailWord_2182481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182481).length < 2 ^ (prefixWord ++ tailWord_2182481).sum := by decide
  have hdescent : baseEnd_2182481 < baseStart_2182481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182496 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 6]
def baseStart_2182496 : Nat := 118140960795 + 2182496 * 2 ^ 59
def prefixEnd_2182496 : Nat := 4983230072969 + 3 ^ 40 * 2182496 * 2
def baseEnd_2182496 : Nat := 249037661003377379569531

theorem tailTrace_2182496 : CollatzResearch.WordTrace tailWord_2182496 prefixEnd_2182496 249037661003377379569531 := by
  unfold tailWord_2182496
  simp only [CollatzResearch.WordTrace]
  refine ⟨39801084350598603743255671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53068112467464804991007561 39801084350598603743255671)
  ·
    refine ⟨59701626525897905614883507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39801084350598603743255671 59701626525897905614883507)
    ·
      refine ⟨89552439788846858422325261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59701626525897905614883507 89552439788846858422325261)
      ·
        refine ⟨33582164920817571908371973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89552439788846858422325261 33582164920817571908371973)
        ·
          refine ⟨6296655922653294732819745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33582164920817571908371973 6296655922653294732819745)
          ·
            refine ⟨4722491941989971049614809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296655922653294732819745 4722491941989971049614809)
            ·
              refine ⟨3541868956492478287211107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4722491941989971049614809 3541868956492478287211107)
              ·
                refine ⟨5312803434738717430816661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3541868956492478287211107 5312803434738717430816661)
                ·
                  refine ⟨249037661003377379569531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5312803434738717430816661 249037661003377379569531)
                  ·
                    rfl

theorem cell22_2182496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_2182496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182496 prefixEnd_2182496 := by exact prefixLift 2182496
  have htrace : WordTrace (prefixWord ++ tailWord_2182496) baseStart_2182496 baseEnd_2182496 := by
    simpa [prefixWord, tailWord_2182496, baseEnd_2182496] using wordTrace_append hprefix tailTrace_2182496
  have hstable : (prefixWord ++ tailWord_2182496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182496).length < 2 ^ (prefixWord ++ tailWord_2182496).sum := by decide
  have hdescent : baseEnd_2182496 < baseStart_2182496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182524 : List Nat := [2, 2, 2, 1, 1, 1, 5, 8]
def baseStart_2182524 : Nat := 118140960795 + 2182524 * 2 ^ 59
def prefixEnd_2182524 : Nat := 4983230072969 + 3 ^ 40 * 2182524 * 2
def baseEnd_2182524 : Nat := 83013618664705488778723

theorem tailTrace_2182524 : CollatzResearch.WordTrace tailWord_2182524 prefixEnd_2182524 83013618664705488778723 := by
  unfold tailWord_2182524
  simp only [CollatzResearch.WordTrace]
  refine ⟨39801594972547884134265313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53068793296730512179020417 39801594972547884134265313)
  ·
    refine ⟨29851196229410913100698985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39801594972547884134265313 29851196229410913100698985)
    ·
      refine ⟨22388397172058184825524239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29851196229410913100698985 22388397172058184825524239)
      ·
        refine ⟨33582595758087277238286359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22388397172058184825524239 33582595758087277238286359)
        ·
          refine ⟨50373893637130915857429539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33582595758087277238286359 50373893637130915857429539)
          ·
            refine ⟨75560840455696373786144309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50373893637130915857429539 75560840455696373786144309)
            ·
              refine ⟨7083828792721535042451029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75560840455696373786144309 7083828792721535042451029)
              ·
                refine ⟨83013618664705488778723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7083828792721535042451029 83013618664705488778723)
                ·
                  rfl

theorem cell22_2182524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 8].length) (baseStart_2182524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182524 prefixEnd_2182524 := by exact prefixLift 2182524
  have htrace : WordTrace (prefixWord ++ tailWord_2182524) baseStart_2182524 baseEnd_2182524 := by
    simpa [prefixWord, tailWord_2182524, baseEnd_2182524] using wordTrace_append hprefix tailTrace_2182524
  have hstable : (prefixWord ++ tailWord_2182524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182524).length < 2 ^ (prefixWord ++ tailWord_2182524).sum := by decide
  have hdescent : baseEnd_2182524 < baseStart_2182524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182562 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2182562 : Nat := 118140960795 + 2182562 * 2 ^ 59
def prefixEnd_2182562 : Nat := 4983230072969 + 3 ^ 40 * 2182562 * 2
def baseEnd_2182562 : Nat := 747135576158929966558391

theorem tailTrace_2182562 : CollatzResearch.WordTrace tailWord_2182562 prefixEnd_2182562 747135576158929966558391 := by
  unfold tailWord_2182562
  simp only [CollatzResearch.WordTrace]
  refine ⟨19901143979739525189603485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53069717279305400505609293 19901143979739525189603485)
  ·
    refine ⟨7462928992402321946101307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19901143979739525189603485 7462928992402321946101307)
    ·
      refine ⟨11194393488603482919151961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7462928992402321946101307 11194393488603482919151961)
      ·
        refine ⟨8395795116452612189363971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11194393488603482919151961 8395795116452612189363971)
        ·
          refine ⟨12593692674678918284045957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8395795116452612189363971 12593692674678918284045957)
          ·
            refine ⟨2361317376502297178258617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12593692674678918284045957 2361317376502297178258617)
            ·
              refine ⟨1770988032376722883693963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2361317376502297178258617 1770988032376722883693963)
              ·
                refine ⟨2656482048565084325540945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770988032376722883693963 2656482048565084325540945)
                ·
                  refine ⟨1992361536423813244155709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2656482048565084325540945 1992361536423813244155709)
                  ·
                    refine ⟨747135576158929966558391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1992361536423813244155709 747135576158929966558391)
                    ·
                      rfl

theorem cell22_2182562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2182562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182562 prefixEnd_2182562 := by exact prefixLift 2182562
  have htrace : WordTrace (prefixWord ++ tailWord_2182562) baseStart_2182562 baseEnd_2182562 := by
    simpa [prefixWord, tailWord_2182562, baseEnd_2182562] using wordTrace_append hprefix tailTrace_2182562
  have hstable : (prefixWord ++ tailWord_2182562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182562).length < 2 ^ (prefixWord ++ tailWord_2182562).sum := by decide
  have hdescent : baseEnd_2182562 < baseStart_2182562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182590 : List Nat := [4, 2, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_2182590 : Nat := 118140960795 + 2182590 * 2 ^ 59
def prefixEnd_2182590 : Nat := 4983230072969 + 3 ^ 40 * 2182590 * 2
def baseEnd_2182590 : Nat := 747145161131147226858305

theorem tailTrace_2182590 : CollatzResearch.WordTrace tailWord_2182590 prefixEnd_2182590 747145161131147226858305 := by
  unfold tailWord_2182590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9950699645357082692554153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53070398108571107693622149 9950699645357082692554153)
  ·
    refine ⟨7463024734017812019415615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9950699645357082692554153 7463024734017812019415615)
    ·
      refine ⟨11194537101026718029123423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7463024734017812019415615 11194537101026718029123423)
      ·
        refine ⟨16791805651540077043685135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11194537101026718029123423 16791805651540077043685135)
        ·
          refine ⟨25187708477310115565527703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16791805651540077043685135 25187708477310115565527703)
          ·
            refine ⟨37781562715965173348291555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25187708477310115565527703 37781562715965173348291555)
            ·
              refine ⟨56672344073947760022437333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37781562715965173348291555 56672344073947760022437333)
              ·
                refine ⟨1328258064233150625525875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56672344073947760022437333 1328258064233150625525875)
                ·
                  refine ⟨1992387096349725938288813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328258064233150625525875 1992387096349725938288813)
                  ·
                    refine ⟨747145161131147226858305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1992387096349725938288813 747145161131147226858305)
                    ·
                      rfl

theorem cell22_2182590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_2182590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182590 prefixEnd_2182590 := by exact prefixLift 2182590
  have htrace : WordTrace (prefixWord ++ tailWord_2182590) baseStart_2182590 baseEnd_2182590 := by
    simpa [prefixWord, tailWord_2182590, baseEnd_2182590] using wordTrace_append hprefix tailTrace_2182590
  have hstable : (prefixWord ++ tailWord_2182590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182590).length < 2 ^ (prefixWord ++ tailWord_2182590).sum := by decide
  have hdescent : baseEnd_2182590 < baseStart_2182590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182616 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_2182616 : Nat := 118140960795 + 2182616 * 2 ^ 59
def prefixEnd_2182616 : Nat := 4983230072969 + 3 ^ 40 * 2182616 * 2
def baseEnd_2182616 : Nat := 747154061462491825708225

theorem tailTrace_2182616 : CollatzResearch.WordTrace tailWord_2182616 prefixEnd_2182616 747154061462491825708225 := by
  unfold tailWord_2182616
  simp only [CollatzResearch.WordTrace]
  refine ⟨39803272730381233990439851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53071030307174978653919801 39803272730381233990439851)
  ·
    refine ⟨59704909095571850985659777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39803272730381233990439851 59704909095571850985659777)
    ·
      refine ⟨44778681821678888239244833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59704909095571850985659777 44778681821678888239244833)
      ·
        refine ⟨33584011366259166179433625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44778681821678888239244833 33584011366259166179433625)
        ·
          refine ⟨25188008524694374634575219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33584011366259166179433625 25188008524694374634575219)
          ·
            refine ⟨37782012787041561951862829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25188008524694374634575219 37782012787041561951862829)
            ·
              refine ⟨14168254795140585731948561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37782012787041561951862829 14168254795140585731948561)
              ·
                refine ⟨10626191096355439298961421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14168254795140585731948561 10626191096355439298961421)
                ·
                  refine ⟨3984821661133289737110533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10626191096355439298961421 3984821661133289737110533)
                  ·
                    refine ⟨747154061462491825708225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984821661133289737110533 747154061462491825708225)
                    ·
                      rfl

theorem cell22_2182616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_2182616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182616 prefixEnd_2182616 := by exact prefixLift 2182616
  have htrace : WordTrace (prefixWord ++ tailWord_2182616) baseStart_2182616 baseEnd_2182616 := by
    simpa [prefixWord, tailWord_2182616, baseEnd_2182616] using wordTrace_append hprefix tailTrace_2182616
  have hstable : (prefixWord ++ tailWord_2182616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182616).length < 2 ^ (prefixWord ++ tailWord_2182616).sum := by decide
  have hdescent : baseEnd_2182616 < baseStart_2182616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182631 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 8]
def baseStart_2182631 : Nat := 118140960795 + 2182631 * 2 ^ 59
def prefixEnd_2182631 : Nat := 4983230072969 + 3 ^ 40 * 2182631 * 2
def baseEnd_2182631 : Nat := 249053065423012262194393

theorem tailTrace_2182631 : CollatzResearch.WordTrace tailWord_2182631 prefixEnd_2182631 249053065423012262194393 := by
  unfold tailWord_2182631
  simp only [CollatzResearch.WordTrace]
  refine ⟨79607092555708125542675747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53071395037138750361783831 79607092555708125542675747)
  ·
    refine ⟨119410638833562188314013621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79607092555708125542675747 119410638833562188314013621)
    ·
      refine ⟨11194747390646455154438777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119410638833562188314013621 11194747390646455154438777)
      ·
        refine ⟨8396060542984841365829083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11194747390646455154438777 8396060542984841365829083)
        ·
          refine ⟨12594090814477262048743625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8396060542984841365829083 12594090814477262048743625)
          ·
            refine ⟨9445568110857946536557719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12594090814477262048743625 9445568110857946536557719)
            ·
              refine ⟨14168352166286919804836579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9445568110857946536557719 14168352166286919804836579)
              ·
                refine ⟨21252528249430379707254869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14168352166286919804836579 21252528249430379707254869)
                ·
                  refine ⟨249053065423012262194393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21252528249430379707254869 249053065423012262194393)
                  ·
                    rfl

theorem cell22_2182631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 8].length) (baseStart_2182631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182631 prefixEnd_2182631 := by exact prefixLift 2182631
  have htrace : WordTrace (prefixWord ++ tailWord_2182631) baseStart_2182631 baseEnd_2182631 := by
    simpa [prefixWord, tailWord_2182631, baseEnd_2182631] using wordTrace_append hprefix tailTrace_2182631
  have hstable : (prefixWord ++ tailWord_2182631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182631).length < 2 ^ (prefixWord ++ tailWord_2182631).sum := by decide
  have hdescent : baseEnd_2182631 < baseStart_2182631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182648 : List Nat := [2, 1, 2, 1, 1, 5, 1, 5, 4]
def baseStart_2182648 : Nat := 118140960795 + 2182648 * 2 ^ 59
def prefixEnd_2182648 : Nat := 4983230072969 + 3 ^ 40 * 2182648 * 2
def baseEnd_2182648 : Nat := 249055005238818136302709

theorem tailTrace_2182648 : CollatzResearch.WordTrace tailWord_2182648 prefixEnd_2182648 249055005238818136302709 := by
  unfold tailWord_2182648
  simp only [CollatzResearch.WordTrace]
  refine ⟨39803856298323268723022299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53071808397764358297363065 39803856298323268723022299)
  ·
    refine ⟨59705784447484903084533449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39803856298323268723022299 59705784447484903084533449)
    ·
      refine ⟨44779338335613677313400087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59705784447484903084533449 44779338335613677313400087)
      ·
        refine ⟨67169007503420515970100131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44779338335613677313400087 67169007503420515970100131)
        ·
          refine ⟨100753511255130773955150197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67169007503420515970100131 100753511255130773955150197)
          ·
            refine ⟨9445641680168510058295331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100753511255130773955150197 9445641680168510058295331)
            ·
              refine ⟨14168462520252765087442997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9445641680168510058295331 14168462520252765087442997)
              ·
                refine ⟨1328293361273696726947781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14168462520252765087442997 1328293361273696726947781)
                ·
                  refine ⟨249055005238818136302709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328293361273696726947781 249055005238818136302709)
                  ·
                    rfl

theorem cell22_2182648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 4].length) (baseStart_2182648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182648 prefixEnd_2182648 := by exact prefixLift 2182648
  have htrace : WordTrace (prefixWord ++ tailWord_2182648) baseStart_2182648 baseEnd_2182648 := by
    simpa [prefixWord, tailWord_2182648, baseEnd_2182648] using wordTrace_append hprefix tailTrace_2182648
  have hstable : (prefixWord ++ tailWord_2182648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182648).length < 2 ^ (prefixWord ++ tailWord_2182648).sum := by decide
  have hdescent : baseEnd_2182648 < baseStart_2182648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182654 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_2182654 : Nat := 118140960795 + 2182654 * 2 ^ 59
def prefixEnd_2182654 : Nat := 4983230072969 + 3 ^ 40 * 2182654 * 2
def baseEnd_2182654 : Nat := 249055689879690797752703

theorem tailTrace_2182654 : CollatzResearch.WordTrace tailWord_2182654 prefixEnd_2182654 249055689879690797752703 := by
  unfold tailWord_2182654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9950991429328100058845377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53071954289749866980508677 9950991429328100058845377)
  ·
    refine ⟨7463243571996075044134033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9950991429328100058845377 7463243571996075044134033)
    ·
      refine ⟨5597432678997056283100525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7463243571996075044134033 5597432678997056283100525)
      ·
        refine ⟨2099037254623896106162697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5597432678997056283100525 2099037254623896106162697)
        ·
          refine ⟨1574277940967922079622023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2099037254623896106162697 1574277940967922079622023)
          ·
            refine ⟨2361416911451883119433035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574277940967922079622023 2361416911451883119433035)
            ·
              refine ⟨3542125367177824679149553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361416911451883119433035 3542125367177824679149553)
              ·
                refine ⟨2656594025383368509362165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3542125367177824679149553 2656594025383368509362165)
                ·
                  refine ⟨249055689879690797752703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2656594025383368509362165 249055689879690797752703)
                  ·
                    rfl

theorem cell22_2182654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_2182654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182654 prefixEnd_2182654 := by exact prefixLift 2182654
  have htrace : WordTrace (prefixWord ++ tailWord_2182654) baseStart_2182654 baseEnd_2182654 := by
    simpa [prefixWord, tailWord_2182654, baseEnd_2182654] using wordTrace_append hprefix tailTrace_2182654
  have hstable : (prefixWord ++ tailWord_2182654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182654).length < 2 ^ (prefixWord ++ tailWord_2182654).sum := by decide
  have hdescent : baseEnd_2182654 < baseStart_2182654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182661 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_2182661 : Nat := 118140960795 + 2182661 * 2 ^ 59
def prefixEnd_2182661 : Nat := 4983230072969 + 3 ^ 40 * 2182661 * 2
def baseEnd_2182661 : Nat := 747169465882126708333087

theorem tailTrace_2182661 : CollatzResearch.WordTrace tailWord_2182661 prefixEnd_2182661 747169465882126708333087 := by
  unfold tailWord_2182661
  simp only [CollatzResearch.WordTrace]
  refine ⟨79608186745599440666267837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53072124497066293777511891 79608186745599440666267837)
  ·
    refine ⟨29853070029599790249850439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79608186745599440666267837 29853070029599790249850439)
    ·
      refine ⟨44779605044399685374775659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29853070029599790249850439 44779605044399685374775659)
      ·
        refine ⟨67169407566599528062163489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44779605044399685374775659 67169407566599528062163489)
        ·
          refine ⟨50377055674949646046622617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67169407566599528062163489 50377055674949646046622617)
          ·
            refine ⟨37782791756212234534966963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50377055674949646046622617 37782791756212234534966963)
            ·
              refine ⟨56674187634318351802450445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37782791756212234534966963 56674187634318351802450445)
              ·
                refine ⟨21252820362869381925918917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56674187634318351802450445 21252820362869381925918917)
                ·
                  refine ⟨3984903818038009111109797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21252820362869381925918917 3984903818038009111109797)
                  ·
                    refine ⟨747169465882126708333087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3984903818038009111109797 747169465882126708333087)
                    ·
                      rfl

theorem cell22_2182661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_2182661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182661 prefixEnd_2182661 := by exact prefixLift 2182661
  have htrace : WordTrace (prefixWord ++ tailWord_2182661) baseStart_2182661 baseEnd_2182661 := by
    simpa [prefixWord, tailWord_2182661, baseEnd_2182661] using wordTrace_append hprefix tailTrace_2182661
  have hstable : (prefixWord ++ tailWord_2182661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182661).length < 2 ^ (prefixWord ++ tailWord_2182661).sum := by decide
  have hdescent : baseEnd_2182661 < baseStart_2182661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182680 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 1, 5]
def baseStart_2182680 : Nat := 118140960795 + 2182680 * 2 ^ 59
def prefixEnd_2182680 : Nat := 4983230072969 + 3 ^ 40 * 2182680 * 2
def baseEnd_2182680 : Nat := 747175969970416992108029

theorem tailTrace_2182680 : CollatzResearch.WordTrace tailWord_2182680 prefixEnd_2182680 747175969970416992108029 := by
  unfold tailWord_2182680
  simp only [CollatzResearch.WordTrace]
  refine ⟨39804439866265303455604747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53072586488353737940806329 39804439866265303455604747)
  ·
    refine ⟨59706659799397955183407121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39804439866265303455604747 59706659799397955183407121)
    ·
      refine ⟨44779994849548466387555341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59706659799397955183407121 44779994849548466387555341)
      ·
        refine ⟨16792498068580674895333253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44779994849548466387555341 16792498068580674895333253)
        ·
          refine ⟨3148593387858876542874985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16792498068580674895333253 3148593387858876542874985)
          ·
            refine ⟨2361445040894157407156239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3148593387858876542874985 2361445040894157407156239)
            ·
              refine ⟨3542167561341236110734359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361445040894157407156239 3542167561341236110734359)
              ·
                refine ⟨5313251342011854166101539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542167561341236110734359 5313251342011854166101539)
                ·
                  refine ⟨7969877013017781249152309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5313251342011854166101539 7969877013017781249152309)
                  ·
                    refine ⟨747175969970416992108029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7969877013017781249152309 747175969970416992108029)
                    ·
                      rfl

theorem cell22_2182680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_2182680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182680 prefixEnd_2182680 := by exact prefixLift 2182680
  have htrace : WordTrace (prefixWord ++ tailWord_2182680) baseStart_2182680 baseEnd_2182680 := by
    simpa [prefixWord, tailWord_2182680, baseEnd_2182680] using wordTrace_append hprefix tailTrace_2182680
  have hstable : (prefixWord ++ tailWord_2182680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182680).length < 2 ^ (prefixWord ++ tailWord_2182680).sum := by decide
  have hdescent : baseEnd_2182680 < baseStart_2182680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182706 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_2182706 : Nat := 118140960795 + 2182706 * 2 ^ 59
def prefixEnd_2182706 : Nat := 4983230072969 + 3 ^ 40 * 2182706 * 2
def baseEnd_2182706 : Nat := 747184870301761590957949

theorem tailTrace_2182706 : CollatzResearch.WordTrace tailWord_2182706 prefixEnd_2182706 747184870301761590957949 := by
  unfold tailWord_2182706
  simp only [CollatzResearch.WordTrace]
  refine ⟨19902457007609103337913993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53073218686957608901103981 19902457007609103337913993)
  ·
    refine ⟨14926842755706827503435495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19902457007609103337913993 14926842755706827503435495)
    ·
      refine ⟨22390264133560241255153243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14926842755706827503435495 22390264133560241255153243)
      ·
        refine ⟨33585396200340361882729865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22390264133560241255153243 33585396200340361882729865)
        ·
          refine ⟨25189047150255271412047399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33585396200340361882729865 25189047150255271412047399)
          ·
            refine ⟨37783570725382907118071099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25189047150255271412047399 37783570725382907118071099)
            ·
              refine ⟨56675356088074360677106649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37783570725382907118071099 56675356088074360677106649)
              ·
                refine ⟨42506517066055770507829987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56675356088074360677106649 42506517066055770507829987)
                ·
                  refine ⟨63759775599083655761744981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42506517066055770507829987 63759775599083655761744981)
                  ·
                    refine ⟨747184870301761590957949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63759775599083655761744981 747184870301761590957949)
                    ·
                      rfl

theorem cell22_2182706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_2182706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182706 prefixEnd_2182706 := by exact prefixLift 2182706
  have htrace : WordTrace (prefixWord ++ tailWord_2182706) baseStart_2182706 baseEnd_2182706 := by
    simpa [prefixWord, tailWord_2182706, baseEnd_2182706] using wordTrace_append hprefix tailTrace_2182706
  have hstable : (prefixWord ++ tailWord_2182706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182706).length < 2 ^ (prefixWord ++ tailWord_2182706).sum := by decide
  have hdescent : baseEnd_2182706 < baseStart_2182706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182710 : List Nat := [5, 1, 2, 1, 3, 2, 8]
def baseStart_2182710 : Nat := 118140960795 + 2182710 * 2 ^ 59
def prefixEnd_2182710 : Nat := 4983230072969 + 3 ^ 40 * 2182710 * 2
def baseEnd_2182710 : Nat := 27673564429018774587331

theorem tailTrace_2182710 : CollatzResearch.WordTrace tailWord_2182710 prefixEnd_2182710 27673564429018774587331 := by
  unfold tailWord_2182710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975623370151370127175099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53073315948281281356534389 4975623370151370127175099)
  ·
    refine ⟨7463435055227055190762649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4975623370151370127175099 7463435055227055190762649)
    ·
      refine ⟨5597576291420291393071987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7463435055227055190762649 5597576291420291393071987)
      ·
        refine ⟨8396364437130437089607981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5597576291420291393071987 8396364437130437089607981)
        ·
          refine ⟨3148636663923913908602993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8396364437130437089607981 3148636663923913908602993)
          ·
            refine ⟨2361477497942935431452245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3148636663923913908602993 2361477497942935431452245)
            ·
              refine ⟨27673564429018774587331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2361477497942935431452245 27673564429018774587331)
              ·
                rfl

theorem cell22_2182710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 8].length) (baseStart_2182710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182710 prefixEnd_2182710 := by exact prefixLift 2182710
  have htrace : WordTrace (prefixWord ++ tailWord_2182710) baseStart_2182710 baseEnd_2182710 := by
    simpa [prefixWord, tailWord_2182710, baseEnd_2182710] using wordTrace_append hprefix tailTrace_2182710
  have hstable : (prefixWord ++ tailWord_2182710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182710).length < 2 ^ (prefixWord ++ tailWord_2182710).sum := by decide
  have hdescent : baseEnd_2182710 < baseStart_2182710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182736 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_2182736 : Nat := 118140960795 + 2182736 * 2 ^ 59
def prefixEnd_2182736 : Nat := 4983230072969 + 3 ^ 40 * 2182736 * 2
def baseEnd_2182736 : Nat := 747195139914851512707857

theorem tailTrace_2182736 : CollatzResearch.WordTrace tailWord_2182736 prefixEnd_2182736 747195139914851512707857 := by
  unfold tailWord_2182736
  simp only [CollatzResearch.WordTrace]
  refine ⟨39805461110163864237624031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53073948146885152316832041 39805461110163864237624031)
  ·
    refine ⟨59708191665245796356436047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39805461110163864237624031 59708191665245796356436047)
    ·
      refine ⟨89562287497868694534654071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59708191665245796356436047 89562287497868694534654071)
      ·
        refine ⟨134343431246803041801981107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89562287497868694534654071 134343431246803041801981107)
        ·
          refine ⟨201515146870204562702971661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134343431246803041801981107 201515146870204562702971661)
          ·
            refine ⟨75568180076326711013614373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201515146870204562702971661 75568180076326711013614373)
            ·
              refine ⟨14169033764311258315052695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75568180076326711013614373 14169033764311258315052695)
              ·
                refine ⟨21253550646466887472579043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14169033764311258315052695 21253550646466887472579043)
                ·
                  refine ⟨31880325969700331208868565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21253550646466887472579043 31880325969700331208868565)
                  ·
                    refine ⟨747195139914851512707857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31880325969700331208868565 747195139914851512707857)
                    ·
                      rfl

theorem cell22_2182736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_2182736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182736 prefixEnd_2182736 := by exact prefixLift 2182736
  have htrace : WordTrace (prefixWord ++ tailWord_2182736) baseStart_2182736 baseEnd_2182736 := by
    simpa [prefixWord, tailWord_2182736, baseEnd_2182736] using wordTrace_append hprefix tailTrace_2182736
  have hstable : (prefixWord ++ tailWord_2182736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182736).length < 2 ^ (prefixWord ++ tailWord_2182736).sum := by decide
  have hdescent : baseEnd_2182736 < baseStart_2182736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182817 : List Nat := [1, 2, 3, 3, 2, 2, 2, 3, 4]
def baseStart_2182817 : Nat := 118140960795 + 2182817 * 2 ^ 59
def prefixEnd_2182817 : Nat := 4983230072969 + 3 ^ 40 * 2182817 * 2
def baseEnd_2182817 : Nat := 249074289290064767144203

theorem tailTrace_2182817 : CollatzResearch.WordTrace tailWord_2182817 prefixEnd_2182817 249074289290064767144203 := by
  unfold tailWord_2182817
  simp only [CollatzResearch.WordTrace]
  refine ⟨79613876533034279308946705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53075917688689519539297803 79613876533034279308946705)
  ·
    refine ⟨59710407399775709481710029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79613876533034279308946705 59710407399775709481710029)
    ·
      refine ⟨22391402774915891055641261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59710407399775709481710029 22391402774915891055641261)
      ·
        refine ⟨8396776040593459145865473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22391402774915891055641261 8396776040593459145865473)
        ·
          refine ⟨6297582030445094359399105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8396776040593459145865473 6297582030445094359399105)
          ·
            refine ⟨4723186522833820769549329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6297582030445094359399105 4723186522833820769549329)
            ·
              refine ⟨3542389892125365577161997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4723186522833820769549329 3542389892125365577161997)
              ·
                refine ⟨1328396209547012091435749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3542389892125365577161997 1328396209547012091435749)
                ·
                  refine ⟨249074289290064767144203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328396209547012091435749 249074289290064767144203)
                  ·
                    rfl

theorem cell22_2182817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 4].length) (baseStart_2182817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182817 prefixEnd_2182817 := by exact prefixLift 2182817
  have htrace : WordTrace (prefixWord ++ tailWord_2182817) baseStart_2182817 baseEnd_2182817 := by
    simpa [prefixWord, tailWord_2182817, baseEnd_2182817] using wordTrace_append hprefix tailTrace_2182817
  have hstable : (prefixWord ++ tailWord_2182817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182817).length < 2 ^ (prefixWord ++ tailWord_2182817).sum := by decide
  have hdescent : baseEnd_2182817 < baseStart_2182817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182873 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 7]
def baseStart_2182873 : Nat := 118140960795 + 2182873 * 2 ^ 59
def prefixEnd_2182873 : Nat := 4983230072969 + 3 ^ 40 * 2182873 * 2
def baseEnd_2182873 : Nat := 249080679271542940677479

theorem tailTrace_2182873 : CollatzResearch.WordTrace tailWord_2182873 prefixEnd_2182873 249080679271542940677479 := by
  unfold tailWord_2182873
  simp only [CollatzResearch.WordTrace]
  refine ⟨79615919020831400872985273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53077279347220933915323515 79615919020831400872985273)
  ·
    refine ⟨59711939265623550654738955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79615919020831400872985273 59711939265623550654738955)
    ·
      refine ⟨89567908898435325982108433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59711939265623550654738955 89567908898435325982108433)
      ·
        refine ⟨67175931673826494486581325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89567908898435325982108433 67175931673826494486581325)
        ·
          refine ⟨25190974377684935432467997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67175931673826494486581325 25190974377684935432467997)
          ·
            refine ⟨9446615391631850787175499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25190974377684935432467997 9446615391631850787175499)
            ·
              refine ⟨14169923087447776180763249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9446615391631850787175499 14169923087447776180763249)
              ·
                refine ⟨10627442315585832135572437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14169923087447776180763249 10627442315585832135572437)
                ·
                  refine ⟨249080679271542940677479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10627442315585832135572437 249080679271542940677479)
                  ·
                    rfl

theorem cell22_2182873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_2182873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182873 prefixEnd_2182873 := by exact prefixLift 2182873
  have htrace : WordTrace (prefixWord ++ tailWord_2182873) baseStart_2182873 baseEnd_2182873 := by
    simpa [prefixWord, tailWord_2182873, baseEnd_2182873] using wordTrace_append hprefix tailTrace_2182873
  have hstable : (prefixWord ++ tailWord_2182873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182873).length < 2 ^ (prefixWord ++ tailWord_2182873).sum := by decide
  have hdescent : baseEnd_2182873 < baseStart_2182873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182920 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_2182920 : Nat := 118140960795 + 2182920 * 2 ^ 59
def prefixEnd_2182920 : Nat := 4983230072969 + 3 ^ 40 * 2182920 * 2
def baseEnd_2182920 : Nat := 747258126875136366107293

theorem tailTrace_2182920 : CollatzResearch.WordTrace tailWord_2182920 prefixEnd_2182920 747258126875136366107293 := by
  unfold tailWord_2182920
  simp only [CollatzResearch.WordTrace]
  refine ⟨39808816625830563949973107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53078422167774085266630809 39808816625830563949973107)
  ·
    refine ⟨59713224938745845924959661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39808816625830563949973107 59713224938745845924959661)
    ·
      refine ⟨22392459352029692221859873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59713224938745845924959661 22392459352029692221859873)
      ·
        refine ⟨16794344514022269166394905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22392459352029692221859873 16794344514022269166394905)
        ·
          refine ⟨12595758385516701874796179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16794344514022269166394905 12595758385516701874796179)
          ·
            refine ⟨18893637578275052812194269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12595758385516701874796179 18893637578275052812194269)
            ·
              refine ⟨7085114091853144804572851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18893637578275052812194269 7085114091853144804572851)
              ·
                refine ⟨10627671137779717206859277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7085114091853144804572851 10627671137779717206859277)
                ·
                  refine ⟨3985376676667393952572229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10627671137779717206859277 3985376676667393952572229)
                  ·
                    refine ⟨747258126875136366107293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3985376676667393952572229 747258126875136366107293)
                    ·
                      rfl

theorem cell22_2182920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_2182920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2182920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2182920 prefixEnd_2182920 := by exact prefixLift 2182920
  have htrace : WordTrace (prefixWord ++ tailWord_2182920) baseStart_2182920 baseEnd_2182920 := by
    simpa [prefixWord, tailWord_2182920, baseEnd_2182920] using wordTrace_append hprefix tailTrace_2182920
  have hstable : (prefixWord ++ tailWord_2182920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182920).length < 2 ^ (prefixWord ++ tailWord_2182920).sum := by decide
  have hdescent : baseEnd_2182920 < baseStart_2182920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183018 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_2183018 : Nat := 118140960795 + 2183018 * 2 ^ 59
def prefixEnd_2183018 : Nat := 4983230072969 + 3 ^ 40 * 2183018 * 2
def baseEnd_2183018 : Nat := 747291674277896777156993

theorem tailTrace_2183018 : CollatzResearch.WordTrace tailWord_2183018 prefixEnd_2183018 747291674277896777156993 := by
  unfold tailWord_2183018
  simp only [CollatzResearch.WordTrace]
  refine ⟨19905301901326522659253427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53080805070204060424675805 19905301901326522659253427)
  ·
    refine ⟨29857952851989783988880141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19905301901326522659253427 29857952851989783988880141)
    ·
      refine ⟨11196732319496168995830053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29857952851989783988880141 11196732319496168995830053)
      ·
        refine ⟨2099387309905531686718135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11196732319496168995830053 2099387309905531686718135)
        ·
          refine ⟨3149080964858297530077203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099387309905531686718135 3149080964858297530077203)
          ·
            refine ⟨4723621447287446295115805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149080964858297530077203 4723621447287446295115805)
            ·
              refine ⟨1771358042732792360668427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4723621447287446295115805 1771358042732792360668427)
              ·
                refine ⟨2657037064099188541002641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771358042732792360668427 2657037064099188541002641)
                ·
                  refine ⟨1992777798074391405751981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2657037064099188541002641 1992777798074391405751981)
                  ·
                    refine ⟨747291674277896777156993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1992777798074391405751981 747291674277896777156993)
                    ·
                      rfl

theorem cell22_2183018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_2183018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183018 prefixEnd_2183018 := by exact prefixLift 2183018
  have htrace : WordTrace (prefixWord ++ tailWord_2183018) baseStart_2183018 baseEnd_2183018 := by
    simpa [prefixWord, tailWord_2183018, baseEnd_2183018] using wordTrace_append hprefix tailTrace_2183018
  have hstable : (prefixWord ++ tailWord_2183018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183018).length < 2 ^ (prefixWord ++ tailWord_2183018).sum := by decide
  have hdescent : baseEnd_2183018 < baseStart_2183018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183089 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_2183089 : Nat := 118140960795 + 2183089 * 2 ^ 59
def prefixEnd_2183089 : Nat := 4983230072969 + 3 ^ 40 * 2183089 * 2
def baseEnd_2183089 : Nat := 747315979028876258631775

theorem tailTrace_2183089 : CollatzResearch.WordTrace tailWord_2183089 prefixEnd_2183089 747315979028876258631775 := by
  unfold tailWord_2183089
  simp only [CollatzResearch.WordTrace]
  refine ⟨79623797188048869762848321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53082531458699246508565547 79623797188048869762848321)
  ·
    refine ⟨59717847891036652322136241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79623797188048869762848321 59717847891036652322136241)
    ·
      refine ⟨44788385918277489241602181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59717847891036652322136241 44788385918277489241602181)
      ·
        refine ⟨8397822359677029232800409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44788385918277489241602181 8397822359677029232800409)
        ·
          refine ⟨6298366769757771924600307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8397822359677029232800409 6298366769757771924600307)
          ·
            refine ⟨9447550154636657886900461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6298366769757771924600307 9447550154636657886900461)
            ·
              refine ⟨3542831307988746707587673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9447550154636657886900461 3542831307988746707587673)
              ·
                refine ⟨2657123480991560030690755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3542831307988746707587673 2657123480991560030690755)
                ·
                  refine ⟨3985685221487340046036133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657123480991560030690755 3985685221487340046036133)
                  ·
                    refine ⟨747315979028876258631775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3985685221487340046036133 747315979028876258631775)
                    ·
                      rfl

theorem cell22_2183089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_2183089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183089 prefixEnd_2183089 := by exact prefixLift 2183089
  have htrace : WordTrace (prefixWord ++ tailWord_2183089) baseStart_2183089 baseEnd_2183089 := by
    simpa [prefixWord, tailWord_2183089, baseEnd_2183089] using wordTrace_append hprefix tailTrace_2183089
  have hstable : (prefixWord ++ tailWord_2183089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183089).length < 2 ^ (prefixWord ++ tailWord_2183089).sum := by decide
  have hdescent : baseEnd_2183089 < baseStart_2183089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183102 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2183102 : Nat := 118140960795 + 2183102 * 2 ^ 59
def prefixEnd_2183102 : Nat := 4983230072969 + 3 ^ 40 * 2183102 * 2
def baseEnd_2183102 : Nat := 747320429194548558056735

theorem tailTrace_2183102 : CollatzResearch.WordTrace tailWord_2183102 prefixEnd_2183102 747320429194548558056735 := by
  unfold tailWord_2183102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953033917125221622883945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53082847558001181988714373 9953033917125221622883945)
  ·
    refine ⟨7464775437843916217162959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9953033917125221622883945 7464775437843916217162959)
    ·
      refine ⟨11197163156765874325744439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7464775437843916217162959 11197163156765874325744439)
      ·
        refine ⟨16795744735148811488616659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11197163156765874325744439 16795744735148811488616659)
        ·
          refine ⟨25193617102723217232924989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16795744735148811488616659 25193617102723217232924989)
          ·
            refine ⟨9447606413521206462346871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25193617102723217232924989 9447606413521206462346871)
            ·
              refine ⟨14171409620281809693520307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9447606413521206462346871 14171409620281809693520307)
              ·
                refine ⟨21257114430422714540280461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14171409620281809693520307 21257114430422714540280461)
                ·
                  refine ⟨7971417911408517952605173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21257114430422714540280461 7971417911408517952605173)
                  ·
                    refine ⟨747320429194548558056735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7971417911408517952605173 747320429194548558056735)
                    ·
                      rfl

theorem cell22_2183102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2183102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183102 prefixEnd_2183102 := by exact prefixLift 2183102
  have htrace : WordTrace (prefixWord ++ tailWord_2183102) baseStart_2183102 baseEnd_2183102 := by
    simpa [prefixWord, tailWord_2183102, baseEnd_2183102] using wordTrace_append hprefix tailTrace_2183102
  have hstable : (prefixWord ++ tailWord_2183102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183102).length < 2 ^ (prefixWord ++ tailWord_2183102).sum := by decide
  have hdescent : baseEnd_2183102 < baseStart_2183102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183119 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 2, 3]
def baseStart_2183119 : Nat := 118140960795 + 2183119 * 2 ^ 59
def prefixEnd_2183119 : Nat := 4983230072969 + 3 ^ 40 * 2183119 * 2
def baseEnd_2183119 : Nat := 747326248641966180381683

theorem tailTrace_2183119 : CollatzResearch.WordTrace tailWord_2183119 prefixEnd_2183119 747326248641966180381683 := by
  unfold tailWord_2183119
  simp only [CollatzResearch.WordTrace]
  refine ⟨79624891377940184886440411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53083260918626789924293607 79624891377940184886440411)
  ·
    refine ⟨119437337066910277329660617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79624891377940184886440411 119437337066910277329660617)
    ·
      refine ⟨89578002800182707997245463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119437337066910277329660617 89578002800182707997245463)
      ·
        refine ⟨134367004200274061995868195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89578002800182707997245463 134367004200274061995868195)
        ·
          refine ⟨201550506300411092993802293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134367004200274061995868195 201550506300411092993802293)
          ·
            refine ⟨18895359965663539968168965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201550506300411092993802293 18895359965663539968168965)
            ·
              refine ⟨3542879993561913744031681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18895359965663539968168965 3542879993561913744031681)
              ·
                refine ⟨2657159995171435308023761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3542879993561913744031681 2657159995171435308023761)
                ·
                  refine ⟨1992869996378576481017821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2657159995171435308023761 1992869996378576481017821)
                  ·
                    refine ⟨747326248641966180381683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1992869996378576481017821 747326248641966180381683)
                    ·
                      rfl

theorem cell22_2183119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_2183119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183119 prefixEnd_2183119 := by exact prefixLift 2183119
  have htrace : WordTrace (prefixWord ++ tailWord_2183119) baseStart_2183119 baseEnd_2183119 := by
    simpa [prefixWord, tailWord_2183119, baseEnd_2183119] using wordTrace_append hprefix tailTrace_2183119
  have hstable : (prefixWord ++ tailWord_2183119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183119).length < 2 ^ (prefixWord ++ tailWord_2183119).sum := by decide
  have hdescent : baseEnd_2183119 < baseStart_2183119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183192 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_2183192 : Nat := 118140960795 + 2183192 * 2 ^ 59
def prefixEnd_2183192 : Nat := 4983230072969 + 3 ^ 40 * 2183192 * 2
def baseEnd_2183192 : Nat := 747351238033818323306459

theorem tailTrace_2183192 : CollatzResearch.WordTrace tailWord_2183192 prefixEnd_2183192 747351238033818323306459 := by
  unfold tailWord_2183192
  simp only [CollatzResearch.WordTrace]
  refine ⟨39813776953337859176923915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53085035937783812235898553 39813776953337859176923915)
  ·
    refine ⟨59720665430006788765385873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39813776953337859176923915 59720665430006788765385873)
    ·
      refine ⟨44790499072505091574039405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59720665430006788765385873 44790499072505091574039405)
      ·
        refine ⟨16796437152189409340264777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44790499072505091574039405 16796437152189409340264777)
        ·
          refine ⟨12597327864142057005198583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16796437152189409340264777 12597327864142057005198583)
          ·
            refine ⟨18895991796213085507797875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12597327864142057005198583 18895991796213085507797875)
            ·
              refine ⟨28343987694319628261696813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18895991796213085507797875 28343987694319628261696813)
              ·
                refine ⟨10628995385369860598136305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28343987694319628261696813 10628995385369860598136305)
                ·
                  refine ⟨7971746539027395448602229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10628995385369860598136305 7971746539027395448602229)
                  ·
                    refine ⟨747351238033818323306459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7971746539027395448602229 747351238033818323306459)
                    ·
                      rfl

theorem cell22_2183192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_2183192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183192 prefixEnd_2183192 := by exact prefixLift 2183192
  have htrace : WordTrace (prefixWord ++ tailWord_2183192) baseStart_2183192 baseEnd_2183192 := by
    simpa [prefixWord, tailWord_2183192, baseEnd_2183192] using wordTrace_append hprefix tailTrace_2183192
  have hstable : (prefixWord ++ tailWord_2183192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183192).length < 2 ^ (prefixWord ++ tailWord_2183192).sum := by decide
  have hdescent : baseEnd_2183192 < baseStart_2183192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183267 : List Nat := [1, 1, 1, 5, 1, 1, 4, 8]
def baseStart_2183267 : Nat := 118140960795 + 2183267 * 2 ^ 59
def prefixEnd_2183267 : Nat := 4983230072969 + 3 ^ 40 * 2183267 * 2
def baseEnd_2183267 : Nat := 83041879118504791964581

theorem tailTrace_2183267 : CollatzResearch.WordTrace tailWord_2183267 prefixEnd_2183267 83041879118504791964581 := by
  unfold tailWord_2183267
  simp only [CollatzResearch.WordTrace]
  refine ⟨79630289381404006162828055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53086859587602670775218703 79630289381404006162828055)
  ·
    refine ⟨119445434072106009244242083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79630289381404006162828055 119445434072106009244242083)
    ·
      refine ⟨179168151108159013866363125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119445434072106009244242083 179168151108159013866363125)
      ·
        refine ⟨16797014166389907549971543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179168151108159013866363125 16797014166389907549971543)
        ·
          refine ⟨25195521249584861324957315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16797014166389907549971543 25195521249584861324957315)
          ·
            refine ⟨37793281874377291987435973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25195521249584861324957315 37793281874377291987435973)
            ·
              refine ⟨7086240351445742247644245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37793281874377291987435973 7086240351445742247644245)
              ·
                refine ⟨83041879118504791964581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7086240351445742247644245 83041879118504791964581)
                ·
                  rfl

theorem cell22_2183267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 8].length) (baseStart_2183267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183267 prefixEnd_2183267 := by exact prefixLift 2183267
  have htrace : WordTrace (prefixWord ++ tailWord_2183267) baseStart_2183267 baseEnd_2183267 := by
    simpa [prefixWord, tailWord_2183267, baseEnd_2183267] using wordTrace_append hprefix tailTrace_2183267
  have hstable : (prefixWord ++ tailWord_2183267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183267).length < 2 ^ (prefixWord ++ tailWord_2183267).sum := by decide
  have hdescent : baseEnd_2183267 < baseStart_2183267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183269 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_2183269 : Nat := 118140960795 + 2183269 * 2 ^ 59
def prefixEnd_2183269 : Nat := 4983230072969 + 3 ^ 40 * 2183269 * 2
def baseEnd_2183269 : Nat := 747377596707415789131223

theorem tailTrace_2183269 : CollatzResearch.WordTrace tailWord_2183269 prefixEnd_2183269 747377596707415789131223 := by
  unfold tailWord_2183269
  simp only [CollatzResearch.WordTrace]
  refine ⟨79630362327396760504400861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53086908218264507002933907 79630362327396760504400861)
  ·
    refine ⟨29861385872773785189150323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79630362327396760504400861 29861385872773785189150323)
    ·
      refine ⟨44792078809160677783725485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29861385872773785189150323 44792078809160677783725485)
      ·
        refine ⟨16797029553435254168897057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44792078809160677783725485 16797029553435254168897057)
        ·
          refine ⟨12597772165076440626672793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16797029553435254168897057 12597772165076440626672793)
          ·
            refine ⟨9448329123807330470004595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12597772165076440626672793 9448329123807330470004595)
            ·
              refine ⟨14172493685710995705006893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9448329123807330470004595 14172493685710995705006893)
              ·
                refine ⟨5314685132141623389377585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14172493685710995705006893 5314685132141623389377585)
                ·
                  refine ⟨3986013849106217542033189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5314685132141623389377585 3986013849106217542033189)
                  ·
                    refine ⟨747377596707415789131223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3986013849106217542033189 747377596707415789131223)
                    ·
                      rfl

theorem cell22_2183269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_2183269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183269 prefixEnd_2183269 := by exact prefixLift 2183269
  have htrace : WordTrace (prefixWord ++ tailWord_2183269) baseStart_2183269 baseEnd_2183269 := by
    simpa [prefixWord, tailWord_2183269, baseEnd_2183269] using wordTrace_append hprefix tailTrace_2183269
  have hstable : (prefixWord ++ tailWord_2183269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183269).length < 2 ^ (prefixWord ++ tailWord_2183269).sum := by decide
  have hdescent : baseEnd_2183269 < baseStart_2183269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183286 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_2183286 : Nat := 118140960795 + 2183286 * 2 ^ 59
def prefixEnd_2183286 : Nat := 4983230072969 + 3 ^ 40 * 2183286 * 2
def baseEnd_2183286 : Nat := 747383416154833411456171

theorem tailTrace_2183286 : CollatzResearch.WordTrace tailWord_2183286 prefixEnd_2183286 747383416154833411456171 := by
  unfold tailWord_2183286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976936398020948275485607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53087321578890114938513141 4976936398020948275485607)
  ·
    refine ⟨7465404597031422413228411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4976936398020948275485607 7465404597031422413228411)
    ·
      refine ⟨11198106895547133619842617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7465404597031422413228411 11198106895547133619842617)
      ·
        refine ⟨8398580171660350214881963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11198106895547133619842617 8398580171660350214881963)
        ·
          refine ⟨12597870257490525322322945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8398580171660350214881963 12597870257490525322322945)
          ·
            refine ⟨9448402693117893991742209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12597870257490525322322945 9448402693117893991742209)
            ·
              refine ⟨7086302019838420493806657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9448402693117893991742209 7086302019838420493806657)
              ·
                refine ⟨5314726514878815370354993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7086302019838420493806657 5314726514878815370354993)
                ·
                  refine ⟨3986044886159111527766245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5314726514878815370354993 3986044886159111527766245)
                  ·
                    refine ⟨747383416154833411456171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3986044886159111527766245 747383416154833411456171)
                    ·
                      rfl

theorem cell22_2183286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_2183286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183286 prefixEnd_2183286 := by exact prefixLift 2183286
  have htrace : WordTrace (prefixWord ++ tailWord_2183286) baseStart_2183286 baseEnd_2183286 := by
    simpa [prefixWord, tailWord_2183286, baseEnd_2183286] using wordTrace_append hprefix tailTrace_2183286
  have hstable : (prefixWord ++ tailWord_2183286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183286).length < 2 ^ (prefixWord ++ tailWord_2183286).sum := by decide
  have hdescent : baseEnd_2183286 < baseStart_2183286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183314 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2183314 : Nat := 118140960795 + 2183314 * 2 ^ 59
def prefixEnd_2183314 : Nat := 4983230072969 + 3 ^ 40 * 2183314 * 2
def baseEnd_2183314 : Nat := 747393001127050671756085

theorem tailTrace_2183314 : CollatzResearch.WordTrace tailWord_2183314 prefixEnd_2183314 747393001127050671756085 := by
  unfold tailWord_2183314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19908000903058433297447249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53088002408155822126525997 19908000903058433297447249)
  ·
    refine ⟨14931000677293824973085437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19908000903058433297447249 14931000677293824973085437)
    ·
      refine ⟨5599125253985184364907039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14931000677293824973085437 5599125253985184364907039)
      ·
        refine ⟨8398687880977776547360559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5599125253985184364907039 8398687880977776547360559)
        ·
          refine ⟨12598031821466664821040839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8398687880977776547360559 12598031821466664821040839)
          ·
            refine ⟨18897047732199997231561259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12598031821466664821040839 18897047732199997231561259)
            ·
              refine ⟨28345571598299995847341889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18897047732199997231561259 28345571598299995847341889)
              ·
                refine ⟨21259178698724996885506417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28345571598299995847341889 21259178698724996885506417)
                ·
                  refine ⟨15944384024043747664129813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21259178698724996885506417 15944384024043747664129813)
                  ·
                    refine ⟨747393001127050671756085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15944384024043747664129813 747393001127050671756085)
                    ·
                      rfl

theorem cell22_2183314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2183314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183314 prefixEnd_2183314 := by exact prefixLift 2183314
  have htrace : WordTrace (prefixWord ++ tailWord_2183314) baseStart_2183314 baseEnd_2183314 := by
    simpa [prefixWord, tailWord_2183314, baseEnd_2183314] using wordTrace_append hprefix tailTrace_2183314
  have hstable : (prefixWord ++ tailWord_2183314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183314).length < 2 ^ (prefixWord ++ tailWord_2183314).sum := by decide
  have hdescent : baseEnd_2183314 < baseStart_2183314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183333 : List Nat := [1, 3, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_2183333 : Nat := 118140960795 + 2183333 * 2 ^ 59
def prefixEnd_2183333 : Nat := 4983230072969 + 3 ^ 40 * 2183333 * 2
def baseEnd_2183333 : Nat := 747399505215340955531027

theorem tailTrace_2183333 : CollatzResearch.WordTrace tailWord_2183333 prefixEnd_2183333 747399505215340955531027 := by
  unfold tailWord_2183333
  simp only [CollatzResearch.WordTrace]
  refine ⟨79632696599164899434730653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53088464399443266289820435 79632696599164899434730653)
  ·
    refine ⟨29862261224686837288023995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79632696599164899434730653 29862261224686837288023995)
    ·
      refine ⟨44793391837030255932035993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29862261224686837288023995 44793391837030255932035993)
      ·
        refine ⟨33595043877772691949026995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44793391837030255932035993 33595043877772691949026995)
        ·
          refine ⟨50392565816659037923540493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33595043877772691949026995 50392565816659037923540493)
          ·
            refine ⟨18897212181247139221327685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50392565816659037923540493 18897212181247139221327685)
            ·
              refine ⟨3543227283983838603998941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18897212181247139221327685 3543227283983838603998941)
              ·
                refine ⟨1328710231493939476499603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3543227283983838603998941 1328710231493939476499603)
                ·
                  refine ⟨1993065347240909214749405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328710231493939476499603 1993065347240909214749405)
                  ·
                    refine ⟨747399505215340955531027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993065347240909214749405 747399505215340955531027)
                    ·
                      rfl

theorem cell22_2183333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_2183333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183333 prefixEnd_2183333 := by exact prefixLift 2183333
  have htrace : WordTrace (prefixWord ++ tailWord_2183333) baseStart_2183333 baseEnd_2183333 := by
    simpa [prefixWord, tailWord_2183333, baseEnd_2183333] using wordTrace_append hprefix tailTrace_2183333
  have hstable : (prefixWord ++ tailWord_2183333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183333).length < 2 ^ (prefixWord ++ tailWord_2183333).sum := by decide
  have hdescent : baseEnd_2183333 < baseStart_2183333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183434 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_2183434 : Nat := 118140960795 + 2183434 * 2 ^ 59
def prefixEnd_2183434 : Nat := 4983230072969 + 3 ^ 40 * 2183434 * 2
def baseEnd_2183434 : Nat := 747434079579410358755717

theorem tailTrace_2183434 : CollatzResearch.WordTrace tailWord_2183434 prefixEnd_2183434 747434079579410358755717 := by
  unfold tailWord_2183434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19909095092949748421039339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53090920247865995789438237 19909095092949748421039339)
  ·
    refine ⟨29863642639424622631559009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19909095092949748421039339 29863642639424622631559009)
    ·
      refine ⟨22397731979568466973669257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29863642639424622631559009 22397731979568466973669257)
      ·
        refine ⟨16798298984676350230251943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22397731979568466973669257 16798298984676350230251943)
        ·
          refine ⟨25197448477014525345377915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16798298984676350230251943 25197448477014525345377915)
          ·
            refine ⟨37796172715521788018066873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25197448477014525345377915 37796172715521788018066873)
            ·
              refine ⟨28347129536641341013550155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37796172715521788018066873 28347129536641341013550155)
              ·
                refine ⟨42520694304962011520325233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28347129536641341013550155 42520694304962011520325233)
                ·
                  refine ⟨31890520728721508640243925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42520694304962011520325233 31890520728721508640243925)
                  ·
                    refine ⟨747434079579410358755717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31890520728721508640243925 747434079579410358755717)
                    ·
                      rfl

theorem cell22_2183434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_2183434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183434 prefixEnd_2183434 := by exact prefixLift 2183434
  have htrace : WordTrace (prefixWord ++ tailWord_2183434) baseStart_2183434 baseEnd_2183434 := by
    simpa [prefixWord, tailWord_2183434, baseEnd_2183434] using wordTrace_append hprefix tailTrace_2183434
  have hstable : (prefixWord ++ tailWord_2183434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183434).length < 2 ^ (prefixWord ++ tailWord_2183434).sum := by decide
  have hdescent : baseEnd_2183434 < baseStart_2183434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183470 : List Nat := [4, 1, 3, 3, 1, 2, 1, 7]
def baseStart_2183470 : Nat := 118140960795 + 2183470 * 2 ^ 59
def prefixEnd_2183470 : Nat := 4983230072969 + 3 ^ 40 * 2183470 * 2
def baseEnd_2183470 : Nat := 83049600346124251650623

theorem tailTrace_2183470 : CollatzResearch.WordTrace tailWord_2183470 prefixEnd_2183470 83049600346124251650623 := by
  unfold tailWord_2183470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954711674958571479058483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53091795599779047888311909 9954711674958571479058483)
  ·
    refine ⟨14932067512437857218587725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9954711674958571479058483 14932067512437857218587725)
    ·
      refine ⟨5599525317164196456970397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14932067512437857218587725 5599525317164196456970397)
      ·
        refine ⟨2099821993936573671363899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5599525317164196456970397 2099821993936573671363899)
        ·
          refine ⟨3149732990904860507045849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099821993936573671363899 3149732990904860507045849)
          ·
            refine ⟨2362299743178645380284387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3149732990904860507045849 2362299743178645380284387)
            ·
              refine ⟨3543449614767968070426581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362299743178645380284387 3543449614767968070426581)
              ·
                refine ⟨83049600346124251650623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3543449614767968070426581 83049600346124251650623)
                ·
                  rfl

theorem cell22_2183470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_2183470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183470 prefixEnd_2183470 := by exact prefixLift 2183470
  have htrace : WordTrace (prefixWord ++ tailWord_2183470) baseStart_2183470 baseEnd_2183470 := by
    simpa [prefixWord, tailWord_2183470, baseEnd_2183470] using wordTrace_append hprefix tailTrace_2183470
  have hstable : (prefixWord ++ tailWord_2183470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183470).length < 2 ^ (prefixWord ++ tailWord_2183470).sum := by decide
  have hdescent : baseEnd_2183470 < baseStart_2183470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183556 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_2183556 : Nat := 118140960795 + 2183556 * 2 ^ 59
def prefixEnd_2183556 : Nat := 4983230072969 + 3 ^ 40 * 2183556 * 2
def baseEnd_2183556 : Nat := 747475842672642707205343

theorem tailTrace_2183556 : CollatzResearch.WordTrace tailWord_2183556 prefixEnd_2183556 747475842672642707205343 := by
  unfold tailWord_2183556
  simp only [CollatzResearch.WordTrace]
  refine ⟨39820415038678504260049261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53093886718238005680065681 39820415038678504260049261)
  ·
    refine ⟨14932655639504439097518473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39820415038678504260049261 14932655639504439097518473)
    ·
      refine ⟨11199491729628329323138855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14932655639504439097518473 11199491729628329323138855)
      ·
        refine ⟨16799237594442493984708283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11199491729628329323138855 16799237594442493984708283)
        ·
          refine ⟨25198856391663740977062425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16799237594442493984708283 25198856391663740977062425)
          ·
            refine ⟨18899142293747805732796819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25198856391663740977062425 18899142293747805732796819)
            ·
              refine ⟨28348713440621708599195229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18899142293747805732796819 28348713440621708599195229)
              ·
                refine ⟨10630767540233140724698211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28348713440621708599195229 10630767540233140724698211)
                ·
                  refine ⟨15946151310349711087047317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10630767540233140724698211 15946151310349711087047317)
                  ·
                    refine ⟨747475842672642707205343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15946151310349711087047317 747475842672642707205343)
                    ·
                      rfl

theorem cell22_2183556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_2183556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183556 prefixEnd_2183556 := by exact prefixLift 2183556
  have htrace : WordTrace (prefixWord ++ tailWord_2183556) baseStart_2183556 baseEnd_2183556 := by
    simpa [prefixWord, tailWord_2183556, baseEnd_2183556] using wordTrace_append hprefix tailTrace_2183556
  have hstable : (prefixWord ++ tailWord_2183556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183556).length < 2 ^ (prefixWord ++ tailWord_2183556).sum := by decide
  have hdescent : baseEnd_2183556 < baseStart_2183556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183592 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2183592 : Nat := 118140960795 + 2183592 * 2 ^ 59
def prefixEnd_2183592 : Nat := 4983230072969 + 3 ^ 40 * 2183592 * 2
def baseEnd_2183592 : Nat := 747488166208350613305233

theorem tailTrace_2183592 : CollatzResearch.WordTrace tailWord_2183592 prefixEnd_2183592 747488166208350613305233 := by
  unfold tailWord_2183592
  simp only [CollatzResearch.WordTrace]
  refine ⟨39821071552613293334204515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53094762070151057778939353 39821071552613293334204515)
  ·
    refine ⟨59731607328919940001306773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39821071552613293334204515 59731607328919940001306773)
    ·
      refine ⟨2799919093543122187561255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59731607328919940001306773 2799919093543122187561255)
      ·
        refine ⟨4199878640314683281341883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2799919093543122187561255 4199878640314683281341883)
        ·
          refine ⟨6299817960472024922012825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4199878640314683281341883 6299817960472024922012825)
          ·
            refine ⟨4724863470354018691509619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6299817960472024922012825 4724863470354018691509619)
            ·
              refine ⟨7087295205531028037264429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724863470354018691509619 7087295205531028037264429)
              ·
                refine ⟨2657735702074135513974161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7087295205531028037264429 2657735702074135513974161)
                ·
                  refine ⟨1993301776555601635480621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2657735702074135513974161 1993301776555601635480621)
                  ·
                    refine ⟨747488166208350613305233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993301776555601635480621 747488166208350613305233)
                    ·
                      rfl

theorem cell22_2183592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2183592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183592 prefixEnd_2183592 := by exact prefixLift 2183592
  have htrace : WordTrace (prefixWord ++ tailWord_2183592) baseStart_2183592 baseEnd_2183592 := by
    simpa [prefixWord, tailWord_2183592, baseEnd_2183592] using wordTrace_append hprefix tailTrace_2183592
  have hstable : (prefixWord ++ tailWord_2183592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183592).length < 2 ^ (prefixWord ++ tailWord_2183592).sum := by decide
  have hdescent : baseEnd_2183592 < baseStart_2183592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183631 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 2, 5]
def baseStart_2183631 : Nat := 118140960795 + 2183631 * 2 ^ 59
def prefixEnd_2183631 : Nat := 4983230072969 + 3 ^ 40 * 2183631 * 2
def baseEnd_2183631 : Nat := 747501516705367511580113

theorem tailTrace_2183631 : CollatzResearch.WordTrace tailWord_2183631 prefixEnd_2183631 747501516705367511580113 := by
  unfold tailWord_2183631
  simp only [CollatzResearch.WordTrace]
  refine ⟨79643565552085296329078747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53095710368056864219385831 79643565552085296329078747)
  ·
    refine ⟨119465348328127944493618121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79643565552085296329078747 119465348328127944493618121)
    ·
      refine ⟨89599011246095958370213591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119465348328127944493618121 89599011246095958370213591)
      ·
        refine ⟨134398516869143937555320387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89599011246095958370213591 134398516869143937555320387)
        ·
          refine ⟨201597775303715906332980581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134398516869143937555320387 201597775303715906332980581)
          ·
            refine ⟨37799582869446732437433859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201597775303715906332980581 37799582869446732437433859)
            ·
              refine ⟨56699374304170098656150789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37799582869446732437433859 56699374304170098656150789)
              ·
                refine ⟨10631132682031893498028273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56699374304170098656150789 10631132682031893498028273)
                ·
                  refine ⟨7973349511523920123521205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10631132682031893498028273 7973349511523920123521205)
                  ·
                    refine ⟨747501516705367511580113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7973349511523920123521205 747501516705367511580113)
                    ·
                      rfl

theorem cell22_2183631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_2183631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183631 prefixEnd_2183631 := by exact prefixLift 2183631
  have htrace : WordTrace (prefixWord ++ tailWord_2183631) baseStart_2183631 baseEnd_2183631 := by
    simpa [prefixWord, tailWord_2183631, baseEnd_2183631] using wordTrace_append hprefix tailTrace_2183631
  have hstable : (prefixWord ++ tailWord_2183631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183631).length < 2 ^ (prefixWord ++ tailWord_2183631).sum := by decide
  have hdescent : baseEnd_2183631 < baseStart_2183631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183637 : List Nat := [1, 3, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_2183637 : Nat := 118140960795 + 2183637 * 2 ^ 59
def prefixEnd_2183637 : Nat := 4983230072969 + 3 ^ 40 * 2183637 * 2
def baseEnd_2183637 : Nat := 747503570627985495930095

theorem tailTrace_2183637 : CollatzResearch.WordTrace tailWord_2183637 prefixEnd_2183637 747503570627985495930095 := by
  unfold tailWord_2183637
  simp only [CollatzResearch.WordTrace]
  refine ⟨79643784390063559353797165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53095856260042372902531443 79643784390063559353797165)
  ·
    refine ⟨29866419146273834757673937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79643784390063559353797165 29866419146273834757673937)
    ·
      refine ⟨22399814359705376068255453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29866419146273834757673937 22399814359705376068255453)
      ·
        refine ⟨8399930384889516025595795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22399814359705376068255453 8399930384889516025595795)
        ·
          refine ⟨12599895577334274038393693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8399930384889516025595795 12599895577334274038393693)
          ·
            refine ⟨4724960841500352764397635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12599895577334274038393693 4724960841500352764397635)
            ·
              refine ⟨7087441262250529146596453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724960841500352764397635 7087441262250529146596453)
              ·
                refine ⟨1328895236671974214986835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7087441262250529146596453 1328895236671974214986835)
                ·
                  refine ⟨1993342855007961322480253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328895236671974214986835 1993342855007961322480253)
                  ·
                    refine ⟨747503570627985495930095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993342855007961322480253 747503570627985495930095)
                    ·
                      rfl

theorem cell22_2183637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_2183637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183637 prefixEnd_2183637 := by exact prefixLift 2183637
  have htrace : WordTrace (prefixWord ++ tailWord_2183637) baseStart_2183637 baseEnd_2183637 := by
    simpa [prefixWord, tailWord_2183637, baseEnd_2183637] using wordTrace_append hprefix tailTrace_2183637
  have hstable : (prefixWord ++ tailWord_2183637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183637).length < 2 ^ (prefixWord ++ tailWord_2183637).sum := by decide
  have hdescent : baseEnd_2183637 < baseStart_2183637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183663 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 1, 4]
def baseStart_2183663 : Nat := 118140960795 + 2183663 * 2 ^ 59
def prefixEnd_2183663 : Nat := 4983230072969 + 3 ^ 40 * 2183663 * 2
def baseEnd_2183663 : Nat := 747512470959330094780015

theorem tailTrace_2183663 : CollatzResearch.WordTrace tailWord_2183663 prefixEnd_2183663 747512470959330094780015 := by
  unfold tailWord_2183663
  simp only [CollatzResearch.WordTrace]
  refine ⟨79644732687969365794243643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53096488458646243862829095 79644732687969365794243643)
  ·
    refine ⟨119467099031954048691365465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79644732687969365794243643 119467099031954048691365465)
    ·
      refine ⟨89600324273965536518524099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119467099031954048691365465 89600324273965536518524099)
      ·
        refine ⟨134400486410948304777786149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89600324273965536518524099 134400486410948304777786149)
        ·
          refine ⟨25200091202052807145834903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134400486410948304777786149 25200091202052807145834903)
          ·
            refine ⟨37800136803079210718752355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25200091202052807145834903 37800136803079210718752355)
            ·
              refine ⟨56700205204618816078128533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37800136803079210718752355 56700205204618816078128533)
              ·
                refine ⟨2657822118966507003662275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56700205204618816078128533 2657822118966507003662275)
                ·
                  refine ⟨3986733178449760505493413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657822118966507003662275 3986733178449760505493413)
                  ·
                    refine ⟨747512470959330094780015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3986733178449760505493413 747512470959330094780015)
                    ·
                      rfl

theorem cell22_2183663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_2183663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183663 prefixEnd_2183663 := by exact prefixLift 2183663
  have htrace : WordTrace (prefixWord ++ tailWord_2183663) baseStart_2183663 baseEnd_2183663 := by
    simpa [prefixWord, tailWord_2183663, baseEnd_2183663] using wordTrace_append hprefix tailTrace_2183663
  have hstable : (prefixWord ++ tailWord_2183663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183663).length < 2 ^ (prefixWord ++ tailWord_2183663).sum := by decide
  have hdescent : baseEnd_2183663 < baseStart_2183663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183708 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2183708 : Nat := 118140960795 + 2183708 * 2 ^ 59
def prefixEnd_2183708 : Nat := 4983230072969 + 3 ^ 40 * 2183708 * 2
def baseEnd_2183708 : Nat := 747527875378964977404877

theorem tailTrace_2183708 : CollatzResearch.WordTrace tailWord_2183708 prefixEnd_2183708 747527875378964977404877 := by
  unfold tailWord_2183708
  simp only [CollatzResearch.WordTrace]
  refine ⟨39823186986403169239815889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53097582648537558986421185 39823186986403169239815889)
  ·
    refine ⟨29867390239802376929861917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39823186986403169239815889 29867390239802376929861917)
    ·
      refine ⟨11200271339925891348698219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29867390239802376929861917 11200271339925891348698219)
      ·
        refine ⟨16800407009888837023047329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11200271339925891348698219 16800407009888837023047329)
        ·
          refine ⟨12600305257416627767285497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16800407009888837023047329 12600305257416627767285497)
          ·
            refine ⟨9450228943062470825464123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12600305257416627767285497 9450228943062470825464123)
            ·
              refine ⟨14175343414593706238196185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9450228943062470825464123 14175343414593706238196185)
              ·
                refine ⟨10631507560945279678647139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14175343414593706238196185 10631507560945279678647139)
                ·
                  refine ⟨15947261341417919517970709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10631507560945279678647139 15947261341417919517970709)
                  ·
                    refine ⟨747527875378964977404877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15947261341417919517970709 747527875378964977404877)
                    ·
                      rfl

theorem cell22_2183708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2183708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183708 prefixEnd_2183708 := by exact prefixLift 2183708
  have htrace : WordTrace (prefixWord ++ tailWord_2183708) baseStart_2183708 baseEnd_2183708 := by
    simpa [prefixWord, tailWord_2183708, baseEnd_2183708] using wordTrace_append hprefix tailTrace_2183708
  have hstable : (prefixWord ++ tailWord_2183708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183708).length < 2 ^ (prefixWord ++ tailWord_2183708).sum := by decide
  have hdescent : baseEnd_2183708 < baseStart_2183708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183755 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 3, 3]
def baseStart_2183755 : Nat := 118140960795 + 2183755 * 2 ^ 59
def prefixEnd_2183755 : Nat := 4983230072969 + 3 ^ 40 * 2183755 * 2
def baseEnd_2183755 : Nat := 747543964439472521479733

theorem tailTrace_2183755 : CollatzResearch.WordTrace tailWord_2183755 prefixEnd_2183755 747543964439472521479733 := by
  unfold tailWord_2183755
  simp only [CollatzResearch.WordTrace]
  refine ⟨79648088203636065506592719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53098725469090710337728479 79648088203636065506592719)
  ·
    refine ⟨119472132305454098259889079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79648088203636065506592719 119472132305454098259889079)
    ·
      refine ⟨179208198458181147389833619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119472132305454098259889079 179208198458181147389833619)
      ·
        refine ⟨268812297687271721084750429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179208198458181147389833619 268812297687271721084750429)
        ·
          refine ⟨100804611632726895406781411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268812297687271721084750429 100804611632726895406781411)
          ·
            refine ⟨151206917449090343110172117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100804611632726895406781411 151206917449090343110172117)
            ·
              refine ⟨3543912127713054916644659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 151206917449090343110172117 3543912127713054916644659)
              ·
                refine ⟨5315868191569582374966989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543912127713054916644659 5315868191569582374966989)
                ·
                  refine ⟨1993450571838593390612621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5315868191569582374966989 1993450571838593390612621)
                  ·
                    refine ⟨747543964439472521479733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993450571838593390612621 747543964439472521479733)
                    ·
                      rfl

theorem cell22_2183755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 3].length) (baseStart_2183755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183755 prefixEnd_2183755 := by exact prefixLift 2183755
  have htrace : WordTrace (prefixWord ++ tailWord_2183755) baseStart_2183755 baseEnd_2183755 := by
    simpa [prefixWord, tailWord_2183755, baseEnd_2183755] using wordTrace_append hprefix tailTrace_2183755
  have hstable : (prefixWord ++ tailWord_2183755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183755).length < 2 ^ (prefixWord ++ tailWord_2183755).sum := by decide
  have hdescent : baseEnd_2183755 < baseStart_2183755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183783 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2183783 : Nat := 118140960795 + 2183783 * 2 ^ 59
def prefixEnd_2183783 : Nat := 4983230072969 + 3 ^ 40 * 2183783 * 2
def baseEnd_2183783 : Nat := 747553549411689781779647

theorem tailTrace_2183783 : CollatzResearch.WordTrace tailWord_2183783 prefixEnd_2183783 747553549411689781779647 := by
  unfold tailWord_2183783
  simp only [CollatzResearch.WordTrace]
  refine ⟨79649109447534626288612003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53099406298356417525741335 79649109447534626288612003)
  ·
    refine ⟨119473664171301939432918005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79649109447534626288612003 119473664171301939432918005)
    ·
      refine ⟨11200656016059556821836063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119473664171301939432918005 11200656016059556821836063)
      ·
        refine ⟨16800984024089335232754095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11200656016059556821836063 16800984024089335232754095)
        ·
          refine ⟨25201476036134002849131143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16800984024089335232754095 25201476036134002849131143)
          ·
            refine ⟨37802214054201004273696715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25201476036134002849131143 37802214054201004273696715)
            ·
              refine ⟨56703321081301506410545073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37802214054201004273696715 56703321081301506410545073)
              ·
                refine ⟨42527490810976129807908805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56703321081301506410545073 42527490810976129807908805)
                ·
                  refine ⟨7973904527058024338982901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42527490810976129807908805 7973904527058024338982901)
                  ·
                    refine ⟨747553549411689781779647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7973904527058024338982901 747553549411689781779647)
                    ·
                      rfl

theorem cell22_2183783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2183783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183783 prefixEnd_2183783 := by exact prefixLift 2183783
  have htrace : WordTrace (prefixWord ++ tailWord_2183783) baseStart_2183783 baseEnd_2183783 := by
    simpa [prefixWord, tailWord_2183783, baseEnd_2183783] using wordTrace_append hprefix tailTrace_2183783
  have hstable : (prefixWord ++ tailWord_2183783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183783).length < 2 ^ (prefixWord ++ tailWord_2183783).sum := by decide
  have hdescent : baseEnd_2183783 < baseStart_2183783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183845 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 4, 3]
def baseStart_2183845 : Nat := 118140960795 + 2183845 * 2 ^ 59
def prefixEnd_2183845 : Nat := 4983230072969 + 3 ^ 40 * 2183845 * 2
def baseEnd_2183845 : Nat := 747574773278742286729457

theorem tailTrace_2183845 : CollatzResearch.WordTrace tailWord_2183845 prefixEnd_2183845 747574773278742286729457 := by
  unfold tailWord_2183845
  simp only [CollatzResearch.WordTrace]
  refine ⟨79651370773310010877368989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53100913848873340584912659 79651370773310010877368989)
  ·
    refine ⟨29869264039991254079013371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79651370773310010877368989 29869264039991254079013371)
    ·
      refine ⟨44803896059986881118520057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29869264039991254079013371 44803896059986881118520057)
      ·
        refine ⟨33602922044990160838890043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44803896059986881118520057 33602922044990160838890043)
        ·
          refine ⟨50404383067485241258335065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33602922044990160838890043 50404383067485241258335065)
          ·
            refine ⟨37803287300613930943751299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50404383067485241258335065 37803287300613930943751299)
            ·
              refine ⟨56704930950920896415626949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37803287300613930943751299 56704930950920896415626949)
              ·
                refine ⟨10632174553297668077930053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56704930950920896415626949 10632174553297668077930053)
                ·
                  refine ⟨1993532728743312764611885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10632174553297668077930053 1993532728743312764611885)
                  ·
                    refine ⟨747574773278742286729457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993532728743312764611885 747574773278742286729457)
                    ·
                      rfl

theorem cell22_2183845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_2183845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183845 prefixEnd_2183845 := by exact prefixLift 2183845
  have htrace : WordTrace (prefixWord ++ tailWord_2183845) baseStart_2183845 baseEnd_2183845 := by
    simpa [prefixWord, tailWord_2183845, baseEnd_2183845] using wordTrace_append hprefix tailTrace_2183845
  have hstable : (prefixWord ++ tailWord_2183845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183845).length < 2 ^ (prefixWord ++ tailWord_2183845).sum := by decide
  have hdescent : baseEnd_2183845 < baseStart_2183845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183888 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_2183888 : Nat := 118140960795 + 2183888 * 2 ^ 59
def prefixEnd_2183888 : Nat := 4983230072969 + 3 ^ 40 * 2183888 * 2
def baseEnd_2183888 : Nat := 747589493057504507904325

theorem tailTrace_2183888 : CollatzResearch.WordTrace tailWord_2183888 prefixEnd_2183888 747589493057504507904325 := by
  unfold tailWord_2183888
  simp only [CollatzResearch.WordTrace]
  refine ⟨39826469556077114610592159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53101959408102819480789545 39826469556077114610592159)
  ·
    refine ⟨59739704334115671915888239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39826469556077114610592159 59739704334115671915888239)
    ·
      refine ⟨89609556501173507873832359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59739704334115671915888239 89609556501173507873832359)
      ·
        refine ⟨134414334751760261810748539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89609556501173507873832359 134414334751760261810748539)
        ·
          refine ⟨201621502127640392716122809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134414334751760261810748539 201621502127640392716122809)
          ·
            refine ⟨151216126595730294537092107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201621502127640392716122809 151216126595730294537092107)
            ·
              refine ⟨226824189893595441805638161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151216126595730294537092107 226824189893595441805638161)
              ·
                refine ⟨170118142420196581354228621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226824189893595441805638161 170118142420196581354228621)
                ·
                  refine ⟨63794303407573718007835733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170118142420196581354228621 63794303407573718007835733)
                  ·
                    refine ⟨747589493057504507904325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63794303407573718007835733 747589493057504507904325)
                    ·
                      rfl

theorem cell22_2183888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_2183888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183888 prefixEnd_2183888 := by exact prefixLift 2183888
  have htrace : WordTrace (prefixWord ++ tailWord_2183888) baseStart_2183888 baseEnd_2183888 := by
    simpa [prefixWord, tailWord_2183888, baseEnd_2183888] using wordTrace_append hprefix tailTrace_2183888
  have hstable : (prefixWord ++ tailWord_2183888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183888).length < 2 ^ (prefixWord ++ tailWord_2183888).sum := by decide
  have hdescent : baseEnd_2183888 < baseStart_2183888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183892 : List Nat := [2, 4, 1, 3, 2, 1, 1, 8]
def baseStart_2183892 : Nat := 118140960795 + 2183892 * 2 ^ 59
def prefixEnd_2183892 : Nat := 4983230072969 + 3 ^ 40 * 2183892 * 2
def baseEnd_2183892 : Nat := 83065651371027758978257

theorem tailTrace_2183892 : CollatzResearch.WordTrace tailWord_2183892 prefixEnd_2183892 83065651371027758978257 := by
  unfold tailWord_2183892
  simp only [CollatzResearch.WordTrace]
  refine ⟨39826542502069868952164965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53102056669426491936219953 39826542502069868952164965)
  ·
    refine ⟨7467476719138100428530931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39826542502069868952164965 7467476719138100428530931)
    ·
      refine ⟨11201215078707150642796397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7467476719138100428530931 11201215078707150642796397)
      ·
        refine ⟨4200455654515181491048649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11201215078707150642796397 4200455654515181491048649)
        ·
          refine ⟨3150341740886386118286487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4200455654515181491048649 3150341740886386118286487)
          ·
            refine ⟨4725512611329579177429731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150341740886386118286487 4725512611329579177429731)
            ·
              refine ⟨7088268916994368766144597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4725512611329579177429731 7088268916994368766144597)
              ·
                refine ⟨83065651371027758978257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7088268916994368766144597 83065651371027758978257)
                ·
                  rfl

theorem cell22_2183892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 8].length) (baseStart_2183892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183892 prefixEnd_2183892 := by exact prefixLift 2183892
  have htrace : WordTrace (prefixWord ++ tailWord_2183892) baseStart_2183892 baseEnd_2183892 := by
    simpa [prefixWord, tailWord_2183892, baseEnd_2183892] using wordTrace_append hprefix tailTrace_2183892
  have hstable : (prefixWord ++ tailWord_2183892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183892).length < 2 ^ (prefixWord ++ tailWord_2183892).sum := by decide
  have hdescent : baseEnd_2183892 < baseStart_2183892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183920 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 5]
def baseStart_2183920 : Nat := 118140960795 + 2183920 * 2 ^ 59
def prefixEnd_2183920 : Nat := 4983230072969 + 3 ^ 40 * 2183920 * 2
def baseEnd_2183920 : Nat := 249200149103822363701409

theorem tailTrace_2183920 : CollatzResearch.WordTrace tailWord_2183920 prefixEnd_2183920 249200149103822363701409 := by
  unfold tailWord_2183920
  simp only [CollatzResearch.WordTrace]
  refine ⟨39827053124019149343174607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53102737498692199124232809 39827053124019149343174607)
  ·
    refine ⟨59740579686028724014761911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39827053124019149343174607 59740579686028724014761911)
    ·
      refine ⟨89610869529043086022142867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59740579686028724014761911 89610869529043086022142867)
      ·
        refine ⟨134416304293564629033214301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89610869529043086022142867 134416304293564629033214301)
        ·
          refine ⟨50406114110086735887455363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134416304293564629033214301 50406114110086735887455363)
          ·
            refine ⟨75609171165130103831183045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50406114110086735887455363 75609171165130103831183045)
            ·
              refine ⟨14176719593461894468346821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75609171165130103831183045 14176719593461894468346821)
              ·
                refine ⟨2658134923774105212815029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14176719593461894468346821 2658134923774105212815029)
                ·
                  refine ⟨249200149103822363701409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2658134923774105212815029 249200149103822363701409)
                  ·
                    rfl

theorem cell22_2183920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_2183920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183920 prefixEnd_2183920 := by exact prefixLift 2183920
  have htrace : WordTrace (prefixWord ++ tailWord_2183920) baseStart_2183920 baseEnd_2183920 := by
    simpa [prefixWord, tailWord_2183920, baseEnd_2183920] using wordTrace_append hprefix tailTrace_2183920
  have hstable : (prefixWord ++ tailWord_2183920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183920).length < 2 ^ (prefixWord ++ tailWord_2183920).sum := by decide
  have hdescent : baseEnd_2183920 < baseStart_2183920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183980 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_2183980 : Nat := 118140960795 + 2183980 * 2 ^ 59
def prefixEnd_2183980 : Nat := 4983230072969 + 3 ^ 40 * 2183980 * 2
def baseEnd_2183980 : Nat := 747620986537646934604043

theorem tailTrace_2183980 : CollatzResearch.WordTrace tailWord_2183980 prefixEnd_2183980 747620986537646934604043 := by
  unfold tailWord_2183980
  simp only [CollatzResearch.WordTrace]
  refine ⟨39828147313910464466766697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53104196418547285955688929 39828147313910464466766697)
  ·
    refine ⟨29871110485432848350075023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39828147313910464466766697 29871110485432848350075023)
    ·
      refine ⟨44806665728149272525112535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29871110485432848350075023 44806665728149272525112535)
      ·
        refine ⟨67209998592223908787668803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44806665728149272525112535 67209998592223908787668803)
        ·
          refine ⟨100814997888335863181503205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67209998592223908787668803 100814997888335863181503205)
          ·
            refine ⟨18902812104062974346531851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100814997888335863181503205 18902812104062974346531851)
            ·
              refine ⟨28354218156094461519797777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18902812104062974346531851 28354218156094461519797777)
              ·
                refine ⟨21265663617070846139848333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28354218156094461519797777 21265663617070846139848333)
                ·
                  refine ⟨7974623856401567302443125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21265663617070846139848333 7974623856401567302443125)
                  ·
                    refine ⟨747620986537646934604043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7974623856401567302443125 747620986537646934604043)
                    ·
                      rfl

theorem cell22_2183980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_2183980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2183980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2183980 prefixEnd_2183980 := by exact prefixLift 2183980
  have htrace : WordTrace (prefixWord ++ tailWord_2183980) baseStart_2183980 baseEnd_2183980 := by
    simpa [prefixWord, tailWord_2183980, baseEnd_2183980] using wordTrace_append hprefix tailTrace_2183980
  have hstable : (prefixWord ++ tailWord_2183980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183980).length < 2 ^ (prefixWord ++ tailWord_2183980).sum := by decide
  have hdescent : baseEnd_2183980 < baseStart_2183980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184012 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_2184012 : Nat := 118140960795 + 2184012 * 2 ^ 59
def prefixEnd_2184012 : Nat := 4983230072969 + 3 ^ 40 * 2184012 * 2
def baseEnd_2184012 : Nat := 747631940791609517803945

theorem tailTrace_2184012 : CollatzResearch.WordTrace tailWord_2184012 prefixEnd_2184012 747631940791609517803945 := by
  unfold tailWord_2184012
  simp only [CollatzResearch.WordTrace]
  refine ⟨39828730881852499199349145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53104974509136665599132193 39828730881852499199349145)
  ·
    refine ⟨29871548161389374399511859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39828730881852499199349145 29871548161389374399511859)
    ·
      refine ⟨44807322242084061599267789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29871548161389374399511859 44807322242084061599267789)
      ·
        refine ⟨16802745840781523099725421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44807322242084061599267789 16802745840781523099725421)
        ·
          refine ⟨6301029690293071162397033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16802745840781523099725421 6301029690293071162397033)
          ·
            refine ⟨4725772267719803371797775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6301029690293071162397033 4725772267719803371797775)
            ·
              refine ⟨7088658401579705057696663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4725772267719803371797775 7088658401579705057696663)
              ·
                refine ⟨10632987602369557586544995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7088658401579705057696663 10632987602369557586544995)
                ·
                  refine ⟨15949481403554336379817493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10632987602369557586544995 15949481403554336379817493)
                  ·
                    refine ⟨747631940791609517803945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15949481403554336379817493 747631940791609517803945)
                    ·
                      rfl

theorem cell22_2184012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_2184012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184012 prefixEnd_2184012 := by exact prefixLift 2184012
  have htrace : WordTrace (prefixWord ++ tailWord_2184012) baseStart_2184012 baseEnd_2184012 := by
    simpa [prefixWord, tailWord_2184012, baseEnd_2184012] using wordTrace_append hprefix tailTrace_2184012
  have hstable : (prefixWord ++ tailWord_2184012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184012).length < 2 ^ (prefixWord ++ tailWord_2184012).sum := by decide
  have hdescent : baseEnd_2184012 < baseStart_2184012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184072 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 7]
def baseStart_2184072 : Nat := 118140960795 + 2184072 * 2 ^ 59
def prefixEnd_2184072 : Nat := 4983230072969 + 3 ^ 40 * 2184072 * 2
def baseEnd_2184072 : Nat := 249217493339263120434587

theorem tailTrace_2184072 : CollatzResearch.WordTrace tailWord_2184072 prefixEnd_2184072 249217493339263120434587 := by
  unfold tailWord_2184072
  simp only [CollatzResearch.WordTrace]
  refine ⟨39829825071743814322941235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53106433428991752430588313 39829825071743814322941235)
  ·
    refine ⟨59744737607615721484411853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39829825071743814322941235 59744737607615721484411853)
    ·
      refine ⟨22404276602855895556654445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59744737607615721484411853 22404276602855895556654445)
      ·
        refine ⟨8401603726070960833745417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22404276602855895556654445 8401603726070960833745417)
        ·
          refine ⟨6301202794553220625309063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8401603726070960833745417 6301202794553220625309063)
          ·
            refine ⟨9451804191829830937963595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301202794553220625309063 9451804191829830937963595)
            ·
              refine ⟨14177706287744746406945393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9451804191829830937963595 14177706287744746406945393)
              ·
                refine ⟨10633279715808559805209045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14177706287744746406945393 10633279715808559805209045)
                ·
                  refine ⟨249217493339263120434587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10633279715808559805209045 249217493339263120434587)
                  ·
                    rfl

theorem cell22_2184072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_2184072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184072 prefixEnd_2184072 := by exact prefixLift 2184072
  have htrace : WordTrace (prefixWord ++ tailWord_2184072) baseStart_2184072 baseEnd_2184072 := by
    simpa [prefixWord, tailWord_2184072, baseEnd_2184072] using wordTrace_append hprefix tailTrace_2184072
  have hstable : (prefixWord ++ tailWord_2184072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184072).length < 2 ^ (prefixWord ++ tailWord_2184072).sum := by decide
  have hdescent : baseEnd_2184072 < baseStart_2184072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184076 : List Nat := [2, 2, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_2184076 : Nat := 118140960795 + 2184076 * 2 ^ 59
def prefixEnd_2184076 : Nat := 4983230072969 + 3 ^ 40 * 2184076 * 2
def baseEnd_2184076 : Nat := 747653849299534684203749

theorem tailTrace_2184076 : CollatzResearch.WordTrace tailWord_2184076 prefixEnd_2184076 747653849299534684203749 := by
  unfold tailWord_2184076
  simp only [CollatzResearch.WordTrace]
  refine ⟨39829898017736568664514041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53106530690315424886018721 39829898017736568664514041)
  ·
    refine ⟨29872423513302426498385531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39829898017736568664514041 29872423513302426498385531)
    ·
      refine ⟨44808635269953639747578297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29872423513302426498385531 44808635269953639747578297)
      ·
        refine ⟨33606476452465229810683723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44808635269953639747578297 33606476452465229810683723)
        ·
          refine ⟨50409714678697844716025585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33606476452465229810683723 50409714678697844716025585)
          ·
            refine ⟨37807286009023383537019189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50409714678697844716025585 37807286009023383537019189)
            ·
              refine ⟨3544433063345942206595549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37807286009023383537019189 3544433063345942206595549)
              ·
                refine ⟨1329162398754728327473331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3544433063345942206595549 1329162398754728327473331)
                ·
                  refine ⟨1993743598132092491209997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329162398754728327473331 1993743598132092491209997)
                  ·
                    refine ⟨747653849299534684203749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993743598132092491209997 747653849299534684203749)
                    ·
                      rfl

theorem cell22_2184076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_2184076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184076 prefixEnd_2184076 := by exact prefixLift 2184076
  have htrace : WordTrace (prefixWord ++ tailWord_2184076) baseStart_2184076 baseEnd_2184076 := by
    simpa [prefixWord, tailWord_2184076, baseEnd_2184076] using wordTrace_append hprefix tailTrace_2184076
  have hstable : (prefixWord ++ tailWord_2184076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184076).length < 2 ^ (prefixWord ++ tailWord_2184076).sum := by decide
  have hdescent : baseEnd_2184076 < baseStart_2184076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184093 : List Nat := [1, 4, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_2184093 : Nat := 118140960795 + 2184093 * 2 ^ 59
def prefixEnd_2184093 : Nat := 4983230072969 + 3 ^ 40 * 2184093 * 2
def baseEnd_2184093 : Nat := 747659668746952306528697

theorem tailTrace_2184093 : CollatzResearch.WordTrace tailWord_2184093 prefixEnd_2184093 747659668746952306528697 := by
  unfold tailWord_2184093
  simp only [CollatzResearch.WordTrace]
  refine ⟨79660416076411549232396933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53106944050941032821597955 79660416076411549232396933)
  ·
    refine ⟨14936328014327165481074425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79660416076411549232396933 14936328014327165481074425)
    ·
      refine ⟨11202246010745374110805819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14936328014327165481074425 11202246010745374110805819)
      ·
        refine ⟨16803369016118061166208729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11202246010745374110805819 16803369016118061166208729)
        ·
          refine ⟨12602526762088545874656547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16803369016118061166208729 12602526762088545874656547)
          ·
            refine ⟨18903790143132818811984821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12602526762088545874656547 18903790143132818811984821)
            ·
              refine ⟨1772230325918701763623577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18903790143132818811984821 1772230325918701763623577)
              ·
                refine ⟨1329172744439026322717683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772230325918701763623577 1329172744439026322717683)
                ·
                  refine ⟨1993759116658539484076525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329172744439026322717683 1993759116658539484076525)
                  ·
                    refine ⟨747659668746952306528697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993759116658539484076525 747659668746952306528697)
                    ·
                      rfl

theorem cell22_2184093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_2184093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184093 prefixEnd_2184093 := by exact prefixLift 2184093
  have htrace : WordTrace (prefixWord ++ tailWord_2184093) baseStart_2184093 baseEnd_2184093 := by
    simpa [prefixWord, tailWord_2184093, baseEnd_2184093] using wordTrace_append hprefix tailTrace_2184093
  have hstable : (prefixWord ++ tailWord_2184093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184093).length < 2 ^ (prefixWord ++ tailWord_2184093).sum := by decide
  have hdescent : baseEnd_2184093 < baseStart_2184093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184117 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 8]
def baseStart_2184117 : Nat := 118140960795 + 2184117 * 2 ^ 59
def prefixEnd_2184117 : Nat := 4983230072969 + 3 ^ 40 * 2184117 * 2
def baseEnd_2184117 : Nat := 249222628145808081309541

theorem tailTrace_2184117 : CollatzResearch.WordTrace tailWord_2184117 prefixEnd_2184117 249222628145808081309541 := by
  unfold tailWord_2184117
  simp only [CollatzResearch.WordTrace]
  refine ⟨79661291428324601331270605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53107527618883067554180403 79661291428324601331270605)
  ·
    refine ⟨29872984285621725499226477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79661291428324601331270605 29872984285621725499226477)
    ·
      refine ⟨11202369107108147062209929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29872984285621725499226477 11202369107108147062209929)
      ·
        refine ⟨8401776830331110296657447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11202369107108147062209929 8401776830331110296657447)
        ·
          refine ⟨12602665245496665444986171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401776830331110296657447 12602665245496665444986171)
          ·
            refine ⟨18903997868244998167479257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12602665245496665444986171 18903997868244998167479257)
            ·
              refine ⟨14177998401183748625609443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18903997868244998167479257 14177998401183748625609443)
              ·
                refine ⟨21266997601775622938414165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14177998401183748625609443 21266997601775622938414165)
                ·
                  refine ⟨249222628145808081309541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21266997601775622938414165 249222628145808081309541)
                  ·
                    rfl

theorem cell22_2184117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_2184117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184117 prefixEnd_2184117 := by exact prefixLift 2184117
  have htrace : WordTrace (prefixWord ++ tailWord_2184117) baseStart_2184117 baseEnd_2184117 := by
    simpa [prefixWord, tailWord_2184117, baseEnd_2184117] using wordTrace_append hprefix tailTrace_2184117
  have hstable : (prefixWord ++ tailWord_2184117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184117).length < 2 ^ (prefixWord ++ tailWord_2184117).sum := by decide
  have hdescent : baseEnd_2184117 < baseStart_2184117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184119 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 1, 4]
def baseStart_2184119 : Nat := 118140960795 + 2184119 * 2 ^ 59
def prefixEnd_2184119 : Nat := 4983230072969 + 3 ^ 40 * 2184119 * 2
def baseEnd_2184119 : Nat := 747668569078296905378617

theorem tailTrace_2184119 : CollatzResearch.WordTrace tailWord_2184119 prefixEnd_2184119 747668569078296905378617 := by
  unfold tailWord_2184119
  simp only [CollatzResearch.WordTrace]
  refine ⟨79661364374317355672843411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53107576249544903781895607 79661364374317355672843411)
  ·
    refine ⟨119492046561476033509265117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79661364374317355672843411 119492046561476033509265117)
    ·
      refine ⟨44809517460553512565974419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119492046561476033509265117 44809517460553512565974419)
      ·
        refine ⟨67214276190830268848961629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44809517460553512565974419 67214276190830268848961629)
        ·
          refine ⟨25205353571561350818360611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67214276190830268848961629 25205353571561350818360611)
          ·
            refine ⟨37808030357342026227540917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25205353571561350818360611 37808030357342026227540917)
            ·
              refine ⟨3544502846000814958831961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37808030357342026227540917 3544502846000814958831961)
              ·
                refine ⟨2658377134500611219123971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3544502846000814958831961 2658377134500611219123971)
                ·
                  refine ⟨3987565701750916828685957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2658377134500611219123971 3987565701750916828685957)
                  ·
                    refine ⟨747668569078296905378617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3987565701750916828685957 747668569078296905378617)
                    ·
                      rfl

theorem cell22_2184119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_2184119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184119 prefixEnd_2184119 := by exact prefixLift 2184119
  have htrace : WordTrace (prefixWord ++ tailWord_2184119) baseStart_2184119 baseEnd_2184119 := by
    simpa [prefixWord, tailWord_2184119, baseEnd_2184119] using wordTrace_append hprefix tailTrace_2184119
  have hstable : (prefixWord ++ tailWord_2184119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184119).length < 2 ^ (prefixWord ++ tailWord_2184119).sum := by decide
  have hdescent : baseEnd_2184119 < baseStart_2184119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184267 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 9]
def baseStart_2184267 : Nat := 118140960795 + 2184267 * 2 ^ 59
def prefixEnd_2184267 : Nat := 4983230072969 + 3 ^ 40 * 2184267 * 2
def baseEnd_2184267 : Nat := 747719232502873852678163

theorem tailTrace_2184267 : CollatzResearch.WordTrace tailWord_2184267 prefixEnd_2184267 747719232502873852678163 := by
  unfold tailWord_2184267
  simp only [CollatzResearch.WordTrace]
  refine ⟨79666762377781176949231055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53111174918520784632820703 79666762377781176949231055)
  ·
    refine ⟨119500143566671765423846583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79666762377781176949231055 119500143566671765423846583)
    ·
      refine ⟨179250215350007648135769875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119500143566671765423846583 179250215350007648135769875)
      ·
        refine ⟨268875323025011472203654813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179250215350007648135769875 268875323025011472203654813)
        ·
          refine ⟨100828246134379302076370555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268875323025011472203654813 100828246134379302076370555)
          ·
            refine ⟨151242369201568953114555833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100828246134379302076370555 151242369201568953114555833)
            ·
              refine ⟨113431776901176714835916875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151242369201568953114555833 113431776901176714835916875)
              ·
                refine ⟨170147665351765072253875313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113431776901176714835916875 170147665351765072253875313)
                ·
                  refine ⟨127610749013823804190406485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170147665351765072253875313 127610749013823804190406485)
                  ·
                    refine ⟨747719232502873852678163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127610749013823804190406485 747719232502873852678163)
                    ·
                      rfl

theorem cell22_2184267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_2184267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184267 prefixEnd_2184267 := by exact prefixLift 2184267
  have htrace : WordTrace (prefixWord ++ tailWord_2184267) baseStart_2184267 baseEnd_2184267 := by
    simpa [prefixWord, tailWord_2184267, baseEnd_2184267] using wordTrace_append hprefix tailTrace_2184267
  have hstable : (prefixWord ++ tailWord_2184267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184267).length < 2 ^ (prefixWord ++ tailWord_2184267).sum := by decide
  have hdescent : baseEnd_2184267 < baseStart_2184267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184301 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2184301 : Nat := 118140960795 + 2184301 * 2 ^ 59
def prefixEnd_2184301 : Nat := 4983230072969 + 3 ^ 40 * 2184301 * 2
def baseEnd_2184301 : Nat := 747730871397709097328059

theorem tailTrace_2184301 : CollatzResearch.WordTrace tailWord_2184301 prefixEnd_2184301 747730871397709097328059 := by
  unfold tailWord_2184301
  simp only [CollatzResearch.WordTrace]
  refine ⟨79668002459658000755968757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53112001639772000503979171 79668002459658000755968757)
  ·
    refine ⟨7468875230592937570872071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79668002459658000755968757 7468875230592937570872071)
    ·
      refine ⟨11203312845889406356308107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7468875230592937570872071 11203312845889406356308107)
      ·
        refine ⟨16804969268834109534462161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11203312845889406356308107 16804969268834109534462161)
        ·
          refine ⟨12603726951625582150846621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16804969268834109534462161 12603726951625582150846621)
          ·
            refine ⟨4726397606859593306567483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12603726951625582150846621 4726397606859593306567483)
            ·
              refine ⟨7089596410289389959851225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4726397606859593306567483 7089596410289389959851225)
              ·
                refine ⟨5317197307717042469888419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7089596410289389959851225 5317197307717042469888419)
                ·
                  refine ⟨7975795961575563704832629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5317197307717042469888419 7975795961575563704832629)
                  ·
                    refine ⟨747730871397709097328059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7975795961575563704832629 747730871397709097328059)
                    ·
                      rfl

theorem cell22_2184301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2184301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184301 prefixEnd_2184301 := by exact prefixLift 2184301
  have htrace : WordTrace (prefixWord ++ tailWord_2184301) baseStart_2184301 baseEnd_2184301 := by
    simpa [prefixWord, tailWord_2184301, baseEnd_2184301] using wordTrace_append hprefix tailTrace_2184301
  have hstable : (prefixWord ++ tailWord_2184301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184301).length < 2 ^ (prefixWord ++ tailWord_2184301).sum := by decide
  have hdescent : baseEnd_2184301 < baseStart_2184301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184350 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2184350 : Nat := 118140960795 + 2184350 * 2 ^ 59
def prefixEnd_2184350 : Nat := 4983230072969 + 3 ^ 40 * 2184350 * 2
def baseEnd_2184350 : Nat := 747747645099089302852909

theorem tailTrace_2184350 : CollatzResearch.WordTrace tailWord_2184350 prefixEnd_2184350 747747645099089302852909 := by
  unfold tailWord_2184350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9958723704560060265562813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53113193090986988083001669 9958723704560060265562813)
  ·
    refine ⟨3734521389210022599586055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9958723704560060265562813 3734521389210022599586055)
    ·
      refine ⟨5601782083815033899379083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3734521389210022599586055 5601782083815033899379083)
      ·
        refine ⟨8402673125722550849068625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5601782083815033899379083 8402673125722550849068625)
        ·
          refine ⟨6302004844291913136801469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8402673125722550849068625 6302004844291913136801469)
          ·
            refine ⟨2363251816609467426300551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6302004844291913136801469 2363251816609467426300551)
            ·
              refine ⟨3544877724914201139450827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363251816609467426300551 3544877724914201139450827)
              ·
                refine ⟨5317316587371301709176241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3544877724914201139450827 5317316587371301709176241)
                ·
                  refine ⟨3987987440528476281882181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5317316587371301709176241 3987987440528476281882181)
                  ·
                    refine ⟨747747645099089302852909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3987987440528476281882181 747747645099089302852909)
                    ·
                      rfl

theorem cell22_2184350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2184350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184350 prefixEnd_2184350 := by exact prefixLift 2184350
  have htrace : WordTrace (prefixWord ++ tailWord_2184350) baseStart_2184350 baseEnd_2184350 := by
    simpa [prefixWord, tailWord_2184350, baseEnd_2184350] using wordTrace_append hprefix tailTrace_2184350
  have hstable : (prefixWord ++ tailWord_2184350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184350).length < 2 ^ (prefixWord ++ tailWord_2184350).sum := by decide
  have hdescent : baseEnd_2184350 < baseStart_2184350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184380 : List Nat := [2, 2, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_2184380 : Nat := 118140960795 + 2184380 * 2 ^ 59
def prefixEnd_2184380 : Nat := 4983230072969 + 3 ^ 40 * 2184380 * 2
def baseEnd_2184380 : Nat := 747757914712179224602817

theorem tailTrace_2184380 : CollatzResearch.WordTrace tailWord_2184380 prefixEnd_2184380 747757914712179224602817 := by
  unfold tailWord_2184380
  simp only [CollatzResearch.WordTrace]
  refine ⟨39835441913185898624047297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53113922550914531498729729 39835441913185898624047297)
  ·
    refine ⟨29876581434889423968035473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39835441913185898624047297 29876581434889423968035473)
    ·
      refine ⟨22407436076167067976026605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29876581434889423968035473 22407436076167067976026605)
      ·
        refine ⟨8402788528562650491009977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22407436076167067976026605 8402788528562650491009977)
        ·
          refine ⟨6302091396421987868257483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8402788528562650491009977 6302091396421987868257483)
          ·
            refine ⟨9453137094632981802386225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6302091396421987868257483 9453137094632981802386225)
            ·
              refine ⟨7089852820974736351789669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9453137094632981802386225 7089852820974736351789669)
              ·
                refine ⟨1329347403932763065960563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7089852820974736351789669 1329347403932763065960563)
                ·
                  refine ⟨1994021105899144598940845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329347403932763065960563 1994021105899144598940845)
                  ·
                    refine ⟨747757914712179224602817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1994021105899144598940845 747757914712179224602817)
                    ·
                      rfl

theorem cell22_2184380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_2184380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184380 prefixEnd_2184380 := by exact prefixLift 2184380
  have htrace : WordTrace (prefixWord ++ tailWord_2184380) baseStart_2184380 baseEnd_2184380 := by
    simpa [prefixWord, tailWord_2184380, baseEnd_2184380] using wordTrace_append hprefix tailTrace_2184380
  have hstable : (prefixWord ++ tailWord_2184380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184380).length < 2 ^ (prefixWord ++ tailWord_2184380).sum := by decide
  have hdescent : baseEnd_2184380 < baseStart_2184380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184453 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_2184453 : Nat := 118140960795 + 2184453 * 2 ^ 59
def prefixEnd_2184453 : Nat := 4983230072969 + 3 ^ 40 * 2184453 * 2
def baseEnd_2184453 : Nat := 747782904104031367527593

theorem tailTrace_2184453 : CollatzResearch.WordTrace tailWord_2184453 prefixEnd_2184453 747782904104031367527593 := by
  unfold tailWord_2184453
  simp only [CollatzResearch.WordTrace]
  refine ⟨79673546355107330715502013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53115697570071553810334675 79673546355107330715502013)
  ·
    refine ⟨29877579883165249018313255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79673546355107330715502013 29877579883165249018313255)
    ·
      refine ⟨44816369824747873527469883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29877579883165249018313255 44816369824747873527469883)
      ·
        refine ⟨67224554737121810291204825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44816369824747873527469883 67224554737121810291204825)
        ·
          refine ⟨50418416052841357718403619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67224554737121810291204825 50418416052841357718403619)
          ·
            refine ⟨75627624079262036577605429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50418416052841357718403619 75627624079262036577605429)
            ·
              refine ⟨7090089757430815929150509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75627624079262036577605429 7090089757430815929150509)
              ·
                refine ⟨2658783659036555973431441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7090089757430815929150509 2658783659036555973431441)
                ·
                  refine ⟨1994087744277416980073581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658783659036555973431441 1994087744277416980073581)
                  ·
                    refine ⟨747782904104031367527593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1994087744277416980073581 747782904104031367527593)
                    ·
                      rfl

theorem cell22_2184453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_2184453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184453 prefixEnd_2184453 := by exact prefixLift 2184453
  have htrace : WordTrace (prefixWord ++ tailWord_2184453) baseStart_2184453 baseEnd_2184453 := by
    simpa [prefixWord, tailWord_2184453, baseEnd_2184453] using wordTrace_append hprefix tailTrace_2184453
  have hstable : (prefixWord ++ tailWord_2184453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184453).length < 2 ^ (prefixWord ++ tailWord_2184453).sum := by decide
  have hdescent : baseEnd_2184453 < baseStart_2184453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184526 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2184526 : Nat := 118140960795 + 2184526 * 2 ^ 59
def prefixEnd_2184526 : Nat := 4983230072969 + 3 ^ 40 * 2184526 * 2
def baseEnd_2184526 : Nat := 747807893495883510452369

theorem tailTrace_2184526 : CollatzResearch.WordTrace tailWord_2184526 prefixEnd_2184526 747807893495883510452369 := by
  unfold tailWord_2184526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959526110480358022863679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53117472589228576121939621 9959526110480358022863679)
  ·
    refine ⟨14939289165720537034295519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9959526110480358022863679 14939289165720537034295519)
    ·
      refine ⟨22408933748580805551443279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14939289165720537034295519 22408933748580805551443279)
      ·
        refine ⟨33613400622871208327164919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22408933748580805551443279 33613400622871208327164919)
        ·
          refine ⟨50420100934306812490747379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33613400622871208327164919 50420100934306812490747379)
          ·
            refine ⟨75630151401460218736121069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50420100934306812490747379 75630151401460218736121069)
            ·
              refine ⟨28361306775547582026045401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75630151401460218736121069 28361306775547582026045401)
              ·
                refine ⟨21270980081660686519534051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28361306775547582026045401 21270980081660686519534051)
                ·
                  refine ⟨31906470122491029779301077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21270980081660686519534051 31906470122491029779301077)
                  ·
                    refine ⟨747807893495883510452369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31906470122491029779301077 747807893495883510452369)
                    ·
                      rfl

theorem cell22_2184526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2184526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184526 prefixEnd_2184526 := by exact prefixLift 2184526
  have htrace : WordTrace (prefixWord ++ tailWord_2184526) baseStart_2184526 baseEnd_2184526 := by
    simpa [prefixWord, tailWord_2184526, baseEnd_2184526] using wordTrace_append hprefix tailTrace_2184526
  have hstable : (prefixWord ++ tailWord_2184526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184526).length < 2 ^ (prefixWord ++ tailWord_2184526).sum := by decide
  have hdescent : baseEnd_2184526 < baseStart_2184526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184532 : List Nat := [2, 4, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_2184532 : Nat := 118140960795 + 2184532 * 2 ^ 59
def prefixEnd_2184532 : Nat := 4983230072969 + 3 ^ 40 * 2184532 * 2
def baseEnd_2184532 : Nat := 747809947418501494802351

theorem tailTrace_2184532 : CollatzResearch.WordTrace tailWord_2184532 prefixEnd_2184532 747809947418501494802351 := by
  unfold tailWord_2184532
  simp only [CollatzResearch.WordTrace]
  refine ⟨39838213860910563603813925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53117618481214084805085233 39838213860910563603813925)
  ·
    refine ⟨7469665098920730675715111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39838213860910563603813925 7469665098920730675715111)
    ·
      refine ⟨11204497648381096013572667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7469665098920730675715111 11204497648381096013572667)
      ·
        refine ⟨16806746472571644020359001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11204497648381096013572667 16806746472571644020359001)
        ·
          refine ⟨12605059854428733015269251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16806746472571644020359001 12605059854428733015269251)
          ·
            refine ⟨18907589781643099522903877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12605059854428733015269251 18907589781643099522903877)
            ·
              refine ⟨3545173084058081160544477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18907589781643099522903877 3545173084058081160544477)
              ·
                refine ⟨1329439906521780435204179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3545173084058081160544477 1329439906521780435204179)
                ·
                  refine ⟨1994159859782670652806269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329439906521780435204179 1994159859782670652806269)
                  ·
                    refine ⟨747809947418501494802351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1994159859782670652806269 747809947418501494802351)
                    ·
                      rfl

theorem cell22_2184532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_2184532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184532 prefixEnd_2184532 := by exact prefixLift 2184532
  have htrace : WordTrace (prefixWord ++ tailWord_2184532) baseStart_2184532 baseEnd_2184532 := by
    simpa [prefixWord, tailWord_2184532, baseEnd_2184532] using wordTrace_append hprefix tailTrace_2184532
  have hstable : (prefixWord ++ tailWord_2184532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184532).length < 2 ^ (prefixWord ++ tailWord_2184532).sum := by decide
  have hdescent : baseEnd_2184532 < baseStart_2184532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184588 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_2184588 : Nat := 118140960795 + 2184588 * 2 ^ 59
def prefixEnd_2184588 : Nat := 4983230072969 + 3 ^ 40 * 2184588 * 2
def baseEnd_2184588 : Nat := 747829117362936015402179

theorem tailTrace_2184588 : CollatzResearch.WordTrace tailWord_2184588 prefixEnd_2184588 747829117362936015402179 := by
  unfold tailWord_2184588
  simp only [CollatzResearch.WordTrace]
  refine ⟨39839235104809124385833209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53118980139745499181110945 39839235104809124385833209)
  ·
    refine ⟨29879426328606843289374907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39839235104809124385833209 29879426328606843289374907)
    ·
      refine ⟨44819139492910264934062361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29879426328606843289374907 44819139492910264934062361)
      ·
        refine ⟨33614354619682698700546771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44819139492910264934062361 33614354619682698700546771)
        ·
          refine ⟨50421531929524048050820157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33614354619682698700546771 50421531929524048050820157)
          ·
            refine ⟨18908074473571518019057559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50421531929524048050820157 18908074473571518019057559)
            ·
              refine ⟨28362111710357277028586339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18908074473571518019057559 28362111710357277028586339)
              ·
                refine ⟨42543167565535915542879509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28362111710357277028586339 42543167565535915542879509)
                ·
                  refine ⟨1994210979634496041072477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42543167565535915542879509 1994210979634496041072477)
                  ·
                    refine ⟨747829117362936015402179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1994210979634496041072477 747829117362936015402179)
                    ·
                      rfl

theorem cell22_2184588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_2184588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184588 prefixEnd_2184588 := by exact prefixLift 2184588
  have htrace : WordTrace (prefixWord ++ tailWord_2184588) baseStart_2184588 baseEnd_2184588 := by
    simpa [prefixWord, tailWord_2184588, baseEnd_2184588] using wordTrace_append hprefix tailTrace_2184588
  have hstable : (prefixWord ++ tailWord_2184588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184588).length < 2 ^ (prefixWord ++ tailWord_2184588).sum := by decide
  have hdescent : baseEnd_2184588 < baseStart_2184588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184601 : List Nat := [1, 2, 1, 2, 1, 5, 10]
def baseStart_2184601 : Nat := 118140960795 + 2184601 * 2 ^ 59
def prefixEnd_2184601 : Nat := 4983230072969 + 3 ^ 40 * 2184601 * 2
def baseEnd_2184601 : Nat := 27697539538096604252857

theorem tailTrace_2184601 : CollatzResearch.WordTrace tailWord_2184601 prefixEnd_2184601 27697539538096604252857 := by
  unfold tailWord_2184601
  simp only [CollatzResearch.WordTrace]
  refine ⟨79678944358571151991889657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53119296239047434661259771 79678944358571151991889657)
  ·
    refine ⟨59759208268928363993917243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79678944358571151991889657 59759208268928363993917243)
    ·
      refine ⟨89638812403392545990875865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59759208268928363993917243 89638812403392545990875865)
      ·
        refine ⟨67229109302544409493156899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89638812403392545990875865 67229109302544409493156899)
        ·
          refine ⟨100843663953816614239735349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67229109302544409493156899 100843663953816614239735349)
          ·
            refine ⟨9454093495670307584975189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100843663953816614239735349 9454093495670307584975189)
            ·
              refine ⟨27697539538096604252857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9454093495670307584975189 27697539538096604252857)
              ·
                rfl

theorem cell22_2184601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 10].length) (baseStart_2184601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184601 prefixEnd_2184601 := by exact prefixLift 2184601
  have htrace : WordTrace (prefixWord ++ tailWord_2184601) baseStart_2184601 baseEnd_2184601 := by
    simpa [prefixWord, tailWord_2184601, baseEnd_2184601] using wordTrace_append hprefix tailTrace_2184601
  have hstable : (prefixWord ++ tailWord_2184601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184601).length < 2 ^ (prefixWord ++ tailWord_2184601).sum := by decide
  have hdescent : baseEnd_2184601 < baseStart_2184601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184605 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_2184605 : Nat := 118140960795 + 2184605 * 2 ^ 59
def prefixEnd_2184605 : Nat := 4983230072969 + 3 ^ 40 * 2184605 * 2
def baseEnd_2184605 : Nat := 747834936810353637727127

theorem tailTrace_2184605 : CollatzResearch.WordTrace tailWord_2184605 prefixEnd_2184605 747834936810353637727127 := by
  unfold tailWord_2184605
  simp only [CollatzResearch.WordTrace]
  refine ⟨79679090250556660675035269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53119393500371107116690179 79679090250556660675035269)
  ·
    refine ⟨14939829421979373876569113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79679090250556660675035269 14939829421979373876569113)
    ·
      refine ⟨11204872066484530407426835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14939829421979373876569113 11204872066484530407426835)
      ·
        refine ⟨16807308099726795611140253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11204872066484530407426835 16807308099726795611140253)
        ·
          refine ⟨6302740537397548354177595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16807308099726795611140253 6302740537397548354177595)
          ·
            refine ⟨9454110806096322531266393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6302740537397548354177595 9454110806096322531266393)
            ·
              refine ⟨7090583104572241898449795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9454110806096322531266393 7090583104572241898449795)
              ·
                refine ⟨10635874656858362847674693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7090583104572241898449795 10635874656858362847674693)
                ·
                  refine ⟨1994226498160943033939005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10635874656858362847674693 1994226498160943033939005)
                  ·
                    refine ⟨747834936810353637727127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1994226498160943033939005 747834936810353637727127)
                    ·
                      rfl

theorem cell22_2184605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_2184605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184605 prefixEnd_2184605 := by exact prefixLift 2184605
  have htrace : WordTrace (prefixWord ++ tailWord_2184605) baseStart_2184605 baseEnd_2184605 := by
    simpa [prefixWord, tailWord_2184605, baseEnd_2184605] using wordTrace_append hprefix tailTrace_2184605
  have hstable : (prefixWord ++ tailWord_2184605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184605).length < 2 ^ (prefixWord ++ tailWord_2184605).sum := by decide
  have hdescent : baseEnd_2184605 < baseStart_2184605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184607 : List Nat := [1, 1, 2, 5, 1, 3, 3, 2, 4]
def baseStart_2184607 : Nat := 118140960795 + 2184607 * 2 ^ 59
def prefixEnd_2184607 : Nat := 4983230072969 + 3 ^ 40 * 2184607 * 2
def baseEnd_2184607 : Nat := 249278540483742099725707

theorem tailTrace_2184607 : CollatzResearch.WordTrace tailWord_2184607 prefixEnd_2184607 249278540483742099725707 := by
  unfold tailWord_2184607
  simp only [CollatzResearch.WordTrace]
  refine ⟨79679163196549415016608075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53119442131032943344405383 79679163196549415016608075)
  ·
    refine ⟨119518744794824122524912113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79679163196549415016608075 119518744794824122524912113)
    ·
      refine ⟨89639058596118091893684085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119518744794824122524912113 89639058596118091893684085)
      ·
        refine ⟨8403661743386071115032883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89639058596118091893684085 8403661743386071115032883)
        ·
          refine ⟨12605492615079106672549325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8403661743386071115032883 12605492615079106672549325)
          ·
            refine ⟨4727059730654665002205997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12605492615079106672549325 4727059730654665002205997)
            ·
              refine ⟨1772647398995499375827249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4727059730654665002205997 1772647398995499375827249)
              ·
                refine ⟨1329485549246624531870437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772647398995499375827249 1329485549246624531870437)
                ·
                  refine ⟨249278540483742099725707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1329485549246624531870437 249278540483742099725707)
                  ·
                    rfl

theorem cell22_2184607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 4].length) (baseStart_2184607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184607 prefixEnd_2184607 := by exact prefixLift 2184607
  have htrace : WordTrace (prefixWord ++ tailWord_2184607) baseStart_2184607 baseEnd_2184607 := by
    simpa [prefixWord, tailWord_2184607, baseEnd_2184607] using wordTrace_append hprefix tailTrace_2184607
  have hstable : (prefixWord ++ tailWord_2184607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184607).length < 2 ^ (prefixWord ++ tailWord_2184607).sum := by decide
  have hdescent : baseEnd_2184607 < baseStart_2184607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184725 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 6]
def baseStart_2184725 : Nat := 118140960795 + 2184725 * 2 ^ 59
def prefixEnd_2184725 : Nat := 4983230072969 + 3 ^ 40 * 2184725 * 2
def baseEnd_2184725 : Nat := 249292005087571108242253

theorem tailTrace_2184725 : CollatzResearch.WordTrace tailWord_2184725 prefixEnd_2184725 249292005087571108242253 := by
  unfold tailWord_2184725
  simp only [CollatzResearch.WordTrace]
  refine ⟨79683467010121921169403629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53122311340081280779602419 79683467010121921169403629)
  ·
    refine ⟨29881300128795720438526361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79683467010121921169403629 29881300128795720438526361)
    ·
      refine ⟨22410975096596790328894771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29881300128795720438526361 22410975096596790328894771)
      ·
        refine ⟨33616462644895185493342157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22410975096596790328894771 33616462644895185493342157)
        ·
          refine ⟨12606173491835694560003309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33616462644895185493342157 12606173491835694560003309)
          ·
            refine ⟨4727315059438385460001241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12606173491835694560003309 4727315059438385460001241)
            ·
              refine ⟨3545486294578789095000931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4727315059438385460001241 3545486294578789095000931)
              ·
                refine ⟨5318229441868183642501397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3545486294578789095000931 5318229441868183642501397)
                ·
                  refine ⟨249292005087571108242253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5318229441868183642501397 249292005087571108242253)
                  ·
                    rfl

theorem cell22_2184725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_2184725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184725 prefixEnd_2184725 := by exact prefixLift 2184725
  have htrace : WordTrace (prefixWord ++ tailWord_2184725) baseStart_2184725 baseEnd_2184725 := by
    simpa [prefixWord, tailWord_2184725, baseEnd_2184725] using wordTrace_append hprefix tailTrace_2184725
  have hstable : (prefixWord ++ tailWord_2184725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184725).length < 2 ^ (prefixWord ++ tailWord_2184725).sum := by decide
  have hdescent : baseEnd_2184725 < baseStart_2184725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184744 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2184744 : Nat := 118140960795 + 2184744 * 2 ^ 59
def prefixEnd_2184744 : Nat := 4983230072969 + 3 ^ 40 * 2184744 * 2
def baseEnd_2184744 : Nat := 747882519351003608501701

theorem tailTrace_2184744 : CollatzResearch.WordTrace tailWord_2184744 prefixEnd_2184744 747882519351003608501701 := by
  unfold tailWord_2184744
  simp only [CollatzResearch.WordTrace]
  refine ⟨39842079998526543707172643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53122773331368724942896857 39842079998526543707172643)
  ·
    refine ⟨59763119997789815560758965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39842079998526543707172643 59763119997789815560758965)
    ·
      refine ⟨5602792499792795208821153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59763119997789815560758965 5602792499792795208821153)
      ·
        refine ⟨4202094374844596406615865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5602792499792795208821153 4202094374844596406615865)
        ·
          refine ⟨3151570781133447304961899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4202094374844596406615865 3151570781133447304961899)
          ·
            refine ⟨4727356171700170957442849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3151570781133447304961899 4727356171700170957442849)
            ·
              refine ⟨3545517128775128218082137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4727356171700170957442849 3545517128775128218082137)
              ·
                refine ⟨2659137846581346163561603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3545517128775128218082137 2659137846581346163561603)
                ·
                  refine ⟨3988706769872019245342405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659137846581346163561603 3988706769872019245342405)
                  ·
                    refine ⟨747882519351003608501701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3988706769872019245342405 747882519351003608501701)
                    ·
                      rfl

theorem cell22_2184744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2184744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184744 prefixEnd_2184744 := by exact prefixLift 2184744
  have htrace : WordTrace (prefixWord ++ tailWord_2184744) baseStart_2184744 baseEnd_2184744 := by
    simpa [prefixWord, tailWord_2184744, baseEnd_2184744] using wordTrace_append hprefix tailTrace_2184744
  have hstable : (prefixWord ++ tailWord_2184744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184744).length < 2 ^ (prefixWord ++ tailWord_2184744).sum := by decide
  have hdescent : baseEnd_2184744 < baseStart_2184744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184783 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 2, 6]
def baseStart_2184783 : Nat := 118140960795 + 2184783 * 2 ^ 59
def prefixEnd_2184783 : Nat := 4983230072969 + 3 ^ 40 * 2184783 * 2
def baseEnd_2184783 : Nat := 747895869848020506776581

theorem tailTrace_2184783 : CollatzResearch.WordTrace tailWord_2184783 prefixEnd_2184783 747895869848020506776581 := by
  unfold tailWord_2184783
  simp only [CollatzResearch.WordTrace]
  refine ⟨79685582443911797075015003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53123721629274531383343335 79685582443911797075015003)
  ·
    refine ⟨119528373665867695612522505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79685582443911797075015003 119528373665867695612522505)
    ·
      refine ⟨89646280249400771709391879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119528373665867695612522505 89646280249400771709391879)
      ·
        refine ⟨134469420374101157564087819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89646280249400771709391879 134469420374101157564087819)
        ·
          refine ⟨201704130561151736346131729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134469420374101157564087819 201704130561151736346131729)
          ·
            refine ⟨151278097920863802259598797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201704130561151736346131729 151278097920863802259598797)
            ·
              refine ⟨56729286720323925847349549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151278097920863802259598797 56729286720323925847349549)
              ·
                refine ⟨21273482520121472192756081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56729286720323925847349549 21273482520121472192756081)
                ·
                  refine ⟨15955111890091104144567061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21273482520121472192756081 15955111890091104144567061)
                  ·
                    refine ⟨747895869848020506776581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15955111890091104144567061 747895869848020506776581)
                    ·
                      rfl

theorem cell22_2184783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_2184783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184783 prefixEnd_2184783 := by exact prefixLift 2184783
  have htrace : WordTrace (prefixWord ++ tailWord_2184783) baseStart_2184783 baseEnd_2184783 := by
    simpa [prefixWord, tailWord_2184783, baseEnd_2184783] using wordTrace_append hprefix tailTrace_2184783
  have hstable : (prefixWord ++ tailWord_2184783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184783).length < 2 ^ (prefixWord ++ tailWord_2184783).sum := by decide
  have hdescent : baseEnd_2184783 < baseStart_2184783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184836 : List Nat := [2, 3, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_2184836 : Nat := 118140960795 + 2184836 * 2 ^ 59
def prefixEnd_2184836 : Nat := 4983230072969 + 3 ^ 40 * 2184836 * 2
def baseEnd_2184836 : Nat := 747914012831146035201419

theorem tailTrace_2184836 : CollatzResearch.WordTrace tailWord_2184836 prefixEnd_2184836 747914012831146035201419 := by
  unfold tailWord_2184836
  simp only [CollatzResearch.WordTrace]
  refine ⟨39843757756359893563347181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53125010341813191417796241 39843757756359893563347181)
  ·
    refine ⟨14941409158634960086255193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39843757756359893563347181 14941409158634960086255193)
    ·
      refine ⟨11206056868976220064691395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14941409158634960086255193 11206056868976220064691395)
      ·
        refine ⟨16809085303464330097037093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11206056868976220064691395 16809085303464330097037093)
        ·
          refine ⟨3151703494399561893194455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16809085303464330097037093 3151703494399561893194455)
          ·
            refine ⟨4727555241599342839791683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3151703494399561893194455 4727555241599342839791683)
            ·
              refine ⟨7091332862399014259687525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4727555241599342839791683 7091332862399014259687525)
              ·
                refine ⟨1329624911699815173691411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7091332862399014259687525 1329624911699815173691411)
                ·
                  refine ⟨1994437367549722760537117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329624911699815173691411 1994437367549722760537117)
                  ·
                    refine ⟨747914012831146035201419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1994437367549722760537117 747914012831146035201419)
                    ·
                      rfl

theorem cell22_2184836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_2184836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184836 prefixEnd_2184836 := by exact prefixLift 2184836
  have htrace : WordTrace (prefixWord ++ tailWord_2184836) baseStart_2184836 baseEnd_2184836 := by
    simpa [prefixWord, tailWord_2184836, baseEnd_2184836] using wordTrace_append hprefix tailTrace_2184836
  have hstable : (prefixWord ++ tailWord_2184836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184836).length < 2 ^ (prefixWord ++ tailWord_2184836).sum := by decide
  have hdescent : baseEnd_2184836 < baseStart_2184836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184894 : List Nat := [4, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_2184894 : Nat := 118140960795 + 2184894 * 2 ^ 59
def prefixEnd_2184894 : Nat := 4983230072969 + 3 ^ 40 * 2184894 * 2
def baseEnd_2184894 : Nat := 249311289138817739083747

theorem tailTrace_2184894 : CollatzResearch.WordTrace tailWord_2184894 prefixEnd_2184894 249311289138817739083747 := by
  unfold tailWord_2184894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961203868313707879038217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53126420631006442021537157 9961203868313707879038217)
  ·
    refine ⟨7470902901235280909278663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9961203868313707879038217 7470902901235280909278663)
    ·
      refine ⟨11206354351852921363917995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7470902901235280909278663 11206354351852921363917995)
      ·
        refine ⟨16809531527779382045876993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11206354351852921363917995 16809531527779382045876993)
        ·
          refine ⟨12607148645834536534407745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16809531527779382045876993 12607148645834536534407745)
          ·
            refine ⟨9455361484375902400805809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12607148645834536534407745 9455361484375902400805809)
            ·
              refine ⟨7091521113281926800604357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9455361484375902400805809 7091521113281926800604357)
              ·
                refine ⟨1329660208740361275113317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7091521113281926800604357 1329660208740361275113317)
                ·
                  refine ⟨249311289138817739083747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1329660208740361275113317 249311289138817739083747)
                  ·
                    rfl

theorem cell22_2184894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_2184894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184894 prefixEnd_2184894 := by exact prefixLift 2184894
  have htrace : WordTrace (prefixWord ++ tailWord_2184894) baseStart_2184894 baseEnd_2184894 := by
    simpa [prefixWord, tailWord_2184894, baseEnd_2184894] using wordTrace_append hprefix tailTrace_2184894
  have hstable : (prefixWord ++ tailWord_2184894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184894).length < 2 ^ (prefixWord ++ tailWord_2184894).sum := by decide
  have hdescent : baseEnd_2184894 < baseStart_2184894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184920 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_2184920 : Nat := 118140960795 + 2184920 * 2 ^ 59
def prefixEnd_2184920 : Nat := 4983230072969 + 3 ^ 40 * 2184920 * 2
def baseEnd_2184920 : Nat := 747942767747797816101161

theorem tailTrace_2184920 : CollatzResearch.WordTrace tailWord_2184920 prefixEnd_2184920 747942767747797816101161 := by
  unfold tailWord_2184920
  simp only [CollatzResearch.WordTrace]
  refine ⟨39845289622207734736376107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53127052829610312981834809 39845289622207734736376107)
  ·
    refine ⟨59767934433311602104564161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39845289622207734736376107 59767934433311602104564161)
    ·
      refine ⟨44825950824983701578423121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59767934433311602104564161 44825950824983701578423121)
      ·
        refine ⟨33619463118737776183817341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44825950824983701578423121 33619463118737776183817341)
        ·
          refine ⟨12607298669526666068931503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33619463118737776183817341 12607298669526666068931503)
          ·
            refine ⟨18910948004289999103397255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12607298669526666068931503 18910948004289999103397255)
            ·
              refine ⟨28366422006434998655095883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18910948004289999103397255 28366422006434998655095883)
              ·
                refine ⟨42549633009652497982643825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28366422006434998655095883 42549633009652497982643825)
                ·
                  refine ⟨31912224757239373486982869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42549633009652497982643825 31912224757239373486982869)
                  ·
                    refine ⟨747942767747797816101161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31912224757239373486982869 747942767747797816101161)
                    ·
                      rfl

theorem cell22_2184920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_2184920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184920 prefixEnd_2184920 := by exact prefixLift 2184920
  have htrace : WordTrace (prefixWord ++ tailWord_2184920) baseStart_2184920 baseEnd_2184920 := by
    simpa [prefixWord, tailWord_2184920, baseEnd_2184920] using wordTrace_append hprefix tailTrace_2184920
  have hstable : (prefixWord ++ tailWord_2184920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184920).length < 2 ^ (prefixWord ++ tailWord_2184920).sum := by decide
  have hdescent : baseEnd_2184920 < baseStart_2184920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184922 : List Nat := [3, 1, 1, 2, 2, 3, 4, 6]
def baseStart_2184922 : Nat := 118140960795 + 2184922 * 2 ^ 59
def prefixEnd_2184922 : Nat := 4983230072969 + 3 ^ 40 * 2184922 * 2
def baseEnd_2184922 : Nat := 83104828043185608616795

theorem tailTrace_2184922 : CollatzResearch.WordTrace tailWord_2184922 prefixEnd_2184922 83104828043185608616795 := by
  unfold tailWord_2184922
  simp only [CollatzResearch.WordTrace]
  refine ⟨19922663047602055953581255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53127101460272149209550013 19922663047602055953581255)
  ·
    refine ⟨29883994571403083930371883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19922663047602055953581255 29883994571403083930371883)
    ·
      refine ⟨44825991857104625895557825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29883994571403083930371883 44825991857104625895557825)
      ·
        refine ⟨33619493892828469421668369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44825991857104625895557825 33619493892828469421668369)
        ·
          refine ⟨25214620419621352066251277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33619493892828469421668369 25214620419621352066251277)
          ·
            refine ⟨9455482657358007024844229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25214620419621352066251277 9455482657358007024844229)
            ·
              refine ⟨1772902998254626317158293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9455482657358007024844229 1772902998254626317158293)
              ·
                refine ⟨83104828043185608616795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1772902998254626317158293 83104828043185608616795)
                ·
                  rfl

theorem cell22_2184922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_2184922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2184922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2184922 prefixEnd_2184922 := by exact prefixLift 2184922
  have htrace : WordTrace (prefixWord ++ tailWord_2184922) baseStart_2184922 baseEnd_2184922 := by
    simpa [prefixWord, tailWord_2184922, baseEnd_2184922] using wordTrace_append hprefix tailTrace_2184922
  have hstable : (prefixWord ++ tailWord_2184922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184922).length < 2 ^ (prefixWord ++ tailWord_2184922).sum := by decide
  have hdescent : baseEnd_2184922 < baseStart_2184922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185027 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 1, 5]
def baseStart_2185027 : Nat := 118140960795 + 2185027 * 2 ^ 59
def prefixEnd_2185027 : Nat := 4983230072969 + 3 ^ 40 * 2185027 * 2
def baseEnd_2185027 : Nat := 747979396034485203675833

theorem tailTrace_2185027 : CollatzResearch.WordTrace tailWord_2185027 prefixEnd_2185027 747979396034485203675833 := by
  unfold tailWord_2185027
  simp only [CollatzResearch.WordTrace]
  refine ⟨79694481855027826746897335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53129654570018551164598223 79694481855027826746897335)
  ·
    refine ⟨119541722782541740120346003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79694481855027826746897335 119541722782541740120346003)
    ·
      refine ⟨179312584173812610180519005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119541722782541740120346003 179312584173812610180519005)
      ·
        refine ⟨67242219065179728817694627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179312584173812610180519005 67242219065179728817694627)
        ·
          refine ⟨100863328597769593226541941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67242219065179728817694627 100863328597769593226541941)
          ·
            refine ⟨9455937056040899364988307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100863328597769593226541941 9455937056040899364988307)
            ·
              refine ⟨14183905584061349047482461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9455937056040899364988307 14183905584061349047482461)
              ·
                refine ⟨5318964594023005892805923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14183905584061349047482461 5318964594023005892805923)
                ·
                  refine ⟨7978446891034508839208885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5318964594023005892805923 7978446891034508839208885)
                  ·
                    refine ⟨747979396034485203675833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7978446891034508839208885 747979396034485203675833)
                    ·
                      rfl

theorem cell22_2185027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_2185027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185027 prefixEnd_2185027 := by exact prefixLift 2185027
  have htrace : WordTrace (prefixWord ++ tailWord_2185027) baseStart_2185027 baseEnd_2185027 := by
    simpa [prefixWord, tailWord_2185027, baseEnd_2185027] using wordTrace_append hprefix tailTrace_2185027
  have hstable : (prefixWord ++ tailWord_2185027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185027).length < 2 ^ (prefixWord ++ tailWord_2185027).sum := by decide
  have hdescent : baseEnd_2185027 < baseStart_2185027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185044 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2185044 : Nat := 118140960795 + 2185044 * 2 ^ 59
def prefixEnd_2185044 : Nat := 4983230072969 + 3 ^ 40 * 2185044 * 2
def baseEnd_2185044 : Nat := 747985215481902826000781

theorem tailTrace_2185044 : CollatzResearch.WordTrace tailWord_2185044 prefixEnd_2185044 747985215481902826000781 := by
  unfold tailWord_2185044
  simp only [CollatzResearch.WordTrace]
  refine ⟨39847550947983119325133093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53130067930644159100177457 39847550947983119325133093)
  ·
    refine ⟨7471415802746834873462455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39847550947983119325133093 7471415802746834873462455)
    ·
      refine ⟨11207123704120252310193683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7471415802746834873462455 11207123704120252310193683)
      ·
        refine ⟨16810685556180378465290525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11207123704120252310193683 16810685556180378465290525)
        ·
          refine ⟨6304007083567641924483947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16810685556180378465290525 6304007083567641924483947)
          ·
            refine ⟨9456010625351462886725921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6304007083567641924483947 9456010625351462886725921)
            ·
              refine ⟨7092007969013597165044441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9456010625351462886725921 7092007969013597165044441)
              ·
                refine ⟨5319005976760197873783331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7092007969013597165044441 5319005976760197873783331)
                ·
                  refine ⟨7978508965140296810674997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5319005976760197873783331 7978508965140296810674997)
                  ·
                    refine ⟨747985215481902826000781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7978508965140296810674997 747985215481902826000781)
                    ·
                      rfl

theorem cell22_2185044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2185044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185044 prefixEnd_2185044 := by exact prefixLift 2185044
  have htrace : WordTrace (prefixWord ++ tailWord_2185044) baseStart_2185044 baseEnd_2185044 := by
    simpa [prefixWord, tailWord_2185044, baseEnd_2185044] using wordTrace_append hprefix tailTrace_2185044
  have hstable : (prefixWord ++ tailWord_2185044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185044).length < 2 ^ (prefixWord ++ tailWord_2185044).sum := by decide
  have hdescent : baseEnd_2185044 < baseStart_2185044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185078 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2185078 : Nat := 118140960795 + 2185078 * 2 ^ 59
def prefixEnd_2185078 : Nat := 4983230072969 + 3 ^ 40 * 2185078 * 2
def baseEnd_2185078 : Nat := 747996854376738070650677

theorem tailTrace_2185078 : CollatzResearch.WordTrace tailWord_2185078 prefixEnd_2185078 747996854376738070650677 := by
  unfold tailWord_2185078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981021373615191403562743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53130894651895374971335925 4981021373615191403562743)
  ·
    refine ⟨7471532060422787105344115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4981021373615191403562743 7471532060422787105344115)
    ·
      refine ⟨11207298090634180658016173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7471532060422787105344115 11207298090634180658016173)
      ·
        refine ⟨4202736783987817746756065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11207298090634180658016173 4202736783987817746756065)
        ·
          refine ⟨3152052587990863310067049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4202736783987817746756065 3152052587990863310067049)
          ·
            refine ⟨2364039440993147482550287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152052587990863310067049 2364039440993147482550287)
            ·
              refine ⟨3546059161489721223825431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364039440993147482550287 3546059161489721223825431)
              ·
                refine ⟨5319088742234581835738147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546059161489721223825431 5319088742234581835738147)
                ·
                  refine ⟨7978633113351872753607221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5319088742234581835738147 7978633113351872753607221)
                  ·
                    refine ⟨747996854376738070650677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7978633113351872753607221 747996854376738070650677)
                    ·
                      rfl

theorem cell22_2185078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2185078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185078 prefixEnd_2185078 := by exact prefixLift 2185078
  have htrace : WordTrace (prefixWord ++ tailWord_2185078) baseStart_2185078 baseEnd_2185078 := by
    simpa [prefixWord, tailWord_2185078, baseEnd_2185078] using wordTrace_append hprefix tailTrace_2185078
  have hstable : (prefixWord ++ tailWord_2185078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185078).length < 2 ^ (prefixWord ++ tailWord_2185078).sum := by decide
  have hdescent : baseEnd_2185078 < baseStart_2185078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185110 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2185110 : Nat := 118140960795 + 2185110 * 2 ^ 59
def prefixEnd_2185110 : Nat := 4983230072969 + 3 ^ 40 * 2185110 * 2
def baseEnd_2185110 : Nat := 748007808630700653850579

theorem tailTrace_2185110 : CollatzResearch.WordTrace tailWord_2185110 prefixEnd_2185110 748007808630700653850579 := by
  unfold tailWord_2185110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981094319607945745135549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53131672742484754614779189 4981094319607945745135549)
  ·
    refine ⟨1867910369852979654425831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4981094319607945745135549 1867910369852979654425831)
    ·
      refine ⟨2801865554779469481638747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1867910369852979654425831 2801865554779469481638747)
      ·
        refine ⟨4202798332169204222458121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801865554779469481638747 4202798332169204222458121)
        ·
          refine ⟨3152098749126903166843591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4202798332169204222458121 3152098749126903166843591)
          ·
            refine ⟨4728148123690354750265387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152098749126903166843591 4728148123690354750265387)
            ·
              refine ⟨7092222185535532125398081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728148123690354750265387 7092222185535532125398081)
              ·
                refine ⟨5319166639151649094048561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7092222185535532125398081 5319166639151649094048561)
                ·
                  refine ⟨3989374979363736820536421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5319166639151649094048561 3989374979363736820536421)
                  ·
                    refine ⟨748007808630700653850579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3989374979363736820536421 748007808630700653850579)
                    ·
                      rfl

theorem cell22_2185110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2185110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185110 prefixEnd_2185110 := by exact prefixLift 2185110
  have htrace : WordTrace (prefixWord ++ tailWord_2185110) baseStart_2185110 baseEnd_2185110 := by
    simpa [prefixWord, tailWord_2185110, baseEnd_2185110] using wordTrace_append hprefix tailTrace_2185110
  have hstable : (prefixWord ++ tailWord_2185110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185110).length < 2 ^ (prefixWord ++ tailWord_2185110).sum := by decide
  have hdescent : baseEnd_2185110 < baseStart_2185110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185174 : List Nat := [5, 2, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2185174 : Nat := 118140960795 + 2185174 * 2 ^ 59
def prefixEnd_2185174 : Nat := 4983230072969 + 3 ^ 40 * 2185174 * 2
def baseEnd_2185174 : Nat := 748029717138625820250383

theorem tailTrace_2185174 : CollatzResearch.WordTrace tailWord_2185174 prefixEnd_2185174 748029717138625820250383 := by
  unfold tailWord_2185174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981240211593454428281161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53133228923663513901665717 4981240211593454428281161)
  ·
    refine ⟨3735930158695090821210871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4981240211593454428281161 3735930158695090821210871)
    ·
      refine ⟨5603895238042636231816307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3735930158695090821210871 5603895238042636231816307)
      ·
        refine ⟨8405842857063954347724461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5603895238042636231816307 8405842857063954347724461)
        ·
          refine ⟨3152191071398982880396673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8405842857063954347724461 3152191071398982880396673)
          ·
            refine ⟨2364143303549237160297505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152191071398982880396673 2364143303549237160297505)
            ·
              refine ⟨1773107477661927870223129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364143303549237160297505 1773107477661927870223129)
              ·
                refine ⟨1329830608246445902667347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773107477661927870223129 1329830608246445902667347)
                ·
                  refine ⟨1994745912369668854001021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329830608246445902667347 1994745912369668854001021)
                  ·
                    refine ⟨748029717138625820250383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1994745912369668854001021 748029717138625820250383)
                    ·
                      rfl

theorem cell22_2185174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2185174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185174 prefixEnd_2185174 := by exact prefixLift 2185174
  have htrace : WordTrace (prefixWord ++ tailWord_2185174) baseStart_2185174 baseEnd_2185174 := by
    simpa [prefixWord, tailWord_2185174, baseEnd_2185174] using wordTrace_append hprefix tailTrace_2185174
  have hstable : (prefixWord ++ tailWord_2185174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185174).length < 2 ^ (prefixWord ++ tailWord_2185174).sum := by decide
  have hdescent : baseEnd_2185174 < baseStart_2185174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185194 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2185194 : Nat := 118140960795 + 2185194 * 2 ^ 59
def prefixEnd_2185194 : Nat := 4983230072969 + 3 ^ 40 * 2185194 * 2
def baseEnd_2185194 : Nat := 748036563547352434750321

theorem tailTrace_2185194 : CollatzResearch.WordTrace tailWord_2185194 prefixEnd_2185194 748036563547352434750321 := by
  unfold tailWord_2185194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19925143211355703567056659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53133715230281876178817757 19925143211355703567056659)
  ·
    refine ⟨29887714817033555350584989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19925143211355703567056659 29887714817033555350584989)
    ·
      refine ⟨11207893056387583256469371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29887714817033555350584989 11207893056387583256469371)
      ·
        refine ⟨16811839584581374884704057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11207893056387583256469371 16811839584581374884704057)
        ·
          refine ⟨12608879688436031163528043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16811839584581374884704057 12608879688436031163528043)
          ·
            refine ⟨18913319532654046745292065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12608879688436031163528043 18913319532654046745292065)
            ·
              refine ⟨14184989649490535058969049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18913319532654046745292065 14184989649490535058969049)
              ·
                refine ⟨10638742237117901294226787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14184989649490535058969049 10638742237117901294226787)
                ·
                  refine ⟨15958113355676851941340181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10638742237117901294226787 15958113355676851941340181)
                  ·
                    refine ⟨748036563547352434750321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15958113355676851941340181 748036563547352434750321)
                    ·
                      rfl

theorem cell22_2185194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2185194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185194 prefixEnd_2185194 := by exact prefixLift 2185194
  have htrace : WordTrace (prefixWord ++ tailWord_2185194) baseStart_2185194 baseEnd_2185194 := by
    simpa [prefixWord, tailWord_2185194, baseEnd_2185194] using wordTrace_append hprefix tailTrace_2185194
  have hstable : (prefixWord ++ tailWord_2185194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185194).length < 2 ^ (prefixWord ++ tailWord_2185194).sum := by decide
  have hdescent : baseEnd_2185194 < baseStart_2185194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185258 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2185258 : Nat := 118140960795 + 2185258 * 2 ^ 59
def prefixEnd_2185258 : Nat := 4983230072969 + 3 ^ 40 * 2185258 * 2
def baseEnd_2185258 : Nat := 748058472055277601150125

theorem tailTrace_2185258 : CollatzResearch.WordTrace tailWord_2185258 prefixEnd_2185258 748058472055277601150125 := by
  unfold tailWord_2185258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19925726779297738299639107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53135271411460635465704285 19925726779297738299639107)
  ·
    refine ⟨29888590168946607449458661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19925726779297738299639107 29888590168946607449458661)
    ·
      refine ⟨5604110656677488896773499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29888590168946607449458661 5604110656677488896773499)
      ·
        refine ⟨8406165985016233345160249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5604110656677488896773499 8406165985016233345160249)
        ·
          refine ⟨6304624488762175008870187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8406165985016233345160249 6304624488762175008870187)
          ·
            refine ⟨9456936733143262513305281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6304624488762175008870187 9456936733143262513305281)
            ·
              refine ⟨7092702549857446884978961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9456936733143262513305281 7092702549857446884978961)
              ·
                refine ⟨5319526912393085163734221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7092702549857446884978961 5319526912393085163734221)
                ·
                  refine ⟨1994822592147406936400333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5319526912393085163734221 1994822592147406936400333)
                  ·
                    refine ⟨748058472055277601150125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1994822592147406936400333 748058472055277601150125)
                    ·
                      rfl

theorem cell22_2185258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2185258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185258 prefixEnd_2185258 := by exact prefixLift 2185258
  have htrace : WordTrace (prefixWord ++ tailWord_2185258) baseStart_2185258 baseEnd_2185258 := by
    simpa [prefixWord, tailWord_2185258, baseEnd_2185258] using wordTrace_append hprefix tailTrace_2185258
  have hstable : (prefixWord ++ tailWord_2185258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185258).length < 2 ^ (prefixWord ++ tailWord_2185258).sum := by decide
  have hdescent : baseEnd_2185258 < baseStart_2185258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185269 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2185269 : Nat := 118140960795 + 2185269 * 2 ^ 59
def prefixEnd_2185269 : Nat := 4983230072969 + 3 ^ 40 * 2185269 * 2
def baseEnd_2185269 : Nat := 748062237580077239125091

theorem tailTrace_2185269 : CollatzResearch.WordTrace tailWord_2185269 prefixEnd_2185269 748062237580077239125091 := by
  unfold tailWord_2185269
  simp only [CollatzResearch.WordTrace]
  refine ⟨79703308320151102077206861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53135538880100734718137907 79703308320151102077206861)
  ·
    refine ⟨29888740620056663278952573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79703308320151102077206861 29888740620056663278952573)
    ·
      refine ⟨11208277732521248729607215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29888740620056663278952573 11208277732521248729607215)
      ·
        refine ⟨16812416598781873094410823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11208277732521248729607215 16812416598781873094410823)
        ·
          refine ⟨25218624898172809641616235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16812416598781873094410823 25218624898172809641616235)
          ·
            refine ⟨37827937347259214462424353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25218624898172809641616235 37827937347259214462424353)
            ·
              refine ⟨28370953010444410846818265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37827937347259214462424353 28370953010444410846818265)
              ·
                refine ⟨21278214757833308135113699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28370953010444410846818265 21278214757833308135113699)
                ·
                  refine ⟨31917322136749962202670549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21278214757833308135113699 31917322136749962202670549)
                  ·
                    refine ⟨748062237580077239125091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31917322136749962202670549 748062237580077239125091)
                    ·
                      rfl

theorem cell22_2185269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2185269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185269 prefixEnd_2185269 := by exact prefixLift 2185269
  have htrace : WordTrace (prefixWord ++ tailWord_2185269) baseStart_2185269 baseEnd_2185269 := by
    simpa [prefixWord, tailWord_2185269, baseEnd_2185269] using wordTrace_append hprefix tailTrace_2185269
  have hstable : (prefixWord ++ tailWord_2185269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185269).length < 2 ^ (prefixWord ++ tailWord_2185269).sum := by decide
  have hdescent : baseEnd_2185269 < baseStart_2185269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185380 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_2185380 : Nat := 118140960795 + 2185380 * 2 ^ 59
def prefixEnd_2185380 : Nat := 4983230072969 + 3 ^ 40 * 2185380 * 2
def baseEnd_2185380 : Nat := 748100235148509949599751

theorem tailTrace_2185380 : CollatzResearch.WordTrace tailWord_2185380 prefixEnd_2185380 748100235148509949599751 := by
  unfold tailWord_2185380
  simp only [CollatzResearch.WordTrace]
  refine ⟨39853678411374484017248797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53138237881832645356331729 39853678411374484017248797)
  ·
    refine ⟨14945129404265431506468299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39853678411374484017248797 14945129404265431506468299)
    ·
      refine ⟨22417694106398147259702449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14945129404265431506468299 22417694106398147259702449)
      ·
        refine ⟨16813270579798610444776837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22417694106398147259702449 16813270579798610444776837)
        ·
          refine ⟨3152488233712239458395657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16813270579798610444776837 3152488233712239458395657)
          ·
            refine ⟨2364366175284179593796743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152488233712239458395657 2364366175284179593796743)
            ·
              refine ⟨3546549262926269390695115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364366175284179593796743 3546549262926269390695115)
              ·
                refine ⟨5319823894389404086042673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546549262926269390695115 5319823894389404086042673)
                ·
                  refine ⟨3989867920792053064532005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5319823894389404086042673 3989867920792053064532005)
                  ·
                    refine ⟨748100235148509949599751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3989867920792053064532005 748100235148509949599751)
                    ·
                      rfl

theorem cell22_2185380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_2185380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185380 prefixEnd_2185380 := by exact prefixLift 2185380
  have htrace : WordTrace (prefixWord ++ tailWord_2185380) baseStart_2185380 baseEnd_2185380 := by
    simpa [prefixWord, tailWord_2185380, baseEnd_2185380] using wordTrace_append hprefix tailTrace_2185380
  have hstable : (prefixWord ++ tailWord_2185380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185380).length < 2 ^ (prefixWord ++ tailWord_2185380).sum := by decide
  have hdescent : baseEnd_2185380 < baseStart_2185380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185423 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 5]
def baseStart_2185423 : Nat := 118140960795 + 2185423 * 2 ^ 59
def prefixEnd_2185423 : Nat := 4983230072969 + 3 ^ 40 * 2185423 * 2
def baseEnd_2185423 : Nat := 249371651642424056924873

theorem tailTrace_2185423 : CollatzResearch.WordTrace tailWord_2185423 prefixEnd_2185423 249371651642424056924873 := by
  unfold tailWord_2185423
  simp only [CollatzResearch.WordTrace]
  refine ⟨79708925161593186378312923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53139283441062124252208615 79708925161593186378312923)
  ·
    refine ⟨119563387742389779567469385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79708925161593186378312923 119563387742389779567469385)
    ·
      refine ⟨89672540806792334675602039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119563387742389779567469385 89672540806792334675602039)
      ·
        refine ⟨134508811210188502013403059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89672540806792334675602039 134508811210188502013403059)
        ·
          refine ⟨201763216815282753020104589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134508811210188502013403059 201763216815282753020104589)
          ·
            refine ⟨75661206305731032382539221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201763216815282753020104589 75661206305731032382539221)
            ·
              refine ⟨1773309522790571071465763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75661206305731032382539221 1773309522790571071465763)
              ·
                refine ⟨2659964284185856607198645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773309522790571071465763 2659964284185856607198645)
                ·
                  refine ⟨249371651642424056924873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2659964284185856607198645 249371651642424056924873)
                  ·
                    rfl

theorem cell22_2185423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 5].length) (baseStart_2185423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185423 prefixEnd_2185423 := by exact prefixLift 2185423
  have htrace : WordTrace (prefixWord ++ tailWord_2185423) baseStart_2185423 baseEnd_2185423 := by
    simpa [prefixWord, tailWord_2185423, baseEnd_2185423] using wordTrace_append hprefix tailTrace_2185423
  have hstable : (prefixWord ++ tailWord_2185423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185423).length < 2 ^ (prefixWord ++ tailWord_2185423).sum := by decide
  have hdescent : baseEnd_2185423 < baseStart_2185423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185468 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 6]
def baseStart_2185468 : Nat := 118140960795 + 2185468 * 2 ^ 59
def prefixEnd_2185468 : Nat := 4983230072969 + 3 ^ 40 * 2185468 * 2
def baseEnd_2185468 : Nat := 249376786448969017799827

theorem tailTrace_2185468 : CollatzResearch.WordTrace tailWord_2185468 prefixEnd_2185468 249376786448969017799827 := by
  unfold tailWord_2185468
  simp only [CollatzResearch.WordTrace]
  refine ⟨39855283223215079531850529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53140377630953439375800705 39855283223215079531850529)
  ·
    refine ⟨29891462417411309648887897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39855283223215079531850529 29891462417411309648887897)
    ·
      refine ⟨22418596813058482236665923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29891462417411309648887897 22418596813058482236665923)
      ·
        refine ⟨33627895219587723354998885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22418596813058482236665923 33627895219587723354998885)
        ·
          refine ⟨6305230353672698129062291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33627895219587723354998885 6305230353672698129062291)
          ·
            refine ⟨9457845530509047193593437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6305230353672698129062291 9457845530509047193593437)
            ·
              refine ⟨3546692073940892697597539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9457845530509047193593437 3546692073940892697597539)
              ·
                refine ⟨5320038110911339046396309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546692073940892697597539 5320038110911339046396309)
                ·
                  refine ⟨249376786448969017799827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5320038110911339046396309 249376786448969017799827)
                  ·
                    rfl

theorem cell22_2185468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_2185468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185468 prefixEnd_2185468 := by exact prefixLift 2185468
  have htrace : WordTrace (prefixWord ++ tailWord_2185468) baseStart_2185468 baseEnd_2185468 := by
    simpa [prefixWord, tailWord_2185468, baseEnd_2185468] using wordTrace_append hprefix tailTrace_2185468
  have hstable : (prefixWord ++ tailWord_2185468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185468).length < 2 ^ (prefixWord ++ tailWord_2185468).sum := by decide
  have hdescent : baseEnd_2185468 < baseStart_2185468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185496 : List Nat := [2, 1, 2, 3, 1, 2, 1, 10]
def baseStart_2185496 : Nat := 118140960795 + 2185496 * 2 ^ 59
def prefixEnd_2185496 : Nat := 4983230072969 + 3 ^ 40 * 2185496 * 2
def baseEnd_2185496 : Nat := 83126660479902701522155

theorem tailTrace_2185496 : CollatzResearch.WordTrace tailWord_2185496 prefixEnd_2185496 83126660479902701522155 := by
  unfold tailWord_2185496
  simp only [CollatzResearch.WordTrace]
  refine ⟨39855793845164359922860171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53141058460219146563813561 39855793845164359922860171)
  ·
    refine ⟨59783690767746539884290257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39855793845164359922860171 59783690767746539884290257)
    ·
      refine ⟨44837768075809904913217693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59783690767746539884290257 44837768075809904913217693)
      ·
        refine ⟨16814163028428714342456635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44837768075809904913217693 16814163028428714342456635)
        ·
          refine ⟨25221244542643071513684953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16814163028428714342456635 25221244542643071513684953)
          ·
            refine ⟨18915933406982303635263715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25221244542643071513684953 18915933406982303635263715)
            ·
              refine ⟨28373900110473455452895573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18915933406982303635263715 28373900110473455452895573)
              ·
                refine ⟨83126660479902701522155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28373900110473455452895573 83126660479902701522155)
                ·
                  rfl

theorem cell22_2185496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 10].length) (baseStart_2185496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185496 prefixEnd_2185496 := by exact prefixLift 2185496
  have htrace : WordTrace (prefixWord ++ tailWord_2185496) baseStart_2185496 baseEnd_2185496 := by
    simpa [prefixWord, tailWord_2185496, baseEnd_2185496] using wordTrace_append hprefix tailTrace_2185496
  have hstable : (prefixWord ++ tailWord_2185496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185496).length < 2 ^ (prefixWord ++ tailWord_2185496).sum := by decide
  have hdescent : baseEnd_2185496 < baseStart_2185496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185541 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 11]
def baseStart_2185541 : Nat := 118140960795 + 2185541 * 2 ^ 59
def prefixEnd_2185541 : Nat := 4983230072969 + 3 ^ 40 * 2185541 * 2
def baseEnd_2185541 : Nat := 249385116246253065441419

theorem tailTrace_2185541 : CollatzResearch.WordTrace tailWord_2185541 prefixEnd_2185541 249385116246253065441419 := by
  unfold tailWord_2185541
  simp only [CollatzResearch.WordTrace]
  refine ⟨79713228975165692531108477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53142152650110461687405651 79713228975165692531108477)
  ·
    refine ⟨29892460865687134699165679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79713228975165692531108477 29892460865687134699165679)
    ·
      refine ⟨44838691298530702048748519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29892460865687134699165679 44838691298530702048748519)
      ·
        refine ⟨67258036947796053073122779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44838691298530702048748519 67258036947796053073122779)
        ·
          refine ⟨100887055421694079609684169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67258036947796053073122779 100887055421694079609684169)
          ·
            refine ⟨75665291566270559707263127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100887055421694079609684169 75665291566270559707263127)
            ·
              refine ⟨113497937349405839560894691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75665291566270559707263127 113497937349405839560894691)
              ·
                refine ⟨170246906024108759341342037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113497937349405839560894691 170246906024108759341342037)
                ·
                  refine ⟨249385116246253065441419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 170246906024108759341342037 249385116246253065441419)
                  ·
                    rfl

theorem cell22_2185541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_2185541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185541 prefixEnd_2185541 := by exact prefixLift 2185541
  have htrace : WordTrace (prefixWord ++ tailWord_2185541) baseStart_2185541 baseEnd_2185541 := by
    simpa [prefixWord, tailWord_2185541, baseEnd_2185541] using wordTrace_append hprefix tailTrace_2185541
  have hstable : (prefixWord ++ tailWord_2185541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185541).length < 2 ^ (prefixWord ++ tailWord_2185541).sum := by decide
  have hdescent : baseEnd_2185541 < baseStart_2185541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185573 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_2185573 : Nat := 118140960795 + 2185573 * 2 ^ 59
def prefixEnd_2185573 : Nat := 4983230072969 + 3 ^ 40 * 2185573 * 2
def baseEnd_2185573 : Nat := 748166302992721779524159

theorem tailTrace_2185573 : CollatzResearch.WordTrace tailWord_2185573 prefixEnd_2185573 748166302992721779524159 := by
  unfold tailWord_2185573
  simp only [CollatzResearch.WordTrace]
  refine ⟨79714396111049761996273373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53142930740699841330848915 79714396111049761996273373)
  ·
    refine ⟨29892898541643660748602515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79714396111049761996273373 29892898541643660748602515)
    ·
      refine ⟨44839347812465491122903773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29892898541643660748602515 44839347812465491122903773)
      ·
        refine ⟨16814755429674559171088915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44839347812465491122903773 16814755429674559171088915)
        ·
          refine ⟨25222133144511838756633373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16814755429674559171088915 25222133144511838756633373)
          ·
            refine ⟨9458299929191939533737515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25222133144511838756633373 9458299929191939533737515)
            ·
              refine ⟨14187449893787909300606273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9458299929191939533737515 14187449893787909300606273)
              ·
                refine ⟨10640587420340931975454705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14187449893787909300606273 10640587420340931975454705)
                ·
                  refine ⟨7980440565255698981591029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10640587420340931975454705 7980440565255698981591029)
                  ·
                    refine ⟨748166302992721779524159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7980440565255698981591029 748166302992721779524159)
                    ·
                      rfl

theorem cell22_2185573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_2185573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185573 prefixEnd_2185573 := by exact prefixLift 2185573
  have htrace : WordTrace (prefixWord ++ tailWord_2185573) baseStart_2185573 baseEnd_2185573 := by
    simpa [prefixWord, tailWord_2185573, baseEnd_2185573] using wordTrace_append hprefix tailTrace_2185573
  have hstable : (prefixWord ++ tailWord_2185573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185573).length < 2 ^ (prefixWord ++ tailWord_2185573).sum := by decide
  have hdescent : baseEnd_2185573 < baseStart_2185573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185575 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 5]
def baseStart_2185575 : Nat := 118140960795 + 2185575 * 2 ^ 59
def prefixEnd_2185575 : Nat := 4983230072969 + 3 ^ 40 * 2185575 * 2
def baseEnd_2185575 : Nat := 249388995877864813658051

theorem tailTrace_2185575 : CollatzResearch.WordTrace tailWord_2185575 prefixEnd_2185575 249388995877864813658051 := by
  unfold tailWord_2185575
  simp only [CollatzResearch.WordTrace]
  refine ⟨79714469057042516337846179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53142979371361677558564119 79714469057042516337846179)
  ·
    refine ⟨119571703585563774506769269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79714469057042516337846179 119571703585563774506769269)
    ·
      refine ⟨11209847211146603860009619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119571703585563774506769269 11209847211146603860009619)
      ·
        refine ⟨16814770816719905790014429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11209847211146603860009619 16814770816719905790014429)
        ·
          refine ⟨6305539056269964671255411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16814770816719905790014429 6305539056269964671255411)
          ·
            refine ⟨9458308584404947006883117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6305539056269964671255411 9458308584404947006883117)
            ·
              refine ⟨3546865719151855127581169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9458308584404947006883117 3546865719151855127581169)
              ·
                refine ⟨2660149289363891345685877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546865719151855127581169 2660149289363891345685877)
                ·
                  refine ⟨249388995877864813658051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2660149289363891345685877 249388995877864813658051)
                  ·
                    rfl

theorem cell22_2185575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 5].length) (baseStart_2185575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185575 prefixEnd_2185575 := by exact prefixLift 2185575
  have htrace : WordTrace (prefixWord ++ tailWord_2185575) baseStart_2185575 baseEnd_2185575 := by
    simpa [prefixWord, tailWord_2185575, baseEnd_2185575] using wordTrace_append hprefix tailTrace_2185575
  have hstable : (prefixWord ++ tailWord_2185575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185575).length < 2 ^ (prefixWord ++ tailWord_2185575).sum := by decide
  have hdescent : baseEnd_2185575 < baseStart_2185575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185635 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 4, 3]
def baseStart_2185635 : Nat := 118140960795 + 2185635 * 2 ^ 59
def prefixEnd_2185635 : Nat := 4983230072969 + 3 ^ 40 * 2185635 * 2
def baseEnd_2185635 : Nat := 748187526859774284473969

theorem tailTrace_2185635 : CollatzResearch.WordTrace tailWord_2185635 prefixEnd_2185635 748187526859774284473969 := by
  unfold tailWord_2185635
  simp only [CollatzResearch.WordTrace]
  refine ⟨79716657436825146585030359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53144438291216764390020239 79716657436825146585030359)
  ·
    refine ⟨119574986155237719877545539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79716657436825146585030359 119574986155237719877545539)
    ·
      refine ⟨179362479232856579816318309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119574986155237719877545539 179362479232856579816318309)
      ·
        refine ⟨33630464856160608715559683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179362479232856579816318309 33630464856160608715559683)
        ·
          refine ⟨50445697284240913073339525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33630464856160608715559683 50445697284240913073339525)
          ·
            refine ⟨9458568240795171201251161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50445697284240913073339525 9458568240795171201251161)
            ·
              refine ⟨7093926180596378400938371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9458568240795171201251161 7093926180596378400938371)
              ·
                refine ⟨10640889270894567601407557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7093926180596378400938371 10640889270894567601407557)
                ·
                  refine ⟨1995166738292731425263917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10640889270894567601407557 1995166738292731425263917)
                  ·
                    refine ⟨748187526859774284473969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1995166738292731425263917 748187526859774284473969)
                    ·
                      rfl

theorem cell22_2185635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 3].length) (baseStart_2185635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185635 prefixEnd_2185635 := by exact prefixLift 2185635
  have htrace : WordTrace (prefixWord ++ tailWord_2185635) baseStart_2185635 baseEnd_2185635 := by
    simpa [prefixWord, tailWord_2185635, baseEnd_2185635] using wordTrace_append hprefix tailTrace_2185635
  have hstable : (prefixWord ++ tailWord_2185635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185635).length < 2 ^ (prefixWord ++ tailWord_2185635).sum := by decide
  have hdescent : baseEnd_2185635 < baseStart_2185635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185637 : List Nat := [1, 3, 1, 2, 1, 1, 7, 2, 4]
def baseStart_2185637 : Nat := 118140960795 + 2185637 * 2 ^ 59
def prefixEnd_2185637 : Nat := 4983230072969 + 3 ^ 40 * 2185637 * 2
def baseEnd_2185637 : Nat := 249396070500215648641321

theorem tailTrace_2185637 : CollatzResearch.WordTrace tailWord_2185637 prefixEnd_2185637 249396070500215648641321 := by
  unfold tailWord_2185637
  simp only [CollatzResearch.WordTrace]
  refine ⟨79716730382817900926603165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53144486921878600617735443 79716730382817900926603165)
  ·
    refine ⟨29893773893556712847476187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79716730382817900926603165 29893773893556712847476187)
    ·
      refine ⟨44840660840335069271214281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29893773893556712847476187 44840660840335069271214281)
      ·
        refine ⟨33630495630251301953410711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44840660840335069271214281 33630495630251301953410711)
        ·
          refine ⟨50445743445376952930116067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33630495630251301953410711 50445743445376952930116067)
          ·
            refine ⟨75668615168065429395174101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50445743445376952930116067 75668615168065429395174101)
            ·
              refine ⟨1773483168001533501449393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75668615168065429395174101 1773483168001533501449393)
              ·
                refine ⟨1330112376001150126087045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1773483168001533501449393 1330112376001150126087045)
                ·
                  refine ⟨249396070500215648641321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330112376001150126087045 249396070500215648641321)
                  ·
                    rfl

theorem cell22_2185637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_2185637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185637 prefixEnd_2185637 := by exact prefixLift 2185637
  have htrace : WordTrace (prefixWord ++ tailWord_2185637) baseStart_2185637 baseEnd_2185637 := by
    simpa [prefixWord, tailWord_2185637, baseEnd_2185637] using wordTrace_append hprefix tailTrace_2185637
  have hstable : (prefixWord ++ tailWord_2185637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185637).length < 2 ^ (prefixWord ++ tailWord_2185637).sum := by decide
  have hdescent : baseEnd_2185637 < baseStart_2185637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185682 : List Nat := [3, 2, 2, 4, 2, 9]
def baseStart_2185682 : Nat := 118140960795 + 2185682 * 2 ^ 59
def prefixEnd_2185682 : Nat := 4983230072969 + 3 ^ 40 * 2185682 * 2
def baseEnd_2185682 : Nat := 9237081678028170722825

theorem tailTrace_2185682 : CollatzResearch.WordTrace tailWord_2185682 prefixEnd_2185682 9237081678028170722825 := by
  unfold tailWord_2185682
  simp only [CollatzResearch.WordTrace]
  refine ⟨19929592916913718402997825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53145581111769915741327533 19929592916913718402997825)
  ·
    refine ⟨14947194687685288802248369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19929592916913718402997825 14947194687685288802248369)
    ·
      refine ⟨11210396015763966601686277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14947194687685288802248369 11210396015763966601686277)
      ·
        refine ⟨2101949252955743737816177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11210396015763966601686277 2101949252955743737816177)
        ·
          refine ⟨1576461939716807803362133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101949252955743737816177 1576461939716807803362133)
          ·
            refine ⟨9237081678028170722825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1576461939716807803362133 9237081678028170722825)
            ·
              rfl

theorem cell22_2185682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 9].length) (baseStart_2185682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185682 prefixEnd_2185682 := by exact prefixLift 2185682
  have htrace : WordTrace (prefixWord ++ tailWord_2185682) baseStart_2185682 baseEnd_2185682 := by
    simpa [prefixWord, tailWord_2185682, baseEnd_2185682] using wordTrace_append hprefix tailTrace_2185682
  have hstable : (prefixWord ++ tailWord_2185682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185682).length < 2 ^ (prefixWord ++ tailWord_2185682).sum := by decide
  have hdescent : baseEnd_2185682 < baseStart_2185682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185714 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_2185714 : Nat := 118140960795 + 2185714 * 2 ^ 59
def prefixEnd_2185714 : Nat := 4983230072969 + 3 ^ 40 * 2185714 * 2
def baseEnd_2185714 : Nat := 748214570174244411748727

theorem tailTrace_2185714 : CollatzResearch.WordTrace tailWord_2185714 prefixEnd_2185714 748214570174244411748727 := by
  unfold tailWord_2185714
  simp only [CollatzResearch.WordTrace]
  refine ⟨19929884700884735769289049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53146359202359295384770797 19929884700884735769289049)
  ·
    refine ⟨14947413525663551826966787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19929884700884735769289049 14947413525663551826966787)
    ·
      refine ⟨22421120288495327740450181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14947413525663551826966787 22421120288495327740450181)
      ·
        refine ⟨4203960054092873951334409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22421120288495327740450181 4203960054092873951334409)
        ·
          refine ⟨3152970040569655463500807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4203960054092873951334409 3152970040569655463500807)
          ·
            refine ⟨4729455060854483195251211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152970040569655463500807 4729455060854483195251211)
            ·
              refine ⟨7094182591281724792876817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729455060854483195251211 7094182591281724792876817)
              ·
                refine ⟨5320636943461293594657613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7094182591281724792876817 5320636943461293594657613)
                ·
                  refine ⟨1995238853797985097996605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5320636943461293594657613 1995238853797985097996605)
                  ·
                    refine ⟨748214570174244411748727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1995238853797985097996605 748214570174244411748727)
                    ·
                      rfl

theorem cell22_2185714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_2185714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185714 prefixEnd_2185714 := by exact prefixLift 2185714
  have htrace : WordTrace (prefixWord ++ tailWord_2185714) baseStart_2185714 baseEnd_2185714 := by
    simpa [prefixWord, tailWord_2185714, baseEnd_2185714] using wordTrace_append hprefix tailTrace_2185714
  have hstable : (prefixWord ++ tailWord_2185714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185714).length < 2 ^ (prefixWord ++ tailWord_2185714).sum := by decide
  have hdescent : baseEnd_2185714 < baseStart_2185714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185785 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_2185785 : Nat := 118140960795 + 2185785 * 2 ^ 59
def prefixEnd_2185785 : Nat := 4983230072969 + 3 ^ 40 * 2185785 * 2
def baseEnd_2185785 : Nat := 748238874925223893223509

theorem tailTrace_2185785 : CollatzResearch.WordTrace tailWord_2185785 prefixEnd_2185785 748238874925223893223509 := by
  unfold tailWord_2185785
  simp only [CollatzResearch.WordTrace]
  refine ⟨79722128386281722202990809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53148085590854481468660539 79722128386281722202990809)
  ·
    refine ⟨59791596289711291652243107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79722128386281722202990809 59791596289711291652243107)
    ·
      refine ⟨89687394434566937478364661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59791596289711291652243107 89687394434566937478364661)
      ·
        refine ⟨8408193228240650388596687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89687394434566937478364661 8408193228240650388596687)
        ·
          refine ⟨12612289842360975582895031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8408193228240650388596687 12612289842360975582895031)
          ·
            refine ⟨18918434763541463374342547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12612289842360975582895031 18918434763541463374342547)
            ·
              refine ⟨28377652145312195061513821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18918434763541463374342547 28377652145312195061513821)
              ·
                refine ⟨10641619554492073148067683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28377652145312195061513821 10641619554492073148067683)
                ·
                  refine ⟨15962429331738109722101525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10641619554492073148067683 15962429331738109722101525)
                  ·
                    refine ⟨748238874925223893223509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15962429331738109722101525 748238874925223893223509)
                    ·
                      rfl

theorem cell22_2185785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_2185785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185785 prefixEnd_2185785 := by exact prefixLift 2185785
  have htrace : WordTrace (prefixWord ++ tailWord_2185785) baseStart_2185785 baseEnd_2185785 := by
    simpa [prefixWord, tailWord_2185785, baseEnd_2185785] using wordTrace_append hprefix tailTrace_2185785
  have hstable : (prefixWord ++ tailWord_2185785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185785).length < 2 ^ (prefixWord ++ tailWord_2185785).sum := by decide
  have hdescent : baseEnd_2185785 < baseStart_2185785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185789 : List Nat := [1, 4, 1, 3, 2, 1, 3, 3, 4]
def baseStart_2185789 : Nat := 118140960795 + 2185789 * 2 ^ 59
def prefixEnd_2185789 : Nat := 4983230072969 + 3 ^ 40 * 2185789 * 2
def baseEnd_2185789 : Nat := 249413414735656405374499

theorem tailTrace_2185789 : CollatzResearch.WordTrace tailWord_2185789 prefixEnd_2185789 249413414735656405374499 := by
  unfold tailWord_2185789
  simp only [CollatzResearch.WordTrace]
  refine ⟨79722274278267230886136421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53148182852178153924090947 79722274278267230886136421)
  ·
    refine ⟨14947926427175105791150579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79722274278267230886136421 14947926427175105791150579)
    ·
      refine ⟨22421889640762658686725869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14947926427175105791150579 22421889640762658686725869)
      ·
        refine ⟨8408208615285997007522201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22421889640762658686725869 8408208615285997007522201)
        ·
          refine ⟨6306156461464497755641651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8408208615285997007522201 6306156461464497755641651)
          ·
            refine ⟨9459234692196746633462477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6306156461464497755641651 9459234692196746633462477)
            ·
              refine ⟨3547213009573779987548429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9459234692196746633462477 3547213009573779987548429)
              ·
                refine ⟨1330204878590167495330661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3547213009573779987548429 1330204878590167495330661)
                ·
                  refine ⟨249413414735656405374499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1330204878590167495330661 249413414735656405374499)
                  ·
                    rfl

theorem cell22_2185789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_2185789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185789 prefixEnd_2185789 := by exact prefixLift 2185789
  have htrace : WordTrace (prefixWord ++ tailWord_2185789) baseStart_2185789 baseEnd_2185789 := by
    simpa [prefixWord, tailWord_2185789, baseEnd_2185789] using wordTrace_append hprefix tailTrace_2185789
  have hstable : (prefixWord ++ tailWord_2185789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185789).length < 2 ^ (prefixWord ++ tailWord_2185789).sum := by decide
  have hdescent : baseEnd_2185789 < baseStart_2185789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185802 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_2185802 : Nat := 118140960795 + 2185802 * 2 ^ 59
def prefixEnd_2185802 : Nat := 4983230072969 + 3 ^ 40 * 2185802 * 2
def baseEnd_2185802 : Nat := 748244694372641515548457

theorem tailTrace_2185802 : CollatzResearch.WordTrace tailWord_2185802 prefixEnd_2185802 748244694372641515548457 := by
  unfold tailWord_2185802
  simp only [CollatzResearch.WordTrace]
  refine ⟨19930687106805033526589915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53148498951480089404239773 19930687106805033526589915)
  ·
    refine ⟨29896030660207550289884873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19930687106805033526589915 29896030660207550289884873)
    ·
      refine ⟨22422022995155662717413655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29896030660207550289884873 22422022995155662717413655)
      ·
        refine ⟨33633034492733494076120483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22422022995155662717413655 33633034492733494076120483)
        ·
          refine ⟨50449551739100241114180725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33633034492733494076120483 50449551739100241114180725)
          ·
            refine ⟨4729645475540647604454443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50449551739100241114180725 4729645475540647604454443)
            ·
              refine ⟨7094468213310971406681665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729645475540647604454443 7094468213310971406681665)
              ·
                refine ⟨5320851159983228555011249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7094468213310971406681665 5320851159983228555011249)
                ·
                  refine ⟨3990638369987421416258437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5320851159983228555011249 3990638369987421416258437)
                  ·
                    refine ⟨748244694372641515548457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3990638369987421416258437 748244694372641515548457)
                    ·
                      rfl

theorem cell22_2185802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_2185802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2185802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2185802 prefixEnd_2185802 := by exact prefixLift 2185802
  have htrace : WordTrace (prefixWord ++ tailWord_2185802) baseStart_2185802 baseEnd_2185802 := by
    simpa [prefixWord, tailWord_2185802, baseEnd_2185802] using wordTrace_append hprefix tailTrace_2185802
  have hstable : (prefixWord ++ tailWord_2185802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185802).length < 2 ^ (prefixWord ++ tailWord_2185802).sum := by decide
  have hdescent : baseEnd_2185802 < baseStart_2185802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
