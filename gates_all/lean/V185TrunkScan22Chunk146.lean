import V185TrunkScan22Chunk145

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1304938 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_1304938 : Nat := 118140960795 + 1304938 * 2 ^ 59
def prefixEnd_1304938 : Nat := 4983230072969 + 3 ^ 40 * 1304938 * 2
def baseEnd_1304938 : Nat := 446706945544613771849137

theorem tailTrace_1304938 : CollatzResearch.WordTrace tailWord_1304938 prefixEnd_1304938 446706945544613771849137 := by
  unfold tailWord_1304938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11898749736609991628066867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31729999297626644341511645 11898749736609991628066867)
  ·
    refine ⟨17848124604914987442100301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11898749736609991628066867 17848124604914987442100301)
    ·
      refine ⟨6693046726843120290787613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17848124604914987442100301 6693046726843120290787613)
      ·
        refine ⟨2509892522566170109045355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6693046726843120290787613 2509892522566170109045355)
        ·
          refine ⟨3764838783849255163568033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509892522566170109045355 3764838783849255163568033)
          ·
            refine ⟨2823629087886941372676025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3764838783849255163568033 2823629087886941372676025)
            ·
              refine ⟨2117721815915206029507019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2823629087886941372676025 2117721815915206029507019)
              ·
                refine ⟨3176582723872809044260529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117721815915206029507019 3176582723872809044260529)
                ·
                  refine ⟨2382437042904606783195397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176582723872809044260529 2382437042904606783195397)
                  ·
                    refine ⟨446706945544613771849137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382437042904606783195397 446706945544613771849137)
                    ·
                      rfl

theorem cell22_1304938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_1304938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304938 prefixEnd_1304938 := by exact prefixLift 1304938
  have htrace : WordTrace (prefixWord ++ tailWord_1304938) baseStart_1304938 baseEnd_1304938 := by
    simpa [prefixWord, tailWord_1304938, baseEnd_1304938] using wordTrace_append hprefix tailTrace_1304938
  have hstable : (prefixWord ++ tailWord_1304938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304938).length < 2 ^ (prefixWord ++ tailWord_1304938).sum := by decide
  have hdescent : baseEnd_1304938 < baseStart_1304938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304970 : List Nat := [3, 1, 2, 5, 2, 1, 1, 7]
def baseStart_1304970 : Nat := 118140960795 + 1304970 * 2 ^ 59
def prefixEnd_1304970 : Nat := 4983230072969 + 3 ^ 40 * 1304970 * 2
def baseEnd_1304970 : Nat := 49635322199841817227671

theorem tailTrace_1304970 : CollatzResearch.WordTrace tailWord_1304970 prefixEnd_1304970 49635322199841817227671 := by
  unfold tailWord_1304970
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899041520581008994358091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31730777388216023984954909 11899041520581008994358091)
  ·
    refine ⟨17848562280871513491537137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11899041520581008994358091 17848562280871513491537137)
    ·
      refine ⟨13386421710653635118652853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17848562280871513491537137 13386421710653635118652853)
      ·
        refine ⟨1254977035373778292373705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13386421710653635118652853 1254977035373778292373705)
        ·
          refine ⟨941232776530333719280279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254977035373778292373705 941232776530333719280279)
          ·
            refine ⟨1411849164795500578920419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941232776530333719280279 1411849164795500578920419)
            ·
              refine ⟨2117773747193250868380629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411849164795500578920419 2117773747193250868380629)
              ·
                refine ⟨49635322199841817227671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2117773747193250868380629 49635322199841817227671)
                ·
                  rfl

theorem cell22_1304970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_1304970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304970 prefixEnd_1304970 := by exact prefixLift 1304970
  have htrace : WordTrace (prefixWord ++ tailWord_1304970) baseStart_1304970 baseEnd_1304970 := by
    simpa [prefixWord, tailWord_1304970, baseEnd_1304970] using wordTrace_append hprefix tailTrace_1304970
  have hstable : (prefixWord ++ tailWord_1304970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304970).length < 2 ^ (prefixWord ++ tailWord_1304970).sum := by decide
  have hdescent : baseEnd_1304970 < baseStart_1304970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305056 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_1305056 : Nat := 118140960795 + 1305056 * 2 ^ 59
def prefixEnd_1305056 : Nat := 4983230072969 + 3 ^ 40 * 1305056 * 2
def baseEnd_1305056 : Nat := 446747339356100797398775

theorem tailTrace_1305056 : CollatzResearch.WordTrace tailWord_1305056 prefixEnd_1305056 446747339356100797398775 := by
  unfold tailWord_1305056
  simp only [CollatzResearch.WordTrace]
  refine ⟨23799651380006236332531511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31732868506674981776708681 23799651380006236332531511)
  ·
    refine ⟨35699477070009354498797267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23799651380006236332531511 35699477070009354498797267)
    ·
      refine ⟨53549215605014031748195901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35699477070009354498797267 53549215605014031748195901)
      ·
        refine ⟨20080955851880261905573463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53549215605014031748195901 20080955851880261905573463)
        ·
          refine ⟨30121433777820392858360195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20080955851880261905573463 30121433777820392858360195)
          ·
            refine ⟨45182150666730589287540293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30121433777820392858360195 45182150666730589287540293)
            ·
              refine ⟨8471653250011985491413805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45182150666730589287540293 8471653250011985491413805)
              ·
                refine ⟨3176869968754494559280177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8471653250011985491413805 3176869968754494559280177)
                ·
                  refine ⟨2382652476565870919460133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176869968754494559280177 2382652476565870919460133)
                  ·
                    refine ⟨446747339356100797398775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382652476565870919460133 446747339356100797398775)
                    ·
                      rfl

theorem cell22_1305056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_1305056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305056 prefixEnd_1305056 := by exact prefixLift 1305056
  have htrace : WordTrace (prefixWord ++ tailWord_1305056) baseStart_1305056 baseEnd_1305056 := by
    simpa [prefixWord, tailWord_1305056, baseEnd_1305056] using wordTrace_append hprefix tailTrace_1305056
  have hstable : (prefixWord ++ tailWord_1305056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305056).length < 2 ^ (prefixWord ++ tailWord_1305056).sum := by decide
  have hdescent : baseEnd_1305056 < baseStart_1305056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305077 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 6]
def baseStart_1305077 : Nat := 118140960795 + 1305077 * 2 ^ 59
def prefixEnd_1305077 : Nat := 4983230072969 + 3 ^ 40 * 1305077 * 2
def baseEnd_1305077 : Nat := 148918176028421247541237

theorem tailTrace_1305077 : CollatzResearch.WordTrace tailWord_1305077 prefixEnd_1305077 148918176028421247541237 := by
  unfold tailWord_1305077
  simp only [CollatzResearch.WordTrace]
  refine ⟨47600068692936393251577485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31733379128624262167718323 47600068692936393251577485)
  ·
    refine ⟨17850025759851147469341557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47600068692936393251577485 17850025759851147469341557)
    ·
      refine ⟨1673439914986045075250771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17850025759851147469341557 1673439914986045075250771)
      ·
        refine ⟨2510159872479067612876157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673439914986045075250771 2510159872479067612876157)
        ·
          refine ⟨941309952179650354828559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2510159872479067612876157 941309952179650354828559)
          ·
            refine ⟨1411964928269475532242839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941309952179650354828559 1411964928269475532242839)
            ·
              refine ⟨2117947392404213298364259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1411964928269475532242839 2117947392404213298364259)
              ·
                refine ⟨3176921088606319947546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117947392404213298364259 3176921088606319947546389)
                ·
                  refine ⟨148918176028421247541237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3176921088606319947546389 148918176028421247541237)
                  ·
                    rfl

theorem cell22_1305077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_1305077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305077 prefixEnd_1305077 := by exact prefixLift 1305077
  have htrace : WordTrace (prefixWord ++ tailWord_1305077) baseStart_1305077 baseEnd_1305077 := by
    simpa [prefixWord, tailWord_1305077, baseEnd_1305077] using wordTrace_append hprefix tailTrace_1305077
  have hstable : (prefixWord ++ tailWord_1305077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305077).length < 2 ^ (prefixWord ++ tailWord_1305077).sum := by decide
  have hdescent : baseEnd_1305077 < baseStart_1305077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305092 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_1305092 : Nat := 118140960795 + 1305092 * 2 ^ 59
def prefixEnd_1305092 : Nat := 4983230072969 + 3 ^ 40 * 1305092 * 2
def baseEnd_1305092 : Nat := 446759662891808703498665

theorem tailTrace_1305092 : CollatzResearch.WordTrace tailWord_1305092 prefixEnd_1305092 446759662891808703498665 := by
  unfold tailWord_1305092
  simp only [CollatzResearch.WordTrace]
  refine ⟨23800307893941025406686765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31733743858588033875582353 23800307893941025406686765)
  ·
    refine ⟨8925115460227884527507537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23800307893941025406686765 8925115460227884527507537)
    ·
      refine ⟨6693836595170913395630653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8925115460227884527507537 6693836595170913395630653)
      ·
        refine ⟨2510188723189092523361495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6693836595170913395630653 2510188723189092523361495)
        ·
          refine ⟨3765283084783638785042243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2510188723189092523361495 3765283084783638785042243)
          ·
            refine ⟨5647924627175458177563365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765283084783638785042243 5647924627175458177563365)
            ·
              refine ⟨1058985867595398408293131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5647924627175458177563365 1058985867595398408293131)
              ·
                refine ⟨1588478801393097612439697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058985867595398408293131 1588478801393097612439697)
                ·
                  refine ⟨1191359101044823209329773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1588478801393097612439697 1191359101044823209329773)
                  ·
                    refine ⟨446759662891808703498665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191359101044823209329773 446759662891808703498665)
                    ·
                      rfl

theorem cell22_1305092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_1305092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305092 prefixEnd_1305092 := by exact prefixLift 1305092
  have htrace : WordTrace (prefixWord ++ tailWord_1305092) baseStart_1305092 baseEnd_1305092 := by
    simpa [prefixWord, tailWord_1305092, baseEnd_1305092] using wordTrace_append hprefix tailTrace_1305092
  have hstable : (prefixWord ++ tailWord_1305092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305092).length < 2 ^ (prefixWord ++ tailWord_1305092).sum := by decide
  have hdescent : baseEnd_1305092 < baseStart_1305092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305137 : List Nat := [1, 2, 2, 3, 1, 1, 6, 2, 1, 3]
def baseStart_1305137 : Nat := 118140960795 + 1305137 * 2 ^ 59
def prefixEnd_1305137 : Nat := 4983230072969 + 3 ^ 40 * 1305137 * 2
def baseEnd_1305137 : Nat := 446775067311443586123527

theorem tailTrace_1305137 : CollatzResearch.WordTrace tailWord_1305137 prefixEnd_1305137 446775067311443586123527 := by
  unfold tailWord_1305137
  simp only [CollatzResearch.WordTrace]
  refine ⟨47602257072719023498761665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31734838048479348999174443 47602257072719023498761665)
  ·
    refine ⟨35701692804539267624071249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47602257072719023498761665 35701692804539267624071249)
    ·
      refine ⟨26776269603404450718053437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35701692804539267624071249 26776269603404450718053437)
      ·
        refine ⟨10041101101276669019270039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26776269603404450718053437 10041101101276669019270039)
        ·
          refine ⟨15061651651915003528905059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10041101101276669019270039 15061651651915003528905059)
          ·
            refine ⟨22592477477872505293357589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15061651651915003528905059 22592477477872505293357589)
            ·
              refine ⟨1059022381775273685626137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22592477477872505293357589 1059022381775273685626137)
              ·
                refine ⟨794266786331455264219603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059022381775273685626137 794266786331455264219603)
                ·
                  refine ⟨1191400179497182896329405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794266786331455264219603 1191400179497182896329405)
                  ·
                    refine ⟨446775067311443586123527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191400179497182896329405 446775067311443586123527)
                    ·
                      rfl

theorem cell22_1305137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_1305137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305137 prefixEnd_1305137 := by exact prefixLift 1305137
  have htrace : WordTrace (prefixWord ++ tailWord_1305137) baseStart_1305137 baseEnd_1305137 := by
    simpa [prefixWord, tailWord_1305137, baseEnd_1305137] using wordTrace_append hprefix tailTrace_1305137
  have hstable : (prefixWord ++ tailWord_1305137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305137).length < 2 ^ (prefixWord ++ tailWord_1305137).sum := by decide
  have hdescent : baseEnd_1305137 < baseStart_1305137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305148 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1305148 : Nat := 118140960795 + 1305148 * 2 ^ 59
def prefixEnd_1305148 : Nat := 4983230072969 + 3 ^ 40 * 1305148 * 2
def baseEnd_1305148 : Nat := 446778832836243224098493

theorem tailTrace_1305148 : CollatzResearch.WordTrace tailWord_1305148 prefixEnd_1305148 446778832836243224098493 := by
  unfold tailWord_1305148
  simp only [CollatzResearch.WordTrace]
  refine ⟨23801329137839586188706049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31735105517119448251608065 23801329137839586188706049)
  ·
    refine ⟨17850996853379689641529537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23801329137839586188706049 17850996853379689641529537)
    ·
      refine ⟨13388247640034767231147153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17850996853379689641529537 13388247640034767231147153)
      ·
        refine ⟨10041185730026075423360365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13388247640034767231147153 10041185730026075423360365)
        ·
          refine ⟨3765444648759778283760137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10041185730026075423360365 3765444648759778283760137)
          ·
            refine ⟨2824083486569833712820103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3765444648759778283760137 2824083486569833712820103)
            ·
              refine ⟨4236125229854750569230155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824083486569833712820103 4236125229854750569230155)
              ·
                refine ⟨6354187844782125853845233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4236125229854750569230155 6354187844782125853845233)
                ·
                  refine ⟨4765640883586594390383925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6354187844782125853845233 4765640883586594390383925)
                  ·
                    refine ⟨446778832836243224098493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4765640883586594390383925 446778832836243224098493)
                    ·
                      rfl

theorem cell22_1305148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1305148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305148 prefixEnd_1305148 := by exact prefixLift 1305148
  have htrace : WordTrace (prefixWord ++ tailWord_1305148) baseStart_1305148 baseEnd_1305148 := by
    simpa [prefixWord, tailWord_1305148, baseEnd_1305148] using wordTrace_append hprefix tailTrace_1305148
  have hstable : (prefixWord ++ tailWord_1305148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305148).length < 2 ^ (prefixWord ++ tailWord_1305148).sum := by decide
  have hdescent : baseEnd_1305148 < baseStart_1305148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305242 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_1305242 : Nat := 118140960795 + 1305242 * 2 ^ 59
def prefixEnd_1305242 : Nat := 4983230072969 + 3 ^ 40 * 1305242 * 2
def baseEnd_1305242 : Nat := 446811010957258312248205

theorem tailTrace_1305242 : CollatzResearch.WordTrace tailWord_1305242 prefixEnd_1305242 446811010957258312248205 := by
  unfold tailWord_1305242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11901521684334656607833495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31737391158225750954222653 11901521684334656607833495)
  ·
    refine ⟨17852282526501984911750243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11901521684334656607833495 17852282526501984911750243)
    ·
      refine ⟨26778423789752977367625365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17852282526501984911750243 26778423789752977367625365)
      ·
        refine ⟨1255238615144670814107439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26778423789752977367625365 1255238615144670814107439)
        ·
          refine ⟨1882857922717006221161159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255238615144670814107439 1882857922717006221161159)
          ·
            refine ⟨2824286884075509331741739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882857922717006221161159 2824286884075509331741739)
            ·
              refine ⟨4236430326113263997612609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824286884075509331741739 4236430326113263997612609)
              ·
                refine ⟨3177322744584947998209457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4236430326113263997612609 3177322744584947998209457)
                ·
                  refine ⟨2382992058438710998657093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177322744584947998209457 2382992058438710998657093)
                  ·
                    refine ⟨446811010957258312248205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382992058438710998657093 446811010957258312248205)
                    ·
                      rfl

theorem cell22_1305242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_1305242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305242 prefixEnd_1305242 := by exact prefixLift 1305242
  have htrace : WordTrace (prefixWord ++ tailWord_1305242) baseStart_1305242 baseEnd_1305242 := by
    simpa [prefixWord, tailWord_1305242, baseEnd_1305242] using wordTrace_append hprefix tailTrace_1305242
  have hstable : (prefixWord ++ tailWord_1305242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305242).length < 2 ^ (prefixWord ++ tailWord_1305242).sum := by decide
  have hdescent : baseEnd_1305242 < baseStart_1305242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305315 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 3, 4]
def baseStart_1305315 : Nat := 118140960795 + 1305315 * 2 ^ 59
def prefixEnd_1305315 : Nat := 4983230072969 + 3 ^ 40 * 1305315 * 2
def baseEnd_1305315 : Nat := 446836000349110455172981

theorem tailTrace_1305315 : CollatzResearch.WordTrace tailWord_1305315 prefixEnd_1305315 446836000349110455172981 := by
  unfold tailWord_1305315
  simp only [CollatzResearch.WordTrace]
  refine ⟨47608749266074159898741399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31739166177382773265827599 47608749266074159898741399)
  ·
    refine ⟨71413123899111239848112099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47608749266074159898741399 71413123899111239848112099)
    ·
      refine ⟨107119685848666859772168149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71413123899111239848112099 107119685848666859772168149)
      ·
        refine ⟨2510617637078129525910191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 107119685848666859772168149 2510617637078129525910191)
        ·
          refine ⟨3765926455617194288865287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2510617637078129525910191 3765926455617194288865287)
          ·
            refine ⟨5648889683425791433297931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765926455617194288865287 5648889683425791433297931)
            ·
              refine ⟨8473334525138687149946897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648889683425791433297931 8473334525138687149946897)
              ·
                refine ⟨6355000893854015362460173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8473334525138687149946897 6355000893854015362460173)
                ·
                  refine ⟨2383125335195255760922565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6355000893854015362460173 2383125335195255760922565)
                  ·
                    refine ⟨446836000349110455172981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2383125335195255760922565 446836000349110455172981)
                    ·
                      rfl

theorem cell22_1305315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 4].length) (baseStart_1305315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305315 prefixEnd_1305315 := by exact prefixLift 1305315
  have htrace : WordTrace (prefixWord ++ tailWord_1305315) baseStart_1305315 baseEnd_1305315 := by
    simpa [prefixWord, tailWord_1305315, baseEnd_1305315] using wordTrace_append hprefix tailTrace_1305315
  have hstable : (prefixWord ++ tailWord_1305315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305315).length < 2 ^ (prefixWord ++ tailWord_1305315).sum := by decide
  have hdescent : baseEnd_1305315 < baseStart_1305315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305330 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_1305330 : Nat := 118140960795 + 1305330 * 2 ^ 59
def prefixEnd_1305330 : Nat := 4983230072969 + 3 ^ 40 * 1305330 * 2
def baseEnd_1305330 : Nat := 148947045051885138682645

theorem tailTrace_1305330 : CollatzResearch.WordTrace tailWord_1305330 prefixEnd_1305330 148947045051885138682645 := by
  unfold tailWord_1305330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902324090254954365134361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31739530907346544973691629 11902324090254954365134361)
  ·
    refine ⟨8926743067691215773850771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11902324090254954365134361 8926743067691215773850771)
    ·
      refine ⟨13390114601536823660776157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8926743067691215773850771 13390114601536823660776157)
      ·
        refine ⟨5021292975576308872791059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13390114601536823660776157 5021292975576308872791059)
        ·
          refine ⟨7531939463364463309186589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5021292975576308872791059 7531939463364463309186589)
          ·
            refine ⟨2824477298761673740944971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7531939463364463309186589 2824477298761673740944971)
            ·
              refine ⟨4236715948142510611417457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824477298761673740944971 4236715948142510611417457)
              ·
                refine ⟨3177536961106882958563093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4236715948142510611417457 3177536961106882958563093)
                ·
                  refine ⟨148947045051885138682645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3177536961106882958563093 148947045051885138682645)
                  ·
                    rfl

theorem cell22_1305330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_1305330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305330 prefixEnd_1305330 := by exact prefixLift 1305330
  have htrace : WordTrace (prefixWord ++ tailWord_1305330) baseStart_1305330 baseEnd_1305330 := by
    simpa [prefixWord, tailWord_1305330, baseEnd_1305330] using wordTrace_append hprefix tailTrace_1305330
  have hstable : (prefixWord ++ tailWord_1305330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305330).length < 2 ^ (prefixWord ++ tailWord_1305330).sum := by decide
  have hdescent : baseEnd_1305330 < baseStart_1305330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305345 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1305345 : Nat := 118140960795 + 1305345 * 2 ^ 59
def prefixEnd_1305345 : Nat := 4983230072969 + 3 ^ 40 * 1305345 * 2
def baseEnd_1305345 : Nat := 446846269962200376922889

theorem tailTrace_1305345 : CollatzResearch.WordTrace tailWord_1305345 prefixEnd_1305345 446846269962200376922889 := by
  unfold tailWord_1305345
  simp only [CollatzResearch.WordTrace]
  refine ⟨47609843455965475022333489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31739895637310316681555659 47609843455965475022333489)
  ·
    refine ⟨35707382591974106266750117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47609843455965475022333489 35707382591974106266750117)
    ·
      refine ⟨6695134235995144925015647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35707382591974106266750117 6695134235995144925015647)
      ·
        refine ⟨10042701353992717387523471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695134235995144925015647 10042701353992717387523471)
        ·
          refine ⟨15064052030989076081285207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10042701353992717387523471 15064052030989076081285207)
          ·
            refine ⟨22596078046483614121927811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15064052030989076081285207 22596078046483614121927811)
            ·
              refine ⟨33894117069725421182891717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22596078046483614121927811 33894117069725421182891717)
              ·
                refine ⟨6355146950573516471792197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33894117069725421182891717 6355146950573516471792197)
                ·
                  refine ⟨1191590053232534338461037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6355146950573516471792197 1191590053232534338461037)
                  ·
                    refine ⟨446846269962200376922889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191590053232534338461037 446846269962200376922889)
                    ·
                      rfl

theorem cell22_1305345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1305345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305345 prefixEnd_1305345 := by exact prefixLift 1305345
  have htrace : WordTrace (prefixWord ++ tailWord_1305345) baseStart_1305345 baseEnd_1305345 := by
    simpa [prefixWord, tailWord_1305345, baseEnd_1305345] using wordTrace_append hprefix tailTrace_1305345
  have hstable : (prefixWord ++ tailWord_1305345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305345).length < 2 ^ (prefixWord ++ tailWord_1305345).sum := by decide
  have hdescent : baseEnd_1305345 < baseStart_1305345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305398 : List Nat := [5, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1305398 : Nat := 118140960795 + 1305398 * 2 ^ 59
def prefixEnd_1305398 : Nat := 4983230072969 + 3 ^ 40 * 1305398 * 2
def baseEnd_1305398 : Nat := 148954804315108635115909

theorem tailTrace_1305398 : CollatzResearch.WordTrace tailWord_1305398 prefixEnd_1305398 148954804315108635115909 := by
  unfold tailWord_1305398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975736032798341567125803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31741184349848976716008565 2975736032798341567125803)
  ·
    refine ⟨4463604049197512350688705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2975736032798341567125803 4463604049197512350688705)
    ·
      refine ⟨3347703036898134263016529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4463604049197512350688705 3347703036898134263016529)
      ·
        refine ⟨2510777277673600697262397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3347703036898134263016529 2510777277673600697262397)
        ·
          refine ⟨941541479127600261473399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2510777277673600697262397 941541479127600261473399)
          ·
            refine ⟨1412312218691400392210099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941541479127600261473399 1412312218691400392210099)
            ·
              refine ⟨2118468328037100588315149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412312218691400392210099 2118468328037100588315149)
              ·
                refine ⟨794425623013912720618181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2118468328037100588315149 794425623013912720618181)
                ·
                  refine ⟨148954804315108635115909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 794425623013912720618181 148954804315108635115909)
                  ·
                    rfl

theorem cell22_1305398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1305398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305398 prefixEnd_1305398 := by exact prefixLift 1305398
  have htrace : WordTrace (prefixWord ++ tailWord_1305398) baseStart_1305398 baseEnd_1305398 := by
    simpa [prefixWord, tailWord_1305398, baseEnd_1305398] using wordTrace_append hprefix tailTrace_1305398
  have hstable : (prefixWord ++ tailWord_1305398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305398).length < 2 ^ (prefixWord ++ tailWord_1305398).sum := by decide
  have hdescent : baseEnd_1305398 < baseStart_1305398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305409 : List Nat := [1, 2, 5, 3, 2, 1, 8]
def baseStart_1305409 : Nat := 118140960795 + 1305409 * 2 ^ 59
def prefixEnd_1305409 : Nat := 4983230072969 + 3 ^ 40 * 1305409 * 2
def baseEnd_1305409 : Nat := 16550673276671316419359

theorem tailTrace_1305409 : CollatzResearch.WordTrace tailWord_1305409 prefixEnd_1305409 16550673276671316419359 := by
  unfold tailWord_1305409
  simp only [CollatzResearch.WordTrace]
  refine ⟨47612177727733613952663281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31741451818489075968442187 47612177727733613952663281)
  ·
    refine ⟨35709133295800210464497461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47612177727733613952663281 35709133295800210464497461)
    ·
      refine ⟨3347731246481269731046637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35709133295800210464497461 3347731246481269731046637)
      ·
        refine ⟨1255399217430476149142489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3347731246481269731046637 1255399217430476149142489)
        ·
          refine ⟨941549413072857111856867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1255399217430476149142489 941549413072857111856867)
          ·
            refine ⟨1412324119609285667785301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941549413072857111856867 1412324119609285667785301)
            ·
              refine ⟨16550673276671316419359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1412324119609285667785301 16550673276671316419359)
              ·
                rfl

theorem cell22_1305409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 8].length) (baseStart_1305409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305409 prefixEnd_1305409 := by exact prefixLift 1305409
  have htrace : WordTrace (prefixWord ++ tailWord_1305409) baseStart_1305409 baseEnd_1305409 := by
    simpa [prefixWord, tailWord_1305409, baseEnd_1305409] using wordTrace_append hprefix tailTrace_1305409
  have hstable : (prefixWord ++ tailWord_1305409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305409).length < 2 ^ (prefixWord ++ tailWord_1305409).sum := by decide
  have hdescent : baseEnd_1305409 < baseStart_1305409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305420 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 7]
def baseStart_1305420 : Nat := 118140960795 + 1305420 * 2 ^ 59
def prefixEnd_1305420 : Nat := 4983230072969 + 3 ^ 40 * 1305420 * 2
def baseEnd_1305420 : Nat := 148957314664975060432553

theorem tailTrace_1305420 : CollatzResearch.WordTrace tailWord_1305420 prefixEnd_1305420 148957314664975060432553 := by
  unfold tailWord_1305420
  simp only [CollatzResearch.WordTrace]
  refine ⟨23806289465346881415656857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31741719287129175220875809 23806289465346881415656857)
  ·
    refine ⟨17854717099010161061742643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23806289465346881415656857 17854717099010161061742643)
    ·
      refine ⟨26782075648515241592613965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17854717099010161061742643 26782075648515241592613965)
      ·
        refine ⟨10043278368193215597230237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26782075648515241592613965 10043278368193215597230237)
        ·
          refine ⟨3766229388072455848961339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10043278368193215597230237 3766229388072455848961339)
          ·
            refine ⟨5649344082108683773442009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3766229388072455848961339 5649344082108683773442009)
            ·
              refine ⟨4237008061581512830081507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5649344082108683773442009 4237008061581512830081507)
              ·
                refine ⟨6355512092372269245122261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237008061581512830081507 6355512092372269245122261)
                ·
                  refine ⟨148957314664975060432553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6355512092372269245122261 148957314664975060432553)
                  ·
                    rfl

theorem cell22_1305420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_1305420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305420 prefixEnd_1305420 := by exact prefixLift 1305420
  have htrace : WordTrace (prefixWord ++ tailWord_1305420) baseStart_1305420 baseEnd_1305420 := by
    simpa [prefixWord, tailWord_1305420, baseEnd_1305420] using wordTrace_append hprefix tailTrace_1305420
  have hstable : (prefixWord ++ tailWord_1305420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305420).length < 2 ^ (prefixWord ++ tailWord_1305420).sum := by decide
  have hdescent : baseEnd_1305420 < baseStart_1305420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305495 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 1, 6]
def baseStart_1305495 : Nat := 118140960795 + 1305495 * 2 ^ 59
def prefixEnd_1305495 : Nat := 4983230072969 + 3 ^ 40 * 1305495 * 2
def baseEnd_1305495 : Nat := 446897618027649985672429

theorem tailTrace_1305495 : CollatzResearch.WordTrace tailWord_1305495 prefixEnd_1305495 446897618027649985672429 := by
  unfold tailWord_1305495
  simp only [CollatzResearch.WordTrace]
  refine ⟨47615314405422050640293939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31743542936948033760195959 47615314405422050640293939)
  ·
    refine ⟨71422971608133075960440909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47615314405422050640293939 71422971608133075960440909)
    ·
      refine ⟨26783614353049903485165341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71422971608133075960440909 26783614353049903485165341)
      ·
        refine ⟨10043855382393713806937003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26783614353049903485165341 10043855382393713806937003)
        ·
          refine ⟨15065783073590570710405505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043855382393713806937003 15065783073590570710405505)
          ·
            refine ⟨11299337305192928032804129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15065783073590570710405505 11299337305192928032804129)
            ·
              refine ⟨8474502978894696024603097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11299337305192928032804129 8474502978894696024603097)
              ·
                refine ⟨6355877234171022018452323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8474502978894696024603097 6355877234171022018452323)
                ·
                  refine ⟨9533815851256533027678485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6355877234171022018452323 9533815851256533027678485)
                  ·
                    refine ⟨446897618027649985672429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9533815851256533027678485 446897618027649985672429)
                    ·
                      rfl

theorem cell22_1305495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_1305495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305495 prefixEnd_1305495 := by exact prefixLift 1305495
  have htrace : WordTrace (prefixWord ++ tailWord_1305495) baseStart_1305495 baseEnd_1305495 := by
    simpa [prefixWord, tailWord_1305495, baseEnd_1305495] using wordTrace_append hprefix tailTrace_1305495
  have hstable : (prefixWord ++ tailWord_1305495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305495).length < 2 ^ (prefixWord ++ tailWord_1305495).sum := by decide
  have hdescent : baseEnd_1305495 < baseStart_1305495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305576 : List Nat := [2, 1, 4, 1, 1, 1, 5, 3, 1, 3]
def baseStart_1305576 : Nat := 118140960795 + 1305576 * 2 ^ 59
def prefixEnd_1305576 : Nat := 4983230072969 + 3 ^ 40 * 1305576 * 2
def baseEnd_1305576 : Nat := 446925345982992774397181

theorem tailTrace_1305576 : CollatzResearch.WordTrace tailWord_1305576 prefixEnd_1305576 446925345982992774397181 := by
  unfold tailWord_1305576
  simp only [CollatzResearch.WordTrace]
  refine ⟨23809134359064300736996291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31745512478752400982661721 23809134359064300736996291)
  ·
    refine ⟨35713701538596451105494437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23809134359064300736996291 35713701538596451105494437)
    ·
      refine ⟨6696319038486834582280207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35713701538596451105494437 6696319038486834582280207)
      ·
        refine ⟨10044478557730251873420311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696319038486834582280207 10044478557730251873420311)
        ·
          refine ⟨15066717836595377810130467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10044478557730251873420311 15066717836595377810130467)
          ·
            refine ⟨22600076754893066715195701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15066717836595377810130467 22600076754893066715195701)
            ·
              refine ⟨2118757195771225004549597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22600076754893066715195701 2118757195771225004549597)
              ·
                refine ⟨794533948414209376706099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2118757195771225004549597 794533948414209376706099)
                ·
                  refine ⟨1191800922621314065059149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794533948414209376706099 1191800922621314065059149)
                  ·
                    refine ⟨446925345982992774397181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191800922621314065059149 446925345982992774397181)
                    ·
                      rfl

theorem cell22_1305576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_1305576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305576 prefixEnd_1305576 := by exact prefixLift 1305576
  have htrace : WordTrace (prefixWord ++ tailWord_1305576) baseStart_1305576 baseEnd_1305576 := by
    simpa [prefixWord, tailWord_1305576, baseEnd_1305576] using wordTrace_append hprefix tailTrace_1305576
  have hstable : (prefixWord ++ tailWord_1305576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305576).length < 2 ^ (prefixWord ++ tailWord_1305576).sum := by decide
  have hdescent : baseEnd_1305576 < baseStart_1305576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305711 : List Nat := [1, 1, 2, 1, 3, 3, 1, 6, 1, 3]
def baseStart_1305711 : Nat := 118140960795 + 1305711 * 2 ^ 59
def prefixEnd_1305711 : Nat := 4983230072969 + 3 ^ 40 * 1305711 * 2
def baseEnd_1305711 : Nat := 446971559241897422271767

theorem tailTrace_1305711 : CollatzResearch.WordTrace tailWord_1305711 prefixEnd_1305711 446971559241897422271767 := by
  unfold tailWord_1305711
  simp only [CollatzResearch.WordTrace]
  refine ⟨47623192572639519530156987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31748795048426346353437991 47623192572639519530156987)
  ·
    refine ⟨71434788858959279295235481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47623192572639519530156987 71434788858959279295235481)
    ·
      refine ⟨53576091644219459471426611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71434788858959279295235481 53576091644219459471426611)
      ·
        refine ⟨80364137466329189207139917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53576091644219459471426611 80364137466329189207139917)
        ·
          refine ⟨30136551549873445952677469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80364137466329189207139917 30136551549873445952677469)
          ·
            refine ⟨11301206831202542232254051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30136551549873445952677469 11301206831202542232254051)
            ·
              refine ⟨16951810246803813348381077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11301206831202542232254051 16951810246803813348381077)
              ·
                refine ⟨794616105318928750705363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16951810246803813348381077 794616105318928750705363)
                ·
                  refine ⟨1191924157978393126058045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794616105318928750705363 1191924157978393126058045)
                  ·
                    refine ⟨446971559241897422271767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191924157978393126058045 446971559241897422271767)
                    ·
                      rfl

theorem cell22_1305711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 1, 3].length) (baseStart_1305711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305711 prefixEnd_1305711 := by exact prefixLift 1305711
  have htrace : WordTrace (prefixWord ++ tailWord_1305711) baseStart_1305711 baseEnd_1305711 := by
    simpa [prefixWord, tailWord_1305711, baseEnd_1305711] using wordTrace_append hprefix tailTrace_1305711
  have hstable : (prefixWord ++ tailWord_1305711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305711).length < 2 ^ (prefixWord ++ tailWord_1305711).sum := by decide
  have hdescent : baseEnd_1305711 < baseStart_1305711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305762 : List Nat := [3, 3, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1305762 : Nat := 118140960795 + 1305762 * 2 ^ 59
def prefixEnd_1305762 : Nat := 4983230072969 + 3 ^ 40 * 1305762 * 2
def baseEnd_1305762 : Nat := 446989017584150289246611

theorem tailTrace_1305762 : CollatzResearch.WordTrace tailWord_1305762 prefixEnd_1305762 446989017584150289246611 := by
  unfold tailWord_1305762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11906263173863688810065885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31750035130303170160175693 11906263173863688810065885)
  ·
    refine ⟨4464848690198883303774707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11906263173863688810065885 4464848690198883303774707)
    ·
      refine ⟨6697273035298324955662061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4464848690198883303774707 6697273035298324955662061)
      ·
        refine ⟨2511477388236871858373273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6697273035298324955662061 2511477388236871858373273)
        ·
          refine ⟨1883608041177653893779955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2511477388236871858373273 1883608041177653893779955)
          ·
            refine ⟨2825412061766480840669933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883608041177653893779955 2825412061766480840669933)
            ·
              refine ⟨1059529523162430315251225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2825412061766480840669933 1059529523162430315251225)
              ·
                refine ⟨794647142371822736438419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059529523162430315251225 794647142371822736438419)
                ·
                  refine ⟨1191970713557734104657629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794647142371822736438419 1191970713557734104657629)
                  ·
                    refine ⟨446989017584150289246611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191970713557734104657629 446989017584150289246611)
                    ·
                      rfl

theorem cell22_1305762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1305762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305762 prefixEnd_1305762 := by exact prefixLift 1305762
  have htrace : WordTrace (prefixWord ++ tailWord_1305762) baseStart_1305762 baseEnd_1305762 := by
    simpa [prefixWord, tailWord_1305762, baseEnd_1305762] using wordTrace_append hprefix tailTrace_1305762
  have hstable : (prefixWord ++ tailWord_1305762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305762).length < 2 ^ (prefixWord ++ tailWord_1305762).sum := by decide
  have hdescent : baseEnd_1305762 < baseStart_1305762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305784 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 6, 3]
def baseStart_1305784 : Nat := 118140960795 + 1305784 * 2 ^ 59
def prefixEnd_1305784 : Nat := 4983230072969 + 3 ^ 40 * 1305784 * 2
def baseEnd_1305784 : Nat := 446996548633749565196543

theorem tailTrace_1305784 : CollatzResearch.WordTrace tailWord_1305784 prefixEnd_1305784 446996548633749565196543 := by
  unfold tailWord_1305784
  simp only [CollatzResearch.WordTrace]
  refine ⟨23812927550687526498782203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31750570067583368665042937 23812927550687526498782203)
  ·
    refine ⟨35719391326031289748173305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23812927550687526498782203 35719391326031289748173305)
    ·
      refine ⟨26789543494523467311129979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35719391326031289748173305 26789543494523467311129979)
      ·
        refine ⟨40184315241785200966694969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26789543494523467311129979 40184315241785200966694969)
        ·
          refine ⟨30138236431338900725021227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40184315241785200966694969 30138236431338900725021227)
          ·
            refine ⟨45207354647008351087531841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30138236431338900725021227 45207354647008351087531841)
            ·
              refine ⟨33905515985256263315648881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45207354647008351087531841 33905515985256263315648881)
              ·
                refine ⟨25429136988942197486736661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33905515985256263315648881 25429136988942197486736661)
                ·
                  refine ⟨1191990796356665507190781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25429136988942197486736661 1191990796356665507190781)
                  ·
                    refine ⟨446996548633749565196543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191990796356665507190781 446996548633749565196543)
                    ·
                      rfl

theorem cell22_1305784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_1305784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305784 prefixEnd_1305784 := by exact prefixLift 1305784
  have htrace : WordTrace (prefixWord ++ tailWord_1305784) baseStart_1305784 baseEnd_1305784 := by
    simpa [prefixWord, tailWord_1305784, baseEnd_1305784] using wordTrace_append hprefix tailTrace_1305784
  have hstable : (prefixWord ++ tailWord_1305784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305784).length < 2 ^ (prefixWord ++ tailWord_1305784).sum := by decide
  have hdescent : baseEnd_1305784 < baseStart_1305784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305788 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_1305788 : Nat := 118140960795 + 1305788 * 2 ^ 59
def prefixEnd_1305788 : Nat := 4983230072969 + 3 ^ 40 * 1305788 * 2
def baseEnd_1305788 : Nat := 446997917915494888096531

theorem tailTrace_1305788 : CollatzResearch.WordTrace tailWord_1305788 prefixEnd_1305788 446997917915494888096531 := by
  unfold tailWord_1305788
  simp only [CollatzResearch.WordTrace]
  refine ⟨23813000496680280840355009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31750667328907041120473345 23813000496680280840355009)
  ·
    refine ⟨17859750372510210630266257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23813000496680280840355009 17859750372510210630266257)
    ·
      refine ⟨13394812779382657972699693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17859750372510210630266257 13394812779382657972699693)
      ·
        refine ⟨5023054792268496739762385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13394812779382657972699693 5023054792268496739762385)
        ·
          refine ⟨3767291094201372554821789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5023054792268496739762385 3767291094201372554821789)
          ·
            refine ⟨1412734160325514708058171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3767291094201372554821789 1412734160325514708058171)
            ·
              refine ⟨2119101240488272062087257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412734160325514708058171 2119101240488272062087257)
              ·
                refine ⟨1589325930366204046565443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2119101240488272062087257 1589325930366204046565443)
                ·
                  refine ⟨2383988895549306069848165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589325930366204046565443 2383988895549306069848165)
                  ·
                    refine ⟨446997917915494888096531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2383988895549306069848165 446997917915494888096531)
                    ·
                      rfl

theorem cell22_1305788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_1305788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305788 prefixEnd_1305788 := by exact prefixLift 1305788
  have htrace : WordTrace (prefixWord ++ tailWord_1305788) baseStart_1305788 baseEnd_1305788 := by
    simpa [prefixWord, tailWord_1305788, baseEnd_1305788] using wordTrace_append hprefix tailTrace_1305788
  have hstable : (prefixWord ++ tailWord_1305788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305788).length < 2 ^ (prefixWord ++ tailWord_1305788).sum := by decide
  have hdescent : baseEnd_1305788 < baseStart_1305788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305893 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 5]
def baseStart_1305893 : Nat := 118140960795 + 1305893 * 2 ^ 59
def prefixEnd_1305893 : Nat := 4983230072969 + 3 ^ 40 * 1305893 * 2
def baseEnd_1305893 : Nat := 149011287187103204740403

theorem tailTrace_1305893 : CollatzResearch.WordTrace tailWord_1305893 prefixEnd_1305893 149011287187103204740403 := by
  unfold tailWord_1305893
  simp only [CollatzResearch.WordTrace]
  refine ⟨47629830657980164613282333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31753220438653443075521555 47629830657980164613282333)
  ·
    refine ⟨17861186496742561729980875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47629830657980164613282333 17861186496742561729980875)
    ·
      refine ⟨26791779745113842594971313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17861186496742561729980875 26791779745113842594971313)
      ·
        refine ⟨20093834808835381946228485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26791779745113842594971313 20093834808835381946228485)
        ·
          refine ⟨3767594026656634114917841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20093834808835381946228485 3767594026656634114917841)
          ·
            refine ⟨2825695519992475586188381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767594026656634114917841 2825695519992475586188381)
            ·
              refine ⟨1059635819997178344820643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2825695519992475586188381 1059635819997178344820643)
              ·
                refine ⟨1589453729995767517230965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059635819997178344820643 1589453729995767517230965)
                ·
                  refine ⟨149011287187103204740403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1589453729995767517230965 149011287187103204740403)
                  ·
                    rfl

theorem cell22_1305893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_1305893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305893 prefixEnd_1305893 := by exact prefixLift 1305893
  have htrace : WordTrace (prefixWord ++ tailWord_1305893) baseStart_1305893 baseEnd_1305893 := by
    simpa [prefixWord, tailWord_1305893, baseEnd_1305893] using wordTrace_append hprefix tailTrace_1305893
  have hstable : (prefixWord ++ tailWord_1305893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305893).length < 2 ^ (prefixWord ++ tailWord_1305893).sum := by decide
  have hdescent : baseEnd_1305893 < baseStart_1305893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305904 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 6]
def baseStart_1305904 : Nat := 118140960795 + 1305904 * 2 ^ 59
def prefixEnd_1305904 : Nat := 4983230072969 + 3 ^ 40 * 1305904 * 2
def baseEnd_1305904 : Nat := 149012542362036417398725

theorem tailTrace_1305904 : CollatzResearch.WordTrace tailWord_1305904 prefixEnd_1305904 149012542362036417398725 := by
  unfold tailWord_1305904
  simp only [CollatzResearch.WordTrace]
  refine ⟨23815115930470156745966383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31753487907293542327955177 23815115930470156745966383)
  ·
    refine ⟨35722673895705235118949575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23815115930470156745966383 35722673895705235118949575)
    ·
      refine ⟨53584010843557852678424363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35722673895705235118949575 53584010843557852678424363)
      ·
        refine ⟨80376016265336779017636545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53584010843557852678424363 80376016265336779017636545)
        ·
          refine ⟨60282012199002584263227409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80376016265336779017636545 60282012199002584263227409)
          ·
            refine ⟨45211509149251938197420557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60282012199002584263227409 45211509149251938197420557)
            ·
              refine ⟨16954315930969476824032709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45211509149251938197420557 16954315930969476824032709)
              ·
                refine ⟨3178934237056776904506133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16954315930969476824032709 3178934237056776904506133)
                ·
                  refine ⟨149012542362036417398725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3178934237056776904506133 149012542362036417398725)
                  ·
                    rfl

theorem cell22_1305904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_1305904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305904 prefixEnd_1305904 := by exact prefixLift 1305904
  have htrace : WordTrace (prefixWord ++ tailWord_1305904) baseStart_1305904 baseEnd_1305904 := by
    simpa [prefixWord, tailWord_1305904, baseEnd_1305904] using wordTrace_append hprefix tailTrace_1305904
  have hstable : (prefixWord ++ tailWord_1305904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305904).length < 2 ^ (prefixWord ++ tailWord_1305904).sum := by decide
  have hdescent : baseEnd_1305904 < baseStart_1305904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1305936 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 4, 3]
def baseStart_1305936 : Nat := 118140960795 + 1305936 * 2 ^ 59
def prefixEnd_1305936 : Nat := 4983230072969 + 3 ^ 40 * 1305936 * 2
def baseEnd_1305936 : Nat := 447048581340071835396077

theorem tailTrace_1305936 : CollatzResearch.WordTrace tailWord_1305936 prefixEnd_1305936 447048581340071835396077 := by
  unfold tailWord_1305936
  simp only [CollatzResearch.WordTrace]
  refine ⟨23815699498412191478548831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31754265997882921971398441 23815699498412191478548831)
  ·
    refine ⟨35723549247618287217823247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23815699498412191478548831 35723549247618287217823247)
    ·
      refine ⟨53585323871427430826734871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35723549247618287217823247 53585323871427430826734871)
      ·
        refine ⟨80377985807141146240102307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53585323871427430826734871 80377985807141146240102307)
        ·
          refine ⟨120566978710711719360153461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80377985807141146240102307 120566978710711719360153461)
          ·
            refine ⟨11303154254129223690014387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120566978710711719360153461 11303154254129223690014387)
            ·
              refine ⟨16954731381193835535021581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11303154254129223690014387 16954731381193835535021581)
              ·
                refine ⟨6358024267947688325633093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16954731381193835535021581 6358024267947688325633093)
                ·
                  refine ⟨1192129550240191561056205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6358024267947688325633093 1192129550240191561056205)
                  ·
                    refine ⟨447048581340071835396077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1192129550240191561056205 447048581340071835396077)
                    ·
                      rfl

theorem cell22_1305936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_1305936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1305936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1305936 prefixEnd_1305936 := by exact prefixLift 1305936
  have htrace : WordTrace (prefixWord ++ tailWord_1305936) baseStart_1305936 baseEnd_1305936 := by
    simpa [prefixWord, tailWord_1305936, baseEnd_1305936] using wordTrace_append hprefix tailTrace_1305936
  have hstable : (prefixWord ++ tailWord_1305936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1305936).length < 2 ^ (prefixWord ++ tailWord_1305936).sum := by decide
  have hdescent : baseEnd_1305936 < baseStart_1305936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1305936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306088 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1306088 : Nat := 118140960795 + 1306088 * 2 ^ 59
def prefixEnd_1306088 : Nat := 4983230072969 + 3 ^ 40 * 1306088 * 2
def baseEnd_1306088 : Nat := 447100614046394105595611

theorem tailTrace_1306088 : CollatzResearch.WordTrace tailWord_1306088 prefixEnd_1306088 447100614046394105595611 := by
  unfold tailWord_1306088
  simp only [CollatzResearch.WordTrace]
  refine ⟨23818471446136856458315459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31757961928182475277753945 23818471446136856458315459)
  ·
    refine ⟨35727707169205284687473189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23818471446136856458315459 35727707169205284687473189)
    ·
      refine ⟨6698945094225990878901223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35727707169205284687473189 6698945094225990878901223)
      ·
        refine ⟨10048417641338986318351835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6698945094225990878901223 10048417641338986318351835)
        ·
          refine ⟨15072626462008479477527753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10048417641338986318351835 15072626462008479477527753)
          ·
            refine ⟨11304469846506359608145815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15072626462008479477527753 11304469846506359608145815)
            ·
              refine ⟨16956704769759539412218723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11304469846506359608145815 16956704769759539412218723)
              ·
                refine ⟨25435057154639309118328085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16956704769759539412218723 25435057154639309118328085)
                ·
                  refine ⟨1192268304123717614921629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25435057154639309118328085 1192268304123717614921629)
                  ·
                    refine ⟨447100614046394105595611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1192268304123717614921629 447100614046394105595611)
                    ·
                      rfl

theorem cell22_1306088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1306088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306088 prefixEnd_1306088 := by exact prefixLift 1306088
  have htrace : WordTrace (prefixWord ++ tailWord_1306088) baseStart_1306088 baseEnd_1306088 := by
    simpa [prefixWord, tailWord_1306088, baseEnd_1306088] using wordTrace_append hprefix tailTrace_1306088
  have hstable : (prefixWord ++ tailWord_1306088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306088).length < 2 ^ (prefixWord ++ tailWord_1306088).sum := by decide
  have hdescent : baseEnd_1306088 < baseStart_1306088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306122 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_1306122 : Nat := 118140960795 + 1306122 * 2 ^ 59
def prefixEnd_1306122 : Nat := 4983230072969 + 3 ^ 40 * 1306122 * 2
def baseEnd_1306122 : Nat := 447112252941229350245507

theorem tailTrace_1306122 : CollatzResearch.WordTrace tailWord_1306122 prefixEnd_1306122 447112252941229350245507 := by
  unfold tailWord_1306122
  simp only [CollatzResearch.WordTrace]
  refine ⟨11909545743537634180842155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31758788649433691148912413 11909545743537634180842155)
  ·
    refine ⟨17864318615306451271263233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11909545743537634180842155 17864318615306451271263233)
    ·
      refine ⟨13398238961479838453447425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17864318615306451271263233 13398238961479838453447425)
      ·
        refine ⟨10048679221109878840085569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13398238961479838453447425 10048679221109878840085569)
        ·
          refine ⟨7536509415832409130064177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10048679221109878840085569 7536509415832409130064177)
          ·
            refine ⟨5652382061874306847548133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7536509415832409130064177 5652382061874306847548133)
            ·
              refine ⟨1059821636601432533915275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5652382061874306847548133 1059821636601432533915275)
              ·
                refine ⟨1589732454902148800872913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059821636601432533915275 1589732454902148800872913)
                ·
                  refine ⟨1192299341176611600654685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1589732454902148800872913 1192299341176611600654685)
                  ·
                    refine ⟨447112252941229350245507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1192299341176611600654685 447112252941229350245507)
                    ·
                      rfl

theorem cell22_1306122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_1306122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306122 prefixEnd_1306122 := by exact prefixLift 1306122
  have htrace : WordTrace (prefixWord ++ tailWord_1306122) baseStart_1306122 baseEnd_1306122 := by
    simpa [prefixWord, tailWord_1306122, baseEnd_1306122] using wordTrace_append hprefix tailTrace_1306122
  have hstable : (prefixWord ++ tailWord_1306122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306122).length < 2 ^ (prefixWord ++ tailWord_1306122).sum := by decide
  have hdescent : baseEnd_1306122 < baseStart_1306122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306163 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 5]
def baseStart_1306163 : Nat := 118140960795 + 1306163 * 2 ^ 59
def prefixEnd_1306163 : Nat := 4983230072969 + 3 ^ 40 * 1306163 * 2
def baseEnd_1306163 : Nat := 149042096026372969990127

theorem tailTrace_1306163 : CollatzResearch.WordTrace tailWord_1306163 prefixEnd_1306163 149042096026372969990127 := by
  unfold tailWord_1306163
  simp only [CollatzResearch.WordTrace]
  refine ⟨47639678367002000725611143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31759785578001333817074095 47639678367002000725611143)
  ·
    refine ⟨71459517550503001088416715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47639678367002000725611143 71459517550503001088416715)
    ·
      refine ⟨107189276325754501632625073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71459517550503001088416715 107189276325754501632625073)
      ·
        refine ⟨80391957244315876224468805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107189276325754501632625073 80391957244315876224468805)
        ·
          refine ⟨15073491983309226792087901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80391957244315876224468805 15073491983309226792087901)
          ·
            refine ⟨5652559493740960047032963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15073491983309226792087901 5652559493740960047032963)
            ·
              refine ⟨8478839240611440070549445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652559493740960047032963 8478839240611440070549445)
              ·
                refine ⟨1589782357614645013228021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8478839240611440070549445 1589782357614645013228021)
                ·
                  refine ⟨149042096026372969990127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1589782357614645013228021 149042096026372969990127)
                  ·
                    rfl

theorem cell22_1306163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 5].length) (baseStart_1306163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306163 prefixEnd_1306163 := by exact prefixLift 1306163
  have htrace : WordTrace (prefixWord ++ tailWord_1306163) baseStart_1306163 baseEnd_1306163 := by
    simpa [prefixWord, tailWord_1306163, baseEnd_1306163] using wordTrace_append hprefix tailTrace_1306163
  have hstable : (prefixWord ++ tailWord_1306163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306163).length < 2 ^ (prefixWord ++ tailWord_1306163).sum := by decide
  have hdescent : baseEnd_1306163 < baseStart_1306163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306167 : List Nat := [1, 1, 3, 1, 2, 5, 1, 4, 1, 3]
def baseStart_1306167 : Nat := 118140960795 + 1306167 * 2 ^ 59
def prefixEnd_1306167 : Nat := 4983230072969 + 3 ^ 40 * 1306167 * 2
def baseEnd_1306167 : Nat := 447127657360864232870369

theorem tailTrace_1306167 : CollatzResearch.WordTrace tailWord_1306167 prefixEnd_1306167 447127657360864232870369 := by
  unfold tailWord_1306167
  simp only [CollatzResearch.WordTrace]
  refine ⟨47639824258987509408756755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31759882839325006272504503 47639824258987509408756755)
  ·
    refine ⟨71459736388481264113135133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47639824258987509408756755 71459736388481264113135133)
    ·
      refine ⟨26797401145680474042425675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71459736388481264113135133 26797401145680474042425675)
      ·
        refine ⟨40196101718520711063638513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26797401145680474042425675 40196101718520711063638513)
        ·
          refine ⟨30147076288890533297728885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40196101718520711063638513 30147076288890533297728885)
          ·
            refine ⟨2826288402083487496662083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30147076288890533297728885 2826288402083487496662083)
            ·
              refine ⟨4239432603125231244993125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826288402083487496662083 4239432603125231244993125)
              ·
                refine ⟨794893613085980858436211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4239432603125231244993125 794893613085980858436211)
                ·
                  refine ⟨1192340419628971287654317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794893613085980858436211 1192340419628971287654317)
                  ·
                    refine ⟨447127657360864232870369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1192340419628971287654317 447127657360864232870369)
                    ·
                      rfl

theorem cell22_1306167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_1306167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306167 prefixEnd_1306167 := by exact prefixLift 1306167
  have htrace : WordTrace (prefixWord ++ tailWord_1306167) baseStart_1306167 baseEnd_1306167 := by
    simpa [prefixWord, tailWord_1306167, baseEnd_1306167] using wordTrace_append hprefix tailTrace_1306167
  have hstable : (prefixWord ++ tailWord_1306167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306167).length < 2 ^ (prefixWord ++ tailWord_1306167).sum := by decide
  have hdescent : baseEnd_1306167 < baseStart_1306167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306193 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_1306193 : Nat := 118140960795 + 1306193 * 2 ^ 59
def prefixEnd_1306193 : Nat := 4983230072969 + 3 ^ 40 * 1306193 * 2
def baseEnd_1306193 : Nat := 447136557692208831720289

theorem tailTrace_1306193 : CollatzResearch.WordTrace tailWord_1306193 prefixEnd_1306193 447136557692208831720289 := by
  unfold tailWord_1306193
  simp only [CollatzResearch.WordTrace]
  refine ⟨47640772556893315849203233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31760515037928877232802155 47640772556893315849203233)
  ·
    refine ⟨35730579417669986886902425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47640772556893315849203233 35730579417669986886902425)
    ·
      refine ⟨26797934563252490165176819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35730579417669986886902425 26797934563252490165176819)
      ·
        refine ⟨40196901844878735247765229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26797934563252490165176819 40196901844878735247765229)
        ·
          refine ⟨15073838191829525717911961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40196901844878735247765229 15073838191829525717911961)
          ·
            refine ⟨11305378643872144288433971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15073838191829525717911961 11305378643872144288433971)
            ·
              refine ⟨16958067965808216432650957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11305378643872144288433971 16958067965808216432650957)
              ·
                refine ⟨6359275487178081162244109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16958067965808216432650957 6359275487178081162244109)
                ·
                  refine ⟨2384728307691780435841541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6359275487178081162244109 2384728307691780435841541)
                  ·
                    refine ⟨447136557692208831720289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2384728307691780435841541 447136557692208831720289)
                    ·
                      rfl

theorem cell22_1306193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_1306193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306193 prefixEnd_1306193 := by exact prefixLift 1306193
  have htrace : WordTrace (prefixWord ++ tailWord_1306193) baseStart_1306193 baseEnd_1306193 := by
    simpa [prefixWord, tailWord_1306193, baseEnd_1306193] using wordTrace_append hprefix tailTrace_1306193
  have hstable : (prefixWord ++ tailWord_1306193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306193).length < 2 ^ (prefixWord ++ tailWord_1306193).sum := by decide
  have hdescent : baseEnd_1306193 < baseStart_1306193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306270 : List Nat := [4, 3, 1, 1, 1, 2, 10]
def baseStart_1306270 : Nat := 118140960795 + 1306270 * 2 ^ 59
def prefixEnd_1306270 : Nat := 4983230072969 + 3 ^ 40 * 1306270 * 2
def baseEnd_1306270 : Nat := 16561589495029862872039

theorem tailTrace_1306270 : CollatzResearch.WordTrace tailWord_1306270 prefixEnd_1306270 16561589495029862872039 := by
  unfold tailWord_1306270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5955447622201794749969533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31762387318409571999837509 5955447622201794749969533)
  ·
    refine ⟨2233292858325673031238575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5955447622201794749969533 2233292858325673031238575)
    ·
      refine ⟨3349939287488509546857863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2233292858325673031238575 3349939287488509546857863)
      ·
        refine ⟨5024908931232764320286795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349939287488509546857863 5024908931232764320286795)
        ·
          refine ⟨7537363396849146480430193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024908931232764320286795 7537363396849146480430193)
          ·
            refine ⟨5653022547636859860322645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7537363396849146480430193 5653022547636859860322645)
            ·
              refine ⟨16561589495029862872039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5653022547636859860322645 16561589495029862872039)
              ·
                rfl

theorem cell22_1306270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 10].length) (baseStart_1306270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306270 prefixEnd_1306270 := by exact prefixLift 1306270
  have htrace : WordTrace (prefixWord ++ tailWord_1306270) baseStart_1306270 baseEnd_1306270 := by
    simpa [prefixWord, tailWord_1306270, baseEnd_1306270] using wordTrace_append hprefix tailTrace_1306270
  have hstable : (prefixWord ++ tailWord_1306270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306270).length < 2 ^ (prefixWord ++ tailWord_1306270).sum := by decide
  have hdescent : baseEnd_1306270 < baseStart_1306270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306460 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1306460 : Nat := 118140960795 + 1306460 * 2 ^ 59
def prefixEnd_1306460 : Nat := 4983230072969 + 3 ^ 40 * 1306460 * 2
def baseEnd_1306460 : Nat := 447227957248709135294471

theorem tailTrace_1306460 : CollatzResearch.WordTrace tailWord_1306460 prefixEnd_1306460 447227957248709135294471 := by
  unfold tailWord_1306460
  simp only [CollatzResearch.WordTrace]
  refine ⟨23825255423463010224586417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31767007231284013632781889 23825255423463010224586417)
  ·
    refine ⟨17868941567597257668439813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23825255423463010224586417 17868941567597257668439813)
    ·
      refine ⟨3350426543924485812832465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17868941567597257668439813 3350426543924485812832465)
      ·
        refine ⟨2512819907943364359624349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3350426543924485812832465 2512819907943364359624349)
        ·
          refine ⟨942307465478761634859131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2512819907943364359624349 942307465478761634859131)
          ·
            refine ⟨1413461198218142452288697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942307465478761634859131 1413461198218142452288697)
            ·
              refine ⟨1060095898663606839216523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1413461198218142452288697 1060095898663606839216523)
              ·
                refine ⟨1590143847995410258824785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060095898663606839216523 1590143847995410258824785)
                ·
                  refine ⟨1192607885996557694118589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1590143847995410258824785 1192607885996557694118589)
                  ·
                    refine ⟨447227957248709135294471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1192607885996557694118589 447227957248709135294471)
                    ·
                      rfl

theorem cell22_1306460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1306460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306460 prefixEnd_1306460 := by exact prefixLift 1306460
  have htrace : WordTrace (prefixWord ++ tailWord_1306460) baseStart_1306460 baseEnd_1306460 := by
    simpa [prefixWord, tailWord_1306460, baseEnd_1306460] using wordTrace_append hprefix tailTrace_1306460
  have hstable : (prefixWord ++ tailWord_1306460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306460).length < 2 ^ (prefixWord ++ tailWord_1306460).sum := by decide
  have hdescent : baseEnd_1306460 < baseStart_1306460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306465 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1306465 : Nat := 118140960795 + 1306465 * 2 ^ 59
def prefixEnd_1306465 : Nat := 4983230072969 + 3 ^ 40 * 1306465 * 2
def baseEnd_1306465 : Nat := 447229668850890788919455

theorem tailTrace_1306465 : CollatzResearch.WordTrace tailWord_1306465 prefixEnd_1306465 447229668850890788919455 := by
  unfold tailWord_1306465
  simp only [CollatzResearch.WordTrace]
  refine ⟨47650693211907906303104849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31767128807938604202069899 47650693211907906303104849)
  ·
    refine ⟨35738019908930929727328637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47650693211907906303104849 35738019908930929727328637)
    ·
      refine ⟨13401757465849098647748239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35738019908930929727328637 13401757465849098647748239)
      ·
        refine ⟨20102636198773647971622359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13401757465849098647748239 20102636198773647971622359)
        ·
          refine ⟨30153954298160471957433539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20102636198773647971622359 30153954298160471957433539)
          ·
            refine ⟨45230931447240707936150309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30153954298160471957433539 45230931447240707936150309)
            ·
              refine ⟨8480799646357632738028183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45230931447240707936150309 8480799646357632738028183)
              ·
                refine ⟨12721199469536449107042275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8480799646357632738028183 12721199469536449107042275)
                ·
                  refine ⟨19081799204304673660563413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12721199469536449107042275 19081799204304673660563413)
                  ·
                    refine ⟨447229668850890788919455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19081799204304673660563413 447229668850890788919455)
                    ·
                      rfl

theorem cell22_1306465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1306465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306465 prefixEnd_1306465 := by exact prefixLift 1306465
  have htrace : WordTrace (prefixWord ++ tailWord_1306465) baseStart_1306465 baseEnd_1306465 := by
    simpa [prefixWord, tailWord_1306465, baseEnd_1306465] using wordTrace_append hprefix tailTrace_1306465
  have hstable : (prefixWord ++ tailWord_1306465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306465).length < 2 ^ (prefixWord ++ tailWord_1306465).sum := by decide
  have hdescent : baseEnd_1306465 < baseStart_1306465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306514 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1306514 : Nat := 118140960795 + 1306514 * 2 ^ 59
def prefixEnd_1306514 : Nat := 4983230072969 + 3 ^ 40 * 1306514 * 2
def baseEnd_1306514 : Nat := 447246442552270994444305

theorem tailTrace_1306514 : CollatzResearch.WordTrace tailWord_1306514 prefixEnd_1306514 447246442552270994444305 := by
  unfold tailWord_1306514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11913120097182596917909649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31768320259153591781092397 11913120097182596917909649)
  ·
    refine ⟨8934840072886947688432237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11913120097182596917909649 8934840072886947688432237)
    ·
      refine ⟨3350565027332605383162089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8934840072886947688432237 3350565027332605383162089)
      ·
        refine ⟨2512923770499454037371567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3350565027332605383162089 2512923770499454037371567)
        ·
          refine ⟨3769385655749181056057351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512923770499454037371567 3769385655749181056057351)
          ·
            refine ⟨5654078483623771584086027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3769385655749181056057351 5654078483623771584086027)
            ·
              refine ⟨8481117725435657376129041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5654078483623771584086027 8481117725435657376129041)
              ·
                refine ⟨6360838294076743032096781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8481117725435657376129041 6360838294076743032096781)
                ·
                  refine ⟨2385314360278778637036293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6360838294076743032096781 2385314360278778637036293)
                  ·
                    refine ⟨447246442552270994444305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2385314360278778637036293 447246442552270994444305)
                    ·
                      rfl

theorem cell22_1306514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1306514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306514 prefixEnd_1306514 := by exact prefixLift 1306514
  have htrace : WordTrace (prefixWord ++ tailWord_1306514) baseStart_1306514 baseEnd_1306514 := by
    simpa [prefixWord, tailWord_1306514, baseEnd_1306514] using wordTrace_append hprefix tailTrace_1306514
  have hstable : (prefixWord ++ tailWord_1306514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306514).length < 2 ^ (prefixWord ++ tailWord_1306514).sum := by decide
  have hdescent : baseEnd_1306514 < baseStart_1306514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306529 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 6]
def baseStart_1306529 : Nat := 118140960795 + 1306529 * 2 ^ 59
def prefixEnd_1306529 : Nat := 4983230072969 + 3 ^ 40 * 1306529 * 2
def baseEnd_1306529 : Nat := 149083859119605318439753

theorem tailTrace_1306529 : CollatzResearch.WordTrace tailWord_1306529 prefixEnd_1306529 149083859119605318439753 := by
  unfold tailWord_1306529
  simp only [CollatzResearch.WordTrace]
  refine ⟨47653027483676045233434641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31768684989117363488956427 47653027483676045233434641)
  ·
    refine ⟨35739770612757033925075981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47653027483676045233434641 35739770612757033925075981)
    ·
      refine ⟨13402413979783887721903493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35739770612757033925075981 13402413979783887721903493)
      ·
        refine ⟨2512952621209478947856905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13402413979783887721903493 2512952621209478947856905)
        ·
          refine ⟨1884714465907109210892679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2512952621209478947856905 1884714465907109210892679)
          ·
            refine ⟨2827071698860663816339019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884714465907109210892679 2827071698860663816339019)
            ·
              refine ⟨4240607548290995724508529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827071698860663816339019 4240607548290995724508529)
              ·
                refine ⟨3180455661218246793381397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4240607548290995724508529 3180455661218246793381397)
                ·
                  refine ⟨149083859119605318439753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3180455661218246793381397 149083859119605318439753)
                  ·
                    rfl

theorem cell22_1306529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_1306529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306529 prefixEnd_1306529 := by exact prefixLift 1306529
  have htrace : WordTrace (prefixWord ++ tailWord_1306529) baseStart_1306529 baseEnd_1306529 := by
    simpa [prefixWord, tailWord_1306529, baseEnd_1306529] using wordTrace_append hprefix tailTrace_1306529
  have hstable : (prefixWord ++ tailWord_1306529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306529).length < 2 ^ (prefixWord ++ tailWord_1306529).sum := by decide
  have hdescent : baseEnd_1306529 < baseStart_1306529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306548 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1306548 : Nat := 118140960795 + 1306548 * 2 ^ 59
def prefixEnd_1306548 : Nat := 4983230072969 + 3 ^ 40 * 1306548 * 2
def baseEnd_1306548 : Nat := 447258081447106239094201

theorem tailTrace_1306548 : CollatzResearch.WordTrace tailWord_1306548 prefixEnd_1306548 447258081447106239094201 := by
  unfold tailWord_1306548
  simp only [CollatzResearch.WordTrace]
  refine ⟨23826860235303605739188149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31769146980404807652250865 23826860235303605739188149)
  ·
    refine ⟨2233768147059713038048889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23826860235303605739188149 2233768147059713038048889)
    ·
      refine ⟨1675326110294784778536667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2233768147059713038048889 1675326110294784778536667)
      ·
        refine ⟨2512989165442177167805001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1675326110294784778536667 2512989165442177167805001)
        ·
          refine ⟨1884741874081632875853751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2512989165442177167805001 1884741874081632875853751)
          ·
            refine ⟨2827112811122449313780627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884741874081632875853751 2827112811122449313780627)
            ·
              refine ⟨4240669216683673970670941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827112811122449313780627 4240669216683673970670941)
              ·
                refine ⟨1590250956256377739001603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4240669216683673970670941 1590250956256377739001603)
                ·
                  refine ⟨2385376434384566608502405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590250956256377739001603 2385376434384566608502405)
                  ·
                    refine ⟨447258081447106239094201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2385376434384566608502405 447258081447106239094201)
                    ·
                      rfl

theorem cell22_1306548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1306548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306548 prefixEnd_1306548 := by exact prefixLift 1306548
  have htrace : WordTrace (prefixWord ++ tailWord_1306548) baseStart_1306548 baseEnd_1306548 := by
    simpa [prefixWord, tailWord_1306548, baseEnd_1306548] using wordTrace_append hprefix tailTrace_1306548
  have hstable : (prefixWord ++ tailWord_1306548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306548).length < 2 ^ (prefixWord ++ tailWord_1306548).sum := by decide
  have hdescent : baseEnd_1306548 < baseStart_1306548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306557 : List Nat := [1, 4, 1, 2, 3, 2, 9]
def baseStart_1306557 : Nat := 118140960795 + 1306557 * 2 ^ 59
def prefixEnd_1306557 : Nat := 4983230072969 + 3 ^ 40 * 1306557 * 2
def baseEnd_1306557 : Nat := 16565228234482711689599

theorem tailTrace_1306557 : CollatzResearch.WordTrace tailWord_1306557 prefixEnd_1306557 16565228234482711689599 := by
  unfold tailWord_1306557
  simp only [CollatzResearch.WordTrace]
  refine ⟨47654048727574606015453925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31769365818383070676969283 47654048727574606015453925)
  ·
    refine ⟨8935134136420238627897611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47654048727574606015453925 8935134136420238627897611)
    ·
      refine ⟨13402701204630357941846417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8935134136420238627897611 13402701204630357941846417)
      ·
        refine ⟨10052025903472768456384813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13402701204630357941846417 10052025903472768456384813)
        ·
          refine ⟨3769509713802288171144305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10052025903472768456384813 3769509713802288171144305)
          ·
            refine ⟨2827132285351716128358229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3769509713802288171144305 2827132285351716128358229)
            ·
              refine ⟨16565228234482711689599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2827132285351716128358229 16565228234482711689599)
              ·
                rfl

theorem cell22_1306557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 9].length) (baseStart_1306557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306557 prefixEnd_1306557 := by exact prefixLift 1306557
  have htrace : WordTrace (prefixWord ++ tailWord_1306557) baseStart_1306557 baseEnd_1306557 := by
    simpa [prefixWord, tailWord_1306557, baseEnd_1306557] using wordTrace_append hprefix tailTrace_1306557
  have hstable : (prefixWord ++ tailWord_1306557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306557).length < 2 ^ (prefixWord ++ tailWord_1306557).sum := by decide
  have hdescent : baseEnd_1306557 < baseStart_1306557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306578 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_1306578 : Nat := 118140960795 + 1306578 * 2 ^ 59
def prefixEnd_1306578 : Nat := 4983230072969 + 3 ^ 40 * 1306578 * 2
def baseEnd_1306578 : Nat := 447268351060196160844109

theorem tailTrace_1306578 : CollatzResearch.WordTrace tailWord_1306578 prefixEnd_1306578 447268351060196160844109 := by
  unfold tailWord_1306578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11913703665124631650492097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31769876440332351067978925 11913703665124631650492097)
  ·
    refine ⟨8935277748843473737869073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11913703665124631650492097 8935277748843473737869073)
    ·
      refine ⟨6701458311632605303401805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8935277748843473737869073 6701458311632605303401805)
      ·
        refine ⟨2513046866862226988775677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6701458311632605303401805 2513046866862226988775677)
        ·
          refine ⟨942392575073335120790879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2513046866862226988775677 942392575073335120790879)
          ·
            refine ⟨1413588862610002681186319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942392575073335120790879 1413588862610002681186319)
            ·
              refine ⟨2120383293915004021779479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413588862610002681186319 2120383293915004021779479)
              ·
                refine ⟨3180574940872506032669219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120383293915004021779479 3180574940872506032669219)
                ·
                  refine ⟨4770862411308759049003829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180574940872506032669219 4770862411308759049003829)
                  ·
                    refine ⟨447268351060196160844109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4770862411308759049003829 447268351060196160844109)
                    ·
                      rfl

theorem cell22_1306578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_1306578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306578 prefixEnd_1306578 := by exact prefixLift 1306578
  have htrace : WordTrace (prefixWord ++ tailWord_1306578) baseStart_1306578 baseEnd_1306578 := by
    simpa [prefixWord, tailWord_1306578, baseEnd_1306578] using wordTrace_append hprefix tailTrace_1306578
  have hstable : (prefixWord ++ tailWord_1306578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306578).length < 2 ^ (prefixWord ++ tailWord_1306578).sum := by decide
  have hdescent : baseEnd_1306578 < baseStart_1306578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306602 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_1306602 : Nat := 118140960795 + 1306602 * 2 ^ 59
def prefixEnd_1306602 : Nat := 4983230072969 + 3 ^ 40 * 1306602 * 2
def baseEnd_1306602 : Nat := 149092188916889366081345

theorem tailTrace_1306602 : CollatzResearch.WordTrace tailWord_1306602 prefixEnd_1306602 149092188916889366081345 := by
  unfold tailWord_1306602
  simp only [CollatzResearch.WordTrace]
  refine ⟨11913922503102894675210515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31770460008274385800561373 11913922503102894675210515)
  ·
    refine ⟨17870883754654342012815773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11913922503102894675210515 17870883754654342012815773)
    ·
      refine ⟨6701581407995378254805915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17870883754654342012815773 6701581407995378254805915)
      ·
        refine ⟨10052372111993067382208873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701581407995378254805915 10052372111993067382208873)
        ·
          refine ⟨7539279083994800536656655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10052372111993067382208873 7539279083994800536656655)
          ·
            refine ⟨11308918625992200804984983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7539279083994800536656655 11308918625992200804984983)
            ·
              refine ⟨16963377938988301207477475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11308918625992200804984983 16963377938988301207477475)
              ·
                refine ⟨25445066908482451811216213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16963377938988301207477475 25445066908482451811216213)
                ·
                  refine ⟨149092188916889366081345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25445066908482451811216213 149092188916889366081345)
                  ·
                    rfl

theorem cell22_1306602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_1306602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306602 prefixEnd_1306602 := by exact prefixLift 1306602
  have htrace : WordTrace (prefixWord ++ tailWord_1306602) baseStart_1306602 baseEnd_1306602 := by
    simpa [prefixWord, tailWord_1306602, baseEnd_1306602] using wordTrace_append hprefix tailTrace_1306602
  have hstable : (prefixWord ++ tailWord_1306602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306602).length < 2 ^ (prefixWord ++ tailWord_1306602).sum := by decide
  have hdescent : baseEnd_1306602 < baseStart_1306602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306679 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 4, 3]
def baseStart_1306679 : Nat := 118140960795 + 1306679 * 2 ^ 59
def prefixEnd_1306679 : Nat := 4983230072969 + 3 ^ 40 * 1306679 * 2
def baseEnd_1306679 : Nat := 447302925424265564068799

theorem tailTrace_1306679 : CollatzResearch.WordTrace tailWord_1306679 prefixEnd_1306679 447302925424265564068799 := by
  unfold tailWord_1306679
  simp only [CollatzResearch.WordTrace]
  refine ⟨47658498433132620851395091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31772332288755080567596727 47658498433132620851395091)
  ·
    refine ⟨71487747649698931277092637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47658498433132620851395091 71487747649698931277092637)
    ·
      refine ⟨26807905368637099228909739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71487747649698931277092637 26807905368637099228909739)
      ·
        refine ⟨40211858052955648843364609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26807905368637099228909739 40211858052955648843364609)
        ·
          refine ⟨30158893539716736632523457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40211858052955648843364609 30158893539716736632523457)
          ·
            refine ⟨22619170154787552474392593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30158893539716736632523457 22619170154787552474392593)
            ·
              refine ⟨16964377616090664355794445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22619170154787552474392593 16964377616090664355794445)
              ·
                refine ⟨6361641606033999133422917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16964377616090664355794445 6361641606033999133422917)
                ·
                  refine ⟨1192807801131374837516797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6361641606033999133422917 1192807801131374837516797)
                  ·
                    refine ⟨447302925424265564068799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1192807801131374837516797 447302925424265564068799)
                    ·
                      rfl

theorem cell22_1306679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_1306679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306679 prefixEnd_1306679 := by exact prefixLift 1306679
  have htrace : WordTrace (prefixWord ++ tailWord_1306679) baseStart_1306679 baseEnd_1306679 := by
    simpa [prefixWord, tailWord_1306679, baseEnd_1306679] using wordTrace_append hprefix tailTrace_1306679
  have hstable : (prefixWord ++ tailWord_1306679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306679).length < 2 ^ (prefixWord ++ tailWord_1306679).sum := by decide
  have hdescent : baseEnd_1306679 < baseStart_1306679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306730 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1306730 : Nat := 118140960795 + 1306730 * 2 ^ 59
def prefixEnd_1306730 : Nat := 4983230072969 + 3 ^ 40 * 1306730 * 2
def baseEnd_1306730 : Nat := 447320383766518431043643

theorem tailTrace_1306730 : CollatzResearch.WordTrace tailWord_1306730 prefixEnd_1306730 447320383766518431043643 := by
  unfold tailWord_1306730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11915089638986964140375411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31773572370631904374334429 11915089638986964140375411)
  ·
    refine ⟨17872634458480446210563117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11915089638986964140375411 17872634458480446210563117)
    ·
      refine ⟨6702237921930167328961169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17872634458480446210563117 6702237921930167328961169)
      ·
        refine ⟨5026678441447625496720877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6702237921930167328961169 5026678441447625496720877)
        ·
          refine ⟨1885004415542859561270329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5026678441447625496720877 1885004415542859561270329)
          ·
            refine ⟨1413753311657144670952747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1885004415542859561270329 1413753311657144670952747)
            ·
              refine ⟨2120629967485717006429121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413753311657144670952747 2120629967485717006429121)
              ·
                refine ⟨1590472475614287754821841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2120629967485717006429121 1590472475614287754821841)
                ·
                  refine ⟨1192854356710715816116381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1590472475614287754821841 1192854356710715816116381)
                  ·
                    refine ⟨447320383766518431043643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1192854356710715816116381 447320383766518431043643)
                    ·
                      rfl

theorem cell22_1306730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1306730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306730 prefixEnd_1306730 := by exact prefixLift 1306730
  have htrace : WordTrace (prefixWord ++ tailWord_1306730) baseStart_1306730 baseEnd_1306730 := by
    simpa [prefixWord, tailWord_1306730, baseEnd_1306730] using wordTrace_append hprefix tailTrace_1306730
  have hstable : (prefixWord ++ tailWord_1306730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306730).length < 2 ^ (prefixWord ++ tailWord_1306730).sum := by decide
  have hdescent : baseEnd_1306730 < baseStart_1306730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306848 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 2, 3]
def baseStart_1306848 : Nat := 118140960795 + 1306848 * 2 ^ 59
def prefixEnd_1306848 : Nat := 4983230072969 + 3 ^ 40 * 1306848 * 2
def baseEnd_1306848 : Nat := 447360777578005456593281

theorem tailTrace_1306848 : CollatzResearch.WordTrace tailWord_1306848 prefixEnd_1306848 447360777578005456593281 := by
  unfold tailWord_1306848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23832331184760181357148599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31776441579680241809531465 23832331184760181357148599)
  ·
    refine ⟨35748496777140272035722899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23832331184760181357148599 35748496777140272035722899)
    ·
      refine ⟨53622745165710408053584349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35748496777140272035722899 53622745165710408053584349)
      ·
        refine ⟨20108529437141403020094131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53622745165710408053584349 20108529437141403020094131)
        ·
          refine ⟨30162794155712104530141197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20108529437141403020094131 30162794155712104530141197)
          ·
            refine ⟨11311047808392039198802949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30162794155712104530141197 11311047808392039198802949)
            ·
              refine ⟨2120821464073507349775553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11311047808392039198802949 2120821464073507349775553)
              ·
                refine ⟨1590616098055130512331665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2120821464073507349775553 1590616098055130512331665)
                ·
                  refine ⟨1192962073541347884248749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1590616098055130512331665 1192962073541347884248749)
                  ·
                    refine ⟨447360777578005456593281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1192962073541347884248749 447360777578005456593281)
                    ·
                      rfl

theorem cell22_1306848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_1306848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306848 prefixEnd_1306848 := by exact prefixLift 1306848
  have htrace : WordTrace (prefixWord ++ tailWord_1306848) baseStart_1306848 baseEnd_1306848 := by
    simpa [prefixWord, tailWord_1306848, baseEnd_1306848] using wordTrace_append hprefix tailTrace_1306848
  have hstable : (prefixWord ++ tailWord_1306848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306848).length < 2 ^ (prefixWord ++ tailWord_1306848).sum := by decide
  have hdescent : baseEnd_1306848 < baseStart_1306848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306878 : List Nat := [4, 2, 2, 1, 1, 1, 5, 6]
def baseStart_1306878 : Nat := 118140960795 + 1306878 * 2 ^ 59
def prefixEnd_1306878 : Nat := 4983230072969 + 3 ^ 40 * 1306878 * 2
def baseEnd_1306878 : Nat := 49707894132343930927021

theorem tailTrace_1306878 : CollatzResearch.WordTrace tailWord_1306878 prefixEnd_1306878 49707894132343930927021 := by
  unfold tailWord_1306878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958219569926459729736161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31777171039607785225259525 5958219569926459729736161)
  ·
    refine ⟨4468664677444844797302121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5958219569926459729736161 4468664677444844797302121)
    ·
      refine ⟨3351498508083633597976591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4468664677444844797302121 3351498508083633597976591)
      ·
        refine ⟨5027247762125450396964887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3351498508083633597976591 5027247762125450396964887)
        ·
          refine ⟨7540871643188175595447331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5027247762125450396964887 7540871643188175595447331)
          ·
            refine ⟨11311307464782263393170997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7540871643188175595447331 11311307464782263393170997)
            ·
              refine ⟨1060435074823337193109781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11311307464782263393170997 1060435074823337193109781)
              ·
                refine ⟨49707894132343930927021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1060435074823337193109781 49707894132343930927021)
                ·
                  rfl

theorem cell22_1306878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_1306878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306878 prefixEnd_1306878 := by exact prefixLift 1306878
  have htrace : WordTrace (prefixWord ++ tailWord_1306878) baseStart_1306878 baseEnd_1306878 := by
    simpa [prefixWord, tailWord_1306878, baseEnd_1306878] using wordTrace_append hprefix tailTrace_1306878
  have hstable : (prefixWord ++ tailWord_1306878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306878).length < 2 ^ (prefixWord ++ tailWord_1306878).sum := by decide
  have hdescent : baseEnd_1306878 < baseStart_1306878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1306936 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_1306936 : Nat := 118140960795 + 1306936 * 2 ^ 59
def prefixEnd_1306936 : Nat := 4983230072969 + 3 ^ 40 * 1306936 * 2
def baseEnd_1306936 : Nat := 447390901776402560393011

theorem tailTrace_1306936 : CollatzResearch.WordTrace tailWord_1306936 prefixEnd_1306936 447390901776402560393011 := by
  unfold tailWord_1306936
  simp only [CollatzResearch.WordTrace]
  refine ⟨23833935996600776871750331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31778581328801035829000441 23833935996600776871750331)
  ·
    refine ⟨35750903994901165307625497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23833935996600776871750331 35750903994901165307625497)
    ·
      refine ⟨26813177996175873980719123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35750903994901165307625497 26813177996175873980719123)
      ·
        refine ⟨40219766994263810971078685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26813177996175873980719123 40219766994263810971078685)
        ·
          refine ⟨15082412622848929114154507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40219766994263810971078685 15082412622848929114154507)
          ·
            refine ⟨22623618934273393671231761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15082412622848929114154507 22623618934273393671231761)
            ·
              refine ⟨16967714200705045253423821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22623618934273393671231761 16967714200705045253423821)
              ·
                refine ⟨6362892825264391970033933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16967714200705045253423821 6362892825264391970033933)
                ·
                  refine ⟨2386084809474146988762725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6362892825264391970033933 2386084809474146988762725)
                  ·
                    refine ⟨447390901776402560393011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2386084809474146988762725 447390901776402560393011)
                    ·
                      rfl

theorem cell22_1306936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_1306936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1306936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1306936 prefixEnd_1306936 := by exact prefixLift 1306936
  have htrace : WordTrace (prefixWord ++ tailWord_1306936) baseStart_1306936 baseEnd_1306936 := by
    simpa [prefixWord, tailWord_1306936, baseEnd_1306936] using wordTrace_append hprefix tailTrace_1306936
  have hstable : (prefixWord ++ tailWord_1306936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1306936).length < 2 ^ (prefixWord ++ tailWord_1306936).sum := by decide
  have hdescent : baseEnd_1306936 < baseStart_1306936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1306936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307092 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1307092 : Nat := 118140960795 + 1307092 * 2 ^ 59
def prefixEnd_1307092 : Nat := 4983230072969 + 3 ^ 40 * 1307092 * 2
def baseEnd_1307092 : Nat := 149148101254823384497511

theorem tailTrace_1307092 : CollatzResearch.WordTrace tailWord_1307092 prefixEnd_1307092 149148101254823384497511 := by
  unfold tailWord_1307092
  simp only [CollatzResearch.WordTrace]
  refine ⟨23836780890318196193089765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31782374520424261590786353 23836780890318196193089765)
  ·
    refine ⟨4469396416934661786204331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23836780890318196193089765 4469396416934661786204331)
    ·
      refine ⟨6704094625401992679306497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469396416934661786204331 6704094625401992679306497)
      ·
        refine ⟨5028070969051494509479873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6704094625401992679306497 5028070969051494509479873)
        ·
          refine ⟨3771053226788620882109905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5028070969051494509479873 3771053226788620882109905)
          ·
            refine ⟨2828289920091465661582429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3771053226788620882109905 2828289920091465661582429)
            ·
              refine ⟨1060608720034299623093411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2828289920091465661582429 1060608720034299623093411)
              ·
                refine ⟨1590913080051449434640117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060608720034299623093411 1590913080051449434640117)
                ·
                  refine ⟨149148101254823384497511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1590913080051449434640117 149148101254823384497511)
                  ·
                    rfl

theorem cell22_1307092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1307092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307092 prefixEnd_1307092 := by exact prefixLift 1307092
  have htrace : WordTrace (prefixWord ++ tailWord_1307092) baseStart_1307092 baseEnd_1307092 := by
    simpa [prefixWord, tailWord_1307092, baseEnd_1307092] using wordTrace_append hprefix tailTrace_1307092
  have hstable : (prefixWord ++ tailWord_1307092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307092).length < 2 ^ (prefixWord ++ tailWord_1307092).sum := by decide
  have hdescent : baseEnd_1307092 < baseStart_1307092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307103 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 6]
def baseStart_1307103 : Nat := 118140960795 + 1307103 * 2 ^ 59
def prefixEnd_1307103 : Nat := 4983230072969 + 3 ^ 40 * 1307103 * 2
def baseEnd_1307103 : Nat := 149149356429756597155833

theorem tailTrace_1307103 : CollatzResearch.WordTrace tailWord_1307103 prefixEnd_1307103 149149356429756597155833 := by
  unfold tailWord_1307103
  simp only [CollatzResearch.WordTrace]
  refine ⟨47673962983596541264829963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31782641989064360843219975 47673962983596541264829963)
  ·
    refine ⟨71510944475394811897244945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47673962983596541264829963 71510944475394811897244945)
    ·
      refine ⟨53633208356546108922933709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71510944475394811897244945 53633208356546108922933709)
      ·
        refine ⟨20112453133704790846100141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53633208356546108922933709 20112453133704790846100141)
        ·
          refine ⟨7542169925139296567287553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20112453133704790846100141 7542169925139296567287553)
          ·
            refine ⟨5656627443854472425465665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7542169925139296567287553 5656627443854472425465665)
            ·
              refine ⟨4242470582890854319099249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5656627443854472425465665 4242470582890854319099249)
              ·
                refine ⟨3181852937168140739324437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4242470582890854319099249 3181852937168140739324437)
                ·
                  refine ⟨149149356429756597155833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3181852937168140739324437 149149356429756597155833)
                  ·
                    rfl

theorem cell22_1307103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 6].length) (baseStart_1307103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307103 prefixEnd_1307103 := by exact prefixLift 1307103
  have htrace : WordTrace (prefixWord ++ tailWord_1307103) baseStart_1307103 baseEnd_1307103 := by
    simpa [prefixWord, tailWord_1307103, baseEnd_1307103] using wordTrace_append hprefix tailTrace_1307103
  have hstable : (prefixWord ++ tailWord_1307103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307103).length < 2 ^ (prefixWord ++ tailWord_1307103).sum := by decide
  have hdescent : baseEnd_1307103 < baseStart_1307103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307105 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_1307105 : Nat := 118140960795 + 1307105 * 2 ^ 59
def prefixEnd_1307105 : Nat := 4983230072969 + 3 ^ 40 * 1307105 * 2
def baseEnd_1307105 : Nat := 447448753930142452917493

theorem tailTrace_1307105 : CollatzResearch.WordTrace tailWord_1307105 prefixEnd_1307105 447448753930142452917493 := by
  unfold tailWord_1307105
  simp only [CollatzResearch.WordTrace]
  refine ⟨47674035929589295606402769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31782690619726197070935179 47674035929589295606402769)
  ·
    refine ⟨35755526947191971704802077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47674035929589295606402769 35755526947191971704802077)
    ·
      refine ⟨13408322605196989389300779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35755526947191971704802077 13408322605196989389300779)
      ·
        refine ⟨20112483907795484083951169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13408322605196989389300779 20112483907795484083951169)
        ·
          refine ⟨15084362930846613062963377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20112483907795484083951169 15084362930846613062963377)
          ·
            refine ⟨11313272198134959797222533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15084362930846613062963377 11313272198134959797222533)
            ·
              refine ⟨2121238537150304961979225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11313272198134959797222533 2121238537150304961979225)
              ·
                refine ⟨1590928902862728721484419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2121238537150304961979225 1590928902862728721484419)
                ·
                  refine ⟨2386393354294093082226629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590928902862728721484419 2386393354294093082226629)
                  ·
                    refine ⟨447448753930142452917493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2386393354294093082226629 447448753930142452917493)
                    ·
                      rfl

theorem cell22_1307105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_1307105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307105 prefixEnd_1307105 := by exact prefixLift 1307105
  have htrace : WordTrace (prefixWord ++ tailWord_1307105) baseStart_1307105 baseEnd_1307105 := by
    simpa [prefixWord, tailWord_1307105, baseEnd_1307105] using wordTrace_append hprefix tailTrace_1307105
  have hstable : (prefixWord ++ tailWord_1307105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307105).length < 2 ^ (prefixWord ++ tailWord_1307105).sum := by decide
  have hdescent : baseEnd_1307105 < baseStart_1307105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307135 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 2, 3]
def baseStart_1307135 : Nat := 118140960795 + 1307135 * 2 ^ 59
def prefixEnd_1307135 : Nat := 4983230072969 + 3 ^ 40 * 1307135 * 2
def baseEnd_1307135 : Nat := 447459023543232374667401

theorem tailTrace_1307135 : CollatzResearch.WordTrace tailWord_1307135 prefixEnd_1307135 447459023543232374667401 := by
  unfold tailWord_1307135
  simp only [CollatzResearch.WordTrace]
  refine ⟨47675130119480610729994859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31783420079653740486663239 47675130119480610729994859)
  ·
    refine ⟨71512695179220916094992289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47675130119480610729994859 71512695179220916094992289)
    ·
      refine ⟨53634521384415687071244217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71512695179220916094992289 53634521384415687071244217)
      ·
        refine ⟨40225891038311765303433163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53634521384415687071244217 40225891038311765303433163)
        ·
          refine ⟨60338836557467647955149745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40225891038311765303433163 60338836557467647955149745)
          ·
            refine ⟨45254127418100735966362309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60338836557467647955149745 45254127418100735966362309)
            ·
              refine ⟨8485148890893887993692933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45254127418100735966362309 8485148890893887993692933)
              ·
                refine ⟨1590965417042603998817425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8485148890893887993692933 1590965417042603998817425)
                ·
                  refine ⟨1193224062781952999113069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1590965417042603998817425 1193224062781952999113069)
                  ·
                    refine ⟨447459023543232374667401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1193224062781952999113069 447459023543232374667401)
                    ·
                      rfl

theorem cell22_1307135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_1307135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307135 prefixEnd_1307135 := by exact prefixLift 1307135
  have htrace : WordTrace (prefixWord ++ tailWord_1307135) baseStart_1307135 baseEnd_1307135 := by
    simpa [prefixWord, tailWord_1307135, baseEnd_1307135] using wordTrace_append hprefix tailTrace_1307135
  have hstable : (prefixWord ++ tailWord_1307135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307135).length < 2 ^ (prefixWord ++ tailWord_1307135).sum := by decide
  have hdescent : baseEnd_1307135 < baseStart_1307135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307148 : List Nat := [2, 2, 1, 2, 4, 1, 1, 9]
def baseStart_1307148 : Nat := 118140960795 + 1307148 * 2 ^ 59
def prefixEnd_1307148 : Nat := 4983230072969 + 3 ^ 40 * 1307148 * 2
def baseEnd_1307148 : Nat := 49718163745433852676929

theorem tailTrace_1307148 : CollatzResearch.WordTrace tailWord_1307148 prefixEnd_1307148 49718163745433852676929 := by
  unfold tailWord_1307148
  simp only [CollatzResearch.WordTrace]
  refine ⟨23837802134216756975109049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31783736178955675966812065 23837802134216756975109049)
  ·
    refine ⟨17878351600662567731331787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23837802134216756975109049 17878351600662567731331787)
    ·
      refine ⟨26817527400993851596997681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17878351600662567731331787 26817527400993851596997681)
      ·
        refine ⟨20113145550745388697748261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26817527400993851596997681 20113145550745388697748261)
        ·
          refine ⟨3771214790764760380827799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20113145550745388697748261 3771214790764760380827799)
          ·
            refine ⟨5656822186147140571241699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3771214790764760380827799 5656822186147140571241699)
            ·
              refine ⟨8485233279220710856862549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5656822186147140571241699 8485233279220710856862549)
              ·
                refine ⟨49718163745433852676929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8485233279220710856862549 49718163745433852676929)
                ·
                  rfl

theorem cell22_1307148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 9].length) (baseStart_1307148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307148 prefixEnd_1307148 := by exact prefixLift 1307148
  have htrace : WordTrace (prefixWord ++ tailWord_1307148) baseStart_1307148 baseEnd_1307148 := by
    simpa [prefixWord, tailWord_1307148, baseEnd_1307148] using wordTrace_append hprefix tailTrace_1307148
  have hstable : (prefixWord ++ tailWord_1307148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307148).length < 2 ^ (prefixWord ++ tailWord_1307148).sum := by decide
  have hdescent : baseEnd_1307148 < baseStart_1307148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307188 : List Nat := [2, 5, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1307188 : Nat := 118140960795 + 1307188 * 2 ^ 59
def prefixEnd_1307188 : Nat := 4983230072969 + 3 ^ 40 * 1307188 * 2
def baseEnd_1307188 : Nat := 149159055508785967697413

theorem tailTrace_1307188 : CollatzResearch.WordTrace tailWord_1307188 prefixEnd_1307188 149159055508785967697413 := by
  unfold tailWord_1307188
  simp only [CollatzResearch.WordTrace]
  refine ⟨23838531594144300390837109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31784708792192400521116145 23838531594144300390837109)
  ·
    refine ⟨2234862336951028161640979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23838531594144300390837109 2234862336951028161640979)
    ·
      refine ⟨3352293505426542242461469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234862336951028161640979 3352293505426542242461469)
      ·
        refine ⟨1257110064534953340923051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3352293505426542242461469 1257110064534953340923051)
        ·
          refine ⟨1885665096802430011384577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257110064534953340923051 1885665096802430011384577)
          ·
            refine ⟨1414248822601822508538433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1885665096802430011384577 1414248822601822508538433)
            ·
              refine ⟨1060686616951366881403825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414248822601822508538433 1060686616951366881403825)
              ·
                refine ⟨795514962713525161052869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060686616951366881403825 795514962713525161052869)
                ·
                  refine ⟨149159055508785967697413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795514962713525161052869 149159055508785967697413)
                  ·
                    rfl

theorem cell22_1307188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1307188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307188 prefixEnd_1307188 := by exact prefixLift 1307188
  have htrace : WordTrace (prefixWord ++ tailWord_1307188) baseStart_1307188 baseEnd_1307188 := by
    simpa [prefixWord, tailWord_1307188, baseEnd_1307188] using wordTrace_append hprefix tailTrace_1307188
  have hstable : (prefixWord ++ tailWord_1307188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307188).length < 2 ^ (prefixWord ++ tailWord_1307188).sum := by decide
  have hdescent : baseEnd_1307188 < baseStart_1307188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307210 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_1307210 : Nat := 118140960795 + 1307210 * 2 ^ 59
def prefixEnd_1307210 : Nat := 4983230072969 + 3 ^ 40 * 1307210 * 2
def baseEnd_1307210 : Nat := 149161565858652393014057

theorem tailTrace_1307210 : CollatzResearch.WordTrace tailWord_1307210 prefixEnd_1307210 149161565858652393014057 := by
  unfold tailWord_1307210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11919466398552224634743771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31785243729472599025983389 11919466398552224634743771)
  ·
    refine ⟨17879199597828336952115657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11919466398552224634743771 17879199597828336952115657)
    ·
      refine ⟨13409399698371252714086743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17879199597828336952115657 13409399698371252714086743)
      ·
        refine ⟨20114099547556879071130115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13409399698371252714086743 20114099547556879071130115)
        ·
          refine ⟨30171149321335318606695173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20114099547556879071130115 30171149321335318606695173)
          ·
            refine ⟨5657090497750372238755345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30171149321335318606695173 5657090497750372238755345)
            ·
              refine ⟨4242817873312779179066509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5657090497750372238755345 4242817873312779179066509)
              ·
                refine ⟨1591056702492292192149941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4242817873312779179066509 1591056702492292192149941)
                ·
                  refine ⟨149161565858652393014057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1591056702492292192149941 149161565858652393014057)
                  ·
                    rfl

theorem cell22_1307210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_1307210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307210 prefixEnd_1307210 := by exact prefixLift 1307210
  have htrace : WordTrace (prefixWord ++ tailWord_1307210) baseStart_1307210 baseEnd_1307210 := by
    simpa [prefixWord, tailWord_1307210, baseEnd_1307210] using wordTrace_append hprefix tailTrace_1307210
  have hstable : (prefixWord ++ tailWord_1307210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307210).length < 2 ^ (prefixWord ++ tailWord_1307210).sum := by decide
  have hdescent : baseEnd_1307210 < baseStart_1307210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307274 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_1307274 : Nat := 118140960795 + 1307274 * 2 ^ 59
def prefixEnd_1307274 : Nat := 4983230072969 + 3 ^ 40 * 1307274 * 2
def baseEnd_1307274 : Nat := 447506606083882345441975

theorem tailTrace_1307274 : CollatzResearch.WordTrace tailWord_1307274 prefixEnd_1307274 447506606083882345441975 := by
  unfold tailWord_1307274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11920049966494259367326219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31786799910651358312869917 11920049966494259367326219)
  ·
    refine ⟨17880074949741389050989329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11920049966494259367326219 17880074949741389050989329)
    ·
      refine ⟨13410056212306041788241997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17880074949741389050989329 13410056212306041788241997)
      ·
        refine ⟨5028771079614765670590749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13410056212306041788241997 5028771079614765670590749)
        ·
          refine ⟨1885789154855537126471531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5028771079614765670590749 1885789154855537126471531)
          ·
            refine ⟨2828683732283305689707297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885789154855537126471531 2828683732283305689707297)
            ·
              refine ⟨2121512799212479267280473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2828683732283305689707297 2121512799212479267280473)
              ·
                refine ⟨1591134599409359450460355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2121512799212479267280473 1591134599409359450460355)
                ·
                  refine ⟨2386701899114039175690533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591134599409359450460355 2386701899114039175690533)
                  ·
                    refine ⟨447506606083882345441975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2386701899114039175690533 447506606083882345441975)
                    ·
                      rfl

theorem cell22_1307274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_1307274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307274 prefixEnd_1307274 := by exact prefixLift 1307274
  have htrace : WordTrace (prefixWord ++ tailWord_1307274) baseStart_1307274 baseEnd_1307274 := by
    simpa [prefixWord, tailWord_1307274, baseEnd_1307274] using wordTrace_append hprefix tailTrace_1307274
  have hstable : (prefixWord ++ tailWord_1307274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307274).length < 2 ^ (prefixWord ++ tailWord_1307274).sum := by decide
  have hdescent : baseEnd_1307274 < baseStart_1307274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307283 : List Nat := [1, 1, 1, 2, 1, 2, 2, 12]
def baseStart_1307283 : Nat := 118140960795 + 1307283 * 2 ^ 59
def prefixEnd_1307283 : Nat := 4983230072969 + 3 ^ 40 * 1307283 * 2
def baseEnd_1307283 : Nat := 49723298551978813551883

theorem tailTrace_1307283 : CollatzResearch.WordTrace tailWord_1307283 prefixEnd_1307283 49723298551978813551883 := by
  unfold tailWord_1307283
  simp only [CollatzResearch.WordTrace]
  refine ⟨47680528122944432006382503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31787018748629621337588335 47680528122944432006382503)
  ·
    refine ⟨71520792184416648009573755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47680528122944432006382503 71520792184416648009573755)
    ·
      refine ⟨107281188276624972014360633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71520792184416648009573755 107281188276624972014360633)
      ·
        refine ⟨80460891207468729010770475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107281188276624972014360633 80460891207468729010770475)
        ·
          refine ⟨120691336811203093516155713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80460891207468729010770475 120691336811203093516155713)
          ·
            refine ⟨90518502608402320137116785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120691336811203093516155713 90518502608402320137116785)
            ·
              refine ⟨67888876956301740102837589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90518502608402320137116785 67888876956301740102837589)
              ·
                refine ⟨49723298551978813551883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 67888876956301740102837589 49723298551978813551883)
                ·
                  rfl

theorem cell22_1307283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 12].length) (baseStart_1307283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307283 prefixEnd_1307283 := by exact prefixLift 1307283
  have htrace : WordTrace (prefixWord ++ tailWord_1307283) baseStart_1307283 baseEnd_1307283 := by
    simpa [prefixWord, tailWord_1307283, baseEnd_1307283] using wordTrace_append hprefix tailTrace_1307283
  have hstable : (prefixWord ++ tailWord_1307283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307283).length < 2 ^ (prefixWord ++ tailWord_1307283).sum := by decide
  have hdescent : baseEnd_1307283 < baseStart_1307283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307306 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_1307306 : Nat := 118140960795 + 1307306 * 2 ^ 59
def prefixEnd_1307306 : Nat := 4983230072969 + 3 ^ 40 * 1307306 * 2
def baseEnd_1307306 : Nat := 149172520112614976213959

theorem tailTrace_1307306 : CollatzResearch.WordTrace tailWord_1307306 prefixEnd_1307306 149172520112614976213959 := by
  unfold tailWord_1307306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11920341750465276733617443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31787578001240737956313181 11920341750465276733617443)
  ·
    refine ⟨17880512625697915100426165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11920341750465276733617443 17880512625697915100426165)
    ·
      refine ⟨1676298058659179540664953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17880512625697915100426165 1676298058659179540664953)
      ·
        refine ⟨1257223543994384655498715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1676298058659179540664953 1257223543994384655498715)
        ·
          refine ⟨1885835315991576983248073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257223543994384655498715 1885835315991576983248073)
          ·
            refine ⟨1414376486993682737436055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1885835315991576983248073 1414376486993682737436055)
            ·
              refine ⟨2121564730490524106154083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414376486993682737436055 2121564730490524106154083)
              ·
                refine ⟨3182347095735786159231125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2121564730490524106154083 3182347095735786159231125)
                ·
                  refine ⟨149172520112614976213959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3182347095735786159231125 149172520112614976213959)
                  ·
                    rfl

theorem cell22_1307306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_1307306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307306 prefixEnd_1307306 := by exact prefixLift 1307306
  have htrace : WordTrace (prefixWord ++ tailWord_1307306) baseStart_1307306 baseEnd_1307306 := by
    simpa [prefixWord, tailWord_1307306, baseEnd_1307306] using wordTrace_append hprefix tailTrace_1307306
  have hstable : (prefixWord ++ tailWord_1307306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307306).length < 2 ^ (prefixWord ++ tailWord_1307306).sum := by decide
  have hdescent : baseEnd_1307306 < baseStart_1307306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307317 : List Nat := [1, 3, 3, 3, 1, 2, 2, 7]
def baseStart_1307317 : Nat := 118140960795 + 1307317 * 2 ^ 59
def prefixEnd_1307317 : Nat := 4983230072969 + 3 ^ 40 * 1307317 * 2
def baseEnd_1307317 : Nat := 49724591762516062957427

theorem tailTrace_1307317 : CollatzResearch.WordTrace tailWord_1307317 prefixEnd_1307317 49724591762516062957427 := by
  unfold tailWord_1307317
  simp only [CollatzResearch.WordTrace]
  refine ⟨47681768204821255813120205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31787845469880837208746803 47681768204821255813120205)
  ·
    refine ⟨17880663076807970929920077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47681768204821255813120205 17880663076807970929920077)
    ·
      refine ⟨6705248653802989098720029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17880663076807970929920077 6705248653802989098720029)
      ·
        refine ⟨2514468245176120912020011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6705248653802989098720029 2514468245176120912020011)
        ·
          refine ⟨3771702367764181368030017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514468245176120912020011 3771702367764181368030017)
          ·
            refine ⟨2828776775823136026022513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3771702367764181368030017 2828776775823136026022513)
            ·
              refine ⟨2121582581867352019516885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2828776775823136026022513 2121582581867352019516885)
              ·
                refine ⟨49724591762516062957427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2121582581867352019516885 49724591762516062957427)
                ·
                  rfl

theorem cell22_1307317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 7].length) (baseStart_1307317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307317 prefixEnd_1307317 := by exact prefixLift 1307317
  have htrace : WordTrace (prefixWord ++ tailWord_1307317) baseStart_1307317 baseEnd_1307317 := by
    simpa [prefixWord, tailWord_1307317, baseEnd_1307317] using wordTrace_append hprefix tailTrace_1307317
  have hstable : (prefixWord ++ tailWord_1307317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307317).length < 2 ^ (prefixWord ++ tailWord_1307317).sum := by decide
  have hdescent : baseEnd_1307317 < baseStart_1307317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307360 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_1307360 : Nat := 118140960795 + 1307360 * 2 ^ 59
def prefixEnd_1307360 : Nat := 4983230072969 + 3 ^ 40 * 1307360 * 2
def baseEnd_1307360 : Nat := 447536045641406787791711

theorem tailTrace_1307360 : CollatzResearch.WordTrace tailWord_1307360 prefixEnd_1307360 447536045641406787791711 := by
  unfold tailWord_1307360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23841668271832737078467767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31788891029110316104623689 23841668271832737078467767)
  ·
    refine ⟨35762502407749105617701651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23841668271832737078467767 35762502407749105617701651)
    ·
      refine ⟨53643753611623658426552477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35762502407749105617701651 53643753611623658426552477)
      ·
        refine ⟨20116407604358871909957179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53643753611623658426552477 20116407604358871909957179)
        ·
          refine ⟨30174611406538307864935769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20116407604358871909957179 30174611406538307864935769)
          ·
            refine ⟨22630958554903730898701827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30174611406538307864935769 22630958554903730898701827)
            ·
              refine ⟨33946437832355596348052741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22630958554903730898701827 33946437832355596348052741)
              ·
                refine ⟨6364957093566674315259889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33946437832355596348052741 6364957093566674315259889)
                ·
                  refine ⟨4773717820175005736444917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6364957093566674315259889 4773717820175005736444917)
                  ·
                    refine ⟨447536045641406787791711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4773717820175005736444917 447536045641406787791711)
                    ·
                      rfl

theorem cell22_1307360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_1307360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307360 prefixEnd_1307360 := by exact prefixLift 1307360
  have htrace : WordTrace (prefixWord ++ tailWord_1307360) baseStart_1307360 baseEnd_1307360 := by
    simpa [prefixWord, tailWord_1307360, baseEnd_1307360] using wordTrace_append hprefix tailTrace_1307360
  have hstable : (prefixWord ++ tailWord_1307360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307360).length < 2 ^ (prefixWord ++ tailWord_1307360).sum := by decide
  have hdescent : baseEnd_1307360 < baseStart_1307360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307409 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 1, 4]
def baseStart_1307409 : Nat := 118140960795 + 1307409 * 2 ^ 59
def prefixEnd_1307409 : Nat := 4983230072969 + 3 ^ 40 * 1307409 * 2
def baseEnd_1307409 : Nat := 447552819342786993316561

theorem tailTrace_1307409 : CollatzResearch.WordTrace tailWord_1307409 prefixEnd_1307409 447552819342786993316561 := by
  unfold tailWord_1307409
  simp only [CollatzResearch.WordTrace]
  refine ⟨47685123720487955525469281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31790082480325303683646187 47685123720487955525469281)
  ·
    refine ⟨35763842790365966644101961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47685123720487955525469281 35763842790365966644101961)
    ·
      refine ⟨26822882092774474983076471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35763842790365966644101961 26822882092774474983076471)
      ·
        refine ⟨40234323139161712474614707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26822882092774474983076471 40234323139161712474614707)
        ·
          refine ⟨60351484708742568711922061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40234323139161712474614707 60351484708742568711922061)
          ·
            refine ⟨22631806765778463266970773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60351484708742568711922061 22631806765778463266970773)
            ·
              refine ⟨1060865942145865465639255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22631806765778463266970773 1060865942145865465639255)
              ·
                refine ⟨1591298913218798198458883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060865942145865465639255 1591298913218798198458883)
                ·
                  refine ⟨2386948369828197297688325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591298913218798198458883 2386948369828197297688325)
                  ·
                    refine ⟨447552819342786993316561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2386948369828197297688325 447552819342786993316561)
                    ·
                      rfl

theorem cell22_1307409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_1307409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307409 prefixEnd_1307409 := by exact prefixLift 1307409
  have htrace : WordTrace (prefixWord ++ tailWord_1307409) baseStart_1307409 baseEnd_1307409 := by
    simpa [prefixWord, tailWord_1307409, baseEnd_1307409] using wordTrace_append hprefix tailTrace_1307409
  have hstable : (prefixWord ++ tailWord_1307409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307409).length < 2 ^ (prefixWord ++ tailWord_1307409).sum := by decide
  have hdescent : baseEnd_1307409 < baseStart_1307409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307424 : List Nat := [2, 1, 1, 5, 1, 2, 2, 4, 4]
def baseStart_1307424 : Nat := 118140960795 + 1307424 * 2 ^ 59
def prefixEnd_1307424 : Nat := 4983230072969 + 3 ^ 40 * 1307424 * 2
def baseEnd_1307424 : Nat := 149185984716443984730505

theorem tailTrace_1307424 : CollatzResearch.WordTrace tailWord_1307424 prefixEnd_1307424 149185984716443984730505 := by
  unfold tailWord_1307424
  simp only [CollatzResearch.WordTrace]
  refine ⟨23842835407716806543632663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31790447210289075391510217 23842835407716806543632663)
  ·
    refine ⟨35764253111575209815448995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23842835407716806543632663 35764253111575209815448995)
    ·
      refine ⟨53646379667362814723173493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35764253111575209815448995 53646379667362814723173493)
      ·
        refine ⟨5029348093815263880297515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53646379667362814723173493 5029348093815263880297515)
        ·
          refine ⟨7544022140722895820446273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5029348093815263880297515 7544022140722895820446273)
          ·
            refine ⟨5658016605542171865334705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7544022140722895820446273 5658016605542171865334705)
            ·
              refine ⟨4243512454156628899001029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5658016605542171865334705 4243512454156628899001029)
              ·
                refine ⟨795658585154367918562693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4243512454156628899001029 795658585154367918562693)
                ·
                  refine ⟨149185984716443984730505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795658585154367918562693 149185984716443984730505)
                  ·
                    rfl

theorem cell22_1307424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 4].length) (baseStart_1307424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307424 prefixEnd_1307424 := by exact prefixLift 1307424
  have htrace : WordTrace (prefixWord ++ tailWord_1307424) baseStart_1307424 baseEnd_1307424 := by
    simpa [prefixWord, tailWord_1307424, baseEnd_1307424] using wordTrace_append hprefix tailTrace_1307424
  have hstable : (prefixWord ++ tailWord_1307424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307424).length < 2 ^ (prefixWord ++ tailWord_1307424).sum := by decide
  have hdescent : baseEnd_1307424 < baseStart_1307424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307490 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1307490 : Nat := 118140960795 + 1307490 * 2 ^ 59
def prefixEnd_1307490 : Nat := 4983230072969 + 3 ^ 40 * 1307490 * 2
def baseEnd_1307490 : Nat := 447580547298129782041313

theorem tailTrace_1307490 : CollatzResearch.WordTrace tailWord_1307490 prefixEnd_1307490 447580547298129782041313 := by
  unfold tailWord_1307490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11922019508298626589791981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31792052022129670906111949 11922019508298626589791981)
  ·
    refine ⟨4470757315611984971171993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11922019508298626589791981 4470757315611984971171993)
    ·
      refine ⟨3353067986708988728378995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4470757315611984971171993 3353067986708988728378995)
      ·
        refine ⟨5029601980063483092568493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353067986708988728378995 5029601980063483092568493)
        ·
          refine ⟨1886100742523806159713185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5029601980063483092568493 1886100742523806159713185)
          ·
            refine ⟨1414575556892854619784889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1886100742523806159713185 1414575556892854619784889)
            ·
              refine ⟨1060931667669640964838667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414575556892854619784889 1060931667669640964838667)
              ·
                refine ⟨1591397501504461447258001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1060931667669640964838667 1591397501504461447258001)
                ·
                  refine ⟨1193548126128346085443501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1591397501504461447258001 1193548126128346085443501)
                  ·
                    refine ⟨447580547298129782041313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1193548126128346085443501 447580547298129782041313)
                    ·
                      rfl

theorem cell22_1307490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1307490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307490 prefixEnd_1307490 := by exact prefixLift 1307490
  have htrace : WordTrace (prefixWord ++ tailWord_1307490) baseStart_1307490 baseEnd_1307490 := by
    simpa [prefixWord, tailWord_1307490, baseEnd_1307490] using wordTrace_append hprefix tailTrace_1307490
  have hstable : (prefixWord ++ tailWord_1307490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307490).length < 2 ^ (prefixWord ++ tailWord_1307490).sum := by decide
  have hdescent : baseEnd_1307490 < baseStart_1307490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307576 : List Nat := [2, 1, 2, 1, 2, 5, 2, 3, 4]
def baseStart_1307576 : Nat := 118140960795 + 1307576 * 2 ^ 59
def prefixEnd_1307576 : Nat := 4983230072969 + 3 ^ 40 * 1307576 * 2
def baseEnd_1307576 : Nat := 149203328951884741463683

theorem tailTrace_1307576 : CollatzResearch.WordTrace tailWord_1307576 prefixEnd_1307576 149203328951884741463683 := by
  unfold tailWord_1307576
  simp only [CollatzResearch.WordTrace]
  refine ⟨23845607355441471523399291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31794143140588628697865721 23845607355441471523399291)
  ·
    refine ⟨35768411033162207285098937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23845607355441471523399291 35768411033162207285098937)
    ·
      refine ⟨26826308274871655463824203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35768411033162207285098937 26826308274871655463824203)
      ·
        refine ⟨40239462412307483195736305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26826308274871655463824203 40239462412307483195736305)
        ·
          refine ⟨30179596809230612396802229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40239462412307483195736305 30179596809230612396802229)
          ·
            refine ⟨2829337200865369912200209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30179596809230612396802229 2829337200865369912200209)
            ·
              refine ⟨2122002900649027434150157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2829337200865369912200209 2122002900649027434150157)
              ·
                refine ⟨795751087743385287806309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122002900649027434150157 795751087743385287806309)
                ·
                  refine ⟨149203328951884741463683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795751087743385287806309 149203328951884741463683)
                  ·
                    rfl

theorem cell22_1307576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 4].length) (baseStart_1307576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307576 prefixEnd_1307576 := by exact prefixLift 1307576
  have htrace : WordTrace (prefixWord ++ tailWord_1307576) baseStart_1307576 baseEnd_1307576 := by
    simpa [prefixWord, tailWord_1307576, baseEnd_1307576] using wordTrace_append hprefix tailTrace_1307576
  have hstable : (prefixWord ++ tailWord_1307576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307576).length < 2 ^ (prefixWord ++ tailWord_1307576).sum := by decide
  have hdescent : baseEnd_1307576 < baseStart_1307576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307591 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 2, 3]
def baseStart_1307591 : Nat := 118140960795 + 1307591 * 2 ^ 59
def prefixEnd_1307591 : Nat := 4983230072969 + 3 ^ 40 * 1307591 * 2
def baseEnd_1307591 : Nat := 447615121662199185266003

theorem tailTrace_1307591 : CollatzResearch.WordTrace tailWord_1307591 prefixEnd_1307591 447615121662199185266003 := by
  unfold tailWord_1307591
  simp only [CollatzResearch.WordTrace]
  refine ⟨47691761805828600608594627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31794507870552400405729751 47691761805828600608594627)
  ·
    refine ⟨71537642708742900912891941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47691761805828600608594627 71537642708742900912891941)
    ·
      refine ⟨13413308007889293921167239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71537642708742900912891941 13413308007889293921167239)
      ·
        refine ⟨20119962011833940881750859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13413308007889293921167239 20119962011833940881750859)
        ·
          refine ⟨30179943017750911322626289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20119962011833940881750859 30179943017750911322626289)
          ·
            refine ⟨22634957263313183491969717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30179943017750911322626289 22634957263313183491969717)
            ·
              refine ⟨2122027243435610952372161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22634957263313183491969717 2122027243435610952372161)
              ·
                refine ⟨1591520432576708214279121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2122027243435610952372161 1591520432576708214279121)
                ·
                  refine ⟨1193640324432531160709341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1591520432576708214279121 1193640324432531160709341)
                  ·
                    refine ⟨447615121662199185266003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1193640324432531160709341 447615121662199185266003)
                    ·
                      rfl

theorem cell22_1307591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_1307591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307591 prefixEnd_1307591 := by exact prefixLift 1307591
  have htrace : WordTrace (prefixWord ++ tailWord_1307591) baseStart_1307591 baseEnd_1307591 := by
    simpa [prefixWord, tailWord_1307591, baseEnd_1307591] using wordTrace_append hprefix tailTrace_1307591
  have hstable : (prefixWord ++ tailWord_1307591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307591).length < 2 ^ (prefixWord ++ tailWord_1307591).sum := by decide
  have hdescent : baseEnd_1307591 < baseStart_1307591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307606 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1307606 : Nat := 118140960795 + 1307606 * 2 ^ 59
def prefixEnd_1307606 : Nat := 4983230072969 + 3 ^ 40 * 1307606 * 2
def baseEnd_1307606 : Nat := 447620256468744146140957

theorem tailTrace_1307606 : CollatzResearch.WordTrace tailWord_1307606 prefixEnd_1307606 447620256468744146140957 := by
  unfold tailWord_1307606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2980769306298391135649417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31794872600516172113593781 2980769306298391135649417)
  ·
    refine ⟨2235576979723793351737063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2980769306298391135649417 2235576979723793351737063)
    ·
      refine ⟨3353365469585690027605595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2235576979723793351737063 3353365469585690027605595)
      ·
        refine ⟨5030048204378535041408393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353365469585690027605595 5030048204378535041408393)
        ·
          refine ⟨3772536153283901281056295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5030048204378535041408393 3772536153283901281056295)
          ·
            refine ⟨5658804229925851921584443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772536153283901281056295 5658804229925851921584443)
            ·
              refine ⟨8488206344888777882376665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5658804229925851921584443 8488206344888777882376665)
              ·
                refine ⟨6366154758666583411782499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8488206344888777882376665 6366154758666583411782499)
                ·
                  refine ⟨9549232137999875117673749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6366154758666583411782499 9549232137999875117673749)
                  ·
                    refine ⟨447620256468744146140957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9549232137999875117673749 447620256468744146140957)
                    ·
                      rfl

theorem cell22_1307606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1307606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307606 prefixEnd_1307606 := by exact prefixLift 1307606
  have htrace : WordTrace (prefixWord ++ tailWord_1307606) baseStart_1307606 baseEnd_1307606 := by
    simpa [prefixWord, tailWord_1307606, baseEnd_1307606] using wordTrace_append hprefix tailTrace_1307606
  have hstable : (prefixWord ++ tailWord_1307606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307606).length < 2 ^ (prefixWord ++ tailWord_1307606).sum := by decide
  have hdescent : baseEnd_1307606 < baseStart_1307606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307608 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 2, 3]
def baseStart_1307608 : Nat := 118140960795 + 1307608 * 2 ^ 59
def prefixEnd_1307608 : Nat := 4983230072969 + 3 ^ 40 * 1307608 * 2
def baseEnd_1307608 : Nat := 447620941109616807590951

theorem tailTrace_1307608 : CollatzResearch.WordTrace tailWord_1307608 prefixEnd_1307608 447620941109616807590951 := by
  unfold tailWord_1307608
  simp only [CollatzResearch.WordTrace]
  refine ⟨23846190923383506255981739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31794921231178008341308985 23846190923383506255981739)
  ·
    refine ⟨35769286385075259383972609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23846190923383506255981739 35769286385075259383972609)
    ·
      refine ⟨26826964788806444537979457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35769286385075259383972609 26826964788806444537979457)
      ·
        refine ⟨20120223591604833403484593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26826964788806444537979457 20120223591604833403484593)
        ·
          refine ⟨15090167693703625052613445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20120223591604833403484593 15090167693703625052613445)
          ·
            refine ⟨2829406442569429697365021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15090167693703625052613445 2829406442569429697365021)
            ·
              refine ⟨1061027415963536136511883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2829406442569429697365021 1061027415963536136511883)
              ·
                refine ⟨1591541123945304204767825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061027415963536136511883 1591541123945304204767825)
                ·
                  refine ⟨1193655842958978153575869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1591541123945304204767825 1193655842958978153575869)
                  ·
                    refine ⟨447620941109616807590951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1193655842958978153575869 447620941109616807590951)
                    ·
                      rfl

theorem cell22_1307608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_1307608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307608 prefixEnd_1307608 := by exact prefixLift 1307608
  have htrace : WordTrace (prefixWord ++ tailWord_1307608) baseStart_1307608 baseEnd_1307608 := by
    simpa [prefixWord, tailWord_1307608, baseEnd_1307608] using wordTrace_append hprefix tailTrace_1307608
  have hstable : (prefixWord ++ tailWord_1307608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307608).length < 2 ^ (prefixWord ++ tailWord_1307608).sum := by decide
  have hdescent : baseEnd_1307608 < baseStart_1307608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307621 : List Nat := [1, 3, 1, 6, 1, 1, 1, 8]
def baseStart_1307621 : Nat := 118140960795 + 1307621 * 2 ^ 59
def prefixEnd_1307621 : Nat := 4983230072969 + 3 ^ 40 * 1307621 * 2
def baseEnd_1307621 : Nat := 49736154586143234112879

theorem tailTrace_1307621 : CollatzResearch.WordTrace tailWord_1307621 prefixEnd_1307621 49736154586143234112879 := by
  unfold tailWord_1307621
  simp only [CollatzResearch.WordTrace]
  refine ⟨47692855995719915732186717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31795237330479943821457811 47692855995719915732186717)
  ·
    refine ⟨17884820998394968399570019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47692855995719915732186717 17884820998394968399570019)
    ·
      refine ⟨26827231497592452599355029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17884820998394968399570019 26827231497592452599355029)
      ·
        refine ⟨1257526476449646215594767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26827231497592452599355029 1257526476449646215594767)
        ·
          refine ⟨1886289714674469323392151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257526476449646215594767 1886289714674469323392151)
          ·
            refine ⟨2829434572011703985088227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886289714674469323392151 2829434572011703985088227)
            ·
              refine ⟨4244151858017555977632341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2829434572011703985088227 4244151858017555977632341)
              ·
                refine ⟨49736154586143234112879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4244151858017555977632341 49736154586143234112879)
                ·
                  rfl

theorem cell22_1307621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 8].length) (baseStart_1307621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307621 prefixEnd_1307621 := by exact prefixLift 1307621
  have htrace : WordTrace (prefixWord ++ tailWord_1307621) baseStart_1307621 baseEnd_1307621 := by
    simpa [prefixWord, tailWord_1307621, baseEnd_1307621] using wordTrace_append hprefix tailTrace_1307621
  have hstable : (prefixWord ++ tailWord_1307621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307621).length < 2 ^ (prefixWord ++ tailWord_1307621).sum := by decide
  have hdescent : baseEnd_1307621 < baseStart_1307621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307649 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 7]
def baseStart_1307649 : Nat := 118140960795 + 1307649 * 2 ^ 59
def prefixEnd_1307649 : Nat := 4983230072969 + 3 ^ 40 * 1307649 * 2
def baseEnd_1307649 : Nat := 149211658749168789105275

theorem tailTrace_1307649 : CollatzResearch.WordTrace tailWord_1307649 prefixEnd_1307649 149211658749168789105275 := by
  unfold tailWord_1307649
  simp only [CollatzResearch.WordTrace]
  refine ⟨47693877239618476514206001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31795918159745651009470667 47693877239618476514206001)
  ·
    refine ⟨35770407929713857385654501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47693877239618476514206001 35770407929713857385654501)
    ·
      refine ⟨6706951486821348259810219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35770407929713857385654501 6706951486821348259810219)
      ·
        refine ⟨10060427230232022389715329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6706951486821348259810219 10060427230232022389715329)
        ·
          refine ⟨7545320422674016792286497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10060427230232022389715329 7545320422674016792286497)
          ·
            refine ⟨5658990317005512594214873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7545320422674016792286497 5658990317005512594214873)
            ·
              refine ⟨4244242737754134445661155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5658990317005512594214873 4244242737754134445661155)
              ·
                refine ⟨6366364106631201668491733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244242737754134445661155 6366364106631201668491733)
                ·
                  refine ⟨149211658749168789105275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6366364106631201668491733 149211658749168789105275)
                  ·
                    rfl

theorem cell22_1307649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_1307649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307649 prefixEnd_1307649 := by exact prefixLift 1307649
  have htrace : WordTrace (prefixWord ++ tailWord_1307649) baseStart_1307649 baseEnd_1307649 := by
    simpa [prefixWord, tailWord_1307649, baseEnd_1307649] using wordTrace_append hprefix tailTrace_1307649
  have hstable : (prefixWord ++ tailWord_1307649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307649).length < 2 ^ (prefixWord ++ tailWord_1307649).sum := by decide
  have hdescent : baseEnd_1307649 < baseStart_1307649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307724 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1307724 : Nat := 118140960795 + 1307724 * 2 ^ 59
def prefixEnd_1307724 : Nat := 4983230072969 + 3 ^ 40 * 1307724 * 2
def baseEnd_1307724 : Nat := 447660650280231171690595

theorem tailTrace_1307724 : CollatzResearch.WordTrace tailWord_1307724 prefixEnd_1307724 447660650280231171690595 := by
  unfold tailWord_1307724
  simp only [CollatzResearch.WordTrace]
  refine ⟨23848306357173382161593113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31797741809564509548790817 23848306357173382161593113)
  ·
    refine ⟨17886229767880036621194835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23848306357173382161593113 17886229767880036621194835)
    ·
      refine ⟨26829344651820054931792253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17886229767880036621194835 26829344651820054931792253)
      ·
        refine ⟨10061004244432520599422095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26829344651820054931792253 10061004244432520599422095)
        ·
          refine ⟨15091506366648780899133143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10061004244432520599422095 15091506366648780899133143)
          ·
            refine ⟨22637259549973171348699715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15091506366648780899133143 22637259549973171348699715)
            ·
              refine ⟨33955889324959757023049573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22637259549973171348699715 33955889324959757023049573)
              ·
                refine ⟨6366729248429954441821795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33955889324959757023049573 6366729248429954441821795)
                ·
                  refine ⟨9550093872644931662732693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6366729248429954441821795 9550093872644931662732693)
                  ·
                    refine ⟨447660650280231171690595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9550093872644931662732693 447660650280231171690595)
                    ·
                      rfl

theorem cell22_1307724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1307724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307724 prefixEnd_1307724 := by exact prefixLift 1307724
  have htrace : WordTrace (prefixWord ++ tailWord_1307724) baseStart_1307724 baseEnd_1307724 := by
    simpa [prefixWord, tailWord_1307724, baseEnd_1307724] using wordTrace_append hprefix tailTrace_1307724
  have hstable : (prefixWord ++ tailWord_1307724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307724).length < 2 ^ (prefixWord ++ tailWord_1307724).sum := by decide
  have hdescent : baseEnd_1307724 < baseStart_1307724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307726 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_1307726 : Nat := 118140960795 + 1307726 * 2 ^ 59
def prefixEnd_1307726 : Nat := 4983230072969 + 3 ^ 40 * 1307726 * 2
def baseEnd_1307726 : Nat := 447661334921103833140589

theorem tailTrace_1307726 : CollatzResearch.WordTrace tailWord_1307726 prefixEnd_1307726 447661334921103833140589 := by
  unfold tailWord_1307726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962085707542439833094879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31797790440226345776506021 5962085707542439833094879)
  ·
    refine ⟨8943128561313659749642319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5962085707542439833094879 8943128561313659749642319)
    ·
      refine ⟨13414692841970489624463479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8943128561313659749642319 13414692841970489624463479)
      ·
        refine ⟨20122039262955734436695219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13414692841970489624463479 20122039262955734436695219)
        ·
          refine ⟨30183058894433601655042829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20122039262955734436695219 30183058894433601655042829)
          ·
            refine ⟨11318647085412600620641061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30183058894433601655042829 11318647085412600620641061)
            ·
              refine ⟨2122246328514862616370199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11318647085412600620641061 2122246328514862616370199)
              ·
                refine ⟨3183369492772293924555299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122246328514862616370199 3183369492772293924555299)
                ·
                  refine ⟨4775054239158440886832949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183369492772293924555299 4775054239158440886832949)
                  ·
                    refine ⟨447661334921103833140589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4775054239158440886832949 447661334921103833140589)
                    ·
                      rfl

theorem cell22_1307726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_1307726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307726 prefixEnd_1307726 := by exact prefixLift 1307726
  have htrace : WordTrace (prefixWord ++ tailWord_1307726) baseStart_1307726 baseEnd_1307726 := by
    simpa [prefixWord, tailWord_1307726, baseEnd_1307726] using wordTrace_append hprefix tailTrace_1307726
  have hstable : (prefixWord ++ tailWord_1307726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307726).length < 2 ^ (prefixWord ++ tailWord_1307726).sum := by decide
  have hdescent : baseEnd_1307726 < baseStart_1307726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307818 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_1307818 : Nat := 118140960795 + 1307818 * 2 ^ 59
def prefixEnd_1307818 : Nat := 4983230072969 + 3 ^ 40 * 1307818 * 2
def baseEnd_1307818 : Nat := 149230942800415419946769

theorem tailTrace_1307818 : CollatzResearch.WordTrace tailWord_1307818 prefixEnd_1307818 149230942800415419946769 := by
  unfold tailWord_1307818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11925010294001554594277027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31800027450670812251405405 11925010294001554594277027)
  ·
    refine ⟨17887515441002331891415541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11925010294001554594277027 17887515441002331891415541)
    ·
      refine ⟨1676954572593968614820207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17887515441002331891415541 1676954572593968614820207)
      ·
        refine ⟨2515431858890952922230311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676954572593968614820207 2515431858890952922230311)
        ·
          refine ⟨3773147788336429383345467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515431858890952922230311 3773147788336429383345467)
          ·
            refine ⟨5659721682504644075018201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3773147788336429383345467 5659721682504644075018201)
            ·
              refine ⟨4244791261878483056263651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5659721682504644075018201 4244791261878483056263651)
              ·
                refine ⟨6367186892817724584395477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4244791261878483056263651 6367186892817724584395477)
                ·
                  refine ⟨149230942800415419946769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6367186892817724584395477 149230942800415419946769)
                  ·
                    rfl

theorem cell22_1307818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_1307818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307818 prefixEnd_1307818 := by exact prefixLift 1307818
  have htrace : WordTrace (prefixWord ++ tailWord_1307818) baseStart_1307818 baseEnd_1307818 := by
    simpa [prefixWord, tailWord_1307818, baseEnd_1307818] using wordTrace_append hprefix tailTrace_1307818
  have hstable : (prefixWord ++ tailWord_1307818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307818).length < 2 ^ (prefixWord ++ tailWord_1307818).sum := by decide
  have hdescent : baseEnd_1307818 < baseStart_1307818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307831 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 3, 4]
def baseStart_1307831 : Nat := 118140960795 + 1307831 * 2 ^ 59
def prefixEnd_1307831 : Nat := 4983230072969 + 3 ^ 40 * 1307831 * 2
def baseEnd_1307831 : Nat := 447697278566918559265267

theorem tailTrace_1307831 : CollatzResearch.WordTrace tailWord_1307831 prefixEnd_1307831 447697278566918559265267 := by
  unfold tailWord_1307831
  simp only [CollatzResearch.WordTrace]
  refine ⟨47700515324959121597331347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31800343549972747731554231 47700515324959121597331347)
  ·
    refine ⟨71550772987438682395997021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47700515324959121597331347 71550772987438682395997021)
    ·
      refine ⟨26831539870289505898498883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71550772987438682395997021 26831539870289505898498883)
      ·
        refine ⟨40247309805434258847748325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26831539870289505898498883 40247309805434258847748325)
        ·
          refine ⟨7546370588518923533952811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40247309805434258847748325 7546370588518923533952811)
          ·
            refine ⟨11319555882778385300929217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546370588518923533952811 11319555882778385300929217)
            ·
              refine ⟨8489666912083788975696913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11319555882778385300929217 8489666912083788975696913)
              ·
                refine ⟨6367250184062841731772685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8489666912083788975696913 6367250184062841731772685)
                ·
                  refine ⟨2387718819023565649414757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6367250184062841731772685 2387718819023565649414757)
                  ·
                    refine ⟨447697278566918559265267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2387718819023565649414757 447697278566918559265267)
                    ·
                      rfl

theorem cell22_1307831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_1307831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307831 prefixEnd_1307831 := by exact prefixLift 1307831
  have htrace : WordTrace (prefixWord ++ tailWord_1307831) baseStart_1307831 baseEnd_1307831 := by
    simpa [prefixWord, tailWord_1307831, baseEnd_1307831] using wordTrace_append hprefix tailTrace_1307831
  have hstable : (prefixWord ++ tailWord_1307831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307831).length < 2 ^ (prefixWord ++ tailWord_1307831).sum := by decide
  have hdescent : baseEnd_1307831 < baseStart_1307831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307848 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_1307848 : Nat := 118140960795 + 1307848 * 2 ^ 59
def prefixEnd_1307848 : Nat := 4983230072969 + 3 ^ 40 * 1307848 * 2
def baseEnd_1307848 : Nat := 447703098014336181590215

theorem tailTrace_1307848 : CollatzResearch.WordTrace tailWord_1307848 prefixEnd_1307848 447703098014336181590215 := by
  unfold tailWord_1307848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23850567682948766750350099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31800756910598355667133465 23850567682948766750350099)
  ·
    refine ⟨35775851524423150125525149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23850567682948766750350099 35775851524423150125525149)
    ·
      refine ⟨13415944321658681297071931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35775851524423150125525149 13415944321658681297071931)
      ·
        refine ⟨20123916482488021945607897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13415944321658681297071931 20123916482488021945607897)
        ·
          refine ⟨15092937361866016459205923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20123916482488021945607897 15092937361866016459205923)
          ·
            refine ⟨22639406042799024688808885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15092937361866016459205923 22639406042799024688808885)
            ·
              refine ⟨2122444316512408564575833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22639406042799024688808885 2122444316512408564575833)
              ·
                refine ⟨1591833237384306423431875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2122444316512408564575833 1591833237384306423431875)
                ·
                  refine ⟨2387749856076459635147813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1591833237384306423431875 2387749856076459635147813)
                  ·
                    refine ⟨447703098014336181590215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2387749856076459635147813 447703098014336181590215)
                    ·
                      rfl

theorem cell22_1307848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_1307848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307848 prefixEnd_1307848 := by exact prefixLift 1307848
  have htrace : WordTrace (prefixWord ++ tailWord_1307848) baseStart_1307848 baseEnd_1307848 := by
    simpa [prefixWord, tailWord_1307848, baseEnd_1307848] using wordTrace_append hprefix tailTrace_1307848
  have hstable : (prefixWord ++ tailWord_1307848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307848).length < 2 ^ (prefixWord ++ tailWord_1307848).sum := by decide
  have hdescent : baseEnd_1307848 < baseStart_1307848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307891 : List Nat := [1, 1, 1, 2, 2, 5, 3, 7]
def baseStart_1307891 : Nat := 118140960795 + 1307891 * 2 ^ 59
def prefixEnd_1307891 : Nat := 4983230072969 + 3 ^ 40 * 1307891 * 2
def baseEnd_1307891 : Nat := 49746424199233155862787

theorem tailTrace_1307891 : CollatzResearch.WordTrace tailWord_1307891 prefixEnd_1307891 49746424199233155862787 := by
  unfold tailWord_1307891
  simp only [CollatzResearch.WordTrace]
  refine ⟨47702703704741751844515527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31801802469827834563010351 47702703704741751844515527)
  ·
    refine ⟨71554055557112627766773291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47702703704741751844515527 71554055557112627766773291)
    ·
      refine ⟨107331083335668941650159937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71554055557112627766773291 107331083335668941650159937)
      ·
        refine ⟨80498312501751706237619953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107331083335668941650159937 80498312501751706237619953)
        ·
          refine ⟨60373734376313779678214965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80498312501751706237619953 60373734376313779678214965)
          ·
            refine ⟨5660037597779416844832653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60373734376313779678214965 5660037597779416844832653)
            ·
              refine ⟨2122514099167281316812245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5660037597779416844832653 2122514099167281316812245)
              ·
                refine ⟨49746424199233155862787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2122514099167281316812245 49746424199233155862787)
                ·
                  rfl

theorem cell22_1307891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 7].length) (baseStart_1307891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307891 prefixEnd_1307891 := by exact prefixLift 1307891
  have htrace : WordTrace (prefixWord ++ tailWord_1307891) baseStart_1307891 baseEnd_1307891 := by
    simpa [prefixWord, tailWord_1307891, baseEnd_1307891] using wordTrace_append hprefix tailTrace_1307891
  have hstable : (prefixWord ++ tailWord_1307891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307891).length < 2 ^ (prefixWord ++ tailWord_1307891).sum := by decide
  have hdescent : baseEnd_1307891 < baseStart_1307891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1307940 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_1307940 : Nat := 118140960795 + 1307940 * 2 ^ 59
def prefixEnd_1307940 : Nat := 4983230072969 + 3 ^ 40 * 1307940 * 2
def baseEnd_1307940 : Nat := 447734591494478608289933

theorem tailTrace_1307940 : CollatzResearch.WordTrace tailWord_1307940 prefixEnd_1307940 447734591494478608289933 := by
  unfold tailWord_1307940
  simp only [CollatzResearch.WordTrace]
  refine ⟨23852245440782116606524637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31802993921042822142032849 23852245440782116606524637)
  ·
    refine ⟨8944592040293293727446739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23852245440782116606524637 8944592040293293727446739)
    ·
      refine ⟨13416888060439940591170109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8944592040293293727446739 13416888060439940591170109)
      ·
        refine ⟨5031333022664977721688791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13416888060439940591170109 5031333022664977721688791)
        ·
          refine ⟨7546999533997466582533187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5031333022664977721688791 7546999533997466582533187)
          ·
            refine ⟨11320499300996199873799781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546999533997466582533187 11320499300996199873799781)
            ·
              refine ⟨2122593618936787476337459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11320499300996199873799781 2122593618936787476337459)
              ·
                refine ⟨3183890428405181214506189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122593618936787476337459 3183890428405181214506189)
                ·
                  refine ⟨1193958910651942955439821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3183890428405181214506189 1193958910651942955439821)
                  ·
                    refine ⟨447734591494478608289933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1193958910651942955439821 447734591494478608289933)
                    ·
                      rfl

theorem cell22_1307940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_1307940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1307940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1307940 prefixEnd_1307940 := by exact prefixLift 1307940
  have htrace : WordTrace (prefixWord ++ tailWord_1307940) baseStart_1307940 baseEnd_1307940 := by
    simpa [prefixWord, tailWord_1307940, baseEnd_1307940] using wordTrace_append hprefix tailTrace_1307940
  have hstable : (prefixWord ++ tailWord_1307940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1307940).length < 2 ^ (prefixWord ++ tailWord_1307940).sum := by decide
  have hdescent : baseEnd_1307940 < baseStart_1307940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1307940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308077 : List Nat := [1, 5, 2, 2, 1, 2, 3, 6]
def baseStart_1308077 : Nat := 118140960795 + 1308077 * 2 ^ 59
def prefixEnd_1308077 : Nat := 4983230072969 + 3 ^ 40 * 1308077 * 2
def baseEnd_1308077 : Nat := 49753498821583990846057

theorem tailTrace_1308077 : CollatzResearch.WordTrace tailWord_1308077 prefixEnd_1308077 49753498821583990846057 := by
  unfold tailWord_1308077
  simp only [CollatzResearch.WordTrace]
  refine ⟨47709487682067905610786485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31806325121378603740524323 47709487682067905610786485)
  ·
    refine ⟨4472764470193866151011233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47709487682067905610786485 4472764470193866151011233)
    ·
      refine ⟨3354573352645399613258425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4472764470193866151011233 3354573352645399613258425)
      ·
        refine ⟨2515930014484049709943819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3354573352645399613258425 2515930014484049709943819)
        ·
          refine ⟨3773895021726074564915729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515930014484049709943819 3773895021726074564915729)
          ·
            refine ⟨2830421266294555923686797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3773895021726074564915729 2830421266294555923686797)
            ·
              refine ⟨1061407974860458471382549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2830421266294555923686797 1061407974860458471382549)
              ·
                refine ⟨49753498821583990846057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1061407974860458471382549 49753498821583990846057)
                ·
                  rfl

theorem cell22_1308077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 6].length) (baseStart_1308077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308077 prefixEnd_1308077 := by exact prefixLift 1308077
  have htrace : WordTrace (prefixWord ++ tailWord_1308077) baseStart_1308077 baseEnd_1308077 := by
    simpa [prefixWord, tailWord_1308077, baseEnd_1308077] using wordTrace_append hprefix tailTrace_1308077
  have hstable : (prefixWord ++ tailWord_1308077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308077).length < 2 ^ (prefixWord ++ tailWord_1308077).sum := by decide
  have hdescent : baseEnd_1308077 < baseStart_1308077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308098 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1308098 : Nat := 118140960795 + 1308098 * 2 ^ 59
def prefixEnd_1308098 : Nat := 4983230072969 + 3 ^ 40 * 1308098 * 2
def baseEnd_1308098 : Nat := 447788678123418862839449

theorem tailTrace_1308098 : CollatzResearch.WordTrace tailWord_1308098 prefixEnd_1308098 447788678123418862839449 := by
  unfold tailWord_1308098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11927563403747956549325237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31806835743327884131533965 11927563403747956549325237)
  ·
    refine ⟨1118209069101370926499241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11927563403747956549325237 1118209069101370926499241)
    ·
      refine ⟨838656801826028194874431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1118209069101370926499241 838656801826028194874431)
      ·
        refine ⟨1257985202739042292311647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838656801826028194874431 1257985202739042292311647)
        ·
          refine ⟨1886977804108563438467471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257985202739042292311647 1886977804108563438467471)
          ·
            refine ⟨2830466706162845157701207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886977804108563438467471 2830466706162845157701207)
            ·
              refine ⟨4245700059244267736551811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2830466706162845157701207 4245700059244267736551811)
              ·
                refine ⟨6368550088866401604827717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245700059244267736551811 6368550088866401604827717)
                ·
                  refine ⟨1194103141662450300905197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6368550088866401604827717 1194103141662450300905197)
                  ·
                    refine ⟨447788678123418862839449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1194103141662450300905197 447788678123418862839449)
                    ·
                      rfl

theorem cell22_1308098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1308098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308098 prefixEnd_1308098 := by exact prefixLift 1308098
  have htrace : WordTrace (prefixWord ++ tailWord_1308098) baseStart_1308098 baseEnd_1308098 := by
    simpa [prefixWord, tailWord_1308098, baseEnd_1308098] using wordTrace_append hprefix tailTrace_1308098
  have hstable : (prefixWord ++ tailWord_1308098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308098).length < 2 ^ (prefixWord ++ tailWord_1308098).sum := by decide
  have hdescent : baseEnd_1308098 < baseStart_1308098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308103 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1308103 : Nat := 118140960795 + 1308103 * 2 ^ 59
def prefixEnd_1308103 : Nat := 4983230072969 + 3 ^ 40 * 1308103 * 2
def baseEnd_1308103 : Nat := 447790389725600516464433

theorem tailTrace_1308103 : CollatzResearch.WordTrace tailWord_1308103 prefixEnd_1308103 447790389725600516464433 := by
  unfold tailWord_1308103
  simp only [CollatzResearch.WordTrace]
  refine ⟨47710435979973712051232963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31806957319982474700821975 47710435979973712051232963)
  ·
    refine ⟨71565653969960568076849445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47710435979973712051232963 71565653969960568076849445)
    ·
      refine ⟨13418560119367606514409271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71565653969960568076849445 13418560119367606514409271)
      ·
        refine ⟨20127840179051409771613907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13418560119367606514409271 20127840179051409771613907)
        ·
          refine ⟨30191760268577114657420861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20127840179051409771613907 30191760268577114657420861)
          ·
            refine ⟨11321910100716417996532823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30191760268577114657420861 11321910100716417996532823)
            ·
              refine ⟨16982865151074626994799235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11321910100716417996532823 16982865151074626994799235)
              ·
                refine ⟨25474297726611940492198853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16982865151074626994799235 25474297726611940492198853)
                ·
                  refine ⟨4776430823739738842287285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25474297726611940492198853 4776430823739738842287285)
                  ·
                    refine ⟨447790389725600516464433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4776430823739738842287285 447790389725600516464433)
                    ·
                      rfl

theorem cell22_1308103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1308103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308103 prefixEnd_1308103 := by exact prefixLift 1308103
  have htrace : WordTrace (prefixWord ++ tailWord_1308103) baseStart_1308103 baseEnd_1308103 := by
    simpa [prefixWord, tailWord_1308103, baseEnd_1308103] using wordTrace_append hprefix tailTrace_1308103
  have hstable : (prefixWord ++ tailWord_1308103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308103).length < 2 ^ (prefixWord ++ tailWord_1308103).sum := by decide
  have hdescent : baseEnd_1308103 < baseStart_1308103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308122 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_1308122 : Nat := 118140960795 + 1308122 * 2 ^ 59
def prefixEnd_1308122 : Nat := 4983230072969 + 3 ^ 40 * 1308122 * 2
def baseEnd_1308122 : Nat := 149265631271296933413125

theorem tailTrace_1308122 : CollatzResearch.WordTrace tailWord_1308122 prefixEnd_1308122 149265631271296933413125 := by
  unfold tailWord_1308122
  simp only [CollatzResearch.WordTrace]
  refine ⟨11927782241726219574043655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31807419311269918864116413 11927782241726219574043655)
  ·
    refine ⟨17891673362589329361065483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11927782241726219574043655 17891673362589329361065483)
    ·
      refine ⟨26837510043883994041598225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17891673362589329361065483 26837510043883994041598225)
      ·
        refine ⟨20128132532912995531198669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26837510043883994041598225 20128132532912995531198669)
        ·
          refine ⟨7548049699842373324199501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20128132532912995531198669 7548049699842373324199501)
          ·
            refine ⟨2830518637440889996574813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7548049699842373324199501 2830518637440889996574813)
            ·
              refine ⟨1061444489040333748715555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2830518637440889996574813 1061444489040333748715555)
              ·
                refine ⟨1592166733560500623073333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061444489040333748715555 1592166733560500623073333)
                ·
                  refine ⟨149265631271296933413125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1592166733560500623073333 149265631271296933413125)
                  ·
                    rfl

theorem cell22_1308122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_1308122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308122 prefixEnd_1308122 := by exact prefixLift 1308122
  have htrace : WordTrace (prefixWord ++ tailWord_1308122) baseStart_1308122 baseEnd_1308122 := by
    simpa [prefixWord, tailWord_1308122, baseEnd_1308122] using wordTrace_append hprefix tailTrace_1308122
  have hstable : (prefixWord ++ tailWord_1308122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308122).length < 2 ^ (prefixWord ++ tailWord_1308122).sum := by decide
  have hdescent : baseEnd_1308122 < baseStart_1308122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308163 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 3, 6]
def baseStart_1308163 : Nat := 118140960795 + 1308163 * 2 ^ 59
def prefixEnd_1308163 : Nat := 4983230072969 + 3 ^ 40 * 1308163 * 2
def baseEnd_1308163 : Nat := 447810928951780359964249

theorem tailTrace_1308163 : CollatzResearch.WordTrace tailWord_1308163 prefixEnd_1308163 447810928951780359964249 := by
  unfold tailWord_1308163
  simp only [CollatzResearch.WordTrace]
  refine ⟨47712624359756342298417143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31808416239837561532278095 47712624359756342298417143)
  ·
    refine ⟨71568936539634513447625715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47712624359756342298417143 71568936539634513447625715)
    ·
      refine ⟨107353404809451770171438573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71568936539634513447625715 107353404809451770171438573)
      ·
        refine ⟨40257526803544413814289465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107353404809451770171438573 40257526803544413814289465)
        ·
          refine ⟨30193145102658310360717099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40257526803544413814289465 30193145102658310360717099)
          ·
            refine ⟨45289717653987465541075649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30193145102658310360717099 45289717653987465541075649)
            ·
              refine ⟨33967288240490599155806737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45289717653987465541075649 33967288240490599155806737)
              ·
                refine ⟨25475466180367949366855053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33967288240490599155806737 25475466180367949366855053)
                ·
                  refine ⟨9553299817637981012570645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25475466180367949366855053 9553299817637981012570645)
                  ·
                    refine ⟨447810928951780359964249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9553299817637981012570645 447810928951780359964249)
                    ·
                      rfl

theorem cell22_1308163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_1308163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308163 prefixEnd_1308163 := by exact prefixLift 1308163
  have htrace : WordTrace (prefixWord ++ tailWord_1308163) baseStart_1308163 baseEnd_1308163 := by
    simpa [prefixWord, tailWord_1308163, baseEnd_1308163] using wordTrace_append hprefix tailTrace_1308163
  have hstable : (prefixWord ++ tailWord_1308163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308163).length < 2 ^ (prefixWord ++ tailWord_1308163).sum := by decide
  have hdescent : baseEnd_1308163 < baseStart_1308163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308167 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 6]
def baseStart_1308167 : Nat := 118140960795 + 1308167 * 2 ^ 59
def prefixEnd_1308167 : Nat := 4983230072969 + 3 ^ 40 * 1308167 * 2
def baseEnd_1308167 : Nat := 149270766077841894288079

theorem tailTrace_1308167 : CollatzResearch.WordTrace tailWord_1308167 prefixEnd_1308167 149270766077841894288079 := by
  unfold tailWord_1308167
  simp only [CollatzResearch.WordTrace]
  refine ⟨47712770251741850981562755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31808513501161233987708503 47712770251741850981562755)
  ·
    refine ⟨71569155377612776472344133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47712770251741850981562755 71569155377612776472344133)
    ·
      refine ⟨13419216633302395588564525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71569155377612776472344133 13419216633302395588564525)
      ·
        refine ⟨5032206237488398345711697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13419216633302395588564525 5032206237488398345711697)
        ·
          refine ⟨3774154678116298759283773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5032206237488398345711697 3774154678116298759283773)
          ·
            refine ⟨1415308004293612034731415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3774154678116298759283773 1415308004293612034731415)
            ·
              refine ⟨2122962006440418052097123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415308004293612034731415 2122962006440418052097123)
              ·
                refine ⟨3184443009660627078145685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122962006440418052097123 3184443009660627078145685)
                ·
                  refine ⟨149270766077841894288079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3184443009660627078145685 149270766077841894288079)
                  ·
                    rfl

theorem cell22_1308167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 6].length) (baseStart_1308167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308167 prefixEnd_1308167 := by exact prefixLift 1308167
  have htrace : WordTrace (prefixWord ++ tailWord_1308167) baseStart_1308167 baseEnd_1308167 := by
    simpa [prefixWord, tailWord_1308167, baseEnd_1308167] using wordTrace_append hprefix tailTrace_1308167
  have hstable : (prefixWord ++ tailWord_1308167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308167).length < 2 ^ (prefixWord ++ tailWord_1308167).sum := by decide
  have hdescent : baseEnd_1308167 < baseStart_1308167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308173 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1308173 : Nat := 118140960795 + 1308173 * 2 ^ 59
def prefixEnd_1308173 : Nat := 4983230072969 + 3 ^ 40 * 1308173 * 2
def baseEnd_1308173 : Nat := 149271450718714555738073

theorem tailTrace_1308173 : CollatzResearch.WordTrace tailWord_1308173 prefixEnd_1308173 149271450718714555738073 := by
  unfold tailWord_1308173
  simp only [CollatzResearch.WordTrace]
  refine ⟨47712989089720114006281173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31808659393146742670854115 47712989089720114006281173)
  ·
    refine ⟨1118273181790315172022215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 47712989089720114006281173 1118273181790315172022215)
    ·
      refine ⟨1677409772685472758033323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118273181790315172022215 1677409772685472758033323)
      ·
        refine ⟨2516114659028209137049985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677409772685472758033323 2516114659028209137049985)
        ·
          refine ⟨1887085994271156852787489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2516114659028209137049985 1887085994271156852787489)
          ·
            refine ⟨1415314495703367639590617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1887085994271156852787489 1415314495703367639590617)
            ·
              refine ⟨1061485871777525729692963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415314495703367639590617 1061485871777525729692963)
              ·
                refine ⟨1592228807666288594539445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061485871777525729692963 1592228807666288594539445)
                ·
                  refine ⟨149271450718714555738073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1592228807666288594539445 149271450718714555738073)
                  ·
                    rfl

theorem cell22_1308173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1308173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308173 prefixEnd_1308173 := by exact prefixLift 1308173
  have htrace : WordTrace (prefixWord ++ tailWord_1308173) baseStart_1308173 baseEnd_1308173 := by
    simpa [prefixWord, tailWord_1308173, baseEnd_1308173] using wordTrace_append hprefix tailTrace_1308173
  have hstable : (prefixWord ++ tailWord_1308173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308173).length < 2 ^ (prefixWord ++ tailWord_1308173).sum := by decide
  have hdescent : baseEnd_1308173 < baseStart_1308173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308225 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1308225 : Nat := 118140960795 + 1308225 * 2 ^ 59
def prefixEnd_1308225 : Nat := 4983230072969 + 3 ^ 40 * 1308225 * 2
def baseEnd_1308225 : Nat := 447832152818832864914059

theorem tailTrace_1308225 : CollatzResearch.WordTrace tailWord_1308225 prefixEnd_1308225 447832152818832864914059 := by
  unfold tailWord_1308225
  simp only [CollatzResearch.WordTrace]
  refine ⟨47714885685531726887174129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31809923790354484591449419 47714885685531726887174129)
  ·
    refine ⟨35786164264148795165380597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47714885685531726887174129 35786164264148795165380597)
    ·
      refine ⟨3354952899763949546754431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35786164264148795165380597 3354952899763949546754431)
      ·
        refine ⟨5032429349645924320131647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354952899763949546754431 5032429349645924320131647)
        ·
          refine ⟨7548644024468886480197471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032429349645924320131647 7548644024468886480197471)
          ·
            refine ⟨11322966036703329720296207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7548644024468886480197471 11322966036703329720296207)
            ·
              refine ⟨16984449055054994580444311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11322966036703329720296207 16984449055054994580444311)
              ·
                refine ⟨25476673582582491870666467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16984449055054994580444311 25476673582582491870666467)
                ·
                  refine ⟨38215010373873737805999701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25476673582582491870666467 38215010373873737805999701)
                  ·
                    refine ⟨447832152818832864914059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38215010373873737805999701 447832152818832864914059)
                    ·
                      rfl

theorem cell22_1308225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1308225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308225 prefixEnd_1308225 := by exact prefixLift 1308225
  have htrace : WordTrace (prefixWord ++ tailWord_1308225) baseStart_1308225 baseEnd_1308225 := by
    simpa [prefixWord, tailWord_1308225, baseEnd_1308225] using wordTrace_append hprefix tailTrace_1308225
  have hstable : (prefixWord ++ tailWord_1308225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308225).length < 2 ^ (prefixWord ++ tailWord_1308225).sum := by decide
  have hdescent : baseEnd_1308225 < baseStart_1308225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308240 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 5]
def baseStart_1308240 : Nat := 118140960795 + 1308240 * 2 ^ 59
def prefixEnd_1308240 : Nat := 4983230072969 + 3 ^ 40 * 1308240 * 2
def baseEnd_1308240 : Nat := 149279095875125941929671

theorem tailTrace_1308240 : CollatzResearch.WordTrace tailWord_1308240 prefixEnd_1308240 149279095875125941929671 := by
  unfold tailWord_1308240
  simp only [CollatzResearch.WordTrace]
  refine ⟨23857716390238692224485087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31810288520318256299313449 23857716390238692224485087)
  ·
    refine ⟨35786574585358038336727631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23857716390238692224485087 35786574585358038336727631)
    ·
      refine ⟨53679861878037057505091447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35786574585358038336727631 53679861878037057505091447)
      ·
        refine ⟨80519792817055586257637171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53679861878037057505091447 80519792817055586257637171)
        ·
          refine ⟨120779689225583379386455757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80519792817055586257637171 120779689225583379386455757)
          ·
            refine ⟨45292383459593767269920909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120779689225583379386455757 45292383459593767269920909)
            ·
              refine ⟨16984643797347662726220341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45292383459593767269920909 16984643797347662726220341)
              ·
                refine ⟨1592310356001343380583157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16984643797347662726220341 1592310356001343380583157)
                ·
                  refine ⟨149279095875125941929671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1592310356001343380583157 149279095875125941929671)
                  ·
                    rfl

theorem cell22_1308240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_1308240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308240 prefixEnd_1308240 := by exact prefixLift 1308240
  have htrace : WordTrace (prefixWord ++ tailWord_1308240) baseStart_1308240 baseEnd_1308240 := by
    simpa [prefixWord, tailWord_1308240, baseEnd_1308240] using wordTrace_append hprefix tailTrace_1308240
  have hstable : (prefixWord ++ tailWord_1308240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308240).length < 2 ^ (prefixWord ++ tailWord_1308240).sum := by decide
  have hdescent : baseEnd_1308240 < baseStart_1308240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308261 : List Nat := [1, 3, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_1308261 : Nat := 118140960795 + 1308261 * 2 ^ 59
def prefixEnd_1308261 : Nat := 4983230072969 + 3 ^ 40 * 1308261 * 2
def baseEnd_1308261 : Nat := 447844476354540771013949

theorem tailTrace_1308261 : CollatzResearch.WordTrace tailWord_1308261 prefixEnd_1308261 447844476354540771013949 := by
  unfold tailWord_1308261
  simp only [CollatzResearch.WordTrace]
  refine ⟨47716198713401305035484637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31810799142267536690323091 47716198713401305035484637)
  ·
    refine ⟨17893574517525489388306739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47716198713401305035484637 17893574517525489388306739)
    ·
      refine ⟨26840361776288234082460109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17893574517525489388306739 26840361776288234082460109)
      ·
        refine ⟨10065135666108087780922541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26840361776288234082460109 10065135666108087780922541)
        ·
          refine ⟨3774425874790532917845953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10065135666108087780922541 3774425874790532917845953)
          ·
            refine ⟨2830819406092899688384465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3774425874790532917845953 2830819406092899688384465)
            ·
              refine ⟨2123114554569674766288349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2830819406092899688384465 2123114554569674766288349)
              ·
                refine ⟨796167957963628037358131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2123114554569674766288349 796167957963628037358131)
                ·
                  refine ⟨1194251936945442056037197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796167957963628037358131 1194251936945442056037197)
                  ·
                    refine ⟨447844476354540771013949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1194251936945442056037197 447844476354540771013949)
                    ·
                      rfl

theorem cell22_1308261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_1308261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308261 prefixEnd_1308261 := by exact prefixLift 1308261
  have htrace : WordTrace (prefixWord ++ tailWord_1308261) baseStart_1308261 baseEnd_1308261 := by
    simpa [prefixWord, tailWord_1308261, baseEnd_1308261] using wordTrace_append hprefix tailTrace_1308261
  have hstable : (prefixWord ++ tailWord_1308261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308261).length < 2 ^ (prefixWord ++ tailWord_1308261).sum := by decide
  have hdescent : baseEnd_1308261 < baseStart_1308261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308274 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_1308274 : Nat := 118140960795 + 1308274 * 2 ^ 59
def prefixEnd_1308274 : Nat := 4983230072969 + 3 ^ 40 * 1308274 * 2
def baseEnd_1308274 : Nat := 149282975506737690146303

theorem tailTrace_1308274 : CollatzResearch.WordTrace tailWord_1308274 prefixEnd_1308274 149282975506737690146303 := by
  unfold tailWord_1308274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11929168215588552063926969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31811115241569472170471917 11929168215588552063926969)
  ·
    refine ⟨8946876161691414047945227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11929168215588552063926969 8946876161691414047945227)
    ·
      refine ⟨13420314242537121071917841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8946876161691414047945227 13420314242537121071917841)
      ·
        refine ⟨10065235681902840803938381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13420314242537121071917841 10065235681902840803938381)
        ·
          refine ⟨3774463380713565301476893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10065235681902840803938381 3774463380713565301476893)
          ·
            refine ⟨1415423767767586988053835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3774463380713565301476893 1415423767767586988053835)
            ·
              refine ⟨2123135651651380482080753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415423767767586988053835 2123135651651380482080753)
              ·
                refine ⟨1592351738738535361560565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123135651651380482080753 1592351738738535361560565)
                ·
                  refine ⟨149282975506737690146303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1592351738738535361560565 149282975506737690146303)
                  ·
                    rfl

theorem cell22_1308274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_1308274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308274 prefixEnd_1308274 := by exact prefixLift 1308274
  have htrace : WordTrace (prefixWord ++ tailWord_1308274) baseStart_1308274 baseEnd_1308274 := by
    simpa [prefixWord, tailWord_1308274, baseEnd_1308274] using wordTrace_append hprefix tailTrace_1308274
  have hstable : (prefixWord ++ tailWord_1308274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308274).length < 2 ^ (prefixWord ++ tailWord_1308274).sum := by decide
  have hdescent : baseEnd_1308274 < baseStart_1308274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308302 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_1308302 : Nat := 118140960795 + 1308302 * 2 ^ 59
def prefixEnd_1308302 : Nat := 4983230072969 + 3 ^ 40 * 1308302 * 2
def baseEnd_1308302 : Nat := 149286170497476776912941

theorem tailTrace_1308302 : CollatzResearch.WordTrace tailWord_1308302 prefixEnd_1308302 149286170497476776912941 := by
  unfold tailWord_1308302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964711763281596129715895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31811796070835179358484773 5964711763281596129715895)
  ·
    refine ⟨8947067644922394194573843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5964711763281596129715895 8947067644922394194573843)
    ·
      refine ⟨13420601467383591291860765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8947067644922394194573843 13420601467383591291860765)
      ·
        refine ⟨5032725550268846734447787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13420601467383591291860765 5032725550268846734447787)
        ·
          refine ⟨7549088325403270101671681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032725550268846734447787 7549088325403270101671681)
          ·
            refine ⟨5661816244052452576253761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7549088325403270101671681 5661816244052452576253761)
            ·
              refine ⟨4246362183039339432190321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5661816244052452576253761 4246362183039339432190321)
              ·
                refine ⟨3184771637279504574142741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246362183039339432190321 3184771637279504574142741)
                ·
                  refine ⟨149286170497476776912941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3184771637279504574142741 149286170497476776912941)
                  ·
                    rfl

theorem cell22_1308302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_1308302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308302 prefixEnd_1308302 := by exact prefixLift 1308302
  have htrace : WordTrace (prefixWord ++ tailWord_1308302) baseStart_1308302 baseEnd_1308302 := by
    simpa [prefixWord, tailWord_1308302, baseEnd_1308302] using wordTrace_append hprefix tailTrace_1308302
  have hstable : (prefixWord ++ tailWord_1308302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308302).length < 2 ^ (prefixWord ++ tailWord_1308302).sum := by decide
  have hdescent : baseEnd_1308302 < baseStart_1308302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308473 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 1, 4]
def baseStart_1308473 : Nat := 118140960795 + 1308473 * 2 ^ 59
def prefixEnd_1308473 : Nat := 4983230072969 + 3 ^ 40 * 1308473 * 2
def baseEnd_1308473 : Nat := 447917048287042884713299

theorem tailTrace_1308473 : CollatzResearch.WordTrace tailWord_1308473 prefixEnd_1308473 447917048287042884713299 := by
  unfold tailWord_1308473
  simp only [CollatzResearch.WordTrace]
  refine ⟨47723930988633265242202073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31815953992422176828134715 47723930988633265242202073)
  ·
    refine ⟨35792948241474948931651555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47723930988633265242202073 35792948241474948931651555)
    ·
      refine ⟨53689422362212423397477333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35792948241474948931651555 53689422362212423397477333)
      ·
        refine ⟨1258345836614353673378375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 53689422362212423397477333 1258345836614353673378375)
        ·
          refine ⟨1887518754921530510067563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258345836614353673378375 1887518754921530510067563)
          ·
            refine ⟨2831278132382295765101345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887518754921530510067563 2831278132382295765101345)
            ·
              refine ⟨2123458599286721823826009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831278132382295765101345 2123458599286721823826009)
              ·
                refine ⟨1592593949465041367869507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2123458599286721823826009 1592593949465041367869507)
                ·
                  refine ⟨2388890924197562051804261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592593949465041367869507 2388890924197562051804261)
                  ·
                    refine ⟨447917048287042884713299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2388890924197562051804261 447917048287042884713299)
                    ·
                      rfl

theorem cell22_1308473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_1308473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308473 prefixEnd_1308473 := by exact prefixLift 1308473
  have htrace : WordTrace (prefixWord ++ tailWord_1308473) baseStart_1308473 baseEnd_1308473 := by
    simpa [prefixWord, tailWord_1308473, baseEnd_1308473] using wordTrace_append hprefix tailTrace_1308473
  have hstable : (prefixWord ++ tailWord_1308473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308473).length < 2 ^ (prefixWord ++ tailWord_1308473).sum := by decide
  have hdescent : baseEnd_1308473 < baseStart_1308473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308619 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 4, 4]
def baseStart_1308619 : Nat := 118140960795 + 1308619 * 2 ^ 59
def prefixEnd_1308619 : Nat := 4983230072969 + 3 ^ 40 * 1308619 * 2
def baseEnd_1308619 : Nat := 447967027070747170562851

theorem tailTrace_1308619 : CollatzResearch.WordTrace tailWord_1308619 prefixEnd_1308619 447967027070747170562851 := by
  unfold tailWord_1308619
  simp only [CollatzResearch.WordTrace]
  refine ⟨47729256046104332177016911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31819504030736221451344607 47729256046104332177016911)
  ·
    refine ⟨71593884069156498265525367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47729256046104332177016911 71593884069156498265525367)
    ·
      refine ⟨107390826103734747398288051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71593884069156498265525367 107390826103734747398288051)
      ·
        refine ⟨161086239155602121097432077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107390826103734747398288051 161086239155602121097432077)
        ·
          refine ⟨60407339683350795411537029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161086239155602121097432077 60407339683350795411537029)
          ·
            refine ⟨11326376190628274139663193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60407339683350795411537029 11326376190628274139663193)
            ·
              refine ⟨8494782142971205604747395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11326376190628274139663193 8494782142971205604747395)
              ·
                refine ⟨12742173214456808407121093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8494782142971205604747395 12742173214456808407121093)
                ·
                  refine ⟨2389157477710651576335205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12742173214456808407121093 2389157477710651576335205)
                  ·
                    refine ⟨447967027070747170562851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2389157477710651576335205 447967027070747170562851)
                    ·
                      rfl

theorem cell22_1308619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 4].length) (baseStart_1308619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308619 prefixEnd_1308619 := by exact prefixLift 1308619
  have htrace : WordTrace (prefixWord ++ tailWord_1308619) baseStart_1308619 baseEnd_1308619 := by
    simpa [prefixWord, tailWord_1308619, baseEnd_1308619] using wordTrace_append hprefix tailTrace_1308619
  have hstable : (prefixWord ++ tailWord_1308619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308619).length < 2 ^ (prefixWord ++ tailWord_1308619).sum := by decide
  have hdescent : baseEnd_1308619 < baseStart_1308619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308696 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 5]
def baseStart_1308696 : Nat := 118140960795 + 1308696 * 2 ^ 59
def prefixEnd_1308696 : Nat := 4983230072969 + 3 ^ 40 * 1308696 * 2
def baseEnd_1308696 : Nat := 149331128581448212129205

theorem tailTrace_1308696 : CollatzResearch.WordTrace tailWord_1308696 prefixEnd_1308696 149331128581448212129205 := by
  unfold tailWord_1308696
  simp only [CollatzResearch.WordTrace]
  refine ⟨23866032233412687163784971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31821376311216916218379961 23866032233412687163784971)
  ·
    refine ⟨35799048350119030745677457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23866032233412687163784971 35799048350119030745677457)
    ·
      refine ⟨26849286262589273059258093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35799048350119030745677457 26849286262589273059258093)
      ·
        refine ⟨10068482348470977397221785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26849286262589273059258093 10068482348470977397221785)
        ·
          refine ⟨7551361761353233047916339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10068482348470977397221785 7551361761353233047916339)
          ·
            refine ⟨11327042642029849571874509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7551361761353233047916339 11327042642029849571874509)
            ·
              refine ⟨4247640990761193589452941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11327042642029849571874509 4247640990761193589452941)
              ·
                refine ⟨1592865371535447596044853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4247640990761193589452941 1592865371535447596044853)
                ·
                  refine ⟨149331128581448212129205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1592865371535447596044853 149331128581448212129205)
                  ·
                    rfl

theorem cell22_1308696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_1308696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308696 prefixEnd_1308696 := by exact prefixLift 1308696
  have htrace : WordTrace (prefixWord ++ tailWord_1308696) baseStart_1308696 baseEnd_1308696 := by
    simpa [prefixWord, tailWord_1308696, baseEnd_1308696] using wordTrace_append hprefix tailTrace_1308696
  have hstable : (prefixWord ++ tailWord_1308696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308696).length < 2 ^ (prefixWord ++ tailWord_1308696).sum := by decide
  have hdescent : baseEnd_1308696 < baseStart_1308696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308786 : List Nat := [3, 2, 1, 2, 2, 3, 9]
def baseStart_1308786 : Nat := 118140960795 + 1308786 * 2 ^ 59
def prefixEnd_1308786 : Nat := 4983230072969 + 3 ^ 40 * 1308786 * 2
def baseEnd_1308786 : Nat := 16593488688282014875457

theorem tailTrace_1308786 : CollatzResearch.WordTrace tailWord_1308786 prefixEnd_1308786 16593488688282014875457 := by
  unfold tailWord_1308786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11933836759124829924586553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31823564690999546465564141 11933836759124829924586553)
  ·
    refine ⟨8950377569343622443439915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11933836759124829924586553 8950377569343622443439915)
    ·
      refine ⟨13425566354015433665159873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8950377569343622443439915 13425566354015433665159873)
      ·
        refine ⟨10069174765511575248869905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13425566354015433665159873 10069174765511575248869905)
        ·
          refine ⟨7551881074133681436652429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10069174765511575248869905 7551881074133681436652429)
          ·
            refine ⟨2831955402800130538744661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7551881074133681436652429 2831955402800130538744661)
            ·
              refine ⟨16593488688282014875457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2831955402800130538744661 16593488688282014875457)
              ·
                rfl

theorem cell22_1308786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 9].length) (baseStart_1308786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308786 prefixEnd_1308786 := by exact prefixLift 1308786
  have htrace : WordTrace (prefixWord ++ tailWord_1308786) baseStart_1308786 baseEnd_1308786 := by
    simpa [prefixWord, tailWord_1308786, baseEnd_1308786] using wordTrace_append hprefix tailTrace_1308786
  have hstable : (prefixWord ++ tailWord_1308786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308786).length < 2 ^ (prefixWord ++ tailWord_1308786).sum := by decide
  have hdescent : baseEnd_1308786 < baseStart_1308786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308790 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1308790 : Nat := 118140960795 + 1308790 * 2 ^ 59
def prefixEnd_1308790 : Nat := 4983230072969 + 3 ^ 40 * 1308790 * 2
def baseEnd_1308790 : Nat := 448025563865359724537327

theorem tailTrace_1308790 : CollatzResearch.WordTrace tailWord_1308790 prefixEnd_1308790 448025563865359724537327 := by
  unfold tailWord_1308790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983468308030301773843239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31823661952323218920994549 2983468308030301773843239)
  ·
    refine ⟨4475202462045452660764859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2983468308030301773843239 4475202462045452660764859)
    ·
      refine ⟨6712803693068178991147289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4475202462045452660764859 6712803693068178991147289)
      ·
        refine ⟨5034602769801134243360467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6712803693068178991147289 5034602769801134243360467)
        ·
          refine ⟨7551904154701701365040701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5034602769801134243360467 7551904154701701365040701)
          ·
            refine ⟨2831964058013138011890263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7551904154701701365040701 2831964058013138011890263)
            ·
              refine ⟨4247946087019707017835395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2831964058013138011890263 4247946087019707017835395)
              ·
                refine ⟨6371919130529560526753093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4247946087019707017835395 6371919130529560526753093)
                ·
                  refine ⟨1194734836974292598766205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6371919130529560526753093 1194734836974292598766205)
                  ·
                    refine ⟨448025563865359724537327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1194734836974292598766205 448025563865359724537327)
                    ·
                      rfl

theorem cell22_1308790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1308790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308790 prefixEnd_1308790 := by exact prefixLift 1308790
  have htrace : WordTrace (prefixWord ++ tailWord_1308790) baseStart_1308790 baseEnd_1308790 := by
    simpa [prefixWord, tailWord_1308790, baseEnd_1308790] using wordTrace_append hprefix tailTrace_1308790
  have hstable : (prefixWord ++ tailWord_1308790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308790).length < 2 ^ (prefixWord ++ tailWord_1308790).sum := by decide
  have hdescent : baseEnd_1308790 < baseStart_1308790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308820 : List Nat := [2, 4, 2, 3, 1, 1, 1, 8]
def baseStart_1308820 : Nat := 118140960795 + 1308820 * 2 ^ 59
def prefixEnd_1308820 : Nat := 4983230072969 + 3 ^ 40 * 1308820 * 2
def baseEnd_1308820 : Nat := 49781759275383294031915

theorem tailTrace_1308820 : CollatzResearch.WordTrace tailWord_1308820 prefixEnd_1308820 49781759275383294031915 := by
  unfold tailWord_1308820
  simp only [CollatzResearch.WordTrace]
  refine ⟨23868293559188071752541957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31824391412250762336722609 23868293559188071752541957)
  ·
    refine ⟨4475305042347763453601617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23868293559188071752541957 4475305042347763453601617)
    ·
      refine ⟨3356478781760822590201213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4475305042347763453601617 3356478781760822590201213)
      ·
        refine ⟨1258679543160308471325455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3356478781760822590201213 1258679543160308471325455)
        ·
          refine ⟨1888019314740462706988183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258679543160308471325455 1888019314740462706988183)
          ·
            refine ⟨2832028972110694060482275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888019314740462706988183 2832028972110694060482275)
            ·
              refine ⟨4248043458166041090723413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832028972110694060482275 4248043458166041090723413)
              ·
                refine ⟨49781759275383294031915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4248043458166041090723413 49781759275383294031915)
                ·
                  rfl

theorem cell22_1308820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 8].length) (baseStart_1308820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308820 prefixEnd_1308820 := by exact prefixLift 1308820
  have htrace : WordTrace (prefixWord ++ tailWord_1308820) baseStart_1308820 baseEnd_1308820 := by
    simpa [prefixWord, tailWord_1308820, baseEnd_1308820] using wordTrace_append hprefix tailTrace_1308820
  have hstable : (prefixWord ++ tailWord_1308820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308820).length < 2 ^ (prefixWord ++ tailWord_1308820).sum := by decide
  have hdescent : baseEnd_1308820 < baseStart_1308820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308861 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1308861 : Nat := 118140960795 + 1308861 * 2 ^ 59
def prefixEnd_1308861 : Nat := 4983230072969 + 3 ^ 40 * 1308861 * 2
def baseEnd_1308861 : Nat := 448049868616339206012109

theorem tailTrace_1308861 : CollatzResearch.WordTrace tailWord_1308861 prefixEnd_1308861 448049868616339206012109 := by
  unfold tailWord_1308861
  simp only [CollatzResearch.WordTrace]
  refine ⟨47738082511227607507326437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31825388340818405004884291 47738082511227607507326437)
  ·
    refine ⟨8950890470855176407623707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47738082511227607507326437 8950890470855176407623707)
    ·
      refine ⟨13426335706282764611435561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8950890470855176407623707 13426335706282764611435561)
      ·
        refine ⟨10069751779712073458576671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13426335706282764611435561 10069751779712073458576671)
        ·
          refine ⟨15104627669568110187865007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10069751779712073458576671 15104627669568110187865007)
          ·
            refine ⟨22656941504352165281797511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15104627669568110187865007 22656941504352165281797511)
            ·
              refine ⟨33985412256528247922696267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22656941504352165281797511 33985412256528247922696267)
              ·
                refine ⟨50978118384792371884044401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33985412256528247922696267 50978118384792371884044401)
                ·
                  refine ⟨38233588788594278913033301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50978118384792371884044401 38233588788594278913033301)
                  ·
                    refine ⟨448049868616339206012109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38233588788594278913033301 448049868616339206012109)
                    ·
                      rfl

theorem cell22_1308861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1308861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308861 prefixEnd_1308861 := by exact prefixLift 1308861
  have htrace : WordTrace (prefixWord ++ tailWord_1308861) baseStart_1308861 baseEnd_1308861 := by
    simpa [prefixWord, tailWord_1308861, baseEnd_1308861] using wordTrace_append hprefix tailTrace_1308861
  have hstable : (prefixWord ++ tailWord_1308861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308861).length < 2 ^ (prefixWord ++ tailWord_1308861).sum := by decide
  have hdescent : baseEnd_1308861 < baseStart_1308861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308891 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 3, 5]
def baseStart_1308891 : Nat := 118140960795 + 1308891 * 2 ^ 59
def prefixEnd_1308891 : Nat := 4983230072969 + 3 ^ 40 * 1308891 * 2
def baseEnd_1308891 : Nat := 448060138229429127762017

theorem tailTrace_1308891 : CollatzResearch.WordTrace tailWord_1308891 prefixEnd_1308891 448060138229429127762017 := by
  unfold tailWord_1308891
  simp only [CollatzResearch.WordTrace]
  refine ⟨47739176701118922630918527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31826117800745948420612351 47739176701118922630918527)
  ·
    refine ⟨71608765051678383946377791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47739176701118922630918527 71608765051678383946377791)
    ·
      refine ⟨107413147577517575919566687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71608765051678383946377791 107413147577517575919566687)
      ·
        refine ⟨161119721366276363879350031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107413147577517575919566687 161119721366276363879350031)
        ·
          refine ⟨241679582049414545819025047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161119721366276363879350031 241679582049414545819025047)
          ·
            refine ⟨362519373074121818728537571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241679582049414545819025047 362519373074121818728537571)
            ·
              refine ⟨543779059611182728092806357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362519373074121818728537571 543779059611182728092806357)
              ·
                refine ⟨12744821709637095189675149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 543779059611182728092806357 12744821709637095189675149)
                ·
                  refine ⟨4779308141113910696128181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12744821709637095189675149 4779308141113910696128181)
                  ·
                    refine ⟨448060138229429127762017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4779308141113910696128181 448060138229429127762017)
                    ·
                      rfl

theorem cell22_1308891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_1308891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308891 prefixEnd_1308891 := by exact prefixLift 1308891
  have htrace : WordTrace (prefixWord ++ tailWord_1308891) baseStart_1308891 baseEnd_1308891 := by
    simpa [prefixWord, tailWord_1308891, baseEnd_1308891] using wordTrace_append hprefix tailTrace_1308891
  have hstable : (prefixWord ++ tailWord_1308891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308891).length < 2 ^ (prefixWord ++ tailWord_1308891).sum := by decide
  have hdescent : baseEnd_1308891 < baseStart_1308891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308921 : List Nat := [1, 2, 1, 3, 1, 1, 2, 11]
def baseStart_1308921 : Nat := 118140960795 + 1308921 * 2 ^ 59
def prefixEnd_1308921 : Nat := 4983230072969 + 3 ^ 40 * 1308921 * 2
def baseEnd_1308921 : Nat := 49785600871391005501325

theorem tailTrace_1308921 : CollatzResearch.WordTrace tailWord_1308921 prefixEnd_1308921 49785600871391005501325 := by
  unfold tailWord_1308921
  simp only [CollatzResearch.WordTrace]
  refine ⟨47740270891010237754510617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31826847260673491836340411 47740270891010237754510617)
  ·
    refine ⟨35805203168257678315882963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47740270891010237754510617 35805203168257678315882963)
    ·
      refine ⟨53707804752386517473824445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35805203168257678315882963 53707804752386517473824445)
      ·
        refine ⟨20140426782144944052684167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53707804752386517473824445 20140426782144944052684167)
        ·
          refine ⟨30210640173217416079026251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20140426782144944052684167 30210640173217416079026251)
          ·
            refine ⟨45315960259826124118539377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30210640173217416079026251 45315960259826124118539377)
            ·
              refine ⟨33986970194869593088904533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45315960259826124118539377 33986970194869593088904533)
              ·
                refine ⟨49785600871391005501325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 33986970194869593088904533 49785600871391005501325)
                ·
                  rfl

theorem cell22_1308921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 11].length) (baseStart_1308921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308921 prefixEnd_1308921 := by exact prefixLift 1308921
  have htrace : WordTrace (prefixWord ++ tailWord_1308921) baseStart_1308921 baseEnd_1308921 := by
    simpa [prefixWord, tailWord_1308921, baseEnd_1308921] using wordTrace_append hprefix tailTrace_1308921
  have hstable : (prefixWord ++ tailWord_1308921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308921).length < 2 ^ (prefixWord ++ tailWord_1308921).sum := by decide
  have hdescent : baseEnd_1308921 < baseStart_1308921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1308983 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 5]
def baseStart_1308983 : Nat := 118140960795 + 1308983 * 2 ^ 59
def prefixEnd_1308983 : Nat := 4983230072969 + 3 ^ 40 * 1308983 * 2
def baseEnd_1308983 : Nat := 149363877236523851487245

theorem tailTrace_1308983 : CollatzResearch.WordTrace tailWord_1308983 prefixEnd_1308983 149363877236523851487245 := by
  unfold tailWord_1308983
  simp only [CollatzResearch.WordTrace]
  refine ⟨47742532216785622343267603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31828354811190414895511735 47742532216785622343267603)
  ·
    refine ⟨71613798325178433514901405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47742532216785622343267603 71613798325178433514901405)
    ·
      refine ⟨26855174371941912568088027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71613798325178433514901405 26855174371941912568088027)
      ·
        refine ⟨40282761557912868852132041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26855174371941912568088027 40282761557912868852132041)
        ·
          refine ⟨30212071168434651639099031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40282761557912868852132041 30212071168434651639099031)
          ·
            refine ⟨45318106752651977458648547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30212071168434651639099031 45318106752651977458648547)
            ·
              refine ⟨67977160128977966187972821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45318106752651977458648547 67977160128977966187972821)
              ·
                refine ⟨1593214690522921082530613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 67977160128977966187972821 1593214690522921082530613)
                ·
                  refine ⟨149363877236523851487245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593214690522921082530613 149363877236523851487245)
                  ·
                    rfl

theorem cell22_1308983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 5].length) (baseStart_1308983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1308983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1308983 prefixEnd_1308983 := by exact prefixLift 1308983
  have htrace : WordTrace (prefixWord ++ tailWord_1308983) baseStart_1308983 baseEnd_1308983 := by
    simpa [prefixWord, tailWord_1308983, baseEnd_1308983] using wordTrace_append hprefix tailTrace_1308983
  have hstable : (prefixWord ++ tailWord_1308983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1308983).length < 2 ^ (prefixWord ++ tailWord_1308983).sum := by decide
  have hdescent : baseEnd_1308983 < baseStart_1308983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1308983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309034 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_1309034 : Nat := 118140960795 + 1309034 * 2 ^ 59
def prefixEnd_1309034 : Nat := 4983230072969 + 3 ^ 40 * 1309034 * 2
def baseEnd_1309034 : Nat := 149369696683941473812193

theorem tailTrace_1309034 : CollatzResearch.WordTrace tailWord_1309034 prefixEnd_1309034 149369696683941473812193 := by
  unfold tailWord_1309034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11936098084900214513343539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31829594893067238702249437 11936098084900214513343539)
  ·
    refine ⟨17904147127350321770015309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11936098084900214513343539 17904147127350321770015309)
    ·
      refine ⟨6714055172756370663755741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17904147127350321770015309 6714055172756370663755741)
      ·
        refine ⟨2517770689783638998908403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6714055172756370663755741 2517770689783638998908403)
        ·
          refine ⟨3776656034675458498362605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517770689783638998908403 3776656034675458498362605)
          ·
            refine ⟨1416246013003296936885977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3776656034675458498362605 1416246013003296936885977)
            ·
              refine ⟨1062184509752472702664483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416246013003296936885977 1062184509752472702664483)
              ·
                refine ⟨1593276764628709053996725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062184509752472702664483 1593276764628709053996725)
                ·
                  refine ⟨149369696683941473812193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593276764628709053996725 149369696683941473812193)
                  ·
                    rfl

theorem cell22_1309034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_1309034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309034 prefixEnd_1309034 := by exact prefixLift 1309034
  have htrace : WordTrace (prefixWord ++ tailWord_1309034) baseStart_1309034 baseEnd_1309034 := by
    simpa [prefixWord, tailWord_1309034, baseEnd_1309034] using wordTrace_append hprefix tailTrace_1309034
  have hstable : (prefixWord ++ tailWord_1309034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309034).length < 2 ^ (prefixWord ++ tailWord_1309034).sum := by decide
  have hdescent : baseEnd_1309034 < baseStart_1309034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309060 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1309060 : Nat := 118140960795 + 1309060 * 2 ^ 59
def prefixEnd_1309060 : Nat := 4983230072969 + 3 ^ 40 * 1309060 * 2
def baseEnd_1309060 : Nat := 448117990383169020286499

theorem tailTrace_1309060 : CollatzResearch.WordTrace tailWord_1309060 prefixEnd_1309060 448117990383169020286499 := by
  unfold tailWord_1309060
  simp only [CollatzResearch.WordTrace]
  refine ⟨23872670318753332246910317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31830227091671109662547089 23872670318753332246910317)
  ·
    refine ⟨8952251369532499592591369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23872670318753332246910317 8952251369532499592591369)
    ·
      refine ⟨6714188527149374694443527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8952251369532499592591369 6714188527149374694443527)
      ·
        refine ⟨10071282790724062041665291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6714188527149374694443527 10071282790724062041665291)
        ·
          refine ⟨15106924186086093062497937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10071282790724062041665291 15106924186086093062497937)
          ·
            refine ⟨11330193139564569796873453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15106924186086093062497937 11330193139564569796873453)
            ·
              refine ⟨4248822427336713673827545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11330193139564569796873453 4248822427336713673827545)
              ·
                refine ⟨3186616820502535255370659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4248822427336713673827545 3186616820502535255370659)
                ·
                  refine ⟨4779925230753802883055989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186616820502535255370659 4779925230753802883055989)
                  ·
                    refine ⟨448117990383169020286499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4779925230753802883055989 448117990383169020286499)
                    ·
                      rfl

theorem cell22_1309060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1309060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309060 prefixEnd_1309060 := by exact prefixLift 1309060
  have htrace : WordTrace (prefixWord ++ tailWord_1309060) baseStart_1309060 baseEnd_1309060 := by
    simpa [prefixWord, tailWord_1309060, baseEnd_1309060] using wordTrace_append hprefix tailTrace_1309060
  have hstable : (prefixWord ++ tailWord_1309060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309060).length < 2 ^ (prefixWord ++ tailWord_1309060).sum := by decide
  have hdescent : baseEnd_1309060 < baseStart_1309060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309109 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1309109 : Nat := 118140960795 + 1309109 * 2 ^ 59
def prefixEnd_1309109 : Nat := 4983230072969 + 3 ^ 40 * 1309109 * 2
def baseEnd_1309109 : Nat := 448134764084549225811349

theorem tailTrace_1309109 : CollatzResearch.WordTrace tailWord_1309109 prefixEnd_1309109 448134764084549225811349 := by
  unfold tailWord_1309109
  simp only [CollatzResearch.WordTrace]
  refine ⟨47747127814329145862354381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31831418542886097241569587 47747127814329145862354381)
  ·
    refine ⟨17905172930373429698382893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47747127814329145862354381 17905172930373429698382893)
    ·
      refine ⟨6714439848890036136893585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17905172930373429698382893 6714439848890036136893585)
      ·
        refine ⟨5035829886667527102670189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6714439848890036136893585 5035829886667527102670189)
        ·
          refine ⟨1888436207500322663501321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5035829886667527102670189 1888436207500322663501321)
          ·
            refine ⟨1416327155625241997625991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1888436207500322663501321 1416327155625241997625991)
            ·
              refine ⟨2124490733437862996438987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416327155625241997625991 2124490733437862996438987)
              ·
                refine ⟨3186736100156794494658481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124490733437862996438987 3186736100156794494658481)
                ·
                  refine ⟨2390052075117595870993861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3186736100156794494658481 2390052075117595870993861)
                  ·
                    refine ⟨448134764084549225811349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390052075117595870993861 448134764084549225811349)
                    ·
                      rfl

theorem cell22_1309109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1309109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309109 prefixEnd_1309109 := by exact prefixLift 1309109
  have htrace : WordTrace (prefixWord ++ tailWord_1309109) baseStart_1309109 baseEnd_1309109 := by
    simpa [prefixWord, tailWord_1309109, baseEnd_1309109] using wordTrace_append hprefix tailTrace_1309109
  have hstable : (prefixWord ++ tailWord_1309109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309109).length < 2 ^ (prefixWord ++ tailWord_1309109).sum := by decide
  have hdescent : baseEnd_1309109 < baseStart_1309109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309152 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 5]
def baseStart_1309152 : Nat := 118140960795 + 1309152 * 2 ^ 59
def prefixEnd_1309152 : Nat := 4983230072969 + 3 ^ 40 * 1309152 * 2
def baseEnd_1309152 : Nat := 149383161287770482328739

theorem tailTrace_1309152 : CollatzResearch.WordTrace tailWord_1309152 prefixEnd_1309152 149383161287770482328739 := by
  unfold tailWord_1309152
  simp only [CollatzResearch.WordTrace]
  refine ⟨23874348076586682103084855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31832464102115576137446473 23874348076586682103084855)
  ·
    refine ⟨35811522114880023154627283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23874348076586682103084855 35811522114880023154627283)
    ·
      refine ⟨53717283172320034731940925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35811522114880023154627283 53717283172320034731940925)
      ·
        refine ⟨20143981189620013024477847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53717283172320034731940925 20143981189620013024477847)
        ·
          refine ⟨30215971784430019536716771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20143981189620013024477847 30215971784430019536716771)
          ·
            refine ⟨45323957676645029305075157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30215971784430019536716771 45323957676645029305075157)
            ·
              refine ⟨1062280258046367874337699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45323957676645029305075157 1062280258046367874337699)
              ·
                refine ⟨1593420387069551811506549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062280258046367874337699 1593420387069551811506549)
                ·
                  refine ⟨149383161287770482328739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593420387069551811506549 149383161287770482328739)
                  ·
                    rfl

theorem cell22_1309152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_1309152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309152 prefixEnd_1309152 := by exact prefixLift 1309152
  have htrace : WordTrace (prefixWord ++ tailWord_1309152) baseStart_1309152 baseEnd_1309152 := by
    simpa [prefixWord, tailWord_1309152, baseEnd_1309152] using wordTrace_append hprefix tailTrace_1309152
  have hstable : (prefixWord ++ tailWord_1309152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309152).length < 2 ^ (prefixWord ++ tailWord_1309152).sum := by decide
  have hdescent : baseEnd_1309152 < baseStart_1309152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309190 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1309190 : Nat := 118140960795 + 1309190 * 2 ^ 59
def prefixEnd_1309190 : Nat := 4983230072969 + 3 ^ 40 * 1309190 * 2
def baseEnd_1309190 : Nat := 448162492039892014536101

theorem tailTrace_1309190 : CollatzResearch.WordTrace tailWord_1309190 prefixEnd_1309190 448162492039892014536101 := by
  unfold tailWord_1309190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492190066469865521751657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31833388084690464464035349 1492190066469865521751657)
  ·
    refine ⟨1119142549852399141313743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1492190066469865521751657 1119142549852399141313743)
    ·
      refine ⟨1678713824778598711970615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1119142549852399141313743 1678713824778598711970615)
      ·
        refine ⟨2518070737167898067955923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678713824778598711970615 2518070737167898067955923)
        ·
          refine ⟨3777106105751847101933885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518070737167898067955923 3777106105751847101933885)
          ·
            refine ⟨1416414789656942663225207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3777106105751847101933885 1416414789656942663225207)
            ·
              refine ⟨2124622184485413994837811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416414789656942663225207 2124622184485413994837811)
              ·
                refine ⟨3186933276728120992256717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124622184485413994837811 3186933276728120992256717)
                ·
                  refine ⟨1195099978773045372096269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3186933276728120992256717 1195099978773045372096269)
                  ·
                    refine ⟨448162492039892014536101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1195099978773045372096269 448162492039892014536101)
                    ·
                      rfl

theorem cell22_1309190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1309190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309190 prefixEnd_1309190 := by exact prefixLift 1309190
  have htrace : WordTrace (prefixWord ++ tailWord_1309190) baseStart_1309190 baseEnd_1309190 := by
    simpa [prefixWord, tailWord_1309190, baseEnd_1309190] using wordTrace_append hprefix tailTrace_1309190
  have hstable : (prefixWord ++ tailWord_1309190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309190).length < 2 ^ (prefixWord ++ tailWord_1309190).sum := by decide
  have hdescent : baseEnd_1309190 < baseStart_1309190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309210 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_1309210 : Nat := 118140960795 + 1309210 * 2 ^ 59
def prefixEnd_1309210 : Nat := 4983230072969 + 3 ^ 40 * 1309210 * 2
def baseEnd_1309210 : Nat := 448169338448618629036039

theorem tailTrace_1309210 : CollatzResearch.WordTrace tailWord_1309210 prefixEnd_1309210 448169338448618629036039 := by
  unfold tailWord_1309210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937702896740810027945271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31833874391308826741187389 11937702896740810027945271)
  ·
    refine ⟨17906554345111215041917907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11937702896740810027945271 17906554345111215041917907)
    ·
      refine ⟨26859831517666822562876861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17906554345111215041917907 26859831517666822562876861)
      ·
        refine ⟨10072436819125058461078823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26859831517666822562876861 10072436819125058461078823)
        ·
          refine ⟨15108655228687587691618235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072436819125058461078823 15108655228687587691618235)
          ·
            refine ⟨22662982843031381537427353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15108655228687587691618235 22662982843031381537427353)
            ·
              refine ⟨16997237132273536153070515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22662982843031381537427353 16997237132273536153070515)
              ·
                refine ⟨25495855698410304229605773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16997237132273536153070515 25495855698410304229605773)
                ·
                  refine ⟨9560945886903864086102165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25495855698410304229605773 9560945886903864086102165)
                  ·
                    refine ⟨448169338448618629036039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9560945886903864086102165 448169338448618629036039)
                    ·
                      rfl

theorem cell22_1309210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_1309210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309210 prefixEnd_1309210 := by exact prefixLift 1309210
  have htrace : WordTrace (prefixWord ++ tailWord_1309210) baseStart_1309210 baseEnd_1309210 := by
    simpa [prefixWord, tailWord_1309210, baseEnd_1309210] using wordTrace_append hprefix tailTrace_1309210
  have hstable : (prefixWord ++ tailWord_1309210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309210).length < 2 ^ (prefixWord ++ tailWord_1309210).sum := by decide
  have hdescent : baseEnd_1309210 < baseStart_1309210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309216 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 1, 4]
def baseStart_1309216 : Nat := 118140960795 + 1309216 * 2 ^ 59
def prefixEnd_1309216 : Nat := 4983230072969 + 3 ^ 40 * 1309216 * 2
def baseEnd_1309216 : Nat := 448171392371236613386021

theorem tailTrace_1309216 : CollatzResearch.WordTrace tailWord_1309216 prefixEnd_1309216 448171392371236613386021 := by
  unfold tailWord_1309216
  simp only [CollatzResearch.WordTrace]
  refine ⟨23875515212470751568249751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31834020283294335424333001 23875515212470751568249751)
  ·
    refine ⟨35813272818706127352374627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23875515212470751568249751 35813272818706127352374627)
    ·
      refine ⟨53719909228059191028561941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35813272818706127352374627 53719909228059191028561941)
      ·
        refine ⟨2518120745065274579463841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53719909228059191028561941 2518120745065274579463841)
        ·
          refine ⟨1888590558798955934597881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2518120745065274579463841 1888590558798955934597881)
          ·
            refine ⟨1416442919099216950948411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1888590558798955934597881 1416442919099216950948411)
            ·
              refine ⟨2124664378648825426422617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416442919099216950948411 2124664378648825426422617)
              ·
                refine ⟨1593498283986619069816963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124664378648825426422617 1593498283986619069816963)
                ·
                  refine ⟨2390247425979928604725445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593498283986619069816963 2390247425979928604725445)
                  ·
                    refine ⟨448171392371236613386021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390247425979928604725445 448171392371236613386021)
                    ·
                      rfl

theorem cell22_1309216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_1309216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309216 prefixEnd_1309216 := by exact prefixLift 1309216
  have htrace : WordTrace (prefixWord ++ tailWord_1309216) baseStart_1309216 baseEnd_1309216 := by
    simpa [prefixWord, tailWord_1309216, baseEnd_1309216] using wordTrace_append hprefix tailTrace_1309216
  have hstable : (prefixWord ++ tailWord_1309216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309216).length < 2 ^ (prefixWord ++ tailWord_1309216).sum := by decide
  have hdescent : baseEnd_1309216 < baseStart_1309216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309278 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1309278 : Nat := 118140960795 + 1309278 * 2 ^ 59
def prefixEnd_1309278 : Nat := 4983230072969 + 3 ^ 40 * 1309278 * 2
def baseEnd_1309278 : Nat := 448192616238289118335831

theorem tailTrace_1309278 : CollatzResearch.WordTrace tailWord_1309278 prefixEnd_1309278 448192616238289118335831 := by
  unfold tailWord_1309278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5969161468839610965657061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31835527833811258483504325 5969161468839610965657061)
  ·
    refine ⟨1119217775407427056060699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5969161468839610965657061 1119217775407427056060699)
    ·
      refine ⟨1678826663111140584091049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1119217775407427056060699 1678826663111140584091049)
      ·
        refine ⟨1259119997333355438068287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678826663111140584091049 1259119997333355438068287)
        ·
          refine ⟨1888679996000033157102431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259119997333355438068287 1888679996000033157102431)
          ·
            refine ⟨2833019994000049735653647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888679996000033157102431 2833019994000049735653647)
            ·
              refine ⟨4249529991000074603480471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833019994000049735653647 4249529991000074603480471)
              ·
                refine ⟨6374294986500111905220707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4249529991000074603480471 6374294986500111905220707)
                ·
                  refine ⟨9561442479750167857831061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6374294986500111905220707 9561442479750167857831061)
                  ·
                    refine ⟨448192616238289118335831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9561442479750167857831061 448192616238289118335831)
                    ·
                      rfl

theorem cell22_1309278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1309278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309278 prefixEnd_1309278 := by exact prefixLift 1309278
  have htrace : WordTrace (prefixWord ++ tailWord_1309278) baseStart_1309278 baseEnd_1309278 := by
    simpa [prefixWord, tailWord_1309278, baseEnd_1309278] using wordTrace_append hprefix tailTrace_1309278
  have hstable : (prefixWord ++ tailWord_1309278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309278).length < 2 ^ (prefixWord ++ tailWord_1309278).sum := by decide
  have hdescent : baseEnd_1309278 < baseStart_1309278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309484 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 6]
def baseStart_1309484 : Nat := 118140960795 + 1309484 * 2 ^ 59
def prefixEnd_1309484 : Nat := 4983230072969 + 3 ^ 40 * 1309484 * 2
def baseEnd_1309484 : Nat := 149421044749391082561733

theorem tailTrace_1309484 : CollatzResearch.WordTrace tailWord_1309484 prefixEnd_1309484 149421044749391082561733 := by
  unfold tailWord_1309484
  simp only [CollatzResearch.WordTrace]
  refine ⟨23880402593985292453627753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31840536791980389938170337 23880402593985292453627753)
  ·
    refine ⟨17910301945488969340220815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23880402593985292453627753 17910301945488969340220815)
    ·
      refine ⟨26865452918233454010331223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17910301945488969340220815 26865452918233454010331223)
      ·
        refine ⟨40298179377350181015496835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26865452918233454010331223 40298179377350181015496835)
        ·
          refine ⟨60447269066025271523245253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40298179377350181015496835 60447269066025271523245253)
          ·
            refine ⟨11333862949879738410608485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60447269066025271523245253 11333862949879738410608485)
            ·
              refine ⟨2125099303102450951989091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11333862949879738410608485 2125099303102450951989091)
              ·
                refine ⟨3187648954653676427983637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125099303102450951989091 3187648954653676427983637)
                ·
                  refine ⟨149421044749391082561733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3187648954653676427983637 149421044749391082561733)
                  ·
                    rfl

theorem cell22_1309484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_1309484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309484 prefixEnd_1309484 := by exact prefixLift 1309484
  have htrace : WordTrace (prefixWord ++ tailWord_1309484) baseStart_1309484 baseEnd_1309484 := by
    simpa [prefixWord, tailWord_1309484, baseEnd_1309484] using wordTrace_append hprefix tailTrace_1309484
  have hstable : (prefixWord ++ tailWord_1309484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309484).length < 2 ^ (prefixWord ++ tailWord_1309484).sum := by decide
  have hdescent : baseEnd_1309484 < baseStart_1309484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309516 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_1309516 : Nat := 118140960795 + 1309516 * 2 ^ 59
def prefixEnd_1309516 : Nat := 4983230072969 + 3 ^ 40 * 1309516 * 2
def baseEnd_1309516 : Nat := 448274088502135830885101

theorem tailTrace_1309516 : CollatzResearch.WordTrace tailWord_1309516 prefixEnd_1309516 448274088502135830885101 := by
  unfold tailWord_1309516
  simp only [CollatzResearch.WordTrace]
  refine ⟨23880986161927327186210201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31841314882569769581613601 23880986161927327186210201)
  ·
    refine ⟨17910739621445495389657651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23880986161927327186210201 17910739621445495389657651)
    ·
      refine ⟨26866109432168243084486477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17910739621445495389657651 26866109432168243084486477)
      ·
        refine ⟨10074791037063091156682429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26866109432168243084486477 10074791037063091156682429)
        ·
          refine ⟨3778046638898659183755911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10074791037063091156682429 3778046638898659183755911)
          ·
            refine ⟨5667069958347988775633867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3778046638898659183755911 5667069958347988775633867)
            ·
              refine ⟨8500604937521983163450801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5667069958347988775633867 8500604937521983163450801)
              ·
                refine ⟨6375453703141487372588101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8500604937521983163450801 6375453703141487372588101)
                ·
                  refine ⟨1195397569339028882360269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6375453703141487372588101 1195397569339028882360269)
                  ·
                    refine ⟨448274088502135830885101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1195397569339028882360269 448274088502135830885101)
                    ·
                      rfl

theorem cell22_1309516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_1309516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309516 prefixEnd_1309516 := by exact prefixLift 1309516
  have htrace : WordTrace (prefixWord ++ tailWord_1309516) baseStart_1309516 baseEnd_1309516 := by
    simpa [prefixWord, tailWord_1309516, baseEnd_1309516] using wordTrace_append hprefix tailTrace_1309516
  have hstable : (prefixWord ++ tailWord_1309516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309516).length < 2 ^ (prefixWord ++ tailWord_1309516).sum := by decide
  have hdescent : baseEnd_1309516 < baseStart_1309516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309529 : List Nat := [1, 2, 1, 2, 2, 6, 8]
def baseStart_1309529 : Nat := 118140960795 + 1309529 * 2 ^ 59
def prefixEnd_1309529 : Nat := 4983230072969 + 3 ^ 40 * 1309529 * 2
def baseEnd_1309529 : Nat := 16602908839548449270743

theorem tailTrace_1309529 : CollatzResearch.WordTrace tailWord_1309529 prefixEnd_1309529 16602908839548449270743 := by
  unfold tailWord_1309529
  simp only [CollatzResearch.WordTrace]
  refine ⟨47762446472807557592643641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31841630981871705061762427 47762446472807557592643641)
  ·
    refine ⟨35821834854605668194482731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47762446472807557592643641 35821834854605668194482731)
    ·
      refine ⟨53732752281908502291724097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35821834854605668194482731 53732752281908502291724097)
      ·
        refine ⟨40299564211431376718793073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53732752281908502291724097 40299564211431376718793073)
        ·
          refine ⟨30224673158573532539094805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40299564211431376718793073 30224673158573532539094805)
          ·
            refine ⟨1416781554308134337770069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30224673158573532539094805 1416781554308134337770069)
            ·
              refine ⟨16602908839548449270743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1416781554308134337770069 16602908839548449270743)
              ·
                rfl

theorem cell22_1309529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 8].length) (baseStart_1309529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309529 prefixEnd_1309529 := by exact prefixLift 1309529
  have htrace : WordTrace (prefixWord ++ tailWord_1309529) baseStart_1309529 baseEnd_1309529 := by
    simpa [prefixWord, tailWord_1309529, baseEnd_1309529] using wordTrace_append hprefix tailTrace_1309529
  have hstable : (prefixWord ++ tailWord_1309529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309529).length < 2 ^ (prefixWord ++ tailWord_1309529).sum := by decide
  have hdescent : baseEnd_1309529 < baseStart_1309529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309550 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1309550 : Nat := 118140960795 + 1309550 * 2 ^ 59
def prefixEnd_1309550 : Nat := 4983230072969 + 3 ^ 40 * 1309550 * 2
def baseEnd_1309550 : Nat := 448285727396971075534997

theorem tailTrace_1309550 : CollatzResearch.WordTrace tailWord_1309550 prefixEnd_1309550 448285727396971075534997 := by
  unfold tailWord_1309550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5970401550716434772394763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31842141603820985452772069 5970401550716434772394763)
  ·
    refine ⟨8955602326074652158592145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5970401550716434772394763 8955602326074652158592145)
    ·
      refine ⟨6716701744555989118944109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8955602326074652158592145 6716701744555989118944109)
      ·
        refine ⟨2518763154208495919604041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6716701744555989118944109 2518763154208495919604041)
        ·
          refine ⟨1889072365656371939703031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2518763154208495919604041 1889072365656371939703031)
          ·
            refine ⟨2833608548484557909554547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889072365656371939703031 2833608548484557909554547)
            ·
              refine ⟨4250412822726836864331821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833608548484557909554547 4250412822726836864331821)
              ·
                refine ⟨1593904808522563824124433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4250412822726836864331821 1593904808522563824124433)
                ·
                  refine ⟨1195428606391922868093325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1593904808522563824124433 1195428606391922868093325)
                  ·
                    refine ⟨448285727396971075534997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1195428606391922868093325 448285727396971075534997)
                    ·
                      rfl

theorem cell22_1309550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1309550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309550 prefixEnd_1309550 := by exact prefixLift 1309550
  have htrace : WordTrace (prefixWord ++ tailWord_1309550) baseStart_1309550 baseEnd_1309550 := by
    simpa [prefixWord, tailWord_1309550, baseEnd_1309550] using wordTrace_append hprefix tailTrace_1309550
  have hstable : (prefixWord ++ tailWord_1309550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309550).length < 2 ^ (prefixWord ++ tailWord_1309550).sum := by decide
  have hdescent : baseEnd_1309550 < baseStart_1309550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309591 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 5]
def baseStart_1309591 : Nat := 118140960795 + 1309591 * 2 ^ 59
def prefixEnd_1309591 : Nat := 4983230072969 + 3 ^ 40 * 1309591 * 2
def baseEnd_1309591 : Nat := 149433254178286878419957

theorem tailTrace_1309591 : CollatzResearch.WordTrace tailWord_1309591 prefixEnd_1309591 149433254178286878419957 := by
  unfold tailWord_1309591
  simp only [CollatzResearch.WordTrace]
  refine ⟨47764707798582942181400627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31843138532388628120933751 47764707798582942181400627)
  ·
    refine ⟨71647061697874413272100941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47764707798582942181400627 71647061697874413272100941)
    ·
      refine ⟨26867648136702904977037853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71647061697874413272100941 26867648136702904977037853)
      ·
        refine ⟨10075368051263589366389195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26867648136702904977037853 10075368051263589366389195)
        ·
          refine ⟨15113052076895384049583793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10075368051263589366389195 15113052076895384049583793)
          ·
            refine ⟨11334789057671538037187845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15113052076895384049583793 11334789057671538037187845)
            ·
              refine ⟨2125272948313413381972721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11334789057671538037187845 2125272948313413381972721)
              ·
                refine ⟨1593954711235060036479541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125272948313413381972721 1593954711235060036479541)
                ·
                  refine ⟨149433254178286878419957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593954711235060036479541 149433254178286878419957)
                  ·
                    rfl

theorem cell22_1309591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 5].length) (baseStart_1309591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309591 prefixEnd_1309591 := by exact prefixLift 1309591
  have htrace : WordTrace (prefixWord ++ tailWord_1309591) baseStart_1309591 baseEnd_1309591 := by
    simpa [prefixWord, tailWord_1309591, baseEnd_1309591] using wordTrace_append hprefix tailTrace_1309591
  have hstable : (prefixWord ++ tailWord_1309591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309591).length < 2 ^ (prefixWord ++ tailWord_1309591).sum := by decide
  have hdescent : baseEnd_1309591 < baseStart_1309591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309621 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1309621 : Nat := 118140960795 + 1309621 * 2 ^ 59
def prefixEnd_1309621 : Nat := 4983230072969 + 3 ^ 40 * 1309621 * 2
def baseEnd_1309621 : Nat := 448310032147950557009779

theorem tailTrace_1309621 : CollatzResearch.WordTrace tailWord_1309621 prefixEnd_1309621 448310032147950557009779 := by
  unfold tailWord_1309621
  simp only [CollatzResearch.WordTrace]
  refine ⟨47765801988474257304992717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31843867992316171536661811 47765801988474257304992717)
  ·
    refine ⟨17912175745677846489372269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47765801988474257304992717 17912175745677846489372269)
    ·
      refine ⟨6717065904629192433514601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17912175745677846489372269 6717065904629192433514601)
      ·
        refine ⟨5037799428471894325135951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6717065904629192433514601 5037799428471894325135951)
        ·
          refine ⟨7556699142707841487703927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5037799428471894325135951 7556699142707841487703927)
          ·
            refine ⟨11335048714061762231555891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7556699142707841487703927 11335048714061762231555891)
            ·
              refine ⟨17002573071092643347333837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11335048714061762231555891 17002573071092643347333837)
              ·
                refine ⟨6375964901659741255250189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17002573071092643347333837 6375964901659741255250189)
                ·
                  refine ⟨2390986838122402970718821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6375964901659741255250189 2390986838122402970718821)
                  ·
                    refine ⟨448310032147950557009779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390986838122402970718821 448310032147950557009779)
                    ·
                      rfl

theorem cell22_1309621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1309621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309621 prefixEnd_1309621 := by exact prefixLift 1309621
  have htrace : WordTrace (prefixWord ++ tailWord_1309621) baseStart_1309621 baseEnd_1309621 := by
    simpa [prefixWord, tailWord_1309621, baseEnd_1309621] using wordTrace_append hprefix tailTrace_1309621
  have hstable : (prefixWord ++ tailWord_1309621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309621).length < 2 ^ (prefixWord ++ tailWord_1309621).sum := by decide
  have hdescent : baseEnd_1309621 < baseStart_1309621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309653 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 6]
def baseStart_1309653 : Nat := 118140960795 + 1309653 * 2 ^ 59
def prefixEnd_1309653 : Nat := 4983230072969 + 3 ^ 40 * 1309653 * 2
def baseEnd_1309653 : Nat := 149440328800637713403227

theorem tailTrace_1309653 : CollatzResearch.WordTrace tailWord_1309653 prefixEnd_1309653 149440328800637713403227 := by
  unfold tailWord_1309653
  simp only [CollatzResearch.WordTrace]
  refine ⟨47766969124358326770157613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31844646082905551180105075 47766969124358326770157613)
  ·
    refine ⟨17912613421634372538809105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47766969124358326770157613 17912613421634372538809105)
    ·
      refine ⟨13434460066225779404106829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17912613421634372538809105 13434460066225779404106829)
      ·
        refine ⟨5037922524834667276540061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13434460066225779404106829 5037922524834667276540061)
        ·
          refine ⟨1889220946813000228702523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5037922524834667276540061 1889220946813000228702523)
          ·
            refine ⟨2833831420219500343053785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889220946813000228702523 2833831420219500343053785)
            ·
              refine ⟨2125373565164625257290339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2833831420219500343053785 2125373565164625257290339)
              ·
                refine ⟨3188060347746937885935509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125373565164625257290339 3188060347746937885935509)
                ·
                  refine ⟨149440328800637713403227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3188060347746937885935509 149440328800637713403227)
                  ·
                    rfl

theorem cell22_1309653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_1309653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309653 prefixEnd_1309653 := by exact prefixLift 1309653
  have htrace : WordTrace (prefixWord ++ tailWord_1309653) baseStart_1309653 baseEnd_1309653 := by
    simpa [prefixWord, tailWord_1309653, baseEnd_1309653] using wordTrace_append hprefix tailTrace_1309653
  have hstable : (prefixWord ++ tailWord_1309653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309653).length < 2 ^ (prefixWord ++ tailWord_1309653).sum := by decide
  have hdescent : baseEnd_1309653 < baseStart_1309653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309681 : List Nat := [1, 2, 2, 2, 4, 2, 1, 8]
def baseStart_1309681 : Nat := 118140960795 + 1309681 * 2 ^ 59
def prefixEnd_1309681 : Nat := 4983230072969 + 3 ^ 40 * 1309681 * 2
def baseEnd_1309681 : Nat := 49814507930458933389955

theorem tailTrace_1309681 : CollatzResearch.WordTrace tailWord_1309681 prefixEnd_1309681 49814507930458933389955 := by
  unfold tailWord_1309681
  simp only [CollatzResearch.WordTrace]
  refine ⟨47767990368256887552176897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31845326912171258368117931 47767990368256887552176897)
  ·
    refine ⟨35825992776192665664132673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47767990368256887552176897 35825992776192665664132673)
    ·
      refine ⟨26869494582144499248099505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35825992776192665664132673 26869494582144499248099505)
      ·
        refine ⟨20152120936608374436074629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26869494582144499248099505 20152120936608374436074629)
        ·
          refine ⟨3778522675614070206763993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20152120936608374436074629 3778522675614070206763993)
          ·
            refine ⟨2833892006710552655072995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3778522675614070206763993 2833892006710552655072995)
            ·
              refine ⟨4250838010065828982609493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833892006710552655072995 4250838010065828982609493)
              ·
                refine ⟨49814507930458933389955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4250838010065828982609493 49814507930458933389955)
                ·
                  rfl

theorem cell22_1309681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 8].length) (baseStart_1309681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309681 prefixEnd_1309681 := by exact prefixLift 1309681
  have htrace : WordTrace (prefixWord ++ tailWord_1309681) baseStart_1309681 baseEnd_1309681 := by
    simpa [prefixWord, tailWord_1309681, baseEnd_1309681] using wordTrace_append hprefix tailTrace_1309681
  have hstable : (prefixWord ++ tailWord_1309681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309681).length < 2 ^ (prefixWord ++ tailWord_1309681).sum := by decide
  have hdescent : baseEnd_1309681 < baseStart_1309681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309788 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 6]
def baseStart_1309788 : Nat := 118140960795 + 1309788 * 2 ^ 59
def prefixEnd_1309788 : Nat := 4983230072969 + 3 ^ 40 * 1309788 * 2
def baseEnd_1309788 : Nat := 149455733220272596028089

theorem tailTrace_1309788 : CollatzResearch.WordTrace tailWord_1309788 prefixEnd_1309788 149455733220272596028089 := by
  unfold tailWord_1309788
  simp only [CollatzResearch.WordTrace]
  refine ⟨23885946489434622413161009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31847928652579496550881345 23885946489434622413161009)
  ·
    refine ⟨17914459867075966809870757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23885946489434622413161009 17914459867075966809870757)
    ·
      refine ⟨3358961225076743776850767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17914459867075966809870757 3358961225076743776850767)
      ·
        refine ⟨5038441837615115665276151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3358961225076743776850767 5038441837615115665276151)
        ·
          refine ⟨7557662756422673497914227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038441837615115665276151 7557662756422673497914227)
          ·
            refine ⟨11336494134634010246871341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7557662756422673497914227 11336494134634010246871341)
            ·
              refine ⟨4251185300487753842576753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11336494134634010246871341 4251185300487753842576753)
              ·
                refine ⟨3188388975365815381932565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4251185300487753842576753 3188388975365815381932565)
                ·
                  refine ⟨149455733220272596028089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3188388975365815381932565 149455733220272596028089)
                  ·
                    rfl

theorem cell22_1309788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_1309788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309788 prefixEnd_1309788 := by exact prefixLift 1309788
  have htrace : WordTrace (prefixWord ++ tailWord_1309788) baseStart_1309788 baseEnd_1309788 := by
    simpa [prefixWord, tailWord_1309788, baseEnd_1309788] using wordTrace_append hprefix tailTrace_1309788
  have hstable : (prefixWord ++ tailWord_1309788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309788).length < 2 ^ (prefixWord ++ tailWord_1309788).sum := by decide
  have hdescent : baseEnd_1309788 < baseStart_1309788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309805 : List Nat := [1, 5, 1, 1, 2, 2, 1, 5, 4]
def baseStart_1309805 : Nat := 118140960795 + 1309805 * 2 ^ 59
def prefixEnd_1309805 : Nat := 4983230072969 + 3 ^ 40 * 1309805 * 2
def baseEnd_1309805 : Nat := 149457673036078470136405

theorem tailTrace_1309805 : CollatzResearch.WordTrace tailWord_1309805 prefixEnd_1309805 149457673036078470136405 := by
  unfold tailWord_1309805
  simp only [CollatzResearch.WordTrace]
  refine ⟨47772513019807656729690869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31848342013205104486460579 47772513019807656729690869)
  ·
    refine ⟨4478673095606967818408519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47772513019807656729690869 4478673095606967818408519)
    ·
      refine ⟨6718009643410451727612779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4478673095606967818408519 6718009643410451727612779)
      ·
        refine ⟨10077014465115677591419169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6718009643410451727612779 10077014465115677591419169)
        ·
          refine ⟨7557760848836758193564377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10077014465115677591419169 7557760848836758193564377)
          ·
            refine ⟨5668320636627568645173283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7557760848836758193564377 5668320636627568645173283)
            ·
              refine ⟨8502480954941352967759925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5668320636627568645173283 8502480954941352967759925)
              ·
                refine ⟨797107589525751840727493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8502480954941352967759925 797107589525751840727493)
                ·
                  refine ⟨149457673036078470136405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797107589525751840727493 149457673036078470136405)
                  ·
                    rfl

theorem cell22_1309805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_1309805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309805 prefixEnd_1309805 := by exact prefixLift 1309805
  have htrace : WordTrace (prefixWord ++ tailWord_1309805) baseStart_1309805 baseEnd_1309805 := by
    simpa [prefixWord, tailWord_1309805, baseEnd_1309805] using wordTrace_append hprefix tailTrace_1309805
  have hstable : (prefixWord ++ tailWord_1309805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309805).length < 2 ^ (prefixWord ++ tailWord_1309805).sum := by decide
  have hdescent : baseEnd_1309805 < baseStart_1309805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309850 : List Nat := [3, 1, 1, 5, 1, 1, 4, 6]
def baseStart_1309850 : Nat := 118140960795 + 1309850 * 2 ^ 59
def prefixEnd_1309850 : Nat := 4983230072969 + 3 ^ 40 * 1309850 * 2
def baseEnd_1309850 : Nat := 49820935947541143670453

theorem tailTrace_1309850 : CollatzResearch.WordTrace tailWord_1309850 prefixEnd_1309850 49820935947541143670453 := by
  unfold tailWord_1309850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11943538576161157353769751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31849436203096419610052669 11943538576161157353769751)
  ·
    refine ⟨17915307864241736030654627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11943538576161157353769751 17915307864241736030654627)
    ·
      refine ⟨26872961796362604045981941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17915307864241736030654627 26872961796362604045981941)
      ·
        refine ⟨2519340168408994129310807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26872961796362604045981941 2519340168408994129310807)
        ·
          refine ⟨3779010252613491193966211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2519340168408994129310807 3779010252613491193966211)
          ·
            refine ⟨5668515378920236790949317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779010252613491193966211 5668515378920236790949317)
            ·
              refine ⟨1062846633547544398302997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5668515378920236790949317 1062846633547544398302997)
              ·
                refine ⟨49820935947541143670453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1062846633547544398302997 49820935947541143670453)
                ·
                  rfl

theorem cell22_1309850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_1309850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309850 prefixEnd_1309850 := by exact prefixLift 1309850
  have htrace : WordTrace (prefixWord ++ tailWord_1309850) baseStart_1309850 baseEnd_1309850 := by
    simpa [prefixWord, tailWord_1309850, baseEnd_1309850] using wordTrace_append hprefix tailTrace_1309850
  have hstable : (prefixWord ++ tailWord_1309850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309850).length < 2 ^ (prefixWord ++ tailWord_1309850).sum := by decide
  have hdescent : baseEnd_1309850 < baseStart_1309850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309955 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 1, 5]
def baseStart_1309955 : Nat := 118140960795 + 1309955 * 2 ^ 59
def prefixEnd_1309955 : Nat := 4983230072969 + 3 ^ 40 * 1309955 * 2
def baseEnd_1309955 : Nat := 448424367173685019158755

theorem tailTrace_1309955 : CollatzResearch.WordTrace tailWord_1309955 prefixEnd_1309955 448424367173685019158755 := by
  unfold tailWord_1309955
  simp only [CollatzResearch.WordTrace]
  refine ⟨47777983969264232347651319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31851989312842821565100879 47777983969264232347651319)
  ·
    refine ⟨71666975953896348521476979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47777983969264232347651319 71666975953896348521476979)
    ·
      refine ⟨107500463930844522782215469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71666975953896348521476979 107500463930844522782215469)
      ·
        refine ⟨40312673974066696043330801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107500463930844522782215469 40312673974066696043330801)
        ·
          refine ⟨30234505480550022032498101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40312673974066696043330801 30234505480550022032498101)
          ·
            refine ⟨2834484888801564565546697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30234505480550022032498101 2834484888801564565546697)
            ·
              refine ⟨2125863666601173424160023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834484888801564565546697 2125863666601173424160023)
              ·
                refine ⟨3188795499901760136240035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125863666601173424160023 3188795499901760136240035)
                ·
                  refine ⟨4783193249852640204360053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188795499901760136240035 4783193249852640204360053)
                  ·
                    refine ⟨448424367173685019158755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4783193249852640204360053 448424367173685019158755)
                    ·
                      rfl

theorem cell22_1309955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 5].length) (baseStart_1309955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309955 prefixEnd_1309955 := by exact prefixLift 1309955
  have htrace : WordTrace (prefixWord ++ tailWord_1309955) baseStart_1309955 baseEnd_1309955 := by
    simpa [prefixWord, tailWord_1309955, baseEnd_1309955] using wordTrace_append hprefix tailTrace_1309955
  have hstable : (prefixWord ++ tailWord_1309955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309955).length < 2 ^ (prefixWord ++ tailWord_1309955).sum := by decide
  have hdescent : baseEnd_1309955 < baseStart_1309955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1309989 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_1309989 : Nat := 118140960795 + 1309989 * 2 ^ 59
def prefixEnd_1309989 : Nat := 4983230072969 + 3 ^ 40 * 1309989 * 2
def baseEnd_1309989 : Nat := 448436006068520263808651

theorem tailTrace_1309989 : CollatzResearch.WordTrace tailWord_1309989 prefixEnd_1309989 448436006068520263808651 := by
  unfold tailWord_1309989
  simp only [CollatzResearch.WordTrace]
  refine ⟨47779224051141056154389021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31852816034094037436259347 47779224051141056154389021)
  ·
    refine ⟨17917209019177896057895883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47779224051141056154389021 17917209019177896057895883)
    ·
      refine ⟨26875813528766844086843825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17917209019177896057895883 26875813528766844086843825)
      ·
        refine ⟨20156860146575133065132869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26875813528766844086843825 20156860146575133065132869)
        ·
          refine ⟨3779411277482837449712413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20156860146575133065132869 3779411277482837449712413)
          ·
            refine ⟨1417279229056064043642155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3779411277482837449712413 1417279229056064043642155)
            ·
              refine ⟨2125918843584096065463233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417279229056064043642155 2125918843584096065463233)
              ·
                refine ⟨1594439132688072049097425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125918843584096065463233 1594439132688072049097425)
                ·
                  refine ⟨1195829349516054036823069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1594439132688072049097425 1195829349516054036823069)
                  ·
                    refine ⟨448436006068520263808651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1195829349516054036823069 448436006068520263808651)
                    ·
                      rfl

theorem cell22_1309989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_1309989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1309989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1309989 prefixEnd_1309989 := by exact prefixLift 1309989
  have htrace : WordTrace (prefixWord ++ tailWord_1309989) baseStart_1309989 baseEnd_1309989 := by
    simpa [prefixWord, tailWord_1309989, baseEnd_1309989] using wordTrace_append hprefix tailTrace_1309989
  have hstable : (prefixWord ++ tailWord_1309989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1309989).length < 2 ^ (prefixWord ++ tailWord_1309989).sum := by decide
  have hdescent : baseEnd_1309989 < baseStart_1309989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1309989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310006 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1310006 : Nat := 118140960795 + 1310006 * 2 ^ 59
def prefixEnd_1310006 : Nat := 4983230072969 + 3 ^ 40 * 1310006 * 2
def baseEnd_1310006 : Nat := 448441825515937886133599

theorem tailTrace_1310006 : CollatzResearch.WordTrace tailWord_1310006 prefixEnd_1310006 448441825515937886133599 := by
  unfold tailWord_1310006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986240255754966753609867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31853229394719645371838581 2986240255754966753609867)
  ·
    refine ⟨4479360383632450130414801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2986240255754966753609867 4479360383632450130414801)
    ·
      refine ⟨3359520287724337597811101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4479360383632450130414801 3359520287724337597811101)
      ·
        refine ⟨1259820107896626599179163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3359520287724337597811101 1259820107896626599179163)
        ·
          refine ⟨1889730161844939898768745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259820107896626599179163 1889730161844939898768745)
          ·
            refine ⟨1417297621383704924076559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1889730161844939898768745 1417297621383704924076559)
            ·
              refine ⟨2125946432075557386114839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417297621383704924076559 2125946432075557386114839)
              ·
                refine ⟨3188919648113336079172259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125946432075557386114839 3188919648113336079172259)
                ·
                  refine ⟨4783379472170004118758389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3188919648113336079172259 4783379472170004118758389)
                  ·
                    refine ⟨448441825515937886133599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4783379472170004118758389 448441825515937886133599)
                    ·
                      rfl

theorem cell22_1310006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1310006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310006 prefixEnd_1310006 := by exact prefixLift 1310006
  have htrace : WordTrace (prefixWord ++ tailWord_1310006) baseStart_1310006 baseEnd_1310006 := by
    simpa [prefixWord, tailWord_1310006, baseEnd_1310006] using wordTrace_append hprefix tailTrace_1310006
  have hstable : (prefixWord ++ tailWord_1310006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310006).length < 2 ^ (prefixWord ++ tailWord_1310006).sum := by decide
  have hdescent : baseEnd_1310006 < baseStart_1310006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310038 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1310038 : Nat := 118140960795 + 1310038 * 2 ^ 59
def prefixEnd_1310038 : Nat := 4983230072969 + 3 ^ 40 * 1310038 * 2
def baseEnd_1310038 : Nat := 448452779769900469333501

theorem tailTrace_1310038 : CollatzResearch.WordTrace tailWord_1310038 prefixEnd_1310038 448452779769900469333501 := by
  unfold tailWord_1310038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986313201747721095182673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31854007485309025015281845 2986313201747721095182673)
  ·
    refine ⟨2239734901310790821387005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2986313201747721095182673 2239734901310790821387005)
    ·
      refine ⟨839900587991546558020127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2239734901310790821387005 839900587991546558020127)
      ·
        refine ⟨1259850881987319837030191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839900587991546558020127 1259850881987319837030191)
        ·
          refine ⟨1889776322980979755545287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259850881987319837030191 1889776322980979755545287)
          ·
            refine ⟨2834664484471469633317931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889776322980979755545287 2834664484471469633317931)
            ·
              refine ⟨4251996726707204449976897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834664484471469633317931 4251996726707204449976897)
              ·
                refine ⟨3188997545030403337482673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4251996726707204449976897 3188997545030403337482673)
                ·
                  refine ⟨2391748158772802503112005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3188997545030403337482673 2391748158772802503112005)
                  ·
                    refine ⟨448452779769900469333501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2391748158772802503112005 448452779769900469333501)
                    ·
                      rfl

theorem cell22_1310038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1310038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310038 prefixEnd_1310038 := by exact prefixLift 1310038
  have htrace : WordTrace (prefixWord ++ tailWord_1310038) baseStart_1310038 baseEnd_1310038 := by
    simpa [prefixWord, tailWord_1310038, baseEnd_1310038] using wordTrace_append hprefix tailTrace_1310038
  have hstable : (prefixWord ++ tailWord_1310038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310038).length < 2 ^ (prefixWord ++ tailWord_1310038).sum := by decide
  have hdescent : baseEnd_1310038 < baseStart_1310038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310051 : List Nat := [1, 1, 1, 5, 2, 3, 3, 2, 1, 3]
def baseStart_1310051 : Nat := 118140960795 + 1310051 * 2 ^ 59
def prefixEnd_1310051 : Nat := 4983230072969 + 3 ^ 40 * 1310051 * 2
def baseEnd_1310051 : Nat := 448457229935572768758461

theorem tailTrace_1310051 : CollatzResearch.WordTrace tailWord_1310051 prefixEnd_1310051 448457229935572768758461 := by
  unfold tailWord_1310051
  simp only [CollatzResearch.WordTrace]
  refine ⟨47781485376916440743146007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31854323584610960495430671 47781485376916440743146007)
  ·
    refine ⟨71672228065374661114719011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47781485376916440743146007 71672228065374661114719011)
    ·
      refine ⟨107508342098061991672078517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71672228065374661114719011 107508342098061991672078517)
      ·
        refine ⟨10078907071693311719257361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107508342098061991672078517 10078907071693311719257361)
        ·
          refine ⟨7559180303769983789443021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10078907071693311719257361 7559180303769983789443021)
          ·
            refine ⟨2834692613913743921041133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7559180303769983789443021 2834692613913743921041133)
            ·
              refine ⟨1063009730217653970390425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2834692613913743921041133 1063009730217653970390425)
              ·
                refine ⟨797257297663240477792819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1063009730217653970390425 797257297663240477792819)
                ·
                  refine ⟨1195885946494860716689229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797257297663240477792819 1195885946494860716689229)
                  ·
                    refine ⟨448457229935572768758461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1195885946494860716689229 448457229935572768758461)
                    ·
                      rfl

theorem cell22_1310051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 3].length) (baseStart_1310051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310051 prefixEnd_1310051 := by exact prefixLift 1310051
  have htrace : WordTrace (prefixWord ++ tailWord_1310051) baseStart_1310051 baseEnd_1310051 := by
    simpa [prefixWord, tailWord_1310051, baseEnd_1310051] using wordTrace_append hprefix tailTrace_1310051
  have hstable : (prefixWord ++ tailWord_1310051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310051).length < 2 ^ (prefixWord ++ tailWord_1310051).sum := by decide
  have hdescent : baseEnd_1310051 < baseStart_1310051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310092 : List Nat := [2, 2, 1, 2, 1, 3, 2, 5, 4]
def baseStart_1310092 : Nat := 118140960795 + 1310092 * 2 ^ 59
def prefixEnd_1310092 : Nat := 4983230072969 + 3 ^ 40 * 1310092 * 2
def baseEnd_1310092 : Nat := 149490421691154109494445

theorem tailTrace_1310092 : CollatzResearch.WordTrace tailWord_1310092 prefixEnd_1310092 149490421691154109494445 := by
  unfold tailWord_1310092
  simp only [CollatzResearch.WordTrace]
  refine ⟨23891490384883952372694265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31855320513178603163592353 23891490384883952372694265)
  ·
    refine ⟨17918617788662964279520699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23891490384883952372694265 17918617788662964279520699)
    ·
      refine ⟨26877926682994446419281049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17918617788662964279520699 26877926682994446419281049)
      ·
        refine ⟨20158445012245834814460787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26877926682994446419281049 20158445012245834814460787)
        ·
          refine ⟨30237667518368752221691181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20158445012245834814460787 30237667518368752221691181)
          ·
            refine ⟨11339125319388282083134193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30237667518368752221691181 11339125319388282083134193)
            ·
              refine ⟨8504343989541211562350645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11339125319388282083134193 8504343989541211562350645)
              ·
                refine ⟨797282249019488583970373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8504343989541211562350645 797282249019488583970373)
                ·
                  refine ⟨149490421691154109494445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797282249019488583970373 149490421691154109494445)
                  ·
                    rfl

theorem cell22_1310092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_1310092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310092 prefixEnd_1310092 := by exact prefixLift 1310092
  have htrace : WordTrace (prefixWord ++ tailWord_1310092) baseStart_1310092 baseEnd_1310092 := by
    simpa [prefixWord, tailWord_1310092, baseEnd_1310092] using wordTrace_append hprefix tailTrace_1310092
  have hstable : (prefixWord ++ tailWord_1310092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310092).length < 2 ^ (prefixWord ++ tailWord_1310092).sum := by decide
  have hdescent : baseEnd_1310092 < baseStart_1310092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310109 : List Nat := [1, 4, 2, 1, 3, 2, 1, 4, 4]
def baseStart_1310109 : Nat := 118140960795 + 1310109 * 2 ^ 59
def prefixEnd_1310109 : Nat := 4983230072969 + 3 ^ 40 * 1310109 * 2
def baseEnd_1310109 : Nat := 149492361506959983602761

theorem tailTrace_1310109 : CollatzResearch.WordTrace tailWord_1310109 prefixEnd_1310109 149492361506959983602761 := by
  unfold tailWord_1310109
  simp only [CollatzResearch.WordTrace]
  refine ⟨47783600810706316648757381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31855733873804211099171587 47783600810706316648757381)
  ·
    refine ⟨8959425152007434371642009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47783600810706316648757381 8959425152007434371642009)
    ·
      refine ⟨6719568864005575778731507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8959425152007434371642009 6719568864005575778731507)
      ·
        refine ⟨10079353296008363668097261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6719568864005575778731507 10079353296008363668097261)
        ·
          refine ⟨3779757486003136375536473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10079353296008363668097261 3779757486003136375536473)
          ·
            refine ⟨2834818114502352281652355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3779757486003136375536473 2834818114502352281652355)
            ·
              refine ⟨4252227171753528422478533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2834818114502352281652355 4252227171753528422478533)
              ·
                refine ⟨797292594703786579214725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4252227171753528422478533 797292594703786579214725)
                ·
                  refine ⟨149492361506959983602761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797292594703786579214725 149492361506959983602761)
                  ·
                    rfl

theorem cell22_1310109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_1310109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310109 prefixEnd_1310109 := by exact prefixLift 1310109
  have htrace : WordTrace (prefixWord ++ tailWord_1310109) baseStart_1310109 baseEnd_1310109 := by
    simpa [prefixWord, tailWord_1310109, baseEnd_1310109] using wordTrace_append hprefix tailTrace_1310109
  have hstable : (prefixWord ++ tailWord_1310109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310109).length < 2 ^ (prefixWord ++ tailWord_1310109).sum := by decide
  have hdescent : baseEnd_1310109 < baseStart_1310109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310152 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 5, 3]
def baseStart_1310152 : Nat := 118140960795 + 1310152 * 2 ^ 59
def prefixEnd_1310152 : Nat := 4983230072969 + 3 ^ 40 * 1310152 * 2
def baseEnd_1310152 : Nat := 448491804299642171983151

theorem tailTrace_1310152 : CollatzResearch.WordTrace tailWord_1310152 prefixEnd_1310152 448491804299642171983151 := by
  unfold tailWord_1310152
  simp only [CollatzResearch.WordTrace]
  refine ⟨23892584574775267496286355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31856779433033689995048473 23892584574775267496286355)
  ·
    refine ⟨35838876862162901244429533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23892584574775267496286355 35838876862162901244429533)
    ·
      refine ⟨13439578823311087966661075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35838876862162901244429533 13439578823311087966661075)
      ·
        refine ⟨20159368234966631949991613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13439578823311087966661075 20159368234966631949991613)
        ·
          refine ⟨7559763088112486981246855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20159368234966631949991613 7559763088112486981246855)
          ·
            refine ⟨11339644632168730471870283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7559763088112486981246855 11339644632168730471870283)
            ·
              refine ⟨17009466948253095707805425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11339644632168730471870283 17009466948253095707805425)
              ·
                refine ⟨12757100211189821780854069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17009466948253095707805425 12757100211189821780854069)
                ·
                  refine ⟨1195978144799045791955069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12757100211189821780854069 1195978144799045791955069)
                  ·
                    refine ⟨448491804299642171983151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1195978144799045791955069 448491804299642171983151)
                    ·
                      rfl

theorem cell22_1310152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_1310152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310152 prefixEnd_1310152 := by exact prefixLift 1310152
  have htrace : WordTrace (prefixWord ++ tailWord_1310152) baseStart_1310152 baseEnd_1310152 := by
    simpa [prefixWord, tailWord_1310152, baseEnd_1310152] using wordTrace_append hprefix tailTrace_1310152
  have hstable : (prefixWord ++ tailWord_1310152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310152).length < 2 ^ (prefixWord ++ tailWord_1310152).sum := by decide
  have hdescent : baseEnd_1310152 < baseStart_1310152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310169 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 3, 3]
def baseStart_1310169 : Nat := 118140960795 + 1310169 * 2 ^ 59
def prefixEnd_1310169 : Nat := 4983230072969 + 3 ^ 40 * 1310169 * 2
def baseEnd_1310169 : Nat := 448497623747059794308099

theorem tailTrace_1310169 : CollatzResearch.WordTrace tailWord_1310169 prefixEnd_1310169 448497623747059794308099 := by
  unfold tailWord_1310169
  simp only [CollatzResearch.WordTrace]
  refine ⟨47785789190488946895941561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31857192793659297930627707 47785789190488946895941561)
  ·
    refine ⟨35839341892866710171956171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47785789190488946895941561 35839341892866710171956171)
    ·
      refine ⟨53759012839300065257934257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35839341892866710171956171 53759012839300065257934257)
      ·
        refine ⟨40319259629475048943450693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53759012839300065257934257 40319259629475048943450693)
        ·
          refine ⟨7559861180526571676897005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40319259629475048943450693 7559861180526571676897005)
          ·
            refine ⟨2834947942697464378836377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7559861180526571676897005 2834947942697464378836377)
            ·
              refine ⟨2126210957023098284127283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834947942697464378836377 2126210957023098284127283)
              ·
                refine ⟨3189316435534647426190925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126210957023098284127283 3189316435534647426190925)
                ·
                  refine ⟨1195993663325492784821597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3189316435534647426190925 1195993663325492784821597)
                  ·
                    refine ⟨448497623747059794308099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1195993663325492784821597 448497623747059794308099)
                    ·
                      rfl

theorem cell22_1310169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_1310169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310169 prefixEnd_1310169 := by exact prefixLift 1310169
  have htrace : WordTrace (prefixWord ++ tailWord_1310169) baseStart_1310169 baseEnd_1310169 := by
    simpa [prefixWord, tailWord_1310169, baseEnd_1310169] using wordTrace_append hprefix tailTrace_1310169
  have hstable : (prefixWord ++ tailWord_1310169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310169).length < 2 ^ (prefixWord ++ tailWord_1310169).sum := by decide
  have hdescent : baseEnd_1310169 < baseStart_1310169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310227 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 6]
def baseStart_1310227 : Nat := 118140960795 + 1310227 * 2 ^ 59
def prefixEnd_1310227 : Nat := 4983230072969 + 3 ^ 40 * 1310227 * 2
def baseEnd_1310227 : Nat := 149505826110788992119307

theorem tailTrace_1310227 : CollatzResearch.WordTrace tailWord_1310227 prefixEnd_1310227 149505826110788992119307 := by
  unfold tailWord_1310227
  simp only [CollatzResearch.WordTrace]
  refine ⟨47787904624278822801552935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31858603082852548534368623 47787904624278822801552935)
  ·
    refine ⟨71681856936418234202329403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47787904624278822801552935 71681856936418234202329403)
    ·
      refine ⟨107522785404627351303494105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71681856936418234202329403 107522785404627351303494105)
      ·
        refine ⟨80642089053470513477620579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107522785404627351303494105 80642089053470513477620579)
        ·
          refine ⟨120963133580205770216430869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80642089053470513477620579 120963133580205770216430869)
          ·
            refine ⟨5670146886572145478895197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120963133580205770216430869 5670146886572145478895197)
            ·
              refine ⟨2126305082464554554585699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5670146886572145478895197 2126305082464554554585699)
              ·
                refine ⟨3189457623696831831878549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126305082464554554585699 3189457623696831831878549)
                ·
                  refine ⟨149505826110788992119307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3189457623696831831878549 149505826110788992119307)
                  ·
                    rfl

theorem cell22_1310227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 6].length) (baseStart_1310227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310227 prefixEnd_1310227 := by exact prefixLift 1310227
  have htrace : WordTrace (prefixWord ++ tailWord_1310227) baseStart_1310227 baseEnd_1310227 := by
    simpa [prefixWord, tailWord_1310227, baseEnd_1310227] using wordTrace_append hprefix tailTrace_1310227
  have hstable : (prefixWord ++ tailWord_1310227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310227).length < 2 ^ (prefixWord ++ tailWord_1310227).sum := by decide
  have hdescent : baseEnd_1310227 < baseStart_1310227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310381 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1310381 : Nat := 118140960795 + 1310381 * 2 ^ 59
def prefixEnd_1310381 : Nat := 4983230072969 + 3 ^ 40 * 1310381 * 2
def baseEnd_1310381 : Nat := 448570195679561908007449

theorem tailTrace_1310381 : CollatzResearch.WordTrace tailWord_1310381 prefixEnd_1310381 448570195679561908007449 := by
  unfold tailWord_1310381
  simp only [CollatzResearch.WordTrace]
  refine ⟨47793521465720907102658997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31862347643813938068439331 47793521465720907102658997)
  ·
    refine ⟨4480642637411335040874281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47793521465720907102658997 4480642637411335040874281)
    ·
      refine ⟨3360481978058501280655711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4480642637411335040874281 3360481978058501280655711)
      ·
        refine ⟨5040722967087751920983567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360481978058501280655711 5040722967087751920983567)
        ·
          refine ⟨7561084450631627881475351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040722967087751920983567 7561084450631627881475351)
          ·
            refine ⟨11341626675947441822213027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7561084450631627881475351 11341626675947441822213027)
            ·
              refine ⟨17012440013921162733319541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11341626675947441822213027 17012440013921162733319541)
              ·
                refine ⟨1594916251305109006248707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17012440013921162733319541 1594916251305109006248707)
                ·
                  refine ⟨2392374376957663509373061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1594916251305109006248707 2392374376957663509373061)
                  ·
                    refine ⟨448570195679561908007449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2392374376957663509373061 448570195679561908007449)
                    ·
                      rfl

theorem cell22_1310381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1310381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310381 prefixEnd_1310381 := by exact prefixLift 1310381
  have htrace : WordTrace (prefixWord ++ tailWord_1310381) baseStart_1310381 baseEnd_1310381 := by
    simpa [prefixWord, tailWord_1310381, baseEnd_1310381] using wordTrace_append hprefix tailTrace_1310381
  have hstable : (prefixWord ++ tailWord_1310381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310381).length < 2 ^ (prefixWord ++ tailWord_1310381).sum := by decide
  have hdescent : baseEnd_1310381 < baseStart_1310381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310396 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 6]
def baseStart_1310396 : Nat := 118140960795 + 1310396 * 2 ^ 59
def prefixEnd_1310396 : Nat := 4983230072969 + 3 ^ 40 * 1310396 * 2
def baseEnd_1310396 : Nat := 149525110162035622960801

theorem tailTrace_1310396 : CollatzResearch.WordTrace tailWord_1310396 prefixEnd_1310396 149525110162035622960801 := by
  unfold tailWord_1310396
  simp only [CollatzResearch.WordTrace]
  refine ⟨23897034280333282332227521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31862712373777709776303361 23897034280333282332227521)
  ·
    refine ⟨17922775710249961749170641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23897034280333282332227521 17922775710249961749170641)
    ·
      refine ⟨13442081782687471311877981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17922775710249961749170641 13442081782687471311877981)
      ·
        refine ⟨5040780668507801741954243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13442081782687471311877981 5040780668507801741954243)
        ·
          refine ⟨7561171002761702612931365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040780668507801741954243 7561171002761702612931365)
          ·
            refine ⟨1417719563017819239924631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7561171002761702612931365 1417719563017819239924631)
            ·
              refine ⟨2126579344526728859886947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417719563017819239924631 2126579344526728859886947)
              ·
                refine ⟨3189869016790093289830421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126579344526728859886947 3189869016790093289830421)
                ·
                  refine ⟨149525110162035622960801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3189869016790093289830421 149525110162035622960801)
                  ·
                    rfl

theorem cell22_1310396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_1310396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310396 prefixEnd_1310396 := by exact prefixLift 1310396
  have htrace : WordTrace (prefixWord ++ tailWord_1310396) baseStart_1310396 baseEnd_1310396 := by
    simpa [prefixWord, tailWord_1310396, baseEnd_1310396] using wordTrace_append hprefix tailTrace_1310396
  have hstable : (prefixWord ++ tailWord_1310396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310396).length < 2 ^ (prefixWord ++ tailWord_1310396).sum := by decide
  have hdescent : baseEnd_1310396 < baseStart_1310396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310426 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_1310426 : Nat := 118140960795 + 1310426 * 2 ^ 59
def prefixEnd_1310426 : Nat := 4983230072969 + 3 ^ 40 * 1310426 * 2
def baseEnd_1310426 : Nat := 448585600099196790632311

theorem tailTrace_1310426 : CollatzResearch.WordTrace tailWord_1310426 prefixEnd_1310426 448585600099196790632311 := by
  unfold tailWord_1310426
  simp only [CollatzResearch.WordTrace]
  refine ⟨11948790687639469947011783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31863441833705253192031421 11948790687639469947011783)
  ·
    refine ⟨17923186031459204920517675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11948790687639469947011783 17923186031459204920517675)
    ·
      refine ⟨26884779047188807380776513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17923186031459204920517675 26884779047188807380776513)
      ·
        refine ⟨20163584285391605535582385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26884779047188807380776513 20163584285391605535582385)
        ·
          refine ⟨15122688214043704151686789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20163584285391605535582385 15122688214043704151686789)
          ·
            refine ⟨2835504040133194528441273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15122688214043704151686789 2835504040133194528441273)
            ·
              refine ⟨2126628030099895896330955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2835504040133194528441273 2126628030099895896330955)
              ·
                refine ⟨3189942045149843844496433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126628030099895896330955 3189942045149843844496433)
                ·
                  refine ⟨2392456533862382883372325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3189942045149843844496433 2392456533862382883372325)
                  ·
                    refine ⟨448585600099196790632311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2392456533862382883372325 448585600099196790632311)
                    ·
                      rfl

theorem cell22_1310426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_1310426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310426 prefixEnd_1310426 := by exact prefixLift 1310426
  have htrace : WordTrace (prefixWord ++ tailWord_1310426) baseStart_1310426 baseEnd_1310426 := by
    simpa [prefixWord, tailWord_1310426, baseEnd_1310426] using wordTrace_append hprefix tailTrace_1310426
  have hstable : (prefixWord ++ tailWord_1310426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310426).length < 2 ^ (prefixWord ++ tailWord_1310426).sum := by decide
  have hdescent : baseEnd_1310426 < baseStart_1310426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310428 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1310428 : Nat := 118140960795 + 1310428 * 2 ^ 59
def prefixEnd_1310428 : Nat := 4983230072969 + 3 ^ 40 * 1310428 * 2
def baseEnd_1310428 : Nat := 448586284740069452082305

theorem tailTrace_1310428 : CollatzResearch.WordTrace tailWord_1310428 prefixEnd_1310428 448586284740069452082305 := by
  unfold tailWord_1310428
  simp only [CollatzResearch.WordTrace]
  refine ⟨23897617848275317064809969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31863490464367089419746625 23897617848275317064809969)
  ·
    refine ⟨17923213386206487798607477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23897617848275317064809969 17923213386206487798607477)
    ·
      refine ⟨1680301254956858231119451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17923213386206487798607477 1680301254956858231119451)
      ·
        refine ⟨2520451882435287346679177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680301254956858231119451 2520451882435287346679177)
        ·
          refine ⟨1890338911826465510009383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2520451882435287346679177 1890338911826465510009383)
          ·
            refine ⟨2835508367739698265014075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890338911826465510009383 2835508367739698265014075)
            ·
              refine ⟨4253262551609547397521113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835508367739698265014075 4253262551609547397521113)
              ·
                refine ⟨3189946913707160548140835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4253262551609547397521113 3189946913707160548140835)
                ·
                  refine ⟨4784920370560740822211253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189946913707160548140835 4784920370560740822211253)
                  ·
                    refine ⟨448586284740069452082305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4784920370560740822211253 448586284740069452082305)
                    ·
                      rfl

theorem cell22_1310428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1310428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310428 prefixEnd_1310428 := by exact prefixLift 1310428
  have htrace : WordTrace (prefixWord ++ tailWord_1310428) baseStart_1310428 baseEnd_1310428 := by
    simpa [prefixWord, tailWord_1310428, baseEnd_1310428] using wordTrace_append hprefix tailTrace_1310428
  have hstable : (prefixWord ++ tailWord_1310428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310428).length < 2 ^ (prefixWord ++ tailWord_1310428).sum := by decide
  have hdescent : baseEnd_1310428 < baseStart_1310428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310477 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1310477 : Nat := 118140960795 + 1310477 * 2 ^ 59
def prefixEnd_1310477 : Nat := 4983230072969 + 3 ^ 40 * 1310477 * 2
def baseEnd_1310477 : Nat := 448603058441449657607155

theorem tailTrace_1310477 : CollatzResearch.WordTrace tailWord_1310477 prefixEnd_1310477 448603058441449657607155 := by
  unfold tailWord_1310477
  simp only [CollatzResearch.WordTrace]
  refine ⟨47797022873373115498153685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31864681915582076998769123 47797022873373115498153685)
  ·
    refine ⟨1120242723594682394487977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 47797022873373115498153685 1120242723594682394487977)
    ·
      refine ⟨840182042696011795865983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1120242723594682394487977 840182042696011795865983)
      ·
        refine ⟨1260273064044017693798975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840182042696011795865983 1260273064044017693798975)
        ·
          refine ⟨1890409596066026540698463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260273064044017693798975 1890409596066026540698463)
          ·
            refine ⟨2835614394099039811047695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890409596066026540698463 2835614394099039811047695)
            ·
              refine ⟨4253421591148559716571543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835614394099039811047695 4253421591148559716571543)
              ·
                refine ⟨6380132386722839574857315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253421591148559716571543 6380132386722839574857315)
                ·
                  refine ⟨9570198580084259362285973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6380132386722839574857315 9570198580084259362285973)
                  ·
                    refine ⟨448603058441449657607155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9570198580084259362285973 448603058441449657607155)
                    ·
                      rfl

theorem cell22_1310477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1310477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310477 prefixEnd_1310477 := by exact prefixLift 1310477
  have htrace : WordTrace (prefixWord ++ tailWord_1310477) baseStart_1310477 baseEnd_1310477 := by
    simpa [prefixWord, tailWord_1310477, baseEnd_1310477] using wordTrace_append hprefix tailTrace_1310477
  have hstable : (prefixWord ++ tailWord_1310477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310477).length < 2 ^ (prefixWord ++ tailWord_1310477).sum := by decide
  have hdescent : baseEnd_1310477 < baseStart_1310477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310490 : List Nat := [3, 1, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_1310490 : Nat := 118140960795 + 1310490 * 2 ^ 59
def prefixEnd_1310490 : Nat := 4983230072969 + 3 ^ 40 * 1310490 * 2
def baseEnd_1310490 : Nat := 448607508607121957032115

theorem tailTrace_1310490 : CollatzResearch.WordTrace tailWord_1310490 prefixEnd_1310490 448607508607121957032115 := by
  unfold tailWord_1310490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11949374255581504679594231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31864998014884012478917949 11949374255581504679594231)
  ·
    refine ⟨17924061383372257019391347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11949374255581504679594231 17924061383372257019391347)
    ·
      refine ⟨26886092075058385529087021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17924061383372257019391347 26886092075058385529087021)
      ·
        refine ⟨10082284528146894573407633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26886092075058385529087021 10082284528146894573407633)
        ·
          refine ⟨7561713396110170930055725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10082284528146894573407633 7561713396110170930055725)
          ·
            refine ⟨2835642523541314098770897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7561713396110170930055725 2835642523541314098770897)
            ·
              refine ⟨2126731892655985574078173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2835642523541314098770897 2126731892655985574078173)
              ·
                refine ⟨797524459745994590279315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2126731892655985574078173 797524459745994590279315)
                ·
                  refine ⟨1196286689618991885418973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797524459745994590279315 1196286689618991885418973)
                  ·
                    refine ⟨448607508607121957032115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196286689618991885418973 448607508607121957032115)
                    ·
                      rfl

theorem cell22_1310490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_1310490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310490 prefixEnd_1310490 := by exact prefixLift 1310490
  have htrace : WordTrace (prefixWord ++ tailWord_1310490) baseStart_1310490 baseEnd_1310490 := by
    simpa [prefixWord, tailWord_1310490, baseEnd_1310490] using wordTrace_append hprefix tailTrace_1310490
  have hstable : (prefixWord ++ tailWord_1310490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310490).length < 2 ^ (prefixWord ++ tailWord_1310490).sum := by decide
  have hdescent : baseEnd_1310490 < baseStart_1310490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310518 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1310518 : Nat := 118140960795 + 1310518 * 2 ^ 59
def prefixEnd_1310518 : Nat := 4983230072969 + 3 ^ 40 * 1310518 * 2
def baseEnd_1310518 : Nat := 448617093579339217332029

theorem tailTrace_1310518 : CollatzResearch.WordTrace tailWord_1310518 prefixEnd_1310518 448617093579339217332029 := by
  unfold tailWord_1310518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987407391639036218774763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31865678844149719666930805 2987407391639036218774763)
  ·
    refine ⟨4481111087458554328162145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2987407391639036218774763 4481111087458554328162145)
    ·
      refine ⟨3360833315593915746121609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4481111087458554328162145 3360833315593915746121609)
      ·
        refine ⟨2520624986695436809591207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3360833315593915746121609 2520624986695436809591207)
        ·
          refine ⟨3780937480043155214386811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2520624986695436809591207 3780937480043155214386811)
          ·
            refine ⟨5671406220064732821580217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780937480043155214386811 5671406220064732821580217)
            ·
              refine ⟨4253554665048549616185163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5671406220064732821580217 4253554665048549616185163)
              ·
                refine ⟨6380331997572824424277745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4253554665048549616185163 6380331997572824424277745)
                ·
                  refine ⟨4785248998179618318208309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6380331997572824424277745 4785248998179618318208309)
                  ·
                    refine ⟨448617093579339217332029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4785248998179618318208309 448617093579339217332029)
                    ·
                      rfl

theorem cell22_1310518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1310518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310518 prefixEnd_1310518 := by exact prefixLift 1310518
  have htrace : WordTrace (prefixWord ++ tailWord_1310518) baseStart_1310518 baseEnd_1310518 := by
    simpa [prefixWord, tailWord_1310518, baseEnd_1310518] using wordTrace_append hprefix tailTrace_1310518
  have hstable : (prefixWord ++ tailWord_1310518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310518).length < 2 ^ (prefixWord ++ tailWord_1310518).sum := by decide
  have hdescent : baseEnd_1310518 < baseStart_1310518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310559 : List Nat := [1, 1, 2, 3, 1, 4, 10]
def baseStart_1310559 : Nat := 118140960795 + 1310559 * 2 ^ 59
def prefixEnd_1310559 : Nat := 4983230072969 + 3 ^ 40 * 1310559 * 2
def baseEnd_1310559 : Nat := 16615967730267732483589

theorem tailTrace_1310559 : CollatzResearch.WordTrace tailWord_1310559 prefixEnd_1310559 16615967730267732483589 := by
  unfold tailWord_1310559
  simp only [CollatzResearch.WordTrace]
  refine ⟨47800013659076043502638731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31866675772717362335092487 47800013659076043502638731)
  ·
    refine ⟨71700020488614065253958097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47800013659076043502638731 71700020488614065253958097)
    ·
      refine ⟨53775015366460548940468573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71700020488614065253958097 53775015366460548940468573)
      ·
        refine ⟨20165630762422705852675715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53775015366460548940468573 20165630762422705852675715)
        ·
          refine ⟨30248446143634058779013573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20165630762422705852675715 30248446143634058779013573)
          ·
            refine ⟨5671583651931386021065045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30248446143634058779013573 5671583651931386021065045)
            ·
              refine ⟨16615967730267732483589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5671583651931386021065045 16615967730267732483589)
              ·
                rfl

theorem cell22_1310559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 10].length) (baseStart_1310559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310559 prefixEnd_1310559 := by exact prefixLift 1310559
  have htrace : WordTrace (prefixWord ++ tailWord_1310559) baseStart_1310559 baseEnd_1310559 := by
    simpa [prefixWord, tailWord_1310559, baseEnd_1310559] using wordTrace_append hprefix tailTrace_1310559
  have hstable : (prefixWord ++ tailWord_1310559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310559).length < 2 ^ (prefixWord ++ tailWord_1310559).sum := by decide
  have hdescent : baseEnd_1310559 < baseStart_1310559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310561 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_1310561 : Nat := 118140960795 + 1310561 * 2 ^ 59
def prefixEnd_1310561 : Nat := 4983230072969 + 3 ^ 40 * 1310561 * 2
def baseEnd_1310561 : Nat := 448631813358101438506897

theorem tailTrace_1310561 : CollatzResearch.WordTrace tailWord_1310561 prefixEnd_1310561 448631813358101438506897 := by
  unfold tailWord_1310561
  simp only [CollatzResearch.WordTrace]
  refine ⟨47800086605068797844211537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31866724403379198562807691 47800086605068797844211537)
  ·
    refine ⟨35850064953801598383158653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47800086605068797844211537 35850064953801598383158653)
    ·
      refine ⟨13443774357675599393684495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35850064953801598383158653 13443774357675599393684495)
      ·
        refine ⟨20165661536513399090526743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13443774357675599393684495 20165661536513399090526743)
        ·
          refine ⟨30248492304770098635790115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20165661536513399090526743 30248492304770098635790115)
          ·
            refine ⟨45372738457155147953685173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30248492304770098635790115 45372738457155147953685173)
            ·
              refine ⟨4253694230358295120657985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45372738457155147953685173 4253694230358295120657985)
              ·
                refine ⟨3190270672768721340493489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4253694230358295120657985 3190270672768721340493489)
                ·
                  refine ⟨2392703004576541005370117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3190270672768721340493489 2392703004576541005370117)
                  ·
                    refine ⟨448631813358101438506897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2392703004576541005370117 448631813358101438506897)
                    ·
                      rfl

theorem cell22_1310561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_1310561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310561 prefixEnd_1310561 := by exact prefixLift 1310561
  have htrace : WordTrace (prefixWord ++ tailWord_1310561) baseStart_1310561 baseEnd_1310561 := by
    simpa [prefixWord, tailWord_1310561, baseEnd_1310561] using wordTrace_append hprefix tailTrace_1310561
  have hstable : (prefixWord ++ tailWord_1310561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310561).length < 2 ^ (prefixWord ++ tailWord_1310561).sum := by decide
  have hdescent : baseEnd_1310561 < baseStart_1310561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310591 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 5, 3]
def baseStart_1310591 : Nat := 118140960795 + 1310591 * 2 ^ 59
def prefixEnd_1310591 : Nat := 4983230072969 + 3 ^ 40 * 1310591 * 2
def baseEnd_1310591 : Nat := 448642082971191360256805

theorem tailTrace_1310591 : CollatzResearch.WordTrace tailWord_1310591 prefixEnd_1310591 448642082971191360256805 := by
  unfold tailWord_1310591
  simp only [CollatzResearch.WordTrace]
  refine ⟨47801180794960112967803627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31867453863306741978535751 47801180794960112967803627)
  ·
    refine ⟨71701771192440169451705441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47801180794960112967803627 71701771192440169451705441)
    ·
      refine ⟨53776328394330127088779081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71701771192440169451705441 53776328394330127088779081)
      ·
        refine ⟨40332246295747595316584311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53776328394330127088779081 40332246295747595316584311)
        ·
          refine ⟨60498369443621392974876467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40332246295747595316584311 60498369443621392974876467)
          ·
            refine ⟨90747554165432089462314701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60498369443621392974876467 90747554165432089462314701)
            ·
              refine ⟨34030332812037033548368013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90747554165432089462314701 34030332812037033548368013)
              ·
                refine ⟨12761374804513887580638005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34030332812037033548368013 12761374804513887580638005)
                ·
                  refine ⟨1196378887923176960684813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12761374804513887580638005 1196378887923176960684813)
                  ·
                    refine ⟨448642082971191360256805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196378887923176960684813 448642082971191360256805)
                    ·
                      rfl

theorem cell22_1310591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_1310591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310591 prefixEnd_1310591 := by exact prefixLift 1310591
  have htrace : WordTrace (prefixWord ++ tailWord_1310591) baseStart_1310591 baseEnd_1310591 := by
    simpa [prefixWord, tailWord_1310591, baseEnd_1310591] using wordTrace_append hprefix tailTrace_1310591
  have hstable : (prefixWord ++ tailWord_1310591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310591).length < 2 ^ (prefixWord ++ tailWord_1310591).sum := by decide
  have hdescent : baseEnd_1310591 < baseStart_1310591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310730 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_1310730 : Nat := 118140960795 + 1310730 * 2 ^ 59
def prefixEnd_1310730 : Nat := 4983230072969 + 3 ^ 40 * 1310730 * 2
def baseEnd_1310730 : Nat := 448689665511841331031379

theorem tailTrace_1310730 : CollatzResearch.WordTrace tailWord_1310730 prefixEnd_1310730 448689665511841331031379 := by
  unfold tailWord_1310730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11951562635364134926778411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31870833694304359804742429 11951562635364134926778411)
  ·
    refine ⟨17927343953046202390167617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11951562635364134926778411 17927343953046202390167617)
    ·
      refine ⟨13445507964784651792625713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17927343953046202390167617 13445507964784651792625713)
      ·
        refine ⟨10084130973588488844469285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13445507964784651792625713 10084130973588488844469285)
        ·
          refine ⟨1890774557547841658337991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10084130973588488844469285 1890774557547841658337991)
          ·
            refine ⟨2836161836321762487506987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890774557547841658337991 2836161836321762487506987)
            ·
              refine ⟨4254242754482643731260481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836161836321762487506987 4254242754482643731260481)
              ·
                refine ⟨3190682065861982798445361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4254242754482643731260481 3190682065861982798445361)
                ·
                  refine ⟨2393011549396487098834021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3190682065861982798445361 2393011549396487098834021)
                  ·
                    refine ⟨448689665511841331031379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2393011549396487098834021 448689665511841331031379)
                    ·
                      rfl

theorem cell22_1310730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_1310730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310730 prefixEnd_1310730 := by exact prefixLift 1310730
  have htrace : WordTrace (prefixWord ++ tailWord_1310730) baseStart_1310730 baseEnd_1310730 := by
    simpa [prefixWord, tailWord_1310730, baseEnd_1310730] using wordTrace_append hprefix tailTrace_1310730
  have hstable : (prefixWord ++ tailWord_1310730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310730).length < 2 ^ (prefixWord ++ tailWord_1310730).sum := by decide
  have hdescent : baseEnd_1310730 < baseStart_1310730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310749 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_1310749 : Nat := 118140960795 + 1310749 * 2 ^ 59
def prefixEnd_1310749 : Nat := 4983230072969 + 3 ^ 40 * 1310749 * 2
def baseEnd_1310749 : Nat := 448696169600131614806321

theorem tailTrace_1310749 : CollatzResearch.WordTrace tailWord_1310749 prefixEnd_1310749 448696169600131614806321 := by
  unfold tailWord_1310749
  simp only [CollatzResearch.WordTrace]
  refine ⟨47806943528387705952055301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31871295685591803968036867 47806943528387705952055301)
  ·
    refine ⟨8963801911572694866010369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47806943528387705952055301 8963801911572694866010369)
    ·
      refine ⟨6722851433679521149507777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8963801911572694866010369 6722851433679521149507777)
      ·
        refine ⟨5042138575259640862130833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6722851433679521149507777 5042138575259640862130833)
        ·
          refine ⟨3781603931444730646598125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5042138575259640862130833 3781603931444730646598125)
          ·
            refine ⟨1418101474291773992474297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3781603931444730646598125 1418101474291773992474297)
            ·
              refine ⟨1063576105718830494355723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1418101474291773992474297 1063576105718830494355723)
              ·
                refine ⟨1595364158578245741533585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063576105718830494355723 1595364158578245741533585)
                ·
                  refine ⟨1196523118933684306150189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1595364158578245741533585 1196523118933684306150189)
                  ·
                    refine ⟨448696169600131614806321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196523118933684306150189 448696169600131614806321)
                    ·
                      rfl

theorem cell22_1310749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_1310749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310749 prefixEnd_1310749 := by exact prefixLift 1310749
  have htrace : WordTrace (prefixWord ++ tailWord_1310749) baseStart_1310749 baseEnd_1310749 := by
    simpa [prefixWord, tailWord_1310749, baseEnd_1310749] using wordTrace_append hprefix tailTrace_1310749
  have hstable : (prefixWord ++ tailWord_1310749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310749).length < 2 ^ (prefixWord ++ tailWord_1310749).sum := by decide
  have hdescent : baseEnd_1310749 < baseStart_1310749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310833 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_1310833 : Nat := 118140960795 + 1310833 * 2 ^ 59
def prefixEnd_1310833 : Nat := 4983230072969 + 3 ^ 40 * 1310833 * 2
def baseEnd_1310833 : Nat := 448724924516783395706063

theorem tailTrace_1310833 : CollatzResearch.WordTrace tailWord_1310833 prefixEnd_1310833 448724924516783395706063 := by
  unfold tailWord_1310833
  simp only [CollatzResearch.WordTrace]
  refine ⟨47810007260083388298113153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31873338173388925532075435 47810007260083388298113153)
  ·
    refine ⟨35857505445062541223584865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47810007260083388298113153 35857505445062541223584865)
    ·
      refine ⟨26893129083796905917688649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35857505445062541223584865 26893129083796905917688649)
      ·
        refine ⟨20169846812847679438266487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26893129083796905917688649 20169846812847679438266487)
        ·
          refine ⟨30254770219271519157399731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20169846812847679438266487 30254770219271519157399731)
          ·
            refine ⟨45382155328907278736099597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30254770219271519157399731 45382155328907278736099597)
            ·
              refine ⟨17018308248340229526037349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45382155328907278736099597 17018308248340229526037349)
              ·
                refine ⟨3190932796563793036132003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17018308248340229526037349 3190932796563793036132003)
                ·
                  refine ⟨4786399194845689554198005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3190932796563793036132003 4786399194845689554198005)
                  ·
                    refine ⟨448724924516783395706063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4786399194845689554198005 448724924516783395706063)
                    ·
                      rfl

theorem cell22_1310833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_1310833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310833 prefixEnd_1310833 := by exact prefixLift 1310833
  have htrace : WordTrace (prefixWord ++ tailWord_1310833) baseStart_1310833 baseEnd_1310833 := by
    simpa [prefixWord, tailWord_1310833, baseEnd_1310833] using wordTrace_append hprefix tailTrace_1310833
  have hstable : (prefixWord ++ tailWord_1310833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310833).length < 2 ^ (prefixWord ++ tailWord_1310833).sum := by decide
  have hdescent : baseEnd_1310833 < baseStart_1310833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310848 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_1310848 : Nat := 118140960795 + 1310848 * 2 ^ 59
def prefixEnd_1310848 : Nat := 4983230072969 + 3 ^ 40 * 1310848 * 2
def baseEnd_1310848 : Nat := 448730059323328356581017

theorem tailTrace_1310848 : CollatzResearch.WordTrace tailWord_1310848 prefixEnd_1310848 448730059323328356581017 := by
  unfold tailWord_1310848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23905277177514522929954599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31873702903352697239939465 23905277177514522929954599)
  ·
    refine ⟨35857915766271784394931899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23905277177514522929954599 35857915766271784394931899)
    ·
      refine ⟨53786873649407676592397849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35857915766271784394931899 53786873649407676592397849)
      ·
        refine ⟨40340155237055757444298387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53786873649407676592397849 40340155237055757444298387)
        ·
          refine ⟨60510232855583636166447581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40340155237055757444298387 60510232855583636166447581)
          ·
            refine ⟨22691337320843863562417843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60510232855583636166447581 22691337320843863562417843)
            ·
              refine ⟨34037005981265795343626765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22691337320843863562417843 34037005981265795343626765)
              ·
                refine ⟨12763877242974673253860037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34037005981265795343626765 12763877242974673253860037)
                ·
                  refine ⟨2393226983057751235098757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12763877242974673253860037 2393226983057751235098757)
                  ·
                    refine ⟨448730059323328356581017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2393226983057751235098757 448730059323328356581017)
                    ·
                      rfl

theorem cell22_1310848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_1310848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310848 prefixEnd_1310848 := by exact prefixLift 1310848
  have htrace : WordTrace (prefixWord ++ tailWord_1310848) baseStart_1310848 baseEnd_1310848 := by
    simpa [prefixWord, tailWord_1310848, baseEnd_1310848] using wordTrace_append hprefix tailTrace_1310848
  have hstable : (prefixWord ++ tailWord_1310848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310848).length < 2 ^ (prefixWord ++ tailWord_1310848).sum := by decide
  have hdescent : baseEnd_1310848 < baseStart_1310848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310880 : List Nat := [2, 1, 1, 4, 2, 2, 4, 6]
def baseStart_1310880 : Nat := 118140960795 + 1310880 * 2 ^ 59
def prefixEnd_1310880 : Nat := 4983230072969 + 3 ^ 40 * 1310880 * 2
def baseEnd_1310880 : Nat := 49860112619698993308991

theorem tailTrace_1310880 : CollatzResearch.WordTrace tailWord_1310880 prefixEnd_1310880 49860112619698993308991 := by
  unfold tailWord_1310880
  simp only [CollatzResearch.WordTrace]
  refine ⟨23905860745456557662537047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31874480993942076883382729 23905860745456557662537047)
  ·
    refine ⟨35858791118184836493805571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23905860745456557662537047 35858791118184836493805571)
    ·
      refine ⟨53788186677277254740708357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35858791118184836493805571 53788186677277254740708357)
      ·
        refine ⟨10085285001989485263882817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53788186677277254740708357 10085285001989485263882817)
        ·
          refine ⟨7563963751492113947912113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10085285001989485263882817 7563963751492113947912113)
          ·
            refine ⟨5672972813619085460934085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7563963751492113947912113 5672972813619085460934085)
            ·
              refine ⟨1063682402553578523925141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5672972813619085460934085 1063682402553578523925141)
              ·
                refine ⟨49860112619698993308991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1063682402553578523925141 49860112619698993308991)
                ·
                  rfl

theorem cell22_1310880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 6].length) (baseStart_1310880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310880 prefixEnd_1310880 := by exact prefixLift 1310880
  have htrace : WordTrace (prefixWord ++ tailWord_1310880) baseStart_1310880 baseEnd_1310880 := by
    simpa [prefixWord, tailWord_1310880, baseEnd_1310880] using wordTrace_append hprefix tailTrace_1310880
  have hstable : (prefixWord ++ tailWord_1310880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310880).length < 2 ^ (prefixWord ++ tailWord_1310880).sum := by decide
  have hdescent : baseEnd_1310880 < baseStart_1310880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310897 : List Nat := [1, 2, 2, 5, 3, 1, 8]
def baseStart_1310897 : Nat := 118140960795 + 1310897 * 2 ^ 59
def prefixEnd_1310897 : Nat := 4983230072969 + 3 ^ 40 * 1310897 * 2
def baseEnd_1310897 : Nat := 16620253074989206003921

theorem tailTrace_1310897 : CollatzResearch.WordTrace tailWord_1310897 prefixEnd_1310897 16620253074989206003921 := by
  unfold tailWord_1310897
  simp only [CollatzResearch.WordTrace]
  refine ⟨47812341531851527228442945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31874894354567684818961963 47812341531851527228442945)
  ·
    refine ⟨35859256148888645421332209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47812341531851527228442945 35859256148888645421332209)
    ·
      refine ⟨26894442111666484065999157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35859256148888645421332209 26894442111666484065999157)
      ·
        refine ⟨2521353947968732881187421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26894442111666484065999157 2521353947968732881187421)
        ·
          refine ⟨945507730488274830445283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2521353947968732881187421 945507730488274830445283)
          ·
            refine ⟨1418261595732412245667925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945507730488274830445283 1418261595732412245667925)
            ·
              refine ⟨16620253074989206003921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1418261595732412245667925 16620253074989206003921)
              ·
                rfl

theorem cell22_1310897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 8].length) (baseStart_1310897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310897 prefixEnd_1310897 := by exact prefixLift 1310897
  have htrace : WordTrace (prefixWord ++ tailWord_1310897) baseStart_1310897 baseEnd_1310897 := by
    simpa [prefixWord, tailWord_1310897, baseEnd_1310897] using wordTrace_append hprefix tailTrace_1310897
  have hstable : (prefixWord ++ tailWord_1310897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310897).length < 2 ^ (prefixWord ++ tailWord_1310897).sum := by decide
  have hdescent : baseEnd_1310897 < baseStart_1310897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310912 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 3, 3]
def baseStart_1310912 : Nat := 118140960795 + 1310912 * 2 ^ 59
def prefixEnd_1310912 : Nat := 4983230072969 + 3 ^ 40 * 1310912 * 2
def baseEnd_1310912 : Nat := 448751967831253522980821

theorem tailTrace_1310912 : CollatzResearch.WordTrace tailWord_1310912 prefixEnd_1310912 448751967831253522980821 := by
  unfold tailWord_1310912
  simp only [CollatzResearch.WordTrace]
  refine ⟨23906444313398592395119495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31875259084531456526825993 23906444313398592395119495)
  ·
    refine ⟨35859666470097888592679243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23906444313398592395119495 35859666470097888592679243)
    ·
      refine ⟨53789499705146832889018865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35859666470097888592679243 53789499705146832889018865)
      ·
        refine ⟨40342124778860124666764149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53789499705146832889018865 40342124778860124666764149)
        ·
          refine ⟨3782074198018136687509139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40342124778860124666764149 3782074198018136687509139)
          ·
            refine ⟨5673111297027205031263709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782074198018136687509139 5673111297027205031263709)
            ·
              refine ⟨2127416736385201886723891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5673111297027205031263709 2127416736385201886723891)
              ·
                refine ⟨3191125104577802830085837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127416736385201886723891 3191125104577802830085837)
                ·
                  refine ⟨1196671914216676061282189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3191125104577802830085837 1196671914216676061282189)
                  ·
                    refine ⟨448751967831253522980821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196671914216676061282189 448751967831253522980821)
                    ·
                      rfl

theorem cell22_1310912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_1310912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310912 prefixEnd_1310912 := by exact prefixLift 1310912
  have htrace : WordTrace (prefixWord ++ tailWord_1310912) baseStart_1310912 baseEnd_1310912 := by
    simpa [prefixWord, tailWord_1310912, baseEnd_1310912] using wordTrace_append hprefix tailTrace_1310912
  have hstable : (prefixWord ++ tailWord_1310912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310912).length < 2 ^ (prefixWord ++ tailWord_1310912).sum := by decide
  have hdescent : baseEnd_1310912 < baseStart_1310912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310914 : List Nat := [3, 5, 1, 1, 1, 2, 2, 7]
def baseStart_1310914 : Nat := 118140960795 + 1310914 * 2 ^ 59
def prefixEnd_1310914 : Nat := 4983230072969 + 3 ^ 40 * 1310914 * 2
def baseEnd_1310914 : Nat := 49861405830236242714535

theorem tailTrace_1310914 : CollatzResearch.WordTrace tailWord_1310914 prefixEnd_1310914 49861405830236242714535 := by
  unfold tailWord_1310914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11953240393197484782952949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31875307715193292754541197 11953240393197484782952949)
  ·
    refine ⟨1120616286862264198401839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11953240393197484782952949 1120616286862264198401839)
    ·
      refine ⟨1680924430293396297602759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1120616286862264198401839 1680924430293396297602759)
      ·
        refine ⟨2521386645440094446404139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680924430293396297602759 2521386645440094446404139)
        ·
          refine ⟨3782079968160141669606209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2521386645440094446404139 3782079968160141669606209)
          ·
            refine ⟨2836559976120106252204657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3782079968160141669606209 2836559976120106252204657)
            ·
              refine ⟨2127419982090079689153493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836559976120106252204657 2127419982090079689153493)
              ·
                refine ⟨49861405830236242714535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2127419982090079689153493 49861405830236242714535)
                ·
                  rfl

theorem cell22_1310914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_1310914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310914 prefixEnd_1310914 := by exact prefixLift 1310914
  have htrace : WordTrace (prefixWord ++ tailWord_1310914) baseStart_1310914 baseEnd_1310914 := by
    simpa [prefixWord, tailWord_1310914, baseEnd_1310914] using wordTrace_append hprefix tailTrace_1310914
  have hstable : (prefixWord ++ tailWord_1310914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310914).length < 2 ^ (prefixWord ++ tailWord_1310914).sum := by decide
  have hdescent : baseEnd_1310914 < baseStart_1310914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310923 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 1, 7]
def baseStart_1310923 : Nat := 118140960795 + 1310923 * 2 ^ 59
def prefixEnd_1310923 : Nat := 4983230072969 + 3 ^ 40 * 1310923 * 2
def baseEnd_1310923 : Nat := 448755733356053160955787

theorem tailTrace_1310923 : CollatzResearch.WordTrace tailWord_1310923 prefixEnd_1310923 448755733356053160955787 := by
  unfold tailWord_1310923
  simp only [CollatzResearch.WordTrace]
  refine ⟨47813289829757333668889423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31875526553171555779259615 47813289829757333668889423)
  ·
    refine ⟨71719934744636000503334135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47813289829757333668889423 71719934744636000503334135)
    ·
      refine ⟨107579902116954000755001203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71719934744636000503334135 107579902116954000755001203)
      ·
        refine ⟨161369853175431001132501805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107579902116954000755001203 161369853175431001132501805)
        ·
          refine ⟨60513694940786625424688177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161369853175431001132501805 60513694940786625424688177)
          ·
            refine ⟨45385271205589969068516133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60513694940786625424688177 45385271205589969068516133)
            ·
              refine ⟨8509738351048119200346775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45385271205589969068516133 8509738351048119200346775)
              ·
                refine ⟨12764607526572178800520163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8509738351048119200346775 12764607526572178800520163)
                ·
                  refine ⟨19146911289858268200780245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12764607526572178800520163 19146911289858268200780245)
                  ·
                    refine ⟨448755733356053160955787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19146911289858268200780245 448755733356053160955787)
                    ·
                      rfl

theorem cell22_1310923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_1310923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310923 prefixEnd_1310923 := by exact prefixLift 1310923
  have htrace : WordTrace (prefixWord ++ tailWord_1310923) baseStart_1310923 baseEnd_1310923 := by
    simpa [prefixWord, tailWord_1310923, baseEnd_1310923] using wordTrace_append hprefix tailTrace_1310923
  have hstable : (prefixWord ++ tailWord_1310923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310923).length < 2 ^ (prefixWord ++ tailWord_1310923).sum := by decide
  have hdescent : baseEnd_1310923 < baseStart_1310923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310953 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 8]
def baseStart_1310953 : Nat := 118140960795 + 1310953 * 2 ^ 59
def prefixEnd_1310953 : Nat := 4983230072969 + 3 ^ 40 * 1310953 * 2
def baseEnd_1310953 : Nat := 149588667656381027568565

theorem tailTrace_1310953 : CollatzResearch.WordTrace tailWord_1310953 prefixEnd_1310953 149588667656381027568565 := by
  unfold tailWord_1310953
  simp only [CollatzResearch.WordTrace]
  refine ⟨47814384019648648792481513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31876256013099099194987675 47814384019648648792481513)
  ·
    refine ⟨35860788014736486594361135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47814384019648648792481513 35860788014736486594361135)
    ·
      refine ⟨53791182022104729891541703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35860788014736486594361135 53791182022104729891541703)
      ·
        refine ⟨80686773033157094837312555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53791182022104729891541703 80686773033157094837312555)
        ·
          refine ⟨121030159549735642255968833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80686773033157094837312555 121030159549735642255968833)
          ·
            refine ⟨90772619662301731691976625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121030159549735642255968833 90772619662301731691976625)
            ·
              refine ⟨68079464746726298768982469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90772619662301731691976625 68079464746726298768982469)
              ·
                refine ⟨12764899640011181019184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68079464746726298768982469 12764899640011181019184213)
                ·
                  refine ⟨149588667656381027568565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12764899640011181019184213 149588667656381027568565)
                  ·
                    rfl

theorem cell22_1310953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_1310953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310953 prefixEnd_1310953 := by exact prefixLift 1310953
  have htrace : WordTrace (prefixWord ++ tailWord_1310953) baseStart_1310953 baseEnd_1310953 := by
    simpa [prefixWord, tailWord_1310953, baseEnd_1310953] using wordTrace_append hprefix tailTrace_1310953
  have hstable : (prefixWord ++ tailWord_1310953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310953).length < 2 ^ (prefixWord ++ tailWord_1310953).sum := by decide
  have hdescent : baseEnd_1310953 < baseStart_1310953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1310985 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_1310985 : Nat := 118140960795 + 1310985 * 2 ^ 59
def prefixEnd_1310985 : Nat := 4983230072969 + 3 ^ 40 * 1310985 * 2
def baseEnd_1310985 : Nat := 448776957223105665905597

theorem tailTrace_1310985 : CollatzResearch.WordTrace tailWord_1310985 prefixEnd_1310985 448776957223105665905597 := by
  unfold tailWord_1310985
  simp only [CollatzResearch.WordTrace]
  refine ⟨47815551155532718257646409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31877034103688478838430939 47815551155532718257646409)
  ·
    refine ⟨35861663366649538693234807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47815551155532718257646409 35861663366649538693234807)
    ·
      refine ⟨53792495049974308039852211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35861663366649538693234807 53792495049974308039852211)
      ·
        refine ⟨80688742574961462059778317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53792495049974308039852211 80688742574961462059778317)
        ·
          refine ⟨30258278465610548272416869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80688742574961462059778317 30258278465610548272416869)
          ·
            refine ⟨5673427212301977801078163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30258278465610548272416869 5673427212301977801078163)
            ·
              refine ⟨8510140818452966701617245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5673427212301977801078163 8510140818452966701617245)
              ·
                refine ⟨3191302806919862513106467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8510140818452966701617245 3191302806919862513106467)
                ·
                  refine ⟨4786954210379793769659701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3191302806919862513106467 4786954210379793769659701)
                  ·
                    refine ⟨448776957223105665905597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4786954210379793769659701 448776957223105665905597)
                    ·
                      rfl

theorem cell22_1310985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_1310985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1310985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1310985 prefixEnd_1310985 := by exact prefixLift 1310985
  have htrace : WordTrace (prefixWord ++ tailWord_1310985) baseStart_1310985 baseEnd_1310985 := by
    simpa [prefixWord, tailWord_1310985, baseEnd_1310985] using wordTrace_append hprefix tailTrace_1310985
  have hstable : (prefixWord ++ tailWord_1310985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1310985).length < 2 ^ (prefixWord ++ tailWord_1310985).sum := by decide
  have hdescent : baseEnd_1310985 < baseStart_1310985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1310985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311000 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_1311000 : Nat := 118140960795 + 1311000 * 2 ^ 59
def prefixEnd_1311000 : Nat := 4983230072969 + 3 ^ 40 * 1311000 * 2
def baseEnd_1311000 : Nat := 448782092029650626780551

theorem tailTrace_1311000 : CollatzResearch.WordTrace tailWord_1311000 prefixEnd_1311000 448782092029650626780551 := by
  unfold tailWord_1311000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23908049125239187909721227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31877398833652250546294969 23908049125239187909721227)
  ·
    refine ⟨35862073687858781864581841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23908049125239187909721227 35862073687858781864581841)
    ·
      refine ⟨26896555265894086398436381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35862073687858781864581841 26896555265894086398436381)
      ·
        refine ⟨10086208224710282399413643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26896555265894086398436381 10086208224710282399413643)
        ·
          refine ⟨15129312337065423599120465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10086208224710282399413643 15129312337065423599120465)
          ·
            refine ⟨11346984252799067699340349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15129312337065423599120465 11346984252799067699340349)
            ·
              refine ⟨4255119094799650387252631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11346984252799067699340349 4255119094799650387252631)
              ·
                refine ⟨6382678642199475580878947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4255119094799650387252631 6382678642199475580878947)
                ·
                  refine ⟨9574017963299213371318421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6382678642199475580878947 9574017963299213371318421)
                  ·
                    refine ⟨448782092029650626780551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9574017963299213371318421 448782092029650626780551)
                    ·
                      rfl

theorem cell22_1311000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_1311000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311000 prefixEnd_1311000 := by exact prefixLift 1311000
  have htrace : WordTrace (prefixWord ++ tailWord_1311000) baseStart_1311000 baseEnd_1311000 := by
    simpa [prefixWord, tailWord_1311000, baseEnd_1311000] using wordTrace_append hprefix tailTrace_1311000
  have hstable : (prefixWord ++ tailWord_1311000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311000).length < 2 ^ (prefixWord ++ tailWord_1311000).sum := by decide
  have hdescent : baseEnd_1311000 < baseStart_1311000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311006 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1311006 : Nat := 118140960795 + 1311006 * 2 ^ 59
def prefixEnd_1311006 : Nat := 4983230072969 + 3 ^ 40 * 1311006 * 2
def baseEnd_1311006 : Nat := 448784145952268611130533

theorem tailTrace_1311006 : CollatzResearch.WordTrace tailWord_1311006 prefixEnd_1311006 448784145952268611130533 := by
  unfold tailWord_1311006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977039636057079855520109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31877544725637759229440581 5977039636057079855520109)
  ·
    refine ⟨2241389863521404945820041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5977039636057079855520109 2241389863521404945820041)
    ·
      refine ⟨1681042397641053709365031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2241389863521404945820041 1681042397641053709365031)
      ·
        refine ⟨2521563596461580564047547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1681042397641053709365031 2521563596461580564047547)
        ·
          refine ⟨3782345394692370846071321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2521563596461580564047547 3782345394692370846071321)
          ·
            refine ⟨2836759046019278134553491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3782345394692370846071321 2836759046019278134553491)
            ·
              refine ⟨4255138569028917201830237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2836759046019278134553491 4255138569028917201830237)
              ·
                refine ⟨1595676963385843950686339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4255138569028917201830237 1595676963385843950686339)
                ·
                  refine ⟨2393515445078765926029509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1595676963385843950686339 2393515445078765926029509)
                  ·
                    refine ⟨448784145952268611130533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2393515445078765926029509 448784145952268611130533)
                    ·
                      rfl

theorem cell22_1311006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1311006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311006 prefixEnd_1311006 := by exact prefixLift 1311006
  have htrace : WordTrace (prefixWord ++ tailWord_1311006) baseStart_1311006 baseEnd_1311006 := by
    simpa [prefixWord, tailWord_1311006, baseEnd_1311006] using wordTrace_append hprefix tailTrace_1311006
  have hstable : (prefixWord ++ tailWord_1311006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311006).length < 2 ^ (prefixWord ++ tailWord_1311006).sum := by decide
  have hdescent : baseEnd_1311006 < baseStart_1311006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311047 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 3, 3]
def baseStart_1311047 : Nat := 118140960795 + 1311047 * 2 ^ 59
def prefixEnd_1311047 : Nat := 4983230072969 + 3 ^ 40 * 1311047 * 2
def baseEnd_1311047 : Nat := 448798181090158170855407

theorem tailTrace_1311047 : CollatzResearch.WordTrace tailWord_1311047 prefixEnd_1311047 448798181090158170855407 := by
  unfold tailWord_1311047
  simp only [CollatzResearch.WordTrace]
  refine ⟨47817812481308102846403395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31878541654205401897602263 47817812481308102846403395)
  ·
    refine ⟨71726718721962154269605093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47817812481308102846403395 71726718721962154269605093)
    ·
      refine ⟨13448759760367903925550955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71726718721962154269605093 13448759760367903925550955)
      ·
        refine ⟨20173139640551855888326433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13448759760367903925550955 20173139640551855888326433)
        ·
          refine ⟨15129854730413891916244825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20173139640551855888326433 15129854730413891916244825)
          ·
            refine ⟨11347391047810418937183619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15129854730413891916244825 11347391047810418937183619)
            ·
              refine ⟨17021086571715628405775429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11347391047810418937183619 17021086571715628405775429)
              ·
                refine ⟨3191453732196680326082893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17021086571715628405775429 3191453732196680326082893)
                ·
                  refine ⟨1196795149573755122281085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3191453732196680326082893 1196795149573755122281085)
                  ·
                    refine ⟨448798181090158170855407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196795149573755122281085 448798181090158170855407)
                    ·
                      rfl

theorem cell22_1311047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_1311047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311047 prefixEnd_1311047 := by exact prefixLift 1311047
  have htrace : WordTrace (prefixWord ++ tailWord_1311047) baseStart_1311047 baseEnd_1311047 := by
    simpa [prefixWord, tailWord_1311047, baseEnd_1311047] using wordTrace_append hprefix tailTrace_1311047
  have hstable : (prefixWord ++ tailWord_1311047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311047).length < 2 ^ (prefixWord ++ tailWord_1311047).sum := by decide
  have hdescent : baseEnd_1311047 < baseStart_1311047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311064 : List Nat := [2, 1, 2, 2, 1, 1, 2, 7, 1, 3]
def baseStart_1311064 : Nat := 118140960795 + 1311064 * 2 ^ 59
def prefixEnd_1311064 : Nat := 4983230072969 + 3 ^ 40 * 1311064 * 2
def baseEnd_1311064 : Nat := 448804000537575793180355

theorem tailTrace_1311064 : CollatzResearch.WordTrace tailWord_1311064 prefixEnd_1311064 448804000537575793180355 := by
  unfold tailWord_1311064
  simp only [CollatzResearch.WordTrace]
  refine ⟨23909216261123257374886123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31878955014831009833181497 23909216261123257374886123)
  ·
    refine ⟨35863824391684886062329185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23909216261123257374886123 35863824391684886062329185)
    ·
      refine ⟨26897868293763664546746889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35863824391684886062329185 26897868293763664546746889)
      ·
        refine ⟨20173401220322748410060167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26897868293763664546746889 20173401220322748410060167)
        ·
          refine ⟨30260101830484122615090251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20173401220322748410060167 30260101830484122615090251)
          ·
            refine ⟨45390152745726183922635377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30260101830484122615090251 45390152745726183922635377)
            ·
              refine ⟨34042614559294637941976533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45390152745726183922635377 34042614559294637941976533)
              ·
                refine ⟨797873778733468076765075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34042614559294637941976533 797873778733468076765075)
                ·
                  refine ⟨1196810668100202115147613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797873778733468076765075 1196810668100202115147613)
                  ·
                    refine ⟨448804000537575793180355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196810668100202115147613 448804000537575793180355)
                    ·
                      rfl

theorem cell22_1311064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_1311064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311064 prefixEnd_1311064 := by exact prefixLift 1311064
  have htrace : WordTrace (prefixWord ++ tailWord_1311064) baseStart_1311064 baseEnd_1311064 := by
    simpa [prefixWord, tailWord_1311064, baseEnd_1311064] using wordTrace_append hprefix tailTrace_1311064
  have hstable : (prefixWord ++ tailWord_1311064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311064).length < 2 ^ (prefixWord ++ tailWord_1311064).sum := by decide
  have hdescent : baseEnd_1311064 < baseStart_1311064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311081 : List Nat := [1, 2, 1, 1, 1, 3, 7, 2, 1, 3]
def baseStart_1311081 : Nat := 118140960795 + 1311081 * 2 ^ 59
def prefixEnd_1311081 : Nat := 4983230072969 + 3 ^ 40 * 1311081 * 2
def baseEnd_1311081 : Nat := 448809819984993415505303

theorem tailTrace_1311081 : CollatzResearch.WordTrace tailWord_1311081 prefixEnd_1311081 448809819984993415505303 := by
  unfold tailWord_1311081
  simp only [CollatzResearch.WordTrace]
  refine ⟨47819052563184926653141097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31879368375456617768760731 47819052563184926653141097)
  ·
    refine ⟨35864289422388694989855823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47819052563184926653141097 35864289422388694989855823)
    ·
      refine ⟨53796434133583042484783735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35864289422388694989855823 53796434133583042484783735)
      ·
        refine ⟨80694651200374563727175603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53796434133583042484783735 80694651200374563727175603)
        ·
          refine ⟨121041976800561845590763405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80694651200374563727175603 121041976800561845590763405)
          ·
            refine ⟨45390741300210692096536277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121041976800561845590763405 45390741300210692096536277)
            ·
              refine ⟨1063845499223688096012569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45390741300210692096536277 1063845499223688096012569)
              ·
                refine ⟨797884124417766072009427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1063845499223688096012569 797884124417766072009427)
                ·
                  refine ⟨1196826186626649108014141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797884124417766072009427 1196826186626649108014141)
                  ·
                    refine ⟨448809819984993415505303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196826186626649108014141 448809819984993415505303)
                    ·
                      rfl

theorem cell22_1311081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 3].length) (baseStart_1311081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311081 prefixEnd_1311081 := by exact prefixLift 1311081
  have htrace : WordTrace (prefixWord ++ tailWord_1311081) baseStart_1311081 baseEnd_1311081 := by
    simpa [prefixWord, tailWord_1311081, baseEnd_1311081] using wordTrace_append hprefix tailTrace_1311081
  have hstable : (prefixWord ++ tailWord_1311081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311081).length < 2 ^ (prefixWord ++ tailWord_1311081).sum := by decide
  have hdescent : baseEnd_1311081 < baseStart_1311081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311139 : List Nat := [1, 1, 1, 4, 1, 5, 1, 4, 4]
def baseStart_1311139 : Nat := 118140960795 + 1311139 * 2 ^ 59
def prefixEnd_1311139 : Nat := 4983230072969 + 3 ^ 40 * 1311139 * 2
def baseEnd_1311139 : Nat := 149609891523433532518375

theorem tailTrace_1311139 : CollatzResearch.WordTrace tailWord_1311139 prefixEnd_1311139 149609891523433532518375 := by
  unfold tailWord_1311139
  simp only [CollatzResearch.WordTrace]
  refine ⟨47821167996974802558752471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31880778664649868372501647 47821167996974802558752471)
  ·
    refine ⟨71731751995462203838128707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47821167996974802558752471 71731751995462203838128707)
    ·
      refine ⟨107597627993193305757193061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71731751995462203838128707 107597627993193305757193061)
      ·
        refine ⟨20174555248723744829473699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107597627993193305757193061 20174555248723744829473699)
        ·
          refine ⟨30261832873085617244210549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20174555248723744829473699 30261832873085617244210549)
          ·
            refine ⟨2837046831851776616644739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30261832873085617244210549 2837046831851776616644739)
            ·
              refine ⟨4255570247777664924967109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837046831851776616644739 4255570247777664924967109)
              ·
                refine ⟨797919421458312173431333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4255570247777664924967109 797919421458312173431333)
                ·
                  refine ⟨149609891523433532518375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797919421458312173431333 149609891523433532518375)
                  ·
                    rfl

theorem cell22_1311139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 4].length) (baseStart_1311139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311139 prefixEnd_1311139 := by exact prefixLift 1311139
  have htrace : WordTrace (prefixWord ++ tailWord_1311139) baseStart_1311139 baseEnd_1311139 := by
    simpa [prefixWord, tailWord_1311139, baseEnd_1311139] using wordTrace_append hprefix tailTrace_1311139
  have hstable : (prefixWord ++ tailWord_1311139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311139).length < 2 ^ (prefixWord ++ tailWord_1311139).sum := by decide
  have hdescent : baseEnd_1311139 < baseStart_1311139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311154 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_1311154 : Nat := 118140960795 + 1311154 * 2 ^ 59
def prefixEnd_1311154 : Nat := 4983230072969 + 3 ^ 40 * 1311154 * 2
def baseEnd_1311154 : Nat := 448834809376845558430079

theorem tailTrace_1311154 : CollatzResearch.WordTrace tailWord_1311154 prefixEnd_1311154 448834809376845558430079 := by
  unfold tailWord_1311154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11955428772980115030137129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31881143394613640080365677 11955428772980115030137129)
  ·
    refine ⟨8966571579735086272602847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11955428772980115030137129 8966571579735086272602847)
    ·
      refine ⟨13449857369602629408904271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8966571579735086272602847 13449857369602629408904271)
      ·
        refine ⟨20174786054403944113356407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13449857369602629408904271 20174786054403944113356407)
        ·
          refine ⟨30262179081605916170034611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20174786054403944113356407 30262179081605916170034611)
          ·
            refine ⟨45393268622408874255051917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30262179081605916170034611 45393268622408874255051917)
            ·
              refine ⟨17022475733403327845644469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45393268622408874255051917 17022475733403327845644469)
              ·
                refine ⟨1595857100006561985529169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17022475733403327845644469 1595857100006561985529169)
                ·
                  refine ⟨1196892825004921489146877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1595857100006561985529169 1196892825004921489146877)
                  ·
                    refine ⟨448834809376845558430079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196892825004921489146877 448834809376845558430079)
                    ·
                      rfl

theorem cell22_1311154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_1311154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311154 prefixEnd_1311154 := by exact prefixLift 1311154
  have htrace : WordTrace (prefixWord ++ tailWord_1311154) baseStart_1311154 baseEnd_1311154 := by
    simpa [prefixWord, tailWord_1311154, baseEnd_1311154] using wordTrace_append hprefix tailTrace_1311154
  have hstable : (prefixWord ++ tailWord_1311154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311154).length < 2 ^ (prefixWord ++ tailWord_1311154).sum := by decide
  have hdescent : baseEnd_1311154 < baseStart_1311154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311188 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1311188 : Nat := 118140960795 + 1311188 * 2 ^ 59
def prefixEnd_1311188 : Nat := 4983230072969 + 3 ^ 40 * 1311188 * 2
def baseEnd_1311188 : Nat := 448846448271680803079975

theorem tailTrace_1311188 : CollatzResearch.WordTrace tailWord_1311188 prefixEnd_1311188 448846448271680803079975 := by
  unfold tailWord_1311188
  simp only [CollatzResearch.WordTrace]
  refine ⟨23911477586898641963643109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31881970115864855951524145 23911477586898641963643109)
  ·
    refine ⟨4483402047543495368183083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23911477586898641963643109 4483402047543495368183083)
    ·
      refine ⟨6725103071315243052274625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4483402047543495368183083 6725103071315243052274625)
      ·
        refine ⟨5043827303486432289205969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6725103071315243052274625 5043827303486432289205969)
        ·
          refine ⟨3782870477614824216904477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5043827303486432289205969 3782870477614824216904477)
          ·
            refine ⟨1418576429105559081339179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3782870477614824216904477 1418576429105559081339179)
            ·
              refine ⟨2127864643658338622008769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418576429105559081339179 2127864643658338622008769)
              ·
                refine ⟨1595898482743753966506577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127864643658338622008769 1595898482743753966506577)
                ·
                  refine ⟨1196923862057815474879933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1595898482743753966506577 1196923862057815474879933)
                  ·
                    refine ⟨448846448271680803079975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196923862057815474879933 448846448271680803079975)
                    ·
                      rfl

theorem cell22_1311188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1311188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311188 prefixEnd_1311188 := by exact prefixLift 1311188
  have htrace : WordTrace (prefixWord ++ tailWord_1311188) baseStart_1311188 baseEnd_1311188 := by
    simpa [prefixWord, tailWord_1311188, baseEnd_1311188] using wordTrace_append hprefix tailTrace_1311188
  have hstable : (prefixWord ++ tailWord_1311188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311188).length < 2 ^ (prefixWord ++ tailWord_1311188).sum := by decide
  have hdescent : baseEnd_1311188 < baseStart_1311188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311199 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 3, 3]
def baseStart_1311199 : Nat := 118140960795 + 1311199 * 2 ^ 59
def prefixEnd_1311199 : Nat := 4983230072969 + 3 ^ 40 * 1311199 * 2
def baseEnd_1311199 : Nat := 448850213796480441054941

theorem tailTrace_1311199 : CollatzResearch.WordTrace tailWord_1311199 prefixEnd_1311199 448850213796480441054941 := by
  unfold tailWord_1311199
  simp only [CollatzResearch.WordTrace]
  refine ⟨47823356376757432805936651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31882237584504955203957767 47823356376757432805936651)
  ·
    refine ⟨71735034565136149208904977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47823356376757432805936651 71735034565136149208904977)
    ·
      refine ⟨53801275923852111906678733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71735034565136149208904977 53801275923852111906678733)
      ·
        refine ⟨20175478471444541965004525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53801275923852111906678733 20175478471444541965004525)
        ·
          refine ⟨7565804426791703236876697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20175478471444541965004525 7565804426791703236876697)
          ·
            refine ⟨5674353320093777427657523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7565804426791703236876697 5674353320093777427657523)
            ·
              refine ⟨8511529980140666141486285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674353320093777427657523 8511529980140666141486285)
              ·
                refine ⟨3191823742552749803057357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8511529980140666141486285 3191823742552749803057357)
                ·
                  refine ⟨1196933903457281176146509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3191823742552749803057357 1196933903457281176146509)
                  ·
                    refine ⟨448850213796480441054941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196933903457281176146509 448850213796480441054941)
                    ·
                      rfl

theorem cell22_1311199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_1311199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311199 prefixEnd_1311199 := by exact prefixLift 1311199
  have htrace : WordTrace (prefixWord ++ tailWord_1311199) baseStart_1311199 baseEnd_1311199 := by
    simpa [prefixWord, tailWord_1311199, baseEnd_1311199] using wordTrace_append hprefix tailTrace_1311199
  have hstable : (prefixWord ++ tailWord_1311199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311199).length < 2 ^ (prefixWord ++ tailWord_1311199).sum := by decide
  have hdescent : baseEnd_1311199 < baseStart_1311199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311218 : List Nat := [3, 2, 1, 4, 3, 1, 2, 6]
def baseStart_1311218 : Nat := 118140960795 + 1311218 * 2 ^ 59
def prefixEnd_1311218 : Nat := 4983230072969 + 3 ^ 40 * 1311218 * 2
def baseEnd_1311218 : Nat := 49872968653863413869987

theorem tailTrace_1311218 : CollatzResearch.WordTrace tailWord_1311218 prefixEnd_1311218 49872968653863413869987 := by
  unfold tailWord_1311218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11956012340922149762719577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31882699575792399367252205 11956012340922149762719577)
  ·
    refine ⟨8967009255691612322039683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11956012340922149762719577 8967009255691612322039683)
    ·
      refine ⟨13450513883537418483059525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8967009255691612322039683 13450513883537418483059525)
      ·
        refine ⟨2521971353163265965573661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13450513883537418483059525 2521971353163265965573661)
        ·
          refine ⟨945739257436224737090123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2521971353163265965573661 945739257436224737090123)
          ·
            refine ⟨1418608886154337105635185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945739257436224737090123 1418608886154337105635185)
            ·
              refine ⟨1063956664615752829226389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1418608886154337105635185 1063956664615752829226389)
              ·
                refine ⟨49872968653863413869987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1063956664615752829226389 49872968653863413869987)
                ·
                  rfl

theorem cell22_1311218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_1311218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311218 prefixEnd_1311218 := by exact prefixLift 1311218
  have htrace : WordTrace (prefixWord ++ tailWord_1311218) baseStart_1311218 baseEnd_1311218 := by
    simpa [prefixWord, tailWord_1311218, baseEnd_1311218] using wordTrace_append hprefix tailTrace_1311218
  have hstable : (prefixWord ++ tailWord_1311218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311218).length < 2 ^ (prefixWord ++ tailWord_1311218).sum := by decide
  have hdescent : baseEnd_1311218 < baseStart_1311218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311233 : List Nat := [1, 2, 4, 1, 3, 1, 3, 3, 1, 3]
def baseStart_1311233 : Nat := 118140960795 + 1311233 * 2 ^ 59
def prefixEnd_1311233 : Nat := 4983230072969 + 3 ^ 40 * 1311233 * 2
def baseEnd_1311233 : Nat := 448861852691315685704837

theorem tailTrace_1311233 : CollatzResearch.WordTrace tailWord_1311233 prefixEnd_1311233 448861852691315685704837 := by
  unfold tailWord_1311233
  simp only [CollatzResearch.WordTrace]
  refine ⟨47824596458634256612674353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31883064305756171075116235 47824596458634256612674353)
  ·
    refine ⟨35868447343975692459505765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47824596458634256612674353 35868447343975692459505765)
    ·
      refine ⟨6725333876995442336157331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35868447343975692459505765 6725333876995442336157331)
      ·
        refine ⟨10088000815493163504235997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6725333876995442336157331 10088000815493163504235997)
        ·
          refine ⟨3783000305809936314088499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10088000815493163504235997 3783000305809936314088499)
          ·
            refine ⟨5674500458714904471132749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783000305809936314088499 5674500458714904471132749)
            ·
              refine ⟨2127937672018089176674781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5674500458714904471132749 2127937672018089176674781)
              ·
                refine ⟨797976627006783441253043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2127937672018089176674781 797976627006783441253043)
                ·
                  refine ⟨1196964940510175161879565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797976627006783441253043 1196964940510175161879565)
                  ·
                    refine ⟨448861852691315685704837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1196964940510175161879565 448861852691315685704837)
                    ·
                      rfl

theorem cell22_1311233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_1311233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311233 prefixEnd_1311233 := by exact prefixLift 1311233
  have htrace : WordTrace (prefixWord ++ tailWord_1311233) baseStart_1311233 baseEnd_1311233 := by
    simpa [prefixWord, tailWord_1311233, baseEnd_1311233] using wordTrace_append hprefix tailTrace_1311233
  have hstable : (prefixWord ++ tailWord_1311233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311233).length < 2 ^ (prefixWord ++ tailWord_1311233).sum := by decide
  have hdescent : baseEnd_1311233 < baseStart_1311233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311289 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_1311289 : Nat := 118140960795 + 1311289 * 2 ^ 59
def prefixEnd_1311289 : Nat := 4983230072969 + 3 ^ 40 * 1311289 * 2
def baseEnd_1311289 : Nat := 448881022635750206304665

theorem tailTrace_1311289 : CollatzResearch.WordTrace tailWord_1311289 prefixEnd_1311289 448881022635750206304665 := by
  unfold tailWord_1311289
  simp only [CollatzResearch.WordTrace]
  refine ⟨47826638946431378176712921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31884425964287585451141947 47826638946431378176712921)
  ·
    refine ⟨35869979209823533632534691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47826638946431378176712921 35869979209823533632534691)
    ·
      refine ⟨53804968814735300448802037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35869979209823533632534691 53804968814735300448802037)
      ·
        refine ⟨5044215826381434417075191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53804968814735300448802037 5044215826381434417075191)
        ·
          refine ⟨7566323739572151625612787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5044215826381434417075191 7566323739572151625612787)
          ·
            refine ⟨11349485609358227438419181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7566323739572151625612787 11349485609358227438419181)
            ·
              refine ⟨4256057103509335289407193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11349485609358227438419181 4256057103509335289407193)
              ·
                refine ⟨3192042827632001467055395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256057103509335289407193 3192042827632001467055395)
                ·
                  refine ⟨4788064241448002200583093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192042827632001467055395 4788064241448002200583093)
                  ·
                    refine ⟨448881022635750206304665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4788064241448002200583093 448881022635750206304665)
                    ·
                      rfl

theorem cell22_1311289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_1311289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311289 prefixEnd_1311289 := by exact prefixLift 1311289
  have htrace : WordTrace (prefixWord ++ tailWord_1311289) baseStart_1311289 baseEnd_1311289 := by
    simpa [prefixWord, tailWord_1311289, baseEnd_1311289] using wordTrace_append hprefix tailTrace_1311289
  have hstable : (prefixWord ++ tailWord_1311289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311289).length < 2 ^ (prefixWord ++ tailWord_1311289).sum := by decide
  have hdescent : baseEnd_1311289 < baseStart_1311289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311293 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_1311293 : Nat := 118140960795 + 1311293 * 2 ^ 59
def prefixEnd_1311293 : Nat := 4983230072969 + 3 ^ 40 * 1311293 * 2
def baseEnd_1311293 : Nat := 448882391917495529204653

theorem tailTrace_1311293 : CollatzResearch.WordTrace tailWord_1311293 prefixEnd_1311293 448882391917495529204653 := by
  unfold tailWord_1311293
  simp only [CollatzResearch.WordTrace]
  refine ⟨47826784838416886859858533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31884523225611257906572355 47826784838416886859858533)
  ·
    refine ⟨8967522157203166286223475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47826784838416886859858533 8967522157203166286223475)
    ·
      refine ⟨13451283235804749429335213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8967522157203166286223475 13451283235804749429335213)
      ·
        refine ⟨5044231213426781036000705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13451283235804749429335213 5044231213426781036000705)
        ·
          refine ⟨3783173410070085777000529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5044231213426781036000705 3783173410070085777000529)
          ·
            refine ⟨2837380057552564332750397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3783173410070085777000529 2837380057552564332750397)
            ·
              refine ⟨1064017521582211624781399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2837380057552564332750397 1064017521582211624781399)
              ·
                refine ⟨1596026282373317437172099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064017521582211624781399 1596026282373317437172099)
                ·
                  refine ⟨2394039423559976155758149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596026282373317437172099 2394039423559976155758149)
                  ·
                    refine ⟨448882391917495529204653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2394039423559976155758149 448882391917495529204653)
                    ·
                      rfl

theorem cell22_1311293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_1311293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311293 prefixEnd_1311293 := by exact prefixLift 1311293
  have htrace : WordTrace (prefixWord ++ tailWord_1311293) baseStart_1311293 baseEnd_1311293 := by
    simpa [prefixWord, tailWord_1311293, baseEnd_1311293] using wordTrace_append hprefix tailTrace_1311293
  have hstable : (prefixWord ++ tailWord_1311293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311293).length < 2 ^ (prefixWord ++ tailWord_1311293).sum := by decide
  have hdescent : baseEnd_1311293 < baseStart_1311293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311306 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_1311306 : Nat := 118140960795 + 1311306 * 2 ^ 59
def prefixEnd_1311306 : Nat := 4983230072969 + 3 ^ 40 * 1311306 * 2
def baseEnd_1311306 : Nat := 448886842083167828629613

theorem tailTrace_1311306 : CollatzResearch.WordTrace tailWord_1311306 prefixEnd_1311306 448886842083167828629613 := by
  unfold tailWord_1311306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11956814746842447520020443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31884839324913193386721181 11956814746842447520020443)
  ·
    refine ⟨17935222120263671280030665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11956814746842447520020443 17935222120263671280030665)
    ·
      refine ⟨13451416590197753460022999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17935222120263671280030665 13451416590197753460022999)
      ·
        refine ⟨20177124885296630190034499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13451416590197753460022999 20177124885296630190034499)
        ·
          refine ⟨30265687327944945285051749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20177124885296630190034499 30265687327944945285051749)
          ·
            refine ⟨5674816373989677240947203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30265687327944945285051749 5674816373989677240947203)
            ·
              refine ⟨8512224560984515861420805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674816373989677240947203 8512224560984515861420805)
              ·
                refine ⟨1596042105184596724016401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8512224560984515861420805 1596042105184596724016401)
                ·
                  refine ⟨1197031578888447543012301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1596042105184596724016401 1197031578888447543012301)
                  ·
                    refine ⟨448886842083167828629613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197031578888447543012301 448886842083167828629613)
                    ·
                      rfl

theorem cell22_1311306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_1311306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311306 prefixEnd_1311306 := by exact prefixLift 1311306
  have htrace : WordTrace (prefixWord ++ tailWord_1311306) baseStart_1311306 baseEnd_1311306 := by
    simpa [prefixWord, tailWord_1311306, baseEnd_1311306] using wordTrace_append hprefix tailTrace_1311306
  have hstable : (prefixWord ++ tailWord_1311306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311306).length < 2 ^ (prefixWord ++ tailWord_1311306).sum := by decide
  have hdescent : baseEnd_1311306 < baseStart_1311306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311411 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 1, 4]
def baseStart_1311411 : Nat := 118140960795 + 1311411 * 2 ^ 59
def prefixEnd_1311411 : Nat := 4983230072969 + 3 ^ 40 * 1311411 * 2
def baseEnd_1311411 : Nat := 448922785728982554754291

theorem tailTrace_1311411 : CollatzResearch.WordTrace tailWord_1311411 prefixEnd_1311411 448922785728982554754291 := by
  unfold tailWord_1311411
  simp only [CollatzResearch.WordTrace]
  refine ⟨47831088651989393012654087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31887392434659595341769391 47831088651989393012654087)
  ·
    refine ⟨71746632977984089518981131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47831088651989393012654087 71746632977984089518981131)
    ·
      refine ⟨107619949466976134278471697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71746632977984089518981131 107619949466976134278471697)
      ·
        refine ⟨80714962100232100708853773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107619949466976134278471697 80714962100232100708853773)
        ·
          refine ⟨30268110787587037765820165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80714962100232100708853773 30268110787587037765820165)
          ·
            refine ⟨5675270772672569581091281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30268110787587037765820165 5675270772672569581091281)
            ·
              refine ⟨4256453079504427185818461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675270772672569581091281 4256453079504427185818461)
              ·
                refine ⟨1596169904814160194681923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4256453079504427185818461 1596169904814160194681923)
                ·
                  refine ⟨2394254857221240292022885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596169904814160194681923 2394254857221240292022885)
                  ·
                    refine ⟨448922785728982554754291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2394254857221240292022885 448922785728982554754291)
                    ·
                      rfl

theorem cell22_1311411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 4].length) (baseStart_1311411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311411 prefixEnd_1311411 := by exact prefixLift 1311411
  have htrace : WordTrace (prefixWord ++ tailWord_1311411) baseStart_1311411 baseEnd_1311411 := by
    simpa [prefixWord, tailWord_1311411, baseEnd_1311411] using wordTrace_append hprefix tailTrace_1311411
  have hstable : (prefixWord ++ tailWord_1311411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311411).length < 2 ^ (prefixWord ++ tailWord_1311411).sum := by decide
  have hdescent : baseEnd_1311411 < baseStart_1311411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311499 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 9]
def baseStart_1311499 : Nat := 118140960795 + 1311499 * 2 ^ 59
def prefixEnd_1311499 : Nat := 4983230072969 + 3 ^ 40 * 1311499 * 2
def baseEnd_1311499 : Nat := 149650969975793219518007

theorem tailTrace_1311499 : CollatzResearch.WordTrace tailWord_1311499 prefixEnd_1311499 149650969975793219518007 := by
  unfold tailWord_1311499
  simp only [CollatzResearch.WordTrace]
  refine ⟨47834298275670584041857551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31889532183780389361238367 47834298275670584041857551)
  ·
    refine ⟨71751447413505876062786327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47834298275670584041857551 71751447413505876062786327)
    ·
      refine ⟨107627171120258814094179491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71751447413505876062786327 107627171120258814094179491)
      ·
        refine ⟨161440756680388221141269237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107627171120258814094179491 161440756680388221141269237)
        ·
          refine ⟨15135070938786395731993991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161440756680388221141269237 15135070938786395731993991)
          ·
            refine ⟨22702606408179593597990987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15135070938786395731993991 22702606408179593597990987)
            ·
              refine ⟨34053909612269390396986481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22702606408179593597990987 34053909612269390396986481)
              ·
                refine ⟨25540432209202042797739861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34053909612269390396986481 25540432209202042797739861)
                ·
                  refine ⟨149650969975793219518007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25540432209202042797739861 149650969975793219518007)
                  ·
                    rfl

theorem cell22_1311499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 9].length) (baseStart_1311499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311499 prefixEnd_1311499 := by exact prefixLift 1311499
  have htrace : WordTrace (prefixWord ++ tailWord_1311499) baseStart_1311499 baseEnd_1311499 := by
    simpa [prefixWord, tailWord_1311499, baseEnd_1311499] using wordTrace_append hprefix tailTrace_1311499
  have hstable : (prefixWord ++ tailWord_1311499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311499).length < 2 ^ (prefixWord ++ tailWord_1311499).sum := by decide
  have hdescent : baseEnd_1311499 < baseStart_1311499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311520 : List Nat := [2, 1, 1, 5, 1, 2, 1, 5, 1, 3]
def baseStart_1311520 : Nat := 118140960795 + 1311520 * 2 ^ 59
def prefixEnd_1311520 : Nat := 4983230072969 + 3 ^ 40 * 1311520 * 2
def baseEnd_1311520 : Nat := 448960098656542603778957

theorem tailTrace_1311520 : CollatzResearch.WordTrace tailWord_1311520 prefixEnd_1311520 448960098656542603778957 := by
  unfold tailWord_1311520
  simp only [CollatzResearch.WordTrace]
  refine ⟨23917532104297252314186007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31890042805729669752248009 23917532104297252314186007)
  ·
    refine ⟨35876298156445878471279011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23917532104297252314186007 35876298156445878471279011)
    ·
      refine ⟨53814447234668817706918517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35876298156445878471279011 53814447234668817706918517)
      ·
        refine ⟨5045104428250201660023611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53814447234668817706918517 5045104428250201660023611)
        ·
          refine ⟨7567656642375302490035417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5045104428250201660023611 7567656642375302490035417)
          ·
            refine ⟨5675742481781476867526563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7567656642375302490035417 5675742481781476867526563)
            ·
              refine ⟨8513613722672215301289845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5675742481781476867526563 8513613722672215301289845)
              ·
                refine ⟨798151286500520184495923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8513613722672215301289845 798151286500520184495923)
                ·
                  refine ⟨1197226929750780276743885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798151286500520184495923 1197226929750780276743885)
                  ·
                    refine ⟨448960098656542603778957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197226929750780276743885 448960098656542603778957)
                    ·
                      rfl

theorem cell22_1311520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 3].length) (baseStart_1311520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311520 prefixEnd_1311520 := by exact prefixLift 1311520
  have htrace : WordTrace (prefixWord ++ tailWord_1311520) baseStart_1311520 baseEnd_1311520 := by
    simpa [prefixWord, tailWord_1311520, baseEnd_1311520] using wordTrace_append hprefix tailTrace_1311520
  have hstable : (prefixWord ++ tailWord_1311520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311520).length < 2 ^ (prefixWord ++ tailWord_1311520).sum := by decide
  have hdescent : baseEnd_1311520 < baseStart_1311520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311561 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 6]
def baseStart_1311561 : Nat := 118140960795 + 1311561 * 2 ^ 59
def prefixEnd_1311561 : Nat := 4983230072969 + 3 ^ 40 * 1311561 * 2
def baseEnd_1311561 : Nat := 149658044598144054501277

theorem tailTrace_1311561 : CollatzResearch.WordTrace tailWord_1311561 prefixEnd_1311561 149658044598144054501277 := by
  unfold tailWord_1311561
  simp only [CollatzResearch.WordTrace]
  refine ⟨47836559601445968630614537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31891039734297312420409691 47836559601445968630614537)
  ·
    refine ⟨35877419701084476472960903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47836559601445968630614537 35877419701084476472960903)
    ·
      refine ⟨53816129551626714709441355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35877419701084476472960903 53816129551626714709441355)
      ·
        refine ⟨80724194327440072064162033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53816129551626714709441355 80724194327440072064162033)
        ·
          refine ⟨60543145745580054048121525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80724194327440072064162033 60543145745580054048121525)
          ·
            refine ⟨5675919913648130067011393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60543145745580054048121525 5675919913648130067011393)
            ·
              refine ⟨4256939935236097550258545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5675919913648130067011393 4256939935236097550258545)
              ·
                refine ⟨3192704951427073162693909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4256939935236097550258545 3192704951427073162693909)
                ·
                  refine ⟨149658044598144054501277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3192704951427073162693909 149658044598144054501277)
                  ·
                    rfl

theorem cell22_1311561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_1311561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311561 prefixEnd_1311561 := by exact prefixLift 1311561
  have htrace : WordTrace (prefixWord ++ tailWord_1311561) baseStart_1311561 baseEnd_1311561 := by
    simpa [prefixWord, tailWord_1311561, baseEnd_1311561] using wordTrace_append hprefix tailTrace_1311561
  have hstable : (prefixWord ++ tailWord_1311561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311561).length < 2 ^ (prefixWord ++ tailWord_1311561).sum := by decide
  have hdescent : baseEnd_1311561 < baseStart_1311561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311576 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_1311576 : Nat := 118140960795 + 1311576 * 2 ^ 59
def prefixEnd_1311576 : Nat := 4983230072969 + 3 ^ 40 * 1311576 * 2
def baseEnd_1311576 : Nat := 448979268600977124378785

theorem tailTrace_1311576 : CollatzResearch.WordTrace tailWord_1311576 prefixEnd_1311576 448979268600977124378785 := by
  unfold tailWord_1311576
  simp only [CollatzResearch.WordTrace]
  refine ⟨23918553348195813096205291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31891404464261084128273721 23918553348195813096205291)
  ·
    refine ⟨35877830022293719644307937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23918553348195813096205291 35877830022293719644307937)
    ·
      refine ⟨26908372516720289733230953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35877830022293719644307937 26908372516720289733230953)
      ·
        refine ⟨20181279387540217299923215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26908372516720289733230953 20181279387540217299923215)
        ·
          refine ⟨30271919081310325949884823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20181279387540217299923215 30271919081310325949884823)
          ·
            refine ⟨45407878621965488924827235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30271919081310325949884823 45407878621965488924827235)
            ·
              refine ⟨68111817932948233387240853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45407878621965488924827235 68111817932948233387240853)
              ·
                refine ⟨3192741465606948440026915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68111817932948233387240853 3192741465606948440026915)
                ·
                  refine ⟨4789112198410422660040373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3192741465606948440026915 4789112198410422660040373)
                  ·
                    refine ⟨448979268600977124378785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4789112198410422660040373 448979268600977124378785)
                    ·
                      rfl

theorem cell22_1311576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_1311576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311576 prefixEnd_1311576 := by exact prefixLift 1311576
  have htrace : WordTrace (prefixWord ++ tailWord_1311576) baseStart_1311576 baseEnd_1311576 := by
    simpa [prefixWord, tailWord_1311576, baseEnd_1311576] using wordTrace_append hprefix tailTrace_1311576
  have hstable : (prefixWord ++ tailWord_1311576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311576).length < 2 ^ (prefixWord ++ tailWord_1311576).sum := by decide
  have hdescent : baseEnd_1311576 < baseStart_1311576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311580 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1311580 : Nat := 118140960795 + 1311580 * 2 ^ 59
def prefixEnd_1311580 : Nat := 4983230072969 + 3 ^ 40 * 1311580 * 2
def baseEnd_1311580 : Nat := 448980637882722447278773

theorem tailTrace_1311580 : CollatzResearch.WordTrace tailWord_1311580 prefixEnd_1311580 448980637882722447278773 := by
  unfold tailWord_1311580
  simp only [CollatzResearch.WordTrace]
  refine ⟨23918626294188567437778097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31891501725584756583704129 23918626294188567437778097)
  ·
    refine ⟨17938969720641425578333573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23918626294188567437778097 17938969720641425578333573)
    ·
      refine ⟨3363556822620267295937545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17938969720641425578333573 3363556822620267295937545)
      ·
        refine ⟨2522667616965200471953159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3363556822620267295937545 2522667616965200471953159)
        ·
          refine ⟨3784001425447800707929739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2522667616965200471953159 3784001425447800707929739)
          ·
            refine ⟨5676002138171701061894609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784001425447800707929739 5676002138171701061894609)
            ·
              refine ⟨4257001603628775796420957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5676002138171701061894609 4257001603628775796420957)
              ·
                refine ⟨1596375601360790923657859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4257001603628775796420957 1596375601360790923657859)
                ·
                  refine ⟨2394563402041186385486789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596375601360790923657859 2394563402041186385486789)
                  ·
                    refine ⟨448980637882722447278773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2394563402041186385486789 448980637882722447278773)
                    ·
                      rfl

theorem cell22_1311580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1311580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311580 prefixEnd_1311580 := by exact prefixLift 1311580
  have htrace : WordTrace (prefixWord ++ tailWord_1311580) baseStart_1311580 baseEnd_1311580 := by
    simpa [prefixWord, tailWord_1311580, baseEnd_1311580] using wordTrace_append hprefix tailTrace_1311580
  have hstable : (prefixWord ++ tailWord_1311580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311580).length < 2 ^ (prefixWord ++ tailWord_1311580).sum := by decide
  have hdescent : baseEnd_1311580 < baseStart_1311580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311614 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1311614 : Nat := 118140960795 + 1311614 * 2 ^ 59
def prefixEnd_1311614 : Nat := 4983230072969 + 3 ^ 40 * 1311614 * 2
def baseEnd_1311614 : Nat := 448992276777557691928669

theorem tailTrace_1311614 : CollatzResearch.WordTrace tailWord_1311614 prefixEnd_1311614 448992276777557691928669 := by
  unfold tailWord_1311614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5979811583781744835286737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31892328446835972454862597 5979811583781744835286737)
  ·
    refine ⟨4484858687836308626465053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5979811583781744835286737 4484858687836308626465053)
    ·
      refine ⟨1681822007938615734924395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4484858687836308626465053 1681822007938615734924395)
      ·
        refine ⟨2522733011907923602386593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1681822007938615734924395 2522733011907923602386593)
        ·
          refine ⟨1892049758930942701789945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2522733011907923602386593 1892049758930942701789945)
          ·
            refine ⟨1419037319198207026342459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1892049758930942701789945 1419037319198207026342459)
            ·
              refine ⟨2128555978797310539513689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419037319198207026342459 2128555978797310539513689)
              ·
                refine ⟨1596416984097982904635267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2128555978797310539513689 1596416984097982904635267)
                ·
                  refine ⟨2394625476146974356952901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596416984097982904635267 2394625476146974356952901)
                  ·
                    refine ⟨448992276777557691928669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2394625476146974356952901 448992276777557691928669)
                    ·
                      rfl

theorem cell22_1311614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1311614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311614 prefixEnd_1311614 := by exact prefixLift 1311614
  have htrace : WordTrace (prefixWord ++ tailWord_1311614) baseStart_1311614 baseEnd_1311614 := by
    simpa [prefixWord, tailWord_1311614, baseEnd_1311614] using wordTrace_append hprefix tailTrace_1311614
  have hstable : (prefixWord ++ tailWord_1311614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311614).length < 2 ^ (prefixWord ++ tailWord_1311614).sum := by decide
  have hdescent : baseEnd_1311614 < baseStart_1311614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311651 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 7]
def baseStart_1311651 : Nat := 118140960795 + 1311651 * 2 ^ 59
def prefixEnd_1311651 : Nat := 4983230072969 + 3 ^ 40 * 1311651 * 2
def baseEnd_1311651 : Nat := 149668314211233976251185

theorem tailTrace_1311651 : CollatzResearch.WordTrace tailWord_1311651 prefixEnd_1311651 149668314211233976251185 := by
  unfold tailWord_1311651
  simp only [CollatzResearch.WordTrace]
  refine ⟨47839842171119914001390807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31893228114079942667593871 47839842171119914001390807)
  ·
    refine ⟨71759763256679871002086211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47839842171119914001390807 71759763256679871002086211)
    ·
      refine ⟨107639644885019806503129317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71759763256679871002086211 107639644885019806503129317)
      ·
        refine ⟨20182433415941213719336747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107639644885019806503129317 20182433415941213719336747)
        ·
          refine ⟨30273650123911820579005121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20182433415941213719336747 30273650123911820579005121)
          ·
            refine ⟨22705237592933865434253841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30273650123911820579005121 22705237592933865434253841)
            ·
              refine ⟨17028928194700399075690381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22705237592933865434253841 17028928194700399075690381)
              ·
                refine ⟨6385848073012649653383893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17028928194700399075690381 6385848073012649653383893)
                ·
                  refine ⟨149668314211233976251185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6385848073012649653383893 149668314211233976251185)
                  ·
                    rfl

theorem cell22_1311651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 7].length) (baseStart_1311651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311651 prefixEnd_1311651 := by exact prefixLift 1311651
  have htrace : WordTrace (prefixWord ++ tailWord_1311651) baseStart_1311651 baseEnd_1311651 := by
    simpa [prefixWord, tailWord_1311651, baseEnd_1311651] using wordTrace_append hprefix tailTrace_1311651
  have hstable : (prefixWord ++ tailWord_1311651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311651).length < 2 ^ (prefixWord ++ tailWord_1311651).sum := by decide
  have hdescent : baseEnd_1311651 < baseStart_1311651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311696 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 10]
def baseStart_1311696 : Nat := 118140960795 + 1311696 * 2 ^ 59
def prefixEnd_1311696 : Nat := 4983230072969 + 3 ^ 40 * 1311696 * 2
def baseEnd_1311696 : Nat := 149673449017778937126139

theorem tailTrace_1311696 : CollatzResearch.WordTrace tailWord_1311696 prefixEnd_1311696 149673449017778937126139 := by
  unfold tailWord_1311696
  simp only [CollatzResearch.WordTrace]
  refine ⟨23920741727978443343389471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31894322303971257791185961 23920741727978443343389471)
  ·
    refine ⟨35881112591967665015084207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23920741727978443343389471 35881112591967665015084207)
    ·
      refine ⟨53821668887951497522626311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35881112591967665015084207 53821668887951497522626311)
      ·
        refine ⟨80732503331927246283939467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53821668887951497522626311 80732503331927246283939467)
        ·
          refine ⟨121098754997890869425909201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80732503331927246283939467 121098754997890869425909201)
          ·
            refine ⟨90824066248418152069431901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121098754997890869425909201 90824066248418152069431901)
            ·
              refine ⟨34059024843156807026036963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90824066248418152069431901 34059024843156807026036963)
              ·
                refine ⟨51088537264735210539055445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34059024843156807026036963 51088537264735210539055445)
                ·
                  refine ⟨149673449017778937126139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 51088537264735210539055445 149673449017778937126139)
                  ·
                    rfl

theorem cell22_1311696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_1311696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311696 prefixEnd_1311696 := by exact prefixLift 1311696
  have htrace : WordTrace (prefixWord ++ tailWord_1311696) baseStart_1311696 baseEnd_1311696 := by
    simpa [prefixWord, tailWord_1311696, baseEnd_1311696] using wordTrace_append hprefix tailTrace_1311696
  have hstable : (prefixWord ++ tailWord_1311696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311696).length < 2 ^ (prefixWord ++ tailWord_1311696).sum := by decide
  have hdescent : baseEnd_1311696 < baseStart_1311696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311702 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1311702 : Nat := 118140960795 + 1311702 * 2 ^ 59
def prefixEnd_1311702 : Nat := 4983230072969 + 3 ^ 40 * 1311702 * 2
def baseEnd_1311702 : Nat := 149674133658651598576133

theorem tailTrace_1311702 : CollatzResearch.WordTrace tailWord_1311702 prefixEnd_1311702 149674133658651598576133 := by
  unfold tailWord_1311702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2990106393370946856968585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31894468195956766474331573 2990106393370946856968585)
  ·
    refine ⟨2242579795028210142726439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2990106393370946856968585 2242579795028210142726439)
    ·
      refine ⟨3363869692542315214089659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2242579795028210142726439 3363869692542315214089659)
      ·
        refine ⟨5045804538813472821134489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363869692542315214089659 5045804538813472821134489)
        ·
          refine ⟨3784353404110104615850867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5045804538813472821134489 3784353404110104615850867)
          ·
            refine ⟨5676530106165156923776301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784353404110104615850867 5676530106165156923776301)
            ·
              refine ⟨2128698789811933846416113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5676530106165156923776301 2128698789811933846416113)
              ·
                refine ⟨1596524092358950384812085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2128698789811933846416113 1596524092358950384812085)
                ·
                  refine ⟨149674133658651598576133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1596524092358950384812085 149674133658651598576133)
                  ·
                    rfl

theorem cell22_1311702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1311702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311702 prefixEnd_1311702 := by exact prefixLift 1311702
  have htrace : WordTrace (prefixWord ++ tailWord_1311702) baseStart_1311702 baseEnd_1311702 := by
    simpa [prefixWord, tailWord_1311702, baseEnd_1311702] using wordTrace_append hprefix tailTrace_1311702
  have hstable : (prefixWord ++ tailWord_1311702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311702).length < 2 ^ (prefixWord ++ tailWord_1311702).sum := by decide
  have hdescent : baseEnd_1311702 < baseStart_1311702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311745 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1311745 : Nat := 118140960795 + 1311745 * 2 ^ 59
def prefixEnd_1311745 : Nat := 4983230072969 + 3 ^ 40 * 1311745 * 2
def baseEnd_1311745 : Nat := 449037120754717016903267

theorem tailTrace_1311745 : CollatzResearch.WordTrace tailWord_1311745 prefixEnd_1311745 449037120754717016903267 := by
  unfold tailWord_1311745
  simp only [CollatzResearch.WordTrace]
  refine ⟨47843270632779368055312689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31895513755186245370208459 47843270632779368055312689)
  ·
    refine ⟨35882452974584526041484517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47843270632779368055312689 35882452974584526041484517)
    ·
      refine ⟨6727959932734598632778347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35882452974584526041484517 6727959932734598632778347)
      ·
        refine ⟨10091939899101897949167521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6727959932734598632778347 10091939899101897949167521)
        ·
          refine ⟨7568954924326423461875641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10091939899101897949167521 7568954924326423461875641)
          ·
            refine ⟨5676716193244817596406731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7568954924326423461875641 5676716193244817596406731)
            ·
              refine ⟨8515074289867226394610097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5676716193244817596406731 8515074289867226394610097)
              ·
                refine ⟨6386305717400419795957573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8515074289867226394610097 6386305717400419795957573)
                ·
                  refine ⟨1197432322012578711742045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6386305717400419795957573 1197432322012578711742045)
                  ·
                    refine ⟨449037120754717016903267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197432322012578711742045 449037120754717016903267)
                    ·
                      rfl

theorem cell22_1311745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1311745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311745 prefixEnd_1311745 := by exact prefixLift 1311745
  have htrace : WordTrace (prefixWord ++ tailWord_1311745) baseStart_1311745 baseEnd_1311745 := by
    simpa [prefixWord, tailWord_1311745, baseEnd_1311745] using wordTrace_append hprefix tailTrace_1311745
  have hstable : (prefixWord ++ tailWord_1311745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311745).length < 2 ^ (prefixWord ++ tailWord_1311745).sum := by decide
  have hdescent : baseEnd_1311745 < baseStart_1311745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311758 : List Nat := [4, 1, 1, 2, 2, 2, 10]
def baseStart_1311758 : Nat := 118140960795 + 1311758 * 2 ^ 59
def prefixEnd_1311758 : Nat := 4983230072969 + 3 ^ 40 * 1311758 * 2
def baseEnd_1311758 : Nat := 16631169293347752456601

theorem tailTrace_1311758 : CollatzResearch.WordTrace tailWord_1311758 prefixEnd_1311758 16631169293347752456601 := by
  unfold tailWord_1311758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5980468097716533909441991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31895829854488180850357285 5980468097716533909441991)
  ·
    refine ⟨8970702146574800864162987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5980468097716533909441991 8970702146574800864162987)
    ·
      refine ⟨13456053219862201296244481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8970702146574800864162987 13456053219862201296244481)
      ·
        refine ⟨10092039914896650972183361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13456053219862201296244481 10092039914896650972183361)
        ·
          refine ⟨7569029936172488229137521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10092039914896650972183361 7569029936172488229137521)
          ·
            refine ⟨5676772452129366171853141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7569029936172488229137521 5676772452129366171853141)
            ·
              refine ⟨16631169293347752456601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5676772452129366171853141 16631169293347752456601)
              ·
                rfl

theorem cell22_1311758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 10].length) (baseStart_1311758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311758 prefixEnd_1311758 := by exact prefixLift 1311758
  have htrace : WordTrace (prefixWord ++ tailWord_1311758) baseStart_1311758 baseEnd_1311758 := by
    simpa [prefixWord, tailWord_1311758, baseEnd_1311758] using wordTrace_append hprefix tailTrace_1311758
  have hstable : (prefixWord ++ tailWord_1311758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311758).length < 2 ^ (prefixWord ++ tailWord_1311758).sum := by decide
  have hdescent : baseEnd_1311758 < baseStart_1311758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311779 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 2, 3]
def baseStart_1311779 : Nat := 118140960795 + 1311779 * 2 ^ 59
def prefixEnd_1311779 : Nat := 4983230072969 + 3 ^ 40 * 1311779 * 2
def baseEnd_1311779 : Nat := 449048759649552261553163

theorem tailTrace_1311779 : CollatzResearch.WordTrace tailWord_1311779 prefixEnd_1311779 449048759649552261553163 := by
  unfold tailWord_1311779
  simp only [CollatzResearch.WordTrace]
  refine ⟨47844510714656191862050391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31896340476437461241366927 47844510714656191862050391)
  ·
    refine ⟨71766766071984287793075587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47844510714656191862050391 71766766071984287793075587)
    ·
      refine ⟨107650149107976431689613381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71766766071984287793075587 107650149107976431689613381)
      ·
        refine ⟨20184402957745580941802509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107650149107976431689613381 20184402957745580941802509)
        ·
          refine ⟨7569151109154592853175941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20184402957745580941802509 7569151109154592853175941)
          ·
            refine ⟨1419215832966486159970489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7569151109154592853175941 1419215832966486159970489)
            ·
              refine ⟨1064411874724864619977867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419215832966486159970489 1064411874724864619977867)
              ·
                refine ⟨1596617812087296929966801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064411874724864619977867 1596617812087296929966801)
                ·
                  refine ⟨1197463359065472697475101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1596617812087296929966801 1197463359065472697475101)
                  ·
                    refine ⟨449048759649552261553163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197463359065472697475101 449048759649552261553163)
                    ·
                      rfl

theorem cell22_1311779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 3].length) (baseStart_1311779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311779 prefixEnd_1311779 := by exact prefixLift 1311779
  have htrace : WordTrace (prefixWord ++ tailWord_1311779) baseStart_1311779 baseEnd_1311779 := by
    simpa [prefixWord, tailWord_1311779, baseEnd_1311779] using wordTrace_append hprefix tailTrace_1311779
  have hstable : (prefixWord ++ tailWord_1311779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311779).length < 2 ^ (prefixWord ++ tailWord_1311779).sum := by decide
  have hdescent : baseEnd_1311779 < baseStart_1311779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311807 : List Nat := [1, 1, 2, 2, 3, 1, 1, 7, 1, 3]
def baseStart_1311807 : Nat := 118140960795 + 1311807 * 2 ^ 59
def prefixEnd_1311807 : Nat := 4983230072969 + 3 ^ 40 * 1311807 * 2
def baseEnd_1311807 : Nat := 449058344621769521853077

theorem tailTrace_1311807 : CollatzResearch.WordTrace tailWord_1311807 prefixEnd_1311807 449058344621769521853077 := by
  unfold tailWord_1311807
  simp only [CollatzResearch.WordTrace]
  refine ⟨47845531958554752644069675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31897021305703168429379783 47845531958554752644069675)
  ·
    refine ⟨71768297937832128966104513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47845531958554752644069675 71768297937832128966104513)
    ·
      refine ⟨53826223453374096724578385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71768297937832128966104513 53826223453374096724578385)
      ·
        refine ⟨40369667590030572543433789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53826223453374096724578385 40369667590030572543433789)
        ·
          refine ⟨15138625346261464703787671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40369667590030572543433789 15138625346261464703787671)
          ·
            refine ⟨22707938019392197055681507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15138625346261464703787671 22707938019392197055681507)
            ·
              refine ⟨34061907029088295583522261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22707938019392197055681507 34061907029088295583522261)
              ·
                refine ⟨798325945994256927738803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34061907029088295583522261 798325945994256927738803)
                ·
                  refine ⟨1197488918991385391608205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 798325945994256927738803 1197488918991385391608205)
                  ·
                    refine ⟨449058344621769521853077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197488918991385391608205 449058344621769521853077)
                    ·
                      rfl

theorem cell22_1311807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 3].length) (baseStart_1311807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311807 prefixEnd_1311807 := by exact prefixLift 1311807
  have htrace : WordTrace (prefixWord ++ tailWord_1311807) baseStart_1311807 baseEnd_1311807 := by
    simpa [prefixWord, tailWord_1311807, baseEnd_1311807] using wordTrace_append hprefix tailTrace_1311807
  have hstable : (prefixWord ++ tailWord_1311807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311807).length < 2 ^ (prefixWord ++ tailWord_1311807).sum := by decide
  have hdescent : baseEnd_1311807 < baseStart_1311807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311882 : List Nat := [3, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_1311882 : Nat := 118140960795 + 1311882 * 2 ^ 59
def prefixEnd_1311882 : Nat := 4983230072969 + 3 ^ 40 * 1311882 * 2
def baseEnd_1311882 : Nat := 149694672884831442075949

theorem tailTrace_1311882 : CollatzResearch.WordTrace tailWord_1311882 prefixEnd_1311882 149694672884831442075949 := by
  unfold tailWord_1311882
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962066858320760113262475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31898844955522026968699933 11962066858320760113262475)
  ·
    refine ⟨17943100287481140169893713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11962066858320760113262475 17943100287481140169893713)
    ·
      refine ⟨13457325215610855127420285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17943100287481140169893713 13457325215610855127420285)
      ·
        refine ⟨5046496955854070672782607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13457325215610855127420285 5046496955854070672782607)
        ·
          refine ⟨7569745433781106009173911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5046496955854070672782607 7569745433781106009173911)
          ·
            refine ⟨11354618150671659013760867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7569745433781106009173911 11354618150671659013760867)
            ·
              refine ⟨17031927226007488520641301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11354618150671659013760867 17031927226007488520641301)
              ·
                refine ⟨798371588719101024405061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17031927226007488520641301 798371588719101024405061)
                ·
                  refine ⟨149694672884831442075949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798371588719101024405061 149694672884831442075949)
                  ·
                    rfl

theorem cell22_1311882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_1311882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311882 prefixEnd_1311882 := by exact prefixLift 1311882
  have htrace : WordTrace (prefixWord ++ tailWord_1311882) baseStart_1311882 baseEnd_1311882 := by
    simpa [prefixWord, tailWord_1311882, baseEnd_1311882] using wordTrace_append hprefix tailTrace_1311882
  have hstable : (prefixWord ++ tailWord_1311882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311882).length < 2 ^ (prefixWord ++ tailWord_1311882).sum := by decide
  have hdescent : baseEnd_1311882 < baseStart_1311882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311895 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 1, 6]
def baseStart_1311895 : Nat := 118140960795 + 1311895 * 2 ^ 59
def prefixEnd_1311895 : Nat := 4983230072969 + 3 ^ 40 * 1311895 * 2
def baseEnd_1311895 : Nat := 449088468820166625652807

theorem tailTrace_1311895 : CollatzResearch.WordTrace tailWord_1311895 prefixEnd_1311895 449088468820166625652807 := by
  unfold tailWord_1311895
  simp only [CollatzResearch.WordTrace]
  refine ⟨47848741582235943673273139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31899161054823962448848759 47848741582235943673273139)
  ·
    refine ⟨71773112373353915509909709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47848741582235943673273139 71773112373353915509909709)
    ·
      refine ⟨26914917140007718316216141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71773112373353915509909709 26914917140007718316216141)
      ·
        refine ⟨10093093927502894368581053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26914917140007718316216141 10093093927502894368581053)
        ·
          refine ⟨3784910222813585388217895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10093093927502894368581053 3784910222813585388217895)
          ·
            refine ⟨5677365334220378082326843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784910222813585388217895 5677365334220378082326843)
            ·
              refine ⟨8516048001330567123490265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677365334220378082326843 8516048001330567123490265)
              ·
                refine ⟨6387036000997925342617699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516048001330567123490265 6387036000997925342617699)
                ·
                  refine ⟨9580554001496888013926549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6387036000997925342617699 9580554001496888013926549)
                  ·
                    refine ⟨449088468820166625652807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9580554001496888013926549 449088468820166625652807)
                    ·
                      rfl

theorem cell22_1311895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_1311895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311895 prefixEnd_1311895 := by exact prefixLift 1311895
  have htrace : WordTrace (prefixWord ++ tailWord_1311895) baseStart_1311895 baseEnd_1311895 := by
    simpa [prefixWord, tailWord_1311895, baseEnd_1311895] using wordTrace_append hprefix tailTrace_1311895
  have hstable : (prefixWord ++ tailWord_1311895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311895).length < 2 ^ (prefixWord ++ tailWord_1311895).sum := by decide
  have hdescent : baseEnd_1311895 < baseStart_1311895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311914 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1311914 : Nat := 118140960795 + 1311914 * 2 ^ 59
def prefixEnd_1311914 : Nat := 4983230072969 + 3 ^ 40 * 1311914 * 2
def baseEnd_1311914 : Nat := 449094972908456909427749

theorem tailTrace_1311914 : CollatzResearch.WordTrace tailWord_1311914 prefixEnd_1311914 449094972908456909427749 := by
  unfold tailWord_1311914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962358642291777479553699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31899623046111406612143197 11962358642291777479553699)
  ·
    refine ⟨17943537963437666219330549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11962358642291777479553699 17943537963437666219330549)
    ·
      refine ⟨1682206684072281208062239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17943537963437666219330549 1682206684072281208062239)
      ·
        refine ⟨2523310026108421812093359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682206684072281208062239 2523310026108421812093359)
        ·
          refine ⟨3784965039162632718140039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523310026108421812093359 3784965039162632718140039)
          ·
            refine ⟨5677447558743949077210059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784965039162632718140039 5677447558743949077210059)
            ·
              refine ⟨8516171338115923615815089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5677447558743949077210059 8516171338115923615815089)
              ·
                refine ⟨6387128503586942711861317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8516171338115923615815089 6387128503586942711861317)
                ·
                  refine ⟨1197586594422551758473997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6387128503586942711861317 1197586594422551758473997)
                  ·
                    refine ⟨449094972908456909427749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197586594422551758473997 449094972908456909427749)
                    ·
                      rfl

theorem cell22_1311914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1311914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311914 prefixEnd_1311914 := by exact prefixLift 1311914
  have htrace : WordTrace (prefixWord ++ tailWord_1311914) baseStart_1311914 baseEnd_1311914 := by
    simpa [prefixWord, tailWord_1311914, baseEnd_1311914] using wordTrace_append hprefix tailTrace_1311914
  have hstable : (prefixWord ++ tailWord_1311914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311914).length < 2 ^ (prefixWord ++ tailWord_1311914).sum := by decide
  have hdescent : baseEnd_1311914 < baseStart_1311914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1311955 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 5]
def baseStart_1311955 : Nat := 118140960795 + 1311955 * 2 ^ 59
def prefixEnd_1311955 : Nat := 4983230072969 + 3 ^ 40 * 1311955 * 2
def baseEnd_1311955 : Nat := 149703002682115489717541

theorem tailTrace_1311955 : CollatzResearch.WordTrace tailWord_1311955 prefixEnd_1311955 149703002682115489717541 := by
  unfold tailWord_1311955
  simp only [CollatzResearch.WordTrace]
  refine ⟨47850929962018573920457319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31900619974679049280304879 47850929962018573920457319)
  ·
    refine ⟨71776394943027860880685979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47850929962018573920457319 71776394943027860880685979)
    ·
      refine ⟨107664592414541791321028969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71776394943027860880685979 107664592414541791321028969)
      ·
        refine ⟨80748444310906343490771727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107664592414541791321028969 80748444310906343490771727)
        ·
          refine ⟨121122666466359515236157591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80748444310906343490771727 121122666466359515236157591)
          ·
            refine ⟨181683999699539272854236387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121122666466359515236157591 181683999699539272854236387)
            ·
              refine ⟨272525999549308909281354581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181683999699539272854236387 272525999549308909281354581)
              ·
                refine ⟨1596832028609231890320437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 272525999549308909281354581 1596832028609231890320437)
                ·
                  refine ⟨149703002682115489717541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1596832028609231890320437 149703002682115489717541)
                  ·
                    rfl

theorem cell22_1311955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5].length) (baseStart_1311955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1311955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1311955 prefixEnd_1311955 := by exact prefixLift 1311955
  have htrace : WordTrace (prefixWord ++ tailWord_1311955) baseStart_1311955 baseEnd_1311955 := by
    simpa [prefixWord, tailWord_1311955, baseEnd_1311955] using wordTrace_append hprefix tailTrace_1311955
  have hstable : (prefixWord ++ tailWord_1311955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1311955).length < 2 ^ (prefixWord ++ tailWord_1311955).sum := by decide
  have hdescent : baseEnd_1311955 < baseStart_1311955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1311955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312000 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 6]
def baseStart_1312000 : Nat := 118140960795 + 1312000 * 2 ^ 59
def prefixEnd_1312000 : Nat := 4983230072969 + 3 ^ 40 * 1312000 * 2
def baseEnd_1312000 : Nat := 149708137488660450592495

theorem tailTrace_1312000 : CollatzResearch.WordTrace tailWord_1312000 prefixEnd_1312000 149708137488660450592495 := by
  unfold tailWord_1312000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23926285623427773302922727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31901714164570364403896969 23926285623427773302922727)
  ·
    refine ⟨35889428435141659954384091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23926285623427773302922727 35889428435141659954384091)
    ·
      refine ⟨53834142652712489931576137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35889428435141659954384091 53834142652712489931576137)
      ·
        refine ⟨40375606989534367448682103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53834142652712489931576137 40375606989534367448682103)
        ·
          refine ⟨60563410484301551173023155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40375606989534367448682103 60563410484301551173023155)
          ·
            refine ⟨90845115726452326759534733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60563410484301551173023155 90845115726452326759534733)
            ·
              refine ⟨34066918397419622534825525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90845115726452326759534733 34066918397419622534825525)
              ·
                refine ⟨3193773599758089612639893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34066918397419622534825525 3193773599758089612639893)
                ·
                  refine ⟨149708137488660450592495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3193773599758089612639893 149708137488660450592495)
                  ·
                    rfl

theorem cell22_1312000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_1312000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312000 prefixEnd_1312000 := by exact prefixLift 1312000
  have htrace : WordTrace (prefixWord ++ tailWord_1312000) baseStart_1312000 baseEnd_1312000 := by
    simpa [prefixWord, tailWord_1312000, baseEnd_1312000] using wordTrace_append hprefix tailTrace_1312000
  have hstable : (prefixWord ++ tailWord_1312000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312000).length < 2 ^ (prefixWord ++ tailWord_1312000).sum := by decide
  have hdescent : baseEnd_1312000 < baseStart_1312000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312049 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 4, 3]
def baseStart_1312049 : Nat := 118140960795 + 1312049 * 2 ^ 59
def prefixEnd_1312049 : Nat := 4983230072969 + 3 ^ 40 * 1312049 * 2
def baseEnd_1312049 : Nat := 449141186167361557302335

theorem tailTrace_1312049 : CollatzResearch.WordTrace tailWord_1312049 prefixEnd_1312049 449141186167361557302335 := by
  unfold tailWord_1312049
  simp only [CollatzResearch.WordTrace]
  refine ⟨47854358423678027974379201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31902905615785351982919467 47854358423678027974379201)
  ·
    refine ⟨35890768817758520980784401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47854358423678027974379201 35890768817758520980784401)
    ·
      refine ⟨26918076613318890735588301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35890768817758520980784401 26918076613318890735588301)
      ·
        refine ⟨10094278729994584025845613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26918076613318890735588301 10094278729994584025845613)
        ·
          refine ⟨3785354523747969009692105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10094278729994584025845613 3785354523747969009692105)
          ·
            refine ⟨2839015892810976757269079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3785354523747969009692105 2839015892810976757269079)
            ·
              refine ⟨4258523839216465135903619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839015892810976757269079 4258523839216465135903619)
              ·
                refine ⟨6387785758824697703855429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4258523839216465135903619 6387785758824697703855429)
                ·
                  refine ⟨1197709829779630819472893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6387785758824697703855429 1197709829779630819472893)
                  ·
                    refine ⟨449141186167361557302335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197709829779630819472893 449141186167361557302335)
                    ·
                      rfl

theorem cell22_1312049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_1312049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312049 prefixEnd_1312049 := by exact prefixLift 1312049
  have htrace : WordTrace (prefixWord ++ tailWord_1312049) baseStart_1312049 baseEnd_1312049 := by
    simpa [prefixWord, tailWord_1312049, baseEnd_1312049] using wordTrace_append hprefix tailTrace_1312049
  have hstable : (prefixWord ++ tailWord_1312049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312049).length < 2 ^ (prefixWord ++ tailWord_1312049).sum := by decide
  have hdescent : baseEnd_1312049 < baseStart_1312049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312062 : List Nat := [4, 2, 1, 2, 1, 1, 2, 9]
def baseStart_1312062 : Nat := 118140960795 + 1312062 * 2 ^ 59
def prefixEnd_1312062 : Nat := 4983230072969 + 3 ^ 40 * 1312062 * 2
def baseEnd_1312062 : Nat := 49905070703670428525255

theorem tailTrace_1312062 : CollatzResearch.WordTrace tailWord_1312062 prefixEnd_1312062 49905070703670428525255 := by
  unfold tailWord_1312062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5981854071578866399325305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31903221715087287463068293 5981854071578866399325305)
  ·
    refine ⟨4486390553684149799493979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5981854071578866399325305 4486390553684149799493979)
    ·
      refine ⟨6729585830526224699240969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4486390553684149799493979 6729585830526224699240969)
      ·
        refine ⟨5047189372894668524430727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6729585830526224699240969 5047189372894668524430727)
        ·
          refine ⟨7570784059342002786646091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5047189372894668524430727 7570784059342002786646091)
          ·
            refine ⟨11356176089013004179969137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7570784059342002786646091 11356176089013004179969137)
            ·
              refine ⟨8517132066759753134976853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11356176089013004179969137 8517132066759753134976853)
              ·
                refine ⟨49905070703670428525255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8517132066759753134976853 49905070703670428525255)
                ·
                  rfl

theorem cell22_1312062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_1312062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312062 prefixEnd_1312062 := by exact prefixLift 1312062
  have htrace : WordTrace (prefixWord ++ tailWord_1312062) baseStart_1312062 baseEnd_1312062 := by
    simpa [prefixWord, tailWord_1312062, baseEnd_1312062] using wordTrace_append hprefix tailTrace_1312062
  have hstable : (prefixWord ++ tailWord_1312062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312062).length < 2 ^ (prefixWord ++ tailWord_1312062).sum := by decide
  have hdescent : baseEnd_1312062 < baseStart_1312062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312070 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1312070 : Nat := 118140960795 + 1312070 * 2 ^ 59
def prefixEnd_1312070 : Nat := 4983230072969 + 3 ^ 40 * 1312070 * 2
def baseEnd_1312070 : Nat := 449148374896524502527271

theorem tailTrace_1312070 : CollatzResearch.WordTrace tailWord_1312070 prefixEnd_1312070 449148374896524502527271 := by
  unfold tailWord_1312070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495472636143810892527927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31903416237734632373929109 1495472636143810892527927)
  ·
    refine ⟨2243208954215716338791891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1495472636143810892527927 2243208954215716338791891)
    ·
      refine ⟨3364813431323574508187837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243208954215716338791891 3364813431323574508187837)
      ·
        refine ⟨1261805036746340440570439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3364813431323574508187837 1261805036746340440570439)
        ·
          refine ⟨1892707555119510660855659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261805036746340440570439 1892707555119510660855659)
          ·
            refine ⟨2839061332679265991283489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892707555119510660855659 2839061332679265991283489)
            ·
              refine ⟨2129295999509449493462617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839061332679265991283489 2129295999509449493462617)
              ·
                refine ⟨1596971999632087120096963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129295999509449493462617 1596971999632087120096963)
                ·
                  refine ⟨2395457999448130680145445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1596971999632087120096963 2395457999448130680145445)
                  ·
                    refine ⟨449148374896524502527271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2395457999448130680145445 449148374896524502527271)
                    ·
                      rfl

theorem cell22_1312070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1312070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312070 prefixEnd_1312070 := by exact prefixLift 1312070
  have htrace : WordTrace (prefixWord ++ tailWord_1312070) baseStart_1312070 baseEnd_1312070 := by
    simpa [prefixWord, tailWord_1312070, baseEnd_1312070] using wordTrace_append hprefix tailTrace_1312070
  have hstable : (prefixWord ++ tailWord_1312070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312070).length < 2 ^ (prefixWord ++ tailWord_1312070).sum := by decide
  have hdescent : baseEnd_1312070 < baseStart_1312070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312075 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 3, 8]
def baseStart_1312075 : Nat := 118140960795 + 1312075 * 2 ^ 59
def prefixEnd_1312075 : Nat := 4983230072969 + 3 ^ 40 * 1312075 * 2
def baseEnd_1312075 : Nat := 449150086498706156152255

theorem tailTrace_1312075 : CollatzResearch.WordTrace tailWord_1312075 prefixEnd_1312075 449150086498706156152255 := by
  unfold tailWord_1312075
  simp only [CollatzResearch.WordTrace]
  refine ⟨47855306721583834414825679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31903537814389222943217119 47855306721583834414825679)
  ·
    refine ⟨71782960082375751622238519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47855306721583834414825679 71782960082375751622238519)
    ·
      refine ⟨107674440123563627433357779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71782960082375751622238519 107674440123563627433357779)
      ·
        refine ⟨161511660185345441150036669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107674440123563627433357779 161511660185345441150036669)
        ·
          refine ⟨60566872569504540431263751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161511660185345441150036669 60566872569504540431263751)
          ·
            refine ⟨90850308854256810646895627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60566872569504540431263751 90850308854256810646895627)
            ·
              refine ⟨136275463281385215970343441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90850308854256810646895627 136275463281385215970343441)
              ·
                refine ⟨102206597461038911977757581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136275463281385215970343441 102206597461038911977757581)
                ·
                  refine ⟨38327474047889591991659093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102206597461038911977757581 38327474047889591991659093)
                  ·
                    refine ⟨449150086498706156152255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38327474047889591991659093 449150086498706156152255)
                    ·
                      rfl

theorem cell22_1312075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_1312075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312075 prefixEnd_1312075 := by exact prefixLift 1312075
  have htrace : WordTrace (prefixWord ++ tailWord_1312075) baseStart_1312075 baseEnd_1312075 := by
    simpa [prefixWord, tailWord_1312075, baseEnd_1312075] using wordTrace_append hprefix tailTrace_1312075
  have hstable : (prefixWord ++ tailWord_1312075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312075).length < 2 ^ (prefixWord ++ tailWord_1312075).sum := by decide
  have hdescent : baseEnd_1312075 < baseStart_1312075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312158 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1312158 : Nat := 118140960795 + 1312158 * 2 ^ 59
def prefixEnd_1312158 : Nat := 4983230072969 + 3 ^ 40 * 1312158 * 2
def baseEnd_1312158 : Nat := 149726166364973868775667

theorem tailTrace_1312158 : CollatzResearch.WordTrace tailWord_1312158 prefixEnd_1312158 149726166364973868775667 := by
  unfold tailWord_1312158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5982291747535392448762141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31905555986855426393398085 5982291747535392448762141)
  ·
    refine ⟨2243359405325772168285803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5982291747535392448762141 2243359405325772168285803)
    ·
      refine ⟨3365039107988658252428705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243359405325772168285803 3365039107988658252428705)
      ·
        refine ⟨2523779330991493689321529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3365039107988658252428705 2523779330991493689321529)
        ·
          refine ⟨1892834498243620266991147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2523779330991493689321529 1892834498243620266991147)
          ·
            refine ⟨2839251747365430400486721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892834498243620266991147 2839251747365430400486721)
            ·
              refine ⟨2129438810524072800365041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2839251747365430400486721 2129438810524072800365041)
              ·
                refine ⟨1597079107893054600273781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129438810524072800365041 1597079107893054600273781)
                ·
                  refine ⟨149726166364973868775667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1597079107893054600273781 149726166364973868775667)
                  ·
                    rfl

theorem cell22_1312158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1312158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312158 prefixEnd_1312158 := by exact prefixLift 1312158
  have htrace : WordTrace (prefixWord ++ tailWord_1312158) baseStart_1312158 baseEnd_1312158 := by
    simpa [prefixWord, tailWord_1312158, baseEnd_1312158] using wordTrace_append hprefix tailTrace_1312158
  have hstable : (prefixWord ++ tailWord_1312158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312158).length < 2 ^ (prefixWord ++ tailWord_1312158).sum := by decide
  have hdescent : baseEnd_1312158 < baseStart_1312158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312218 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_1312218 : Nat := 118140960795 + 1312218 * 2 ^ 59
def prefixEnd_1312218 : Nat := 4983230072969 + 3 ^ 40 * 1312218 * 2
def baseEnd_1312218 : Nat := 449199038321101449826817

theorem tailTrace_1312218 : CollatzResearch.WordTrace tailWord_1312218 prefixEnd_1312218 449199038321101449826817 := by
  unfold tailWord_1312218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11965130590016442459320327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31907014906710513224854205 11965130590016442459320327)
  ·
    refine ⟨17947695885024663688980491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11965130590016442459320327 17947695885024663688980491)
    ·
      refine ⟨26921543827536995533470737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17947695885024663688980491 26921543827536995533470737)
      ·
        refine ⟨20191157870652746650103053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26921543827536995533470737 20191157870652746650103053)
        ·
          refine ⟨7571684201494779993788645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20191157870652746650103053 7571684201494779993788645)
          ·
            refine ⟨1419690787780271248835371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7571684201494779993788645 1419690787780271248835371)
            ·
              refine ⟨2129536181670406873253057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419690787780271248835371 2129536181670406873253057)
              ·
                refine ⟨1597152136252805154939793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129536181670406873253057 1597152136252805154939793)
                ·
                  refine ⟨1197864102189603866204845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597152136252805154939793 1197864102189603866204845)
                  ·
                    refine ⟨449199038321101449826817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197864102189603866204845 449199038321101449826817)
                    ·
                      rfl

theorem cell22_1312218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_1312218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312218 prefixEnd_1312218 := by exact prefixLift 1312218
  have htrace : WordTrace (prefixWord ++ tailWord_1312218) baseStart_1312218 baseEnd_1312218 := by
    simpa [prefixWord, tailWord_1312218, baseEnd_1312218] using wordTrace_append hprefix tailTrace_1312218
  have hstable : (prefixWord ++ tailWord_1312218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312218).length < 2 ^ (prefixWord ++ tailWord_1312218).sum := by decide
  have hdescent : baseEnd_1312218 < baseStart_1312218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312280 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 3, 3]
def baseStart_1312280 : Nat := 118140960795 + 1312280 * 2 ^ 59
def prefixEnd_1312280 : Nat := 4983230072969 + 3 ^ 40 * 1312280 * 2
def baseEnd_1312280 : Nat := 449220262188153954776627

theorem tailTrace_1312280 : CollatzResearch.WordTrace tailWord_1312280 prefixEnd_1312280 449220262188153954776627 := by
  unfold tailWord_1312280
  simp only [CollatzResearch.WordTrace]
  refine ⟨23931391842920577213019147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31908522457227436284025529 23931391842920577213019147)
  ·
    refine ⟨35897087764380865819528721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23931391842920577213019147 35897087764380865819528721)
    ·
      refine ⟨26922815823285649364646541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35897087764380865819528721 26922815823285649364646541)
      ·
        refine ⟨10096055933732118511742453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26922815823285649364646541 10096055933732118511742453)
        ·
          refine ⟨946505243787386110475855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10096055933732118511742453 946505243787386110475855)
          ·
            refine ⟨1419757865681079165713783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946505243787386110475855 1419757865681079165713783)
            ·
              refine ⟨2129636798521618748570675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419757865681079165713783 2129636798521618748570675)
              ·
                refine ⟨3194455197782428122856013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129636798521618748570675 3194455197782428122856013)
                ·
                  refine ⟨1197920699168410546071005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3194455197782428122856013 1197920699168410546071005)
                  ·
                    refine ⟨449220262188153954776627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197920699168410546071005 449220262188153954776627)
                    ·
                      rfl

theorem cell22_1312280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_1312280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312280 prefixEnd_1312280 := by exact prefixLift 1312280
  have htrace : WordTrace (prefixWord ++ tailWord_1312280) baseStart_1312280 baseEnd_1312280 := by
    simpa [prefixWord, tailWord_1312280, baseEnd_1312280] using wordTrace_append hprefix tailTrace_1312280
  have hstable : (prefixWord ++ tailWord_1312280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312280).length < 2 ^ (prefixWord ++ tailWord_1312280).sum := by decide
  have hdescent : baseEnd_1312280 < baseStart_1312280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312286 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1312286 : Nat := 118140960795 + 1312286 * 2 ^ 59
def prefixEnd_1312286 : Nat := 4983230072969 + 3 ^ 40 * 1312286 * 2
def baseEnd_1312286 : Nat := 449222316110771939126609

theorem tailTrace_1312286 : CollatzResearch.WordTrace tailWord_1312286 prefixEnd_1312286 449222316110771939126609 := by
  unfold tailWord_1312286
  simp only [CollatzResearch.WordTrace]
  refine ⟨5982875315477427181344589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31908668349212944967171141 5982875315477427181344589)
  ·
    refine ⟨2243578243304035193004221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5982875315477427181344589 2243578243304035193004221)
    ·
      refine ⟨841341841239013197376583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2243578243304035193004221 841341841239013197376583)
      ·
        refine ⟨1262012761858519796064875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841341841239013197376583 1262012761858519796064875)
        ·
          refine ⟨1893019142787779694097313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262012761858519796064875 1893019142787779694097313)
          ·
            refine ⟨1419764357090834770572985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1893019142787779694097313 1419764357090834770572985)
            ·
              refine ⟨1064823267818126077929739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419764357090834770572985 1064823267818126077929739)
              ·
                refine ⟨1597234901727189116894609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064823267818126077929739 1597234901727189116894609)
                ·
                  refine ⟨1197926176295391837670957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597234901727189116894609 1197926176295391837670957)
                  ·
                    refine ⟨449222316110771939126609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1197926176295391837670957 449222316110771939126609)
                    ·
                      rfl

theorem cell22_1312286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1312286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312286 prefixEnd_1312286 := by exact prefixLift 1312286
  have htrace : WordTrace (prefixWord ++ tailWord_1312286) baseStart_1312286 baseEnd_1312286 := by
    simpa [prefixWord, tailWord_1312286, baseEnd_1312286] using wordTrace_append hprefix tailTrace_1312286
  have hstable : (prefixWord ++ tailWord_1312286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312286).length < 2 ^ (prefixWord ++ tailWord_1312286).sum := by decide
  have hdescent : baseEnd_1312286 < baseStart_1312286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312319 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 3, 5]
def baseStart_1312319 : Nat := 118140960795 + 1312319 * 2 ^ 59
def prefixEnd_1312319 : Nat := 4983230072969 + 3 ^ 40 * 1312319 * 2
def baseEnd_1312319 : Nat := 449233612685170853051507

theorem tailTrace_1312319 : CollatzResearch.WordTrace tailWord_1312319 prefixEnd_1312319 449233612685170853051507 := by
  unfold tailWord_1312319
  simp only [CollatzResearch.WordTrace]
  refine ⟨47864206132699864086708011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31909470755133242724472007 47864206132699864086708011)
  ·
    refine ⟨71796309199049796130062017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47864206132699864086708011 71796309199049796130062017)
    ·
      refine ⟨53847231899287347097546513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71796309199049796130062017 53847231899287347097546513)
      ·
        refine ⟨40385423924465510323159885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53847231899287347097546513 40385423924465510323159885)
        ·
          refine ⟨15144533971674566371184957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40385423924465510323159885 15144533971674566371184957)
          ·
            refine ⟨5679200239377962389194359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15144533971674566371184957 5679200239377962389194359)
            ·
              refine ⟨8518800359066943583791539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679200239377962389194359 8518800359066943583791539)
              ·
                refine ⟨12778200538600415375687309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8518800359066943583791539 12778200538600415375687309)
                ·
                  refine ⟨4791825201975155765882741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12778200538600415375687309 4791825201975155765882741)
                  ·
                    refine ⟨449233612685170853051507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4791825201975155765882741 449233612685170853051507)
                    ·
                      rfl

theorem cell22_1312319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_1312319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312319 prefixEnd_1312319 := by exact prefixLift 1312319
  have htrace : WordTrace (prefixWord ++ tailWord_1312319) baseStart_1312319 baseEnd_1312319 := by
    simpa [prefixWord, tailWord_1312319, baseEnd_1312319] using wordTrace_append hprefix tailTrace_1312319
  have hstable : (prefixWord ++ tailWord_1312319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312319).length < 2 ^ (prefixWord ++ tailWord_1312319).sum := by decide
  have hdescent : baseEnd_1312319 < baseStart_1312319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312334 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1312334 : Nat := 118140960795 + 1312334 * 2 ^ 59
def prefixEnd_1312334 : Nat := 4983230072969 + 3 ^ 40 * 1312334 * 2
def baseEnd_1312334 : Nat := 449238747491715813926461

theorem tailTrace_1312334 : CollatzResearch.WordTrace tailWord_1312334 prefixEnd_1312334 449238747491715813926461 := by
  unfold tailWord_1312334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5983094153455690206063007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31909835485097014432336037 5983094153455690206063007)
  ·
    refine ⟨8974641230183535309094511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5983094153455690206063007 8974641230183535309094511)
    ·
      refine ⟨13461961845275302963641767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8974641230183535309094511 13461961845275302963641767)
      ·
        refine ⟨20192942767912954445462651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13461961845275302963641767 20192942767912954445462651)
        ·
          refine ⟨30289414151869431668193977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20192942767912954445462651 30289414151869431668193977)
          ·
            refine ⟨22717060613902073751145483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30289414151869431668193977 22717060613902073751145483)
            ·
              refine ⟨34075590920853110626718225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22717060613902073751145483 34075590920853110626718225)
              ·
                refine ⟨25556693190639832970038669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34075590920853110626718225 25556693190639832970038669)
                ·
                  refine ⟨9583759946489937363764501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25556693190639832970038669 9583759946489937363764501)
                  ·
                    refine ⟨449238747491715813926461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9583759946489937363764501 449238747491715813926461)
                    ·
                      rfl

theorem cell22_1312334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1312334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312334 prefixEnd_1312334 := by exact prefixLift 1312334
  have htrace : WordTrace (prefixWord ++ tailWord_1312334) baseStart_1312334 baseEnd_1312334 := by
    simpa [prefixWord, tailWord_1312334, baseEnd_1312334] using wordTrace_append hprefix tailTrace_1312334
  have hstable : (prefixWord ++ tailWord_1312334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312334).length < 2 ^ (prefixWord ++ tailWord_1312334).sum := by decide
  have hdescent : baseEnd_1312334 < baseStart_1312334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312338 : List Nat := [3, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_1312338 : Nat := 118140960795 + 1312338 * 2 ^ 59
def prefixEnd_1312338 : Nat := 4983230072969 + 3 ^ 40 * 1312338 * 2
def baseEnd_1312338 : Nat := 149746705591153712275483

theorem tailTrace_1312338 : CollatzResearch.WordTrace tailWord_1312338 prefixEnd_1312338 149746705591153712275483 := by
  unfold tailWord_1312338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11966224779907757582912417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31909932746420686887766445 11966224779907757582912417)
  ·
    refine ⟨8974668584930818187184313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11966224779907757582912417 8974668584930818187184313)
    ·
      refine ⟨6731001438698113640388235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8974668584930818187184313 6731001438698113640388235)
      ·
        refine ⟨10096502158047170460582353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6731001438698113640388235 10096502158047170460582353)
        ·
          refine ⟨7572376618535377845436765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10096502158047170460582353 7572376618535377845436765)
          ·
            refine ⟨2839641231950766692038787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7572376618535377845436765 2839641231950766692038787)
            ·
              refine ⟨4259461847926150038058181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839641231950766692038787 4259461847926150038058181)
              ·
                refine ⟨798649096486153132135909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4259461847926150038058181 798649096486153132135909)
                ·
                  refine ⟨149746705591153712275483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798649096486153132135909 149746705591153712275483)
                  ·
                    rfl

theorem cell22_1312338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_1312338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312338 prefixEnd_1312338 := by exact prefixLift 1312338
  have htrace : WordTrace (prefixWord ++ tailWord_1312338) baseStart_1312338 baseEnd_1312338 := by
    simpa [prefixWord, tailWord_1312338, baseEnd_1312338] using wordTrace_append hprefix tailTrace_1312338
  have hstable : (prefixWord ++ tailWord_1312338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312338).length < 2 ^ (prefixWord ++ tailWord_1312338).sum := by decide
  have hdescent : baseEnd_1312338 < baseStart_1312338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312368 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 2, 4]
def baseStart_1312368 : Nat := 118140960795 + 1312368 * 2 ^ 59
def prefixEnd_1312368 : Nat := 4983230072969 + 3 ^ 40 * 1312368 * 2
def baseEnd_1312368 : Nat := 449250386386551058576357

theorem tailTrace_1312368 : CollatzResearch.WordTrace tailWord_1312368 prefixEnd_1312368 449250386386551058576357 := by
  unfold tailWord_1312368
  simp only [CollatzResearch.WordTrace]
  refine ⟨23932996654761172727620879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31910662206348230303494505 23932996654761172727620879)
  ·
    refine ⟨35899494982141759091431319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23932996654761172727620879 35899494982141759091431319)
    ·
      refine ⟨53849242473212638637146979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35899494982141759091431319 53849242473212638637146979)
      ·
        refine ⟨80773863709818957955720469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53849242473212638637146979 80773863709818957955720469)
        ·
          refine ⟨3786274861397763654174397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80773863709818957955720469 3786274861397763654174397)
          ·
            refine ⟨1419853073024161370315399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3786274861397763654174397 1419853073024161370315399)
            ·
              refine ⟨2129779609536242055473099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419853073024161370315399 2129779609536242055473099)
              ·
                refine ⟨3194669414304363083209649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129779609536242055473099 3194669414304363083209649)
                ·
                  refine ⟨2396002060728272312407237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3194669414304363083209649 2396002060728272312407237)
                  ·
                    refine ⟨449250386386551058576357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2396002060728272312407237 449250386386551058576357)
                    ·
                      rfl

theorem cell22_1312368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_1312368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312368 prefixEnd_1312368 := by exact prefixLift 1312368
  have htrace : WordTrace (prefixWord ++ tailWord_1312368) baseStart_1312368 baseEnd_1312368 := by
    simpa [prefixWord, tailWord_1312368, baseEnd_1312368] using wordTrace_append hprefix tailTrace_1312368
  have hstable : (prefixWord ++ tailWord_1312368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312368).length < 2 ^ (prefixWord ++ tailWord_1312368).sum := by decide
  have hdescent : baseEnd_1312368 < baseStart_1312368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312398 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_1312398 : Nat := 118140960795 + 1312398 * 2 ^ 59
def prefixEnd_1312398 : Nat := 4983230072969 + 3 ^ 40 * 1312398 * 2
def baseEnd_1312398 : Nat := 449260655999640980326265

theorem tailTrace_1312398 : CollatzResearch.WordTrace tailWord_1312398 prefixEnd_1312398 449260655999640980326265 := by
  unfold tailWord_1312398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5983385937426707572354231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31911391666275773719222565 5983385937426707572354231)
  ·
    refine ⟨8975078906140061358531347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5983385937426707572354231 8975078906140061358531347)
    ·
      refine ⟨13462618359210092037797021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8975078906140061358531347 13462618359210092037797021)
      ·
        refine ⟨5048481884703784514173883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13462618359210092037797021 5048481884703784514173883)
        ·
          refine ⟨7572722827055676771260825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048481884703784514173883 7572722827055676771260825)
          ·
            refine ⟨5679542120291757578445619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7572722827055676771260825 5679542120291757578445619)
            ·
              refine ⟨8519313180437636367668429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679542120291757578445619 8519313180437636367668429)
              ·
                refine ⟨3194742442664113637875661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8519313180437636367668429 3194742442664113637875661)
                ·
                  refine ⟨1198028415999042614203373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3194742442664113637875661 1198028415999042614203373)
                  ·
                    refine ⟨449260655999640980326265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198028415999042614203373 449260655999640980326265)
                    ·
                      rfl

theorem cell22_1312398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_1312398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312398 prefixEnd_1312398 := by exact prefixLift 1312398
  have htrace : WordTrace (prefixWord ++ tailWord_1312398) baseStart_1312398 baseEnd_1312398 := by
    simpa [prefixWord, tailWord_1312398, baseEnd_1312398] using wordTrace_append hprefix tailTrace_1312398
  have hstable : (prefixWord ++ tailWord_1312398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312398).length < 2 ^ (prefixWord ++ tailWord_1312398).sum := by decide
  have hdescent : baseEnd_1312398 < baseStart_1312398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312409 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_1312409 : Nat := 118140960795 + 1312409 * 2 ^ 59
def prefixEnd_1312409 : Nat := 4983230072969 + 3 ^ 40 * 1312409 * 2
def baseEnd_1312409 : Nat := 449264421524440618301231

theorem tailTrace_1312409 : CollatzResearch.WordTrace tailWord_1312409 prefixEnd_1312409 449264421524440618301231 := by
  unfold tailWord_1312409
  simp only [CollatzResearch.WordTrace]
  refine ⟨47867488702373809457484281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31911659134915872971656187 47867488702373809457484281)
  ·
    refine ⟨35900616526780357093113211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47867488702373809457484281 35900616526780357093113211)
    ·
      refine ⟨53850924790170535639669817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35900616526780357093113211 53850924790170535639669817)
      ·
        refine ⟨40388193592627901729752363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53850924790170535639669817 40388193592627901729752363)
        ·
          refine ⟨60582290388941852594628545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40388193592627901729752363 60582290388941852594628545)
          ·
            refine ⟨45436717791706389445971409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60582290388941852594628545 45436717791706389445971409)
            ·
              refine ⟨34077538343779792084478557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45436717791706389445971409 34077538343779792084478557)
              ·
                refine ⟨12779076878917422031679459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34077538343779792084478557 12779076878917422031679459)
                ·
                  refine ⟨19168615318376133047519189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12779076878917422031679459 19168615318376133047519189)
                  ·
                    refine ⟨449264421524440618301231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19168615318376133047519189 449264421524440618301231)
                    ·
                      rfl

theorem cell22_1312409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_1312409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312409 prefixEnd_1312409 := by exact prefixLift 1312409
  have htrace : WordTrace (prefixWord ++ tailWord_1312409) baseStart_1312409 baseEnd_1312409 := by
    simpa [prefixWord, tailWord_1312409, baseEnd_1312409] using wordTrace_append hprefix tailTrace_1312409
  have hstable : (prefixWord ++ tailWord_1312409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312409).length < 2 ^ (prefixWord ++ tailWord_1312409).sum := by decide
  have hdescent : baseEnd_1312409 < baseStart_1312409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312471 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 1, 5]
def baseStart_1312471 : Nat := 118140960795 + 1312471 * 2 ^ 59
def prefixEnd_1312471 : Nat := 4983230072969 + 3 ^ 40 * 1312471 * 2
def baseEnd_1312471 : Nat := 449285645391493123251041

theorem tailTrace_1312471 : CollatzResearch.WordTrace tailWord_1312471 prefixEnd_1312471 449285645391493123251041 := by
  unfold tailWord_1312471
  simp only [CollatzResearch.WordTrace]
  refine ⟨47869750028149194046241267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31913166685432796030827511 47869750028149194046241267)
  ·
    refine ⟨71804625042223791069361901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47869750028149194046241267 71804625042223791069361901)
    ·
      refine ⟨26926734390833921651010713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71804625042223791069361901 26926734390833921651010713)
      ·
        refine ⟨20195050793125441238258035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26926734390833921651010713 20195050793125441238258035)
        ·
          refine ⟨30292576189688161857387053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20195050793125441238258035 30292576189688161857387053)
          ·
            refine ⟨11359716071133060696520145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30292576189688161857387053 11359716071133060696520145)
            ·
              refine ⟨8519787053349795522390109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11359716071133060696520145 8519787053349795522390109)
              ·
                refine ⟨3194920145006173320896291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8519787053349795522390109 3194920145006173320896291)
                ·
                  refine ⟨4792380217509259981344437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194920145006173320896291 4792380217509259981344437)
                  ·
                    refine ⟨449285645391493123251041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4792380217509259981344437 449285645391493123251041)
                    ·
                      rfl

theorem cell22_1312471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_1312471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312471 prefixEnd_1312471 := by exact prefixLift 1312471
  have htrace : WordTrace (prefixWord ++ tailWord_1312471) baseStart_1312471 baseEnd_1312471 := by
    simpa [prefixWord, tailWord_1312471, baseEnd_1312471] using wordTrace_append hprefix tailTrace_1312471
  have hstable : (prefixWord ++ tailWord_1312471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312471).length < 2 ^ (prefixWord ++ tailWord_1312471).sum := by decide
  have hdescent : baseEnd_1312471 < baseStart_1312471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312488 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1312488 : Nat := 118140960795 + 1312488 * 2 ^ 59
def prefixEnd_1312488 : Nat := 4983230072969 + 3 ^ 40 * 1312488 * 2
def baseEnd_1312488 : Nat := 449291464838910745575989

theorem tailTrace_1312488 : CollatzResearch.WordTrace tailWord_1312488 prefixEnd_1312488 449291464838910745575989 := by
  unfold tailWord_1312488
  simp only [CollatzResearch.WordTrace]
  refine ⟨23935185034543802974805059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31913580046058403966406745 23935185034543802974805059)
  ·
    refine ⟨35902777551815704462207589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23935185034543802974805059 35902777551815704462207589)
    ·
      refine ⟨6731770790965444586663923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35902777551815704462207589 6731770790965444586663923)
      ·
        refine ⟨10097656186448166879995885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6731770790965444586663923 10097656186448166879995885)
        ·
          refine ⟨3786621069918062579998457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10097656186448166879995885 3786621069918062579998457)
          ·
            refine ⟨2839965802438546934998843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3786621069918062579998457 2839965802438546934998843)
            ·
              refine ⟨4259948703657820402498265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839965802438546934998843 4259948703657820402498265)
              ·
                refine ⟨3194961527743365301873699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259948703657820402498265 3194961527743365301873699)
                ·
                  refine ⟨4792442291615047952810549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3194961527743365301873699 4792442291615047952810549)
                  ·
                    refine ⟨449291464838910745575989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4792442291615047952810549 449291464838910745575989)
                    ·
                      rfl

theorem cell22_1312488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1312488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312488 prefixEnd_1312488 := by exact prefixLift 1312488
  have htrace : WordTrace (prefixWord ++ tailWord_1312488) baseStart_1312488 baseEnd_1312488 := by
    simpa [prefixWord, tailWord_1312488, baseEnd_1312488] using wordTrace_append hprefix tailTrace_1312488
  have hstable : (prefixWord ++ tailWord_1312488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312488).length < 2 ^ (prefixWord ++ tailWord_1312488).sum := by decide
  have hdescent : baseEnd_1312488 < baseStart_1312488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312533 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_1312533 : Nat := 118140960795 + 1312533 * 2 ^ 59
def prefixEnd_1312533 : Nat := 4983230072969 + 3 ^ 40 * 1312533 * 2
def baseEnd_1312533 : Nat := 449306869258545628200851

theorem tailTrace_1312533 : CollatzResearch.WordTrace tailWord_1312533 prefixEnd_1312533 449306869258545628200851 := by
  unfold tailWord_1312533
  simp only [CollatzResearch.WordTrace]
  refine ⟨47872011353924578634998253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31914674235949719089998835 47872011353924578634998253)
  ·
    refine ⟨17952004257721716988124345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47872011353924578634998253 17952004257721716988124345)
    ·
      refine ⟨13464003193291287741093259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17952004257721716988124345 13464003193291287741093259)
      ·
        refine ⟨20196004789936931611639889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13464003193291287741093259 20196004789936931611639889)
        ·
          refine ⟨15147003592452698708729917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20196004789936931611639889 15147003592452698708729917)
          ·
            refine ⟨5680126347169762015773719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15147003592452698708729917 5680126347169762015773719)
            ·
              refine ⟨8520189520754643023660579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5680126347169762015773719 8520189520754643023660579)
              ·
                refine ⟨12780284281131964535490869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8520189520754643023660579 12780284281131964535490869)
                ·
                  refine ⟨1198151651356121675202269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12780284281131964535490869 1198151651356121675202269)
                  ·
                    refine ⟨449306869258545628200851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198151651356121675202269 449306869258545628200851)
                    ·
                      rfl

theorem cell22_1312533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_1312533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312533 prefixEnd_1312533 := by exact prefixLift 1312533
  have htrace : WordTrace (prefixWord ++ tailWord_1312533) baseStart_1312533 baseEnd_1312533 := by
    simpa [prefixWord, tailWord_1312533, baseEnd_1312533] using wordTrace_append hprefix tailTrace_1312533
  have hstable : (prefixWord ++ tailWord_1312533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312533).length < 2 ^ (prefixWord ++ tailWord_1312533).sum := by decide
  have hdescent : baseEnd_1312533 < baseStart_1312533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312563 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 7]
def baseStart_1312563 : Nat := 118140960795 + 1312563 * 2 ^ 59
def prefixEnd_1312563 : Nat := 4983230072969 + 3 ^ 40 * 1312563 * 2
def baseEnd_1312563 : Nat := 149772379623878516650253

theorem tailTrace_1312563 : CollatzResearch.WordTrace tailWord_1312563 prefixEnd_1312563 149772379623878516650253 := by
  unfold tailWord_1312563
  simp only [CollatzResearch.WordTrace]
  refine ⟨47873105543815893758590343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31915403695877262505726895 47873105543815893758590343)
  ·
    refine ⟨71809658315723840637885515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47873105543815893758590343 71809658315723840637885515)
    ·
      refine ⟨107714487473585760956828273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71809658315723840637885515 107714487473585760956828273)
      ·
        refine ⟨80785865605189320717621205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107714487473585760956828273 80785865605189320717621205)
        ·
          refine ⟨1893418725121624704319247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 80785865605189320717621205 1893418725121624704319247)
          ·
            refine ⟨2840128087682437056478871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893418725121624704319247 2840128087682437056478871)
            ·
              refine ⟨4260192131523655584718307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840128087682437056478871 4260192131523655584718307)
              ·
                refine ⟨6390288197285483377077461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4260192131523655584718307 6390288197285483377077461)
                ·
                  refine ⟨149772379623878516650253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6390288197285483377077461 149772379623878516650253)
                  ·
                    rfl

theorem cell22_1312563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 7].length) (baseStart_1312563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312563 prefixEnd_1312563 := by exact prefixLift 1312563
  have htrace : WordTrace (prefixWord ++ tailWord_1312563) baseStart_1312563 baseEnd_1312563 := by
    simpa [prefixWord, tailWord_1312563, baseEnd_1312563] using wordTrace_append hprefix tailTrace_1312563
  have hstable : (prefixWord ++ tailWord_1312563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312563).length < 2 ^ (prefixWord ++ tailWord_1312563).sum := by decide
  have hdescent : baseEnd_1312563 < baseStart_1312563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312640 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 2, 3]
def baseStart_1312640 : Nat := 118140960795 + 1312640 * 2 ^ 59
def prefixEnd_1312640 : Nat := 4983230072969 + 3 ^ 40 * 1312640 * 2
def baseEnd_1312640 : Nat := 449343497545233015775523

theorem tailTrace_1312640 : CollatzResearch.WordTrace tailWord_1312640 prefixEnd_1312640 449343497545233015775523 := by
  unfold tailWord_1312640
  simp only [CollatzResearch.WordTrace]
  refine ⟨23937956982268467954571687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31917275976357957272762249 23937956982268467954571687)
  ·
    refine ⟨35906935473402701931857531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23937956982268467954571687 35906935473402701931857531)
    ·
      refine ⟨53860403210104052897786297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35906935473402701931857531 53860403210104052897786297)
      ·
        refine ⟨40395302407578039673339723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53860403210104052897786297 40395302407578039673339723)
        ·
          refine ⟨60592953611367059510009585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40395302407578039673339723 60592953611367059510009585)
          ·
            refine ⟨45444715208525294632507189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60592953611367059510009585 45444715208525294632507189)
            ·
              refine ⟨4260442050799246371797549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45444715208525294632507189 4260442050799246371797549)
              ·
                refine ⟨1597665769049717389424081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4260442050799246371797549 1597665769049717389424081)
                ·
                  refine ⟨1198249326787288042068061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597665769049717389424081 1198249326787288042068061)
                  ·
                    refine ⟨449343497545233015775523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198249326787288042068061 449343497545233015775523)
                    ·
                      rfl

theorem cell22_1312640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_1312640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312640 prefixEnd_1312640 := by exact prefixLift 1312640
  have htrace : WordTrace (prefixWord ++ tailWord_1312640) baseStart_1312640 baseEnd_1312640 := by
    simpa [prefixWord, tailWord_1312640, baseEnd_1312640] using wordTrace_append hprefix tailTrace_1312640
  have hstable : (prefixWord ++ tailWord_1312640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312640).length < 2 ^ (prefixWord ++ tailWord_1312640).sum := by decide
  have hdescent : baseEnd_1312640 < baseStart_1312640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312670 : List Nat := [4, 3, 1, 3, 11]
def baseStart_1312670 : Nat := 118140960795 + 1312670 * 2 ^ 59
def prefixEnd_1312670 : Nat := 4983230072969 + 3 ^ 40 * 1312670 * 2
def baseEnd_1312670 : Nat := 1849192457441658179117

theorem tailTrace_1312670 : CollatzResearch.WordTrace tailWord_1312670 prefixEnd_1312670 1849192457441658179117 := by
  unfold tailWord_1312670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984626019303531379091933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31918005436285500688490309 5984626019303531379091933)
  ·
    refine ⟨2244234757238824267159475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5984626019303531379091933 2244234757238824267159475)
    ·
      refine ⟨3366352135858236400739213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2244234757238824267159475 3366352135858236400739213)
      ·
        refine ⟨1262382050946838650277205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3366352135858236400739213 1262382050946838650277205)
        ·
          refine ⟨1849192457441658179117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1262382050946838650277205 1849192457441658179117)
          ·
            rfl

theorem cell22_1312670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 11].length) (baseStart_1312670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312670 prefixEnd_1312670 := by exact prefixLift 1312670
  have htrace : WordTrace (prefixWord ++ tailWord_1312670) baseStart_1312670 baseEnd_1312670 := by
    simpa [prefixWord, tailWord_1312670, baseEnd_1312670] using wordTrace_append hprefix tailTrace_1312670
  have hstable : (prefixWord ++ tailWord_1312670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312670).length < 2 ^ (prefixWord ++ tailWord_1312670).sum := by decide
  have hdescent : baseEnd_1312670 < baseStart_1312670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312674 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1312674 : Nat := 118140960795 + 1312674 * 2 ^ 59
def prefixEnd_1312674 : Nat := 4983230072969 + 3 ^ 40 * 1312674 * 2
def baseEnd_1312674 : Nat := 449355136440068260425419

theorem tailTrace_1312674 : CollatzResearch.WordTrace tailWord_1312674 prefixEnd_1312674 449355136440068260425419 := by
  unfold tailWord_1312674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11969288511603439928970269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31918102697609173143920717 11969288511603439928970269)
  ·
    refine ⟨4488483191851289973363851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11969288511603439928970269 4488483191851289973363851)
    ·
      refine ⟨6732724787776934960045777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4488483191851289973363851 6732724787776934960045777)
      ·
        refine ⟨5049543590832701220034333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6732724787776934960045777 5049543590832701220034333)
        ·
          refine ⟨1893578846562262957512875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5049543590832701220034333 1893578846562262957512875)
          ·
            refine ⟨2840368269843394436269313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893578846562262957512875 2840368269843394436269313)
            ·
              refine ⟨2130276202382545827201985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840368269843394436269313 2130276202382545827201985)
              ·
                refine ⟨1597707151786909370401489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130276202382545827201985 1597707151786909370401489)
                ·
                  refine ⟨1198280363840182027801117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597707151786909370401489 1198280363840182027801117)
                  ·
                    refine ⟨449355136440068260425419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198280363840182027801117 449355136440068260425419)
                    ·
                      rfl

theorem cell22_1312674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1312674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312674 prefixEnd_1312674 := by exact prefixLift 1312674
  have htrace : WordTrace (prefixWord ++ tailWord_1312674) baseStart_1312674 baseEnd_1312674 := by
    simpa [prefixWord, tailWord_1312674, baseEnd_1312674] using wordTrace_append hprefix tailTrace_1312674
  have hstable : (prefixWord ++ tailWord_1312674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312674).length < 2 ^ (prefixWord ++ tailWord_1312674).sum := by decide
  have hdescent : baseEnd_1312674 < baseStart_1312674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312702 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_1312702 : Nat := 118140960795 + 1312702 * 2 ^ 59
def prefixEnd_1312702 : Nat := 4983230072969 + 3 ^ 40 * 1312702 * 2
def baseEnd_1312702 : Nat := 449364721412285520725333

theorem tailTrace_1312702 : CollatzResearch.WordTrace tailWord_1312702 prefixEnd_1312702 449364721412285520725333 := by
  unfold tailWord_1312702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984771911289040062237545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31918783526874880331933573 5984771911289040062237545)
  ·
    refine ⟨4488578933466780046678159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5984771911289040062237545 4488578933466780046678159)
    ·
      refine ⟨6732868400200170070017239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4488578933466780046678159 6732868400200170070017239)
      ·
        refine ⟨10099302600300255105025859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6732868400200170070017239 10099302600300255105025859)
        ·
          refine ⟨15148953900450382657538789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10099302600300255105025859 15148953900450382657538789)
          ·
            refine ⟨2840428856334446748288523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15148953900450382657538789 2840428856334446748288523)
            ·
              refine ⟨4260643284501670122432785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840428856334446748288523 4260643284501670122432785)
              ·
                refine ⟨3195482463376252591824589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4260643284501670122432785 3195482463376252591824589)
                ·
                  refine ⟨1198305923766094721934221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3195482463376252591824589 1198305923766094721934221)
                  ·
                    refine ⟨449364721412285520725333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198305923766094721934221 449364721412285520725333)
                    ·
                      rfl

theorem cell22_1312702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_1312702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312702 prefixEnd_1312702 := by exact prefixLift 1312702
  have htrace : WordTrace (prefixWord ++ tailWord_1312702) baseStart_1312702 baseEnd_1312702 := by
    simpa [prefixWord, tailWord_1312702, baseEnd_1312702] using wordTrace_append hprefix tailTrace_1312702
  have hstable : (prefixWord ++ tailWord_1312702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312702).length < 2 ^ (prefixWord ++ tailWord_1312702).sum := by decide
  have hdescent : baseEnd_1312702 < baseStart_1312702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312792 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 2, 3]
def baseStart_1312792 : Nat := 118140960795 + 1312792 * 2 ^ 59
def prefixEnd_1312792 : Nat := 4983230072969 + 3 ^ 40 * 1312792 * 2
def baseEnd_1312792 : Nat := 449395530251555285975057

theorem tailTrace_1312792 : CollatzResearch.WordTrace tailWord_1312792 prefixEnd_1312792 449395530251555285975057 := by
  unfold tailWord_1312792
  simp only [CollatzResearch.WordTrace]
  refine ⟨23940728929993132934338315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31920971906657510579117753 23940728929993132934338315)
  ·
    refine ⟨35911093394989699401507473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23940728929993132934338315 35911093394989699401507473)
    ·
      refine ⟨26933320046242274551130605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35911093394989699401507473 26933320046242274551130605)
      ·
        refine ⟨10099995017340852956673977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26933320046242274551130605 10099995017340852956673977)
        ·
          refine ⟨7574996263005639717505483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10099995017340852956673977 7574996263005639717505483)
          ·
            refine ⟨11362494394508459576258225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7574996263005639717505483 11362494394508459576258225)
            ·
              refine ⟨8521870795881344682193669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11362494394508459576258225 8521870795881344682193669)
              ·
                refine ⟨1597850774227752127911313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8521870795881344682193669 1597850774227752127911313)
                ·
                  refine ⟨1198388080670814095933485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1597850774227752127911313 1198388080670814095933485)
                  ·
                    refine ⟨449395530251555285975057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198388080670814095933485 449395530251555285975057)
                    ·
                      rfl

theorem cell22_1312792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_1312792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312792 prefixEnd_1312792 := by exact prefixLift 1312792
  have htrace : WordTrace (prefixWord ++ tailWord_1312792) baseStart_1312792 baseEnd_1312792 := by
    simpa [prefixWord, tailWord_1312792, baseEnd_1312792] using wordTrace_append hprefix tailTrace_1312792
  have hstable : (prefixWord ++ tailWord_1312792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312792).length < 2 ^ (prefixWord ++ tailWord_1312792).sum := by decide
  have hdescent : baseEnd_1312792 < baseStart_1312792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312794 : List Nat := [3, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_1312794 : Nat := 118140960795 + 1312794 * 2 ^ 59
def prefixEnd_1312794 : Nat := 4983230072969 + 3 ^ 40 * 1312794 * 2
def baseEnd_1312794 : Nat := 149798738297475982475017

theorem tailTrace_1312794 : CollatzResearch.WordTrace tailWord_1312794 prefixEnd_1312794 149798738297475982475017 := by
  unfold tailWord_1312794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11970382701494755052562359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31921020537319346806832957 11970382701494755052562359)
  ·
    refine ⟨17955574052242132578843539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11970382701494755052562359 17955574052242132578843539)
    ·
      refine ⟨26933361078363198868265309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17955574052242132578843539 26933361078363198868265309)
      ·
        refine ⟨10100010404386199575599491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26933361078363198868265309 10100010404386199575599491)
        ·
          refine ⟨15150015606579299363399237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10100010404386199575599491 15150015606579299363399237)
          ·
            refine ⟨2840627926233618630637357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15150015606579299363399237 2840627926233618630637357)
            ·
              refine ⟨1065235472337606986489009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2840627926233618630637357 1065235472337606986489009)
              ·
                refine ⟨798926604253205239866757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065235472337606986489009 798926604253205239866757)
                ·
                  refine ⟨149798738297475982475017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798926604253205239866757 149798738297475982475017)
                  ·
                    rfl

theorem cell22_1312794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_1312794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312794 prefixEnd_1312794 := by exact prefixLift 1312794
  have htrace : WordTrace (prefixWord ++ tailWord_1312794) baseStart_1312794 baseEnd_1312794 := by
    simpa [prefixWord, tailWord_1312794, baseEnd_1312794] using wordTrace_append hprefix tailTrace_1312794
  have hstable : (prefixWord ++ tailWord_1312794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312794).length < 2 ^ (prefixWord ++ tailWord_1312794).sum := by decide
  have hdescent : baseEnd_1312794 < baseStart_1312794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312805 : List Nat := [1, 3, 1, 2, 2, 4, 2, 7]
def baseStart_1312805 : Nat := 118140960795 + 1312805 * 2 ^ 59
def prefixEnd_1312805 : Nat := 4983230072969 + 3 ^ 40 * 1312805 * 2
def baseEnd_1312805 : Nat := 49933331157469731711113

theorem tailTrace_1312805 : CollatzResearch.WordTrace tailWord_1312805 prefixEnd_1312805 49933331157469731711113 := by
  unfold tailWord_1312805
  simp only [CollatzResearch.WordTrace]
  refine ⟨47881932008939169088899869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31921288005959446059266579 47881932008939169088899869)
  ·
    refine ⟨17955724503352188408337451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47881932008939169088899869 17955724503352188408337451)
    ·
      refine ⟨26933586755028282612506177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17955724503352188408337451 26933586755028282612506177)
      ·
        refine ⟨20200190066271211959379633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26933586755028282612506177 20200190066271211959379633)
        ·
          refine ⟨15150142549703408969534725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20200190066271211959379633 15150142549703408969534725)
          ·
            refine ⟨2840651728069389181787761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15150142549703408969534725 2840651728069389181787761)
            ·
              refine ⟨2130488796052041886340821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840651728069389181787761 2130488796052041886340821)
              ·
                refine ⟨49933331157469731711113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2130488796052041886340821 49933331157469731711113)
                ·
                  rfl

theorem cell22_1312805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 7].length) (baseStart_1312805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312805 prefixEnd_1312805 := by exact prefixLift 1312805
  have htrace : WordTrace (prefixWord ++ tailWord_1312805) baseStart_1312805 baseEnd_1312805 := by
    simpa [prefixWord, tailWord_1312805, baseEnd_1312805] using wordTrace_append hprefix tailTrace_1312805
  have hstable : (prefixWord ++ tailWord_1312805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312805).length < 2 ^ (prefixWord ++ tailWord_1312805).sum := by decide
  have hdescent : baseEnd_1312805 < baseStart_1312805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312912 : List Nat := [2, 1, 1, 1, 1, 1, 5, 6, 4]
def baseStart_1312912 : Nat := 118140960795 + 1312912 * 2 ^ 59
def prefixEnd_1312912 : Nat := 4983230072969 + 3 ^ 40 * 1312912 * 2
def baseEnd_1312912 : Nat := 149812202901304990991563

theorem tailTrace_1312912 : CollatzResearch.WordTrace tailWord_1312912 prefixEnd_1312912 149812202901304990991563 := by
  unfold tailWord_1312912
  simp only [CollatzResearch.WordTrace]
  refine ⟨23942917309775763181522495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31923889746367684242029993 23942917309775763181522495)
  ·
    refine ⟨35914375964663644772283743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23942917309775763181522495 35914375964663644772283743)
    ·
      refine ⟨53871563946995467158425615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35914375964663644772283743 53871563946995467158425615)
      ·
        refine ⟨80807345920493200737638423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53871563946995467158425615 80807345920493200737638423)
        ·
          refine ⟨121211018880739801106457635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80807345920493200737638423 121211018880739801106457635)
          ·
            refine ⟨181816528321109701659686453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121211018880739801106457635 181816528321109701659686453)
            ·
              refine ⟨17045299530104034530595605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181816528321109701659686453 17045299530104034530595605)
              ·
                refine ⟨798998415473626618621669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17045299530104034530595605 798998415473626618621669)
                ·
                  refine ⟨149812202901304990991563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798998415473626618621669 149812202901304990991563)
                  ·
                    rfl

theorem cell22_1312912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 4].length) (baseStart_1312912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312912 prefixEnd_1312912 := by exact prefixLift 1312912
  have htrace : WordTrace (prefixWord ++ tailWord_1312912) baseStart_1312912 baseEnd_1312912 := by
    simpa [prefixWord, tailWord_1312912, baseEnd_1312912] using wordTrace_append hprefix tailTrace_1312912
  have hstable : (prefixWord ++ tailWord_1312912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312912).length < 2 ^ (prefixWord ++ tailWord_1312912).sum := by decide
  have hdescent : baseEnd_1312912 < baseStart_1312912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1312978 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_1312978 : Nat := 118140960795 + 1312978 * 2 ^ 59
def prefixEnd_1312978 : Nat := 4983230072969 + 3 ^ 40 * 1312978 * 2
def baseEnd_1312978 : Nat := 449459201852712800824487

theorem tailTrace_1312978 : CollatzResearch.WordTrace tailWord_1312978 prefixEnd_1312978 449459201852712800824487 := by
  unfold tailWord_1312978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972060459328104908736897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31925494558208279756631725 11972060459328104908736897)
  ·
    refine ⟨8979045344496078681552673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11972060459328104908736897 8979045344496078681552673)
    ·
      refine ⟨6734284008372059011164505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8979045344496078681552673 6734284008372059011164505)
      ·
        refine ⟨5050713006279044258373379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6734284008372059011164505 5050713006279044258373379)
        ·
          refine ⟨7576069509418566387560069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5050713006279044258373379 7576069509418566387560069)
          ·
            refine ⟨1420513033015981197667513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7576069509418566387560069 1420513033015981197667513)
            ·
              refine ⟨1065384774761985898250635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420513033015981197667513 1065384774761985898250635)
              ·
                refine ⟨1598077162142978847375953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065384774761985898250635 1598077162142978847375953)
                ·
                  refine ⟨1198557871607234135531965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1598077162142978847375953 1198557871607234135531965)
                  ·
                    refine ⟨449459201852712800824487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198557871607234135531965 449459201852712800824487)
                    ·
                      rfl

theorem cell22_1312978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_1312978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1312978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1312978 prefixEnd_1312978 := by exact prefixLift 1312978
  have htrace : WordTrace (prefixWord ++ tailWord_1312978) baseStart_1312978 baseEnd_1312978 := by
    simpa [prefixWord, tailWord_1312978, baseEnd_1312978] using wordTrace_append hprefix tailTrace_1312978
  have hstable : (prefixWord ++ tailWord_1312978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1312978).length < 2 ^ (prefixWord ++ tailWord_1312978).sum := by decide
  have hdescent : baseEnd_1312978 < baseStart_1312978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1312978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313006 : List Nat := [4, 1, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_1313006 : Nat := 118140960795 + 1313006 * 2 ^ 59
def prefixEnd_1313006 : Nat := 4983230072969 + 3 ^ 40 * 1313006 * 2
def baseEnd_1313006 : Nat := 449468786824930061124401

theorem tailTrace_1313006 : CollatzResearch.WordTrace tailWord_1313006 prefixEnd_1313006 449468786824930061124401 := by
  unfold tailWord_1313006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5986157885151372552120859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31926175387473986944644581 5986157885151372552120859)
  ·
    refine ⟨8979236827727058828181289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5986157885151372552120859 8979236827727058828181289)
    ·
      refine ⟨6734427620795294121135967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8979236827727058828181289 6734427620795294121135967)
      ·
        refine ⟨10101641431192941181703951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6734427620795294121135967 10101641431192941181703951)
        ·
          refine ⟨15152462146789411772555927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10101641431192941181703951 15152462146789411772555927)
          ·
            refine ⟨22728693220184117658833891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15152462146789411772555927 22728693220184117658833891)
            ·
              refine ⟨34093039830276176488250837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22728693220184117658833891 34093039830276176488250837)
              ·
                refine ⟨799055621022097886443379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34093039830276176488250837 799055621022097886443379)
                ·
                  refine ⟨1198583431533146829665069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799055621022097886443379 1198583431533146829665069)
                  ·
                    refine ⟨449468786824930061124401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198583431533146829665069 449468786824930061124401)
                    ·
                      rfl

theorem cell22_1313006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_1313006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313006 prefixEnd_1313006 := by exact prefixLift 1313006
  have htrace : WordTrace (prefixWord ++ tailWord_1313006) baseStart_1313006 baseEnd_1313006 := by
    simpa [prefixWord, tailWord_1313006, baseEnd_1313006] using wordTrace_append hprefix tailTrace_1313006
  have hstable : (prefixWord ++ tailWord_1313006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313006).length < 2 ^ (prefixWord ++ tailWord_1313006).sum := by decide
  have hdescent : baseEnd_1313006 < baseStart_1313006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313047 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 8]
def baseStart_1313047 : Nat := 118140960795 + 1313047 * 2 ^ 59
def prefixEnd_1313047 : Nat := 4983230072969 + 3 ^ 40 * 1313047 * 2
def baseEnd_1313047 : Nat := 149827607320939873616425

theorem tailTrace_1313047 : CollatzResearch.WordTrace tailWord_1313047 prefixEnd_1313047 149827607320939873616425 := by
  unfold tailWord_1313047
  simp only [CollatzResearch.WordTrace]
  refine ⟨47890758474062444419209395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31927172316041629612806263 47890758474062444419209395)
  ·
    refine ⟨71836137711093666628814093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47890758474062444419209395 71836137711093666628814093)
    ·
      refine ⟨26938551641660124985805285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71836137711093666628814093 26938551641660124985805285)
      ·
        refine ⟨5050978432811273434838491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26938551641660124985805285 5050978432811273434838491)
        ·
          refine ⟨7576467649216910152257737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5050978432811273434838491 7576467649216910152257737)
          ·
            refine ⟨5682350736912682614193303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7576467649216910152257737 5682350736912682614193303)
            ·
              refine ⟨8523526105369023921289955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5682350736912682614193303 8523526105369023921289955)
              ·
                refine ⟨12785289158053535881934933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8523526105369023921289955 12785289158053535881934933)
                ·
                  refine ⟨149827607320939873616425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12785289158053535881934933 149827607320939873616425)
                  ·
                    rfl

theorem cell22_1313047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 8].length) (baseStart_1313047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313047 prefixEnd_1313047 := by exact prefixLift 1313047
  have htrace : WordTrace (prefixWord ++ tailWord_1313047) baseStart_1313047 baseEnd_1313047 := by
    simpa [prefixWord, tailWord_1313047, baseEnd_1313047] using wordTrace_append hprefix tailTrace_1313047
  have hstable : (prefixWord ++ tailWord_1313047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313047).length < 2 ^ (prefixWord ++ tailWord_1313047).sum := by decide
  have hdescent : baseEnd_1313047 < baseStart_1313047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313070 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_1313070 : Nat := 118140960795 + 1313070 * 2 ^ 59
def prefixEnd_1313070 : Nat := 4983230072969 + 3 ^ 40 * 1313070 * 2
def baseEnd_1313070 : Nat := 149830231777618409174735

theorem tailTrace_1313070 : CollatzResearch.WordTrace tailWord_1313070 prefixEnd_1313070 149830231777618409174735 := by
  unfold tailWord_1313070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5986449669122389918412083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31927731568652746231531109 5986449669122389918412083)
  ·
    refine ⟨8979674503683584877618125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5986449669122389918412083 8979674503683584877618125)
    ·
      refine ⟨3367377938881344329106797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8979674503683584877618125 3367377938881344329106797)
      ·
        refine ⟨1262766727080504123415049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3367377938881344329106797 1262766727080504123415049)
        ·
          refine ⟨947075045310378092561287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1262766727080504123415049 947075045310378092561287)
          ·
            refine ⟨1420612567965567138841931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947075045310378092561287 1420612567965567138841931)
            ·
              refine ⟨2130918851948350708262897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420612567965567138841931 2130918851948350708262897)
              ·
                refine ⟨1598189138961263031197173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130918851948350708262897 1598189138961263031197173)
                ·
                  refine ⟨149830231777618409174735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1598189138961263031197173 149830231777618409174735)
                  ·
                    rfl

theorem cell22_1313070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_1313070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313070 prefixEnd_1313070 := by exact prefixLift 1313070
  have htrace : WordTrace (prefixWord ++ tailWord_1313070) baseStart_1313070 baseEnd_1313070 := by
    simpa [prefixWord, tailWord_1313070, baseEnd_1313070] using wordTrace_append hprefix tailTrace_1313070
  have hstable : (prefixWord ++ tailWord_1313070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313070).length < 2 ^ (prefixWord ++ tailWord_1313070).sum := by decide
  have hdescent : baseEnd_1313070 < baseStart_1313070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313081 : List Nat := [1, 2, 1, 6, 1, 1, 2, 4, 4]
def baseStart_1313081 : Nat := 118140960795 + 1313081 * 2 ^ 59
def prefixEnd_1313081 : Nat := 4983230072969 + 3 ^ 40 * 1313081 * 2
def baseEnd_1313081 : Nat := 149831486952551621833057

theorem tailTrace_1313081 : CollatzResearch.WordTrace tailWord_1313081 prefixEnd_1313081 149831486952551621833057 := by
  unfold tailWord_1313081
  simp only [CollatzResearch.WordTrace]
  refine ⟨47891998555939268225947097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31927999037292845483964731 47891998555939268225947097)
  ·
    refine ⟨35918998916954451169460323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47891998555939268225947097 35918998916954451169460323)
    ·
      refine ⟨53878498375431676754190485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35918998916954451169460323 53878498375431676754190485)
      ·
        refine ⟨2525554611348359847852679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53878498375431676754190485 2525554611348359847852679)
        ·
          refine ⟨3788331917022539771779019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525554611348359847852679 3788331917022539771779019)
          ·
            refine ⟨5682497875533809657668529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788331917022539771779019 5682497875533809657668529)
            ·
              refine ⟨4261873406650357243251397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5682497875533809657668529 4261873406650357243251397)
              ·
                refine ⟨799101263746941983109637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4261873406650357243251397 799101263746941983109637)
                ·
                  refine ⟨149831486952551621833057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 799101263746941983109637 149831486952551621833057)
                  ·
                    rfl

theorem cell22_1313081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 4].length) (baseStart_1313081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313081 prefixEnd_1313081 := by exact prefixLift 1313081
  have htrace : WordTrace (prefixWord ++ tailWord_1313081) baseStart_1313081 baseEnd_1313081 := by
    simpa [prefixWord, tailWord_1313081, baseEnd_1313081] using wordTrace_append hprefix tailTrace_1313081
  have hstable : (prefixWord ++ tailWord_1313081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313081).length < 2 ^ (prefixWord ++ tailWord_1313081).sum := by decide
  have hdescent : baseEnd_1313081 < baseStart_1313081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313109 : List Nat := [1, 3, 2, 2, 4, 1, 1, 8]
def baseStart_1313109 : Nat := 118140960795 + 1313109 * 2 ^ 59
def prefixEnd_1313109 : Nat := 4983230072969 + 3 ^ 40 * 1313109 * 2
def baseEnd_1313109 : Nat := 49944893981096902866565

theorem tailTrace_1313109 : CollatzResearch.WordTrace tailWord_1313109 prefixEnd_1313109 49944893981096902866565 := by
  unfold tailWord_1313109
  simp only [CollatzResearch.WordTrace]
  refine ⟨47893019799837829007966381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31928679866558552671977587 47893019799837829007966381)
  ·
    refine ⟨17959882424939185877987393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47893019799837829007966381 17959882424939185877987393)
    ·
      refine ⟨13469911818704389408490545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17959882424939185877987393 13469911818704389408490545)
      ·
        refine ⟨10102433864028292056367909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13469911818704389408490545 10102433864028292056367909)
        ·
          refine ⟨1894206349505304760568983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10102433864028292056367909 1894206349505304760568983)
          ·
            refine ⟨2841309524257957140853475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894206349505304760568983 2841309524257957140853475)
            ·
              refine ⟨4261964286386935711280213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841309524257957140853475 4261964286386935711280213)
              ·
                refine ⟨49944893981096902866565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4261964286386935711280213 49944893981096902866565)
                ·
                  rfl

theorem cell22_1313109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 8].length) (baseStart_1313109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313109 prefixEnd_1313109 := by exact prefixLift 1313109
  have htrace : WordTrace (prefixWord ++ tailWord_1313109) baseStart_1313109 baseEnd_1313109 := by
    simpa [prefixWord, tailWord_1313109, baseEnd_1313109] using wordTrace_append hprefix tailTrace_1313109
  have hstable : (prefixWord ++ tailWord_1313109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313109).length < 2 ^ (prefixWord ++ tailWord_1313109).sum := by decide
  have hdescent : baseEnd_1313109 < baseStart_1313109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313192 : List Nat := [2, 1, 6, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1313192 : Nat := 118140960795 + 1313192 * 2 ^ 59
def prefixEnd_1313192 : Nat := 4983230072969 + 3 ^ 40 * 1313192 * 2
def baseEnd_1313192 : Nat := 449532458426087575973831

theorem tailTrace_1313192 : CollatzResearch.WordTrace tailWord_1313192 prefixEnd_1313192 449532458426087575973831 := by
  unfold tailWord_1313192
  simp only [CollatzResearch.WordTrace]
  refine ⟨23948023529268567091618915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31930698039024756122158553 23948023529268567091618915)
  ·
    refine ⟨35922035293902850637428373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23948023529268567091618915 35922035293902850637428373)
    ·
      refine ⟨1683845404401696123629455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35922035293902850637428373 1683845404401696123629455)
      ·
        refine ⟨2525768106602544185444183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683845404401696123629455 2525768106602544185444183)
        ·
          refine ⟨3788652159903816278166275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525768106602544185444183 3788652159903816278166275)
          ·
            refine ⟨5682978239855724417249413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788652159903816278166275 5682978239855724417249413)
            ·
              refine ⟨1065558419972948328234265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5682978239855724417249413 1065558419972948328234265)
              ·
                refine ⟨799168814979711246175699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065558419972948328234265 799168814979711246175699)
                ·
                  refine ⟨1198753222469566869263549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799168814979711246175699 1198753222469566869263549)
                  ·
                    refine ⟨449532458426087575973831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198753222469566869263549 449532458426087575973831)
                    ·
                      rfl

theorem cell22_1313192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1313192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313192 prefixEnd_1313192 := by exact prefixLift 1313192
  have htrace : WordTrace (prefixWord ++ tailWord_1313192) baseStart_1313192 baseEnd_1313192 := by
    simpa [prefixWord, tailWord_1313192, baseEnd_1313192] using wordTrace_append hprefix tailTrace_1313192
  have hstable : (prefixWord ++ tailWord_1313192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313192).length < 2 ^ (prefixWord ++ tailWord_1313192).sum := by decide
  have hdescent : baseEnd_1313192 < baseStart_1313192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313250 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1313250 : Nat := 118140960795 + 1313250 * 2 ^ 59
def prefixEnd_1313250 : Nat := 4983230072969 + 3 ^ 40 * 1313250 * 2
def baseEnd_1313250 : Nat := 149850771003798252674551

theorem tailTrace_1313250 : CollatzResearch.WordTrace tailWord_1313250 prefixEnd_1313250 149850771003798252674551 := by
  unfold tailWord_1313250
  simp only [CollatzResearch.WordTrace]
  refine ⟨11974540623081752522212301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31932108328218006725899469 11974540623081752522212301)
  ·
    refine ⟨4490452733655657195829613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11974540623081752522212301 4490452733655657195829613)
    ·
      refine ⟨1683919775120871448436105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4490452733655657195829613 1683919775120871448436105)
      ·
        refine ⟨1262939831340653586327079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683919775120871448436105 1262939831340653586327079)
        ·
          refine ⟨1894409747010980379490619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262939831340653586327079 1894409747010980379490619)
          ·
            refine ⟨2841614620516470569235929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894409747010980379490619 2841614620516470569235929)
            ·
              refine ⟨2131210965387352926926947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841614620516470569235929 2131210965387352926926947)
              ·
                refine ⟨3196816448081029390390421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131210965387352926926947 3196816448081029390390421)
                ·
                  refine ⟨149850771003798252674551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3196816448081029390390421 149850771003798252674551)
                  ·
                    rfl

theorem cell22_1313250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1313250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313250 prefixEnd_1313250 := by exact prefixLift 1313250
  have htrace : WordTrace (prefixWord ++ tailWord_1313250) baseStart_1313250 baseEnd_1313250 := by
    simpa [prefixWord, tailWord_1313250, baseEnd_1313250] using wordTrace_append hprefix tailTrace_1313250
  have hstable : (prefixWord ++ tailWord_1313250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313250).length < 2 ^ (prefixWord ++ tailWord_1313250).sum := by decide
  have hdescent : baseEnd_1313250 < baseStart_1313250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313336 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_1313336 : Nat := 118140960795 + 1313336 * 2 ^ 59
def prefixEnd_1313336 : Nat := 4983230072969 + 3 ^ 40 * 1313336 * 2
def baseEnd_1313336 : Nat := 449581752568919200373389

theorem tailTrace_1313336 : CollatzResearch.WordTrace tailWord_1313336 prefixEnd_1313336 449581752568919200373389 := by
  unfold tailWord_1313336
  simp only [CollatzResearch.WordTrace]
  refine ⟨23950649585007723388239931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31934199446676964517653241 23950649585007723388239931)
  ·
    refine ⟨35925974377511585082359897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23950649585007723388239931 35925974377511585082359897)
    ·
      refine ⟨26944480783133688811769923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35925974377511585082359897 26944480783133688811769923)
      ·
        refine ⟨40416721174700533217654885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26944480783133688811769923 40416721174700533217654885)
        ·
          refine ⟨7578135220256349978310291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40416721174700533217654885 7578135220256349978310291)
          ·
            refine ⟨11367202830384524967465437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7578135220256349978310291 11367202830384524967465437)
            ·
              refine ⟨4262701061394196862799539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11367202830384524967465437 4262701061394196862799539)
              ·
                refine ⟨6394051592091295294199309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262701061394196862799539 6394051592091295294199309)
                ·
                  refine ⟨2397769347034235735324741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6394051592091295294199309 2397769347034235735324741)
                  ·
                    refine ⟨449581752568919200373389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2397769347034235735324741 449581752568919200373389)
                    ·
                      rfl

theorem cell22_1313336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_1313336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313336 prefixEnd_1313336 := by exact prefixLift 1313336
  have htrace : WordTrace (prefixWord ++ tailWord_1313336) baseStart_1313336 baseEnd_1313336 := by
    simpa [prefixWord, tailWord_1313336, baseEnd_1313336] using wordTrace_append hprefix tailTrace_1313336
  have hstable : (prefixWord ++ tailWord_1313336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313336).length < 2 ^ (prefixWord ++ tailWord_1313336).sum := by decide
  have hdescent : baseEnd_1313336 < baseStart_1313336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313434 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_1313434 : Nat := 118140960795 + 1313434 * 2 ^ 59
def prefixEnd_1313434 : Nat := 4983230072969 + 3 ^ 40 * 1313434 * 2
def baseEnd_1313434 : Nat := 449615299971679611423089

theorem tailTrace_1313434 : CollatzResearch.WordTrace tailWord_1313434 prefixEnd_1313434 449615299971679611423089 := by
  unfold tailWord_1313434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11976218380915102378386839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31936582349106939675698237 11976218380915102378386839)
  ·
    refine ⟨17964327571372653567580259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11976218380915102378386839 17964327571372653567580259)
    ·
      refine ⟨26946491357058980351370389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17964327571372653567580259 26946491357058980351370389)
      ·
        refine ⟨1263116782362139703970487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26946491357058980351370389 1263116782362139703970487)
        ·
          refine ⟨1894675173543209555955731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263116782362139703970487 1894675173543209555955731)
          ·
            refine ⟨2842012760314814333933597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894675173543209555955731 2842012760314814333933597)
            ·
              refine ⟨1065754785118055375225099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2842012760314814333933597 1065754785118055375225099)
              ·
                refine ⟨1598632177677083062837649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065754785118055375225099 1598632177677083062837649)
                ·
                  refine ⟨1198974133257812297128237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1598632177677083062837649 1198974133257812297128237)
                  ·
                    refine ⟨449615299971679611423089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1198974133257812297128237 449615299971679611423089)
                    ·
                      rfl

theorem cell22_1313434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_1313434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313434 prefixEnd_1313434 := by exact prefixLift 1313434
  have htrace : WordTrace (prefixWord ++ tailWord_1313434) baseStart_1313434 baseEnd_1313434 := by
    simpa [prefixWord, tailWord_1313434, baseEnd_1313434] using wordTrace_append hprefix tailTrace_1313434
  have hstable : (prefixWord ++ tailWord_1313434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313434).length < 2 ^ (prefixWord ++ tailWord_1313434).sum := by decide
  have hdescent : baseEnd_1313434 < baseStart_1313434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313447 : List Nat := [1, 1, 6, 3, 1, 2, 2, 6]
def baseStart_1313447 : Nat := 118140960795 + 1313447 * 2 ^ 59
def prefixEnd_1313447 : Nat := 4983230072969 + 3 ^ 40 * 1313447 * 2
def baseEnd_1313447 : Nat := 49957750015261323427561

theorem tailTrace_1313447 : CollatzResearch.WordTrace tailWord_1313447 prefixEnd_1313447 49957750015261323427561 := by
  unfold tailWord_1313447
  simp only [CollatzResearch.WordTrace]
  refine ⟨47905347672613312733770595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31936898448408875155847063 47905347672613312733770595)
  ·
    refine ⟨71858021508919969100655893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47905347672613312733770595 71858021508919969100655893)
    ·
      refine ⟨3368344758230623551593245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71858021508919969100655893 3368344758230623551593245)
      ·
        refine ⟨1263129284336483831847467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3368344758230623551593245 1263129284336483831847467)
        ·
          refine ⟨1894693926504725747771201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263129284336483831847467 1894693926504725747771201)
          ·
            refine ⟨1421020444878544310828401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894693926504725747771201 1421020444878544310828401)
            ·
              refine ⟨1065765333658908233121301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421020444878544310828401 1065765333658908233121301)
              ·
                refine ⟨49957750015261323427561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1065765333658908233121301 49957750015261323427561)
                ·
                  rfl

theorem cell22_1313447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 6].length) (baseStart_1313447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313447 prefixEnd_1313447 := by exact prefixLift 1313447
  have htrace : WordTrace (prefixWord ++ tailWord_1313447) baseStart_1313447 baseEnd_1313447 := by
    simpa [prefixWord, tailWord_1313447, baseEnd_1313447] using wordTrace_append hprefix tailTrace_1313447
  have hstable : (prefixWord ++ tailWord_1313447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313447).length < 2 ^ (prefixWord ++ tailWord_1313447).sum := by decide
  have hdescent : baseEnd_1313447 < baseStart_1313447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313505 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1313505 : Nat := 118140960795 + 1313505 * 2 ^ 59
def prefixEnd_1313505 : Nat := 4983230072969 + 3 ^ 40 * 1313505 * 2
def baseEnd_1313505 : Nat := 449639604722659092897871

theorem tailTrace_1313505 : CollatzResearch.WordTrace tailWord_1313505 prefixEnd_1313505 449639604722659092897871 := by
  unfold tailWord_1313505
  simp only [CollatzResearch.WordTrace]
  refine ⟨47907463106403188639381969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31938308737602125759587979 47907463106403188639381969)
  ·
    refine ⟨35930597329802391479536477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47907463106403188639381969 35930597329802391479536477)
    ·
      refine ⟨13473973998675896804826179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35930597329802391479536477 13473973998675896804826179)
      ·
        refine ⟨20210960998013845207239269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13473973998675896804826179 20210960998013845207239269)
        ·
          refine ⟨3789555187127595976357363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20210960998013845207239269 3789555187127595976357363)
          ·
            refine ⟨5684332780691393964536045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789555187127595976357363 5684332780691393964536045)
            ·
              refine ⟨2131624792759272736701017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5684332780691393964536045 2131624792759272736701017)
              ·
                refine ⟨1598718594569454552525763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2131624792759272736701017 1598718594569454552525763)
                ·
                  refine ⟨2398077891854181828788645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598718594569454552525763 2398077891854181828788645)
                  ·
                    refine ⟨449639604722659092897871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398077891854181828788645 449639604722659092897871)
                    ·
                      rfl

theorem cell22_1313505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1313505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313505 prefixEnd_1313505 := by exact prefixLift 1313505
  have htrace : WordTrace (prefixWord ++ tailWord_1313505) baseStart_1313505 baseEnd_1313505 := by
    simpa [prefixWord, tailWord_1313505, baseEnd_1313505] using wordTrace_append hprefix tailTrace_1313505
  have hstable : (prefixWord ++ tailWord_1313505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313505).length < 2 ^ (prefixWord ++ tailWord_1313505).sum := by decide
  have hdescent : baseEnd_1313505 < baseStart_1313505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313518 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1313518 : Nat := 118140960795 + 1313518 * 2 ^ 59
def prefixEnd_1313518 : Nat := 4983230072969 + 3 ^ 40 * 1313518 * 2
def baseEnd_1313518 : Nat := 449644054888331392322831

theorem tailTrace_1313518 : CollatzResearch.WordTrace tailWord_1313518 prefixEnd_1313518 449644054888331392322831 := by
  unfold tailWord_1313518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988492156919511482450651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31938624836904061239736805 5988492156919511482450651)
  ·
    refine ⟨8982738235379267223675977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5988492156919511482450651 8982738235379267223675977)
    ·
      refine ⟨6737053676534450417756983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8982738235379267223675977 6737053676534450417756983)
      ·
        refine ⟨10105580514801675626635475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737053676534450417756983 10105580514801675626635475)
        ·
          refine ⟨15158370772202513439953213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10105580514801675626635475 15158370772202513439953213)
          ·
            refine ⟨5684389039575942539982455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15158370772202513439953213 5684389039575942539982455)
            ·
              refine ⟨8526583559363913809973683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5684389039575942539982455 8526583559363913809973683)
              ·
                refine ⟨12789875339045870714960525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8526583559363913809973683 12789875339045870714960525)
                ·
                  refine ⟨4796203252142201518110197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12789875339045870714960525 4796203252142201518110197)
                  ·
                    refine ⟨449644054888331392322831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4796203252142201518110197 449644054888331392322831)
                    ·
                      rfl

theorem cell22_1313518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1313518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313518 prefixEnd_1313518 := by exact prefixLift 1313518
  have htrace : WordTrace (prefixWord ++ tailWord_1313518) baseStart_1313518 baseEnd_1313518 := by
    simpa [prefixWord, tailWord_1313518, baseEnd_1313518] using wordTrace_append hprefix tailTrace_1313518
  have hstable : (prefixWord ++ tailWord_1313518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313518).length < 2 ^ (prefixWord ++ tailWord_1313518).sum := by decide
  have hdescent : baseEnd_1313518 < baseStart_1313518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313522 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_1313522 : Nat := 118140960795 + 1313522 * 2 ^ 59
def prefixEnd_1313522 : Nat := 4983230072969 + 3 ^ 40 * 1313522 * 2
def baseEnd_1313522 : Nat := 449645424170076715222819

theorem tailTrace_1313522 : CollatzResearch.WordTrace tailWord_1313522 prefixEnd_1313522 449645424170076715222819 := by
  unfold tailWord_1313522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977020786835400135687705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31938722098227733695167213 11977020786835400135687705)
  ·
    refine ⟨8982765590126550101765779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11977020786835400135687705 8982765590126550101765779)
    ·
      refine ⟨13474148385189825152648669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8982765590126550101765779 13474148385189825152648669)
      ·
        refine ⟨5052805644446184432243251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13474148385189825152648669 5052805644446184432243251)
        ·
          refine ⟨7579208466669276648364877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052805644446184432243251 7579208466669276648364877)
          ·
            refine ⟨2842203175000978743136829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7579208466669276648364877 2842203175000978743136829)
            ·
              refine ⟨1065826190625367028676311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2842203175000978743136829 1065826190625367028676311)
              ·
                refine ⟨1598739285938050543014467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065826190625367028676311 1598739285938050543014467)
                ·
                  refine ⟨2398108928907075814521701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598739285938050543014467 2398108928907075814521701)
                  ·
                    refine ⟨449645424170076715222819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398108928907075814521701 449645424170076715222819)
                    ·
                      rfl

theorem cell22_1313522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_1313522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313522 prefixEnd_1313522 := by exact prefixLift 1313522
  have htrace : WordTrace (prefixWord ++ tailWord_1313522) baseStart_1313522 baseEnd_1313522 := by
    simpa [prefixWord, tailWord_1313522, baseEnd_1313522] using wordTrace_append hprefix tailTrace_1313522
  have hstable : (prefixWord ++ tailWord_1313522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313522).length < 2 ^ (prefixWord ++ tailWord_1313522).sum := by decide
  have hdescent : baseEnd_1313522 < baseStart_1313522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313533 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_1313533 : Nat := 118140960795 + 1313533 * 2 ^ 59
def prefixEnd_1313533 : Nat := 4983230072969 + 3 ^ 40 * 1313533 * 2
def baseEnd_1313533 : Nat := 449649189694876353197785

theorem tailTrace_1313533 : CollatzResearch.WordTrace tailWord_1313533 prefixEnd_1313533 449649189694876353197785 := by
  unfold tailWord_1313533
  simp only [CollatzResearch.WordTrace]
  refine ⟨47908484350301749421401253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31938989566867832947600835 47908484350301749421401253)
  ·
    refine ⟨8982840815681578016512735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47908484350301749421401253 8982840815681578016512735)
    ·
      refine ⟨13474261223522367024769103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8982840815681578016512735 13474261223522367024769103)
      ·
        refine ⟨20211391835283550537153655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13474261223522367024769103 20211391835283550537153655)
        ·
          refine ⟨30317087752925325805730483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20211391835283550537153655 30317087752925325805730483)
          ·
            refine ⟨45475631629387988708595725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30317087752925325805730483 45475631629387988708595725)
            ·
              refine ⟨17053361861020495765723397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45475631629387988708595725 17053361861020495765723397)
              ·
                refine ⟨3197505348941342956073137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17053361861020495765723397 3197505348941342956073137)
                ·
                  refine ⟨2398129011706007217054853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3197505348941342956073137 2398129011706007217054853)
                  ·
                    refine ⟨449649189694876353197785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398129011706007217054853 449649189694876353197785)
                    ·
                      rfl

theorem cell22_1313533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_1313533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313533 prefixEnd_1313533 := by exact prefixLift 1313533
  have htrace : WordTrace (prefixWord ++ tailWord_1313533) baseStart_1313533 baseEnd_1313533 := by
    simpa [prefixWord, tailWord_1313533, baseEnd_1313533] using wordTrace_append hprefix tailTrace_1313533
  have hstable : (prefixWord ++ tailWord_1313533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313533).length < 2 ^ (prefixWord ++ tailWord_1313533).sum := by decide
  have hdescent : baseEnd_1313533 < baseStart_1313533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313608 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_1313608 : Nat := 118140960795 + 1313608 * 2 ^ 59
def prefixEnd_1313608 : Nat := 4983230072969 + 3 ^ 40 * 1313608 * 2
def baseEnd_1313608 : Nat := 449674863727601157572555

theorem tailTrace_1313608 : CollatzResearch.WordTrace tailWord_1313608 prefixEnd_1313608 449674863727601157572555 := by
  unfold tailWord_1313608
  simp only [CollatzResearch.WordTrace]
  refine ⟨23955609912515018615190739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31940813216686691486920985 23955609912515018615190739)
  ·
    refine ⟨35933414868772527922786109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23955609912515018615190739 35933414868772527922786109)
    ·
      refine ⟨13475030575789697971044791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35933414868772527922786109 13475030575789697971044791)
      ·
        refine ⟨20212545863684546956567187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13475030575789697971044791 20212545863684546956567187)
        ·
          refine ⟨30318818795526820434850781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20212545863684546956567187 30318818795526820434850781)
          ·
            refine ⟨11369557048322557663069043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30318818795526820434850781 11369557048322557663069043)
            ·
              refine ⟨17054335572483836494603565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11369557048322557663069043 17054335572483836494603565)
              ·
                refine ⟨6395375839681438685476337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17054335572483836494603565 6395375839681438685476337)
                ·
                  refine ⟨4796531879761079014107253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6395375839681438685476337 4796531879761079014107253)
                  ·
                    refine ⟨449674863727601157572555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4796531879761079014107253 449674863727601157572555)
                    ·
                      rfl

theorem cell22_1313608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_1313608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313608 prefixEnd_1313608 := by exact prefixLift 1313608
  have htrace : WordTrace (prefixWord ++ tailWord_1313608) baseStart_1313608 baseEnd_1313608 := by
    simpa [prefixWord, tailWord_1313608, baseEnd_1313608] using wordTrace_append hprefix tailTrace_1313608
  have hstable : (prefixWord ++ tailWord_1313608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313608).length < 2 ^ (prefixWord ++ tailWord_1313608).sum := by decide
  have hdescent : baseEnd_1313608 < baseStart_1313608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313655 : List Nat := [1, 1, 3, 1, 1, 2, 1, 8, 4]
def baseStart_1313655 : Nat := 118140960795 + 1313655 * 2 ^ 59
def prefixEnd_1313655 : Nat := 4983230072969 + 3 ^ 40 * 1313655 * 2
def baseEnd_1313655 : Nat := 149896984262702900549137

theorem tailTrace_1313655 : CollatzResearch.WordTrace tailWord_1313655 prefixEnd_1313655 149896984262702900549137 := by
  unfold tailWord_1313655
  simp only [CollatzResearch.WordTrace]
  refine ⟨47912934055859764257342419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31941956037239842838228279 47912934055859764257342419)
  ·
    refine ⟨71869401083789646386013629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47912934055859764257342419 71869401083789646386013629)
    ·
      refine ⟨26951025406421117394755111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71869401083789646386013629 26951025406421117394755111)
      ·
        refine ⟨40426538109631676092132667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26951025406421117394755111 40426538109631676092132667)
        ·
          refine ⟨60639807164447514138199001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40426538109631676092132667 60639807164447514138199001)
          ·
            refine ⟨45479855373335635603649251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60639807164447514138199001 45479855373335635603649251)
            ·
              refine ⟨68219783060003453405473877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45479855373335635603649251 68219783060003453405473877)
              ·
                refine ⟨799450582734415469595397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 68219783060003453405473877 799450582734415469595397)
                ·
                  refine ⟨149896984262702900549137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 799450582734415469595397 149896984262702900549137)
                  ·
                    rfl

theorem cell22_1313655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 4].length) (baseStart_1313655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313655 prefixEnd_1313655 := by exact prefixLift 1313655
  have htrace : WordTrace (prefixWord ++ tailWord_1313655) baseStart_1313655 baseEnd_1313655 := by
    simpa [prefixWord, tailWord_1313655, baseEnd_1313655] using wordTrace_append hprefix tailTrace_1313655
  have hstable : (prefixWord ++ tailWord_1313655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313655).length < 2 ^ (prefixWord ++ tailWord_1313655).sum := by decide
  have hdescent : baseEnd_1313655 < baseStart_1313655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313674 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_1313674 : Nat := 118140960795 + 1313674 * 2 ^ 59
def prefixEnd_1313674 : Nat := 4983230072969 + 3 ^ 40 * 1313674 * 2
def baseEnd_1313674 : Nat := 449697456876398985422353

theorem tailTrace_1313674 : CollatzResearch.WordTrace tailWord_1313674 prefixEnd_1313674 449697456876398985422353 := by
  unfold tailWord_1313674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11978406760697732625571019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31942418028527287001522717 11978406760697732625571019)
  ·
    refine ⟨17967610141046598938356529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11978406760697732625571019 17967610141046598938356529)
    ·
      refine ⟨13475707605784949203767397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17967610141046598938356529 13475707605784949203767397)
      ·
        refine ⟨2526695176084677975706387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13475707605784949203767397 2526695176084677975706387)
        ·
          refine ⟨3790042764127016963559581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526695176084677975706387 3790042764127016963559581)
          ·
            refine ⟨1421266036547631361334843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3790042764127016963559581 1421266036547631361334843)
            ·
              refine ⟨2131899054821447042002265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421266036547631361334843 2131899054821447042002265)
              ·
                refine ⟨1598924291116085281501699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2131899054821447042002265 1598924291116085281501699)
                ·
                  refine ⟨2398386436674127922252549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598924291116085281501699 2398386436674127922252549)
                  ·
                    refine ⟨449697456876398985422353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398386436674127922252549 449697456876398985422353)
                    ·
                      rfl

theorem cell22_1313674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_1313674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313674 prefixEnd_1313674 := by exact prefixLift 1313674
  have htrace : WordTrace (prefixWord ++ tailWord_1313674) baseStart_1313674 baseEnd_1313674 := by
    simpa [prefixWord, tailWord_1313674, baseEnd_1313674] using wordTrace_append hprefix tailTrace_1313674
  have hstable : (prefixWord ++ tailWord_1313674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313674).length < 2 ^ (prefixWord ++ tailWord_1313674).sum := by decide
  have hdescent : baseEnd_1313674 < baseStart_1313674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313685 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1313685 : Nat := 118140960795 + 1313685 * 2 ^ 59
def prefixEnd_1313685 : Nat := 4983230072969 + 3 ^ 40 * 1313685 * 2
def baseEnd_1313685 : Nat := 449701222401198623397319

theorem tailTrace_1313685 : CollatzResearch.WordTrace tailWord_1313685 prefixEnd_1313685 449701222401198623397319 := by
  unfold tailWord_1313685
  simp only [CollatzResearch.WordTrace]
  refine ⟨47914028245751079380934509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31942685497167386253956339 47914028245751079380934509)
  ·
    refine ⟨17967760592156654767850441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47914028245751079380934509 17967760592156654767850441)
    ·
      refine ⟨13475820444117491075887831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17967760592156654767850441 13475820444117491075887831)
      ·
        refine ⟨20213730666176236613831747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13475820444117491075887831 20213730666176236613831747)
        ·
          refine ⟨30320595999264354920747621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20213730666176236613831747 30320595999264354920747621)
          ·
            refine ⟨5685111749862066547640179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30320595999264354920747621 5685111749862066547640179)
            ·
              refine ⟨8527667624793099821460269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685111749862066547640179 8527667624793099821460269)
              ·
                refine ⟨3197875359297412433047601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8527667624793099821460269 3197875359297412433047601)
                ·
                  refine ⟨2398406519473059324785701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3197875359297412433047601 2398406519473059324785701)
                  ·
                    refine ⟨449701222401198623397319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398406519473059324785701 449701222401198623397319)
                    ·
                      rfl

theorem cell22_1313685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1313685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313685 prefixEnd_1313685 := by exact prefixLift 1313685
  have htrace : WordTrace (prefixWord ++ tailWord_1313685) baseStart_1313685 baseEnd_1313685 := by
    simpa [prefixWord, tailWord_1313685, baseEnd_1313685] using wordTrace_append hprefix tailTrace_1313685
  have hstable : (prefixWord ++ tailWord_1313685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313685).length < 2 ^ (prefixWord ++ tailWord_1313685).sum := by decide
  have hdescent : baseEnd_1313685 < baseStart_1313685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313835 : List Nat := [1, 1, 1, 1, 2, 1, 8, 7]
def baseStart_1313835 : Nat := 118140960795 + 1313835 * 2 ^ 59
def prefixEnd_1313835 : Nat := 4983230072969 + 3 ^ 40 * 1313835 * 2
def baseEnd_1313835 : Nat := 49972507829627581349651

theorem tailTrace_1313835 : CollatzResearch.WordTrace tailWord_1313835 prefixEnd_1313835 49972507829627581349651 := by
  unfold tailWord_1313835
  simp only [CollatzResearch.WordTrace]
  refine ⟨47919499195207654998894959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31946332796805103332596639 47919499195207654998894959)
  ·
    refine ⟨71879248792811482498342439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47919499195207654998894959 71879248792811482498342439)
    ·
      refine ⟨107818873189217223747513659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71879248792811482498342439 107818873189217223747513659)
      ·
        refine ⟨161728309783825835621270489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107818873189217223747513659 161728309783825835621270489)
        ·
          refine ⟨121296232337869376715952867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161728309783825835621270489 121296232337869376715952867)
          ·
            refine ⟨181944348506804065073929301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121296232337869376715952867 181944348506804065073929301)
            ·
              refine ⟨2132160334064110137585109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 181944348506804065073929301 2132160334064110137585109)
              ·
                refine ⟨49972507829627581349651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2132160334064110137585109 49972507829627581349651)
                ·
                  rfl

theorem cell22_1313835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 7].length) (baseStart_1313835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313835 prefixEnd_1313835 := by exact prefixLift 1313835
  have htrace : WordTrace (prefixWord ++ tailWord_1313835) baseStart_1313835 baseEnd_1313835 := by
    simpa [prefixWord, tailWord_1313835, baseEnd_1313835] using wordTrace_append hprefix tailTrace_1313835
  have hstable : (prefixWord ++ tailWord_1313835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313835).length < 2 ^ (prefixWord ++ tailWord_1313835).sum := by decide
  have hdescent : baseEnd_1313835 < baseStart_1313835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313850 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_1313850 : Nat := 118140960795 + 1313850 * 2 ^ 59
def prefixEnd_1313850 : Nat := 4983230072969 + 3 ^ 40 * 1313850 * 2
def baseEnd_1313850 : Nat := 449757705273193193021813

theorem tailTrace_1313850 : CollatzResearch.WordTrace tailWord_1313850 prefixEnd_1313850 449757705273193193021813 := by
  unfold tailWord_1313850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980011572538328140172751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31946697526768875040460669 11980011572538328140172751)
  ·
    refine ⟨17970017358807492210259127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11980011572538328140172751 17970017358807492210259127)
    ·
      refine ⟨26955026038211238315388691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17970017358807492210259127 26955026038211238315388691)
      ·
        refine ⟨40432539057316857473083037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26955026038211238315388691 40432539057316857473083037)
        ·
          refine ⟨15162202146493821552406139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40432539057316857473083037 15162202146493821552406139)
          ·
            refine ⟨22743303219740732328609209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15162202146493821552406139 22743303219740732328609209)
            ·
              refine ⟨17057477414805549246456907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22743303219740732328609209 17057477414805549246456907)
              ·
                refine ⟨25586216122208323869685361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17057477414805549246456907 25586216122208323869685361)
                ·
                  refine ⟨19189662091656242902264021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25586216122208323869685361 19189662091656242902264021)
                  ·
                    refine ⟨449757705273193193021813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19189662091656242902264021 449757705273193193021813)
                    ·
                      rfl

theorem cell22_1313850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_1313850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313850 prefixEnd_1313850 := by exact prefixLift 1313850
  have htrace : WordTrace (prefixWord ++ tailWord_1313850) baseStart_1313850 baseEnd_1313850 := by
    simpa [prefixWord, tailWord_1313850, baseEnd_1313850] using wordTrace_append hprefix tailTrace_1313850
  have hstable : (prefixWord ++ tailWord_1313850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313850).length < 2 ^ (prefixWord ++ tailWord_1313850).sum := by decide
  have hdescent : baseEnd_1313850 < baseStart_1313850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313854 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1313854 : Nat := 118140960795 + 1313854 * 2 ^ 59
def prefixEnd_1313854 : Nat := 4983230072969 + 3 ^ 40 * 1313854 * 2
def baseEnd_1313854 : Nat := 449759074554938515921801

theorem tailTrace_1313854 : CollatzResearch.WordTrace tailWord_1313854 prefixEnd_1313854 449759074554938515921801 := by
  unfold tailWord_1313854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5990024022767352655479577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31946794788092547495891077 5990024022767352655479577)
  ·
    refine ⟨4492518017075514491609683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5990024022767352655479577 4492518017075514491609683)
    ·
      refine ⟨6738777025613271737414525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4492518017075514491609683 6738777025613271737414525)
      ·
        refine ⟨2527041384604976901530447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6738777025613271737414525 2527041384604976901530447)
        ·
          refine ⟨3790562076907465352295671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527041384604976901530447 3790562076907465352295671)
          ·
            refine ⟨5685843115361198028443507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790562076907465352295671 5685843115361198028443507)
            ·
              refine ⟨8528764673041797042665261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685843115361198028443507 8528764673041797042665261)
              ·
                refine ⟨3198286752390673890999473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8528764673041797042665261 3198286752390673890999473)
                ·
                  refine ⟨2398715064293005418249605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3198286752390673890999473 2398715064293005418249605)
                  ·
                    refine ⟨449759074554938515921801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2398715064293005418249605 449759074554938515921801)
                    ·
                      rfl

theorem cell22_1313854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1313854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313854 prefixEnd_1313854 := by exact prefixLift 1313854
  have htrace : WordTrace (prefixWord ++ tailWord_1313854) baseStart_1313854 baseEnd_1313854 := by
    simpa [prefixWord, tailWord_1313854, baseEnd_1313854] using wordTrace_append hprefix tailTrace_1313854
  have hstable : (prefixWord ++ tailWord_1313854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313854).length < 2 ^ (prefixWord ++ tailWord_1313854).sum := by decide
  have hdescent : baseEnd_1313854 < baseStart_1313854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313884 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1313884 : Nat := 118140960795 + 1313884 * 2 ^ 59
def prefixEnd_1313884 : Nat := 4983230072969 + 3 ^ 40 * 1313884 * 2
def baseEnd_1313884 : Nat := 449769344168028437671709

theorem tailTrace_1313884 : CollatzResearch.WordTrace tailWord_1313884 prefixEnd_1313884 449769344168028437671709 := by
  unfold tailWord_1313884
  simp only [CollatzResearch.WordTrace]
  refine ⟨23960643186015068183714353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31947524248020090911619137 23960643186015068183714353)
  ·
    refine ⟨17970482389511301137785765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23960643186015068183714353 17970482389511301137785765)
    ·
      refine ⟨3369465448033368963334831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17970482389511301137785765 3369465448033368963334831)
      ·
        refine ⟨5054198172050053445002247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369465448033368963334831 5054198172050053445002247)
        ·
          refine ⟨7581297258075080167503371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5054198172050053445002247 7581297258075080167503371)
          ·
            refine ⟨11371945887112620251255057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581297258075080167503371 11371945887112620251255057)
            ·
              refine ⟨8528959415334465188441293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11371945887112620251255057 8528959415334465188441293)
              ·
                refine ⟨3198359780750424445665485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8528959415334465188441293 3198359780750424445665485)
                ·
                  refine ⟨1199384917781409167124557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3198359780750424445665485 1199384917781409167124557)
                  ·
                    refine ⟨449769344168028437671709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1199384917781409167124557 449769344168028437671709)
                    ·
                      rfl

theorem cell22_1313884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1313884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313884 prefixEnd_1313884 := by exact prefixLift 1313884
  have htrace : WordTrace (prefixWord ++ tailWord_1313884) baseStart_1313884 baseEnd_1313884 := by
    simpa [prefixWord, tailWord_1313884, baseEnd_1313884] using wordTrace_append hprefix tailTrace_1313884
  have hstable : (prefixWord ++ tailWord_1313884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313884).length < 2 ^ (prefixWord ++ tailWord_1313884).sum := by decide
  have hdescent : baseEnd_1313884 < baseStart_1313884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313886 : List Nat := [4, 4, 1, 1, 1, 1, 3, 7]
def baseStart_1313886 : Nat := 118140960795 + 1313886 * 2 ^ 59
def prefixEnd_1313886 : Nat := 4983230072969 + 3 ^ 40 * 1313886 * 2
def baseEnd_1313886 : Nat := 49974447645433455457967

theorem tailTrace_1313886 : CollatzResearch.WordTrace tailWord_1313886 prefixEnd_1313886 49974447645433455457967 := by
  unfold tailWord_1313886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5990169914752861338625189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31947572878681927139334341 5990169914752861338625189)
  ·
    refine ⟨1123156859016161500992223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5990169914752861338625189 1123156859016161500992223)
    ·
      refine ⟨1684735288524242251488335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123156859016161500992223 1684735288524242251488335)
      ·
        refine ⟨2527102932786363377232503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684735288524242251488335 2527102932786363377232503)
        ·
          refine ⟨3790654399179545065848755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527102932786363377232503 3790654399179545065848755)
          ·
            refine ⟨5685981598769317598773133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790654399179545065848755 5685981598769317598773133)
            ·
              refine ⟨2132243099538494099539925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5685981598769317598773133 2132243099538494099539925)
              ·
                refine ⟨49974447645433455457967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2132243099538494099539925 49974447645433455457967)
                ·
                  rfl

theorem cell22_1313886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_1313886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313886 prefixEnd_1313886 := by exact prefixLift 1313886
  have htrace : WordTrace (prefixWord ++ tailWord_1313886) baseStart_1313886 baseEnd_1313886 := by
    simpa [prefixWord, tailWord_1313886, baseEnd_1313886] using wordTrace_append hprefix tailTrace_1313886
  have hstable : (prefixWord ++ tailWord_1313886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313886).length < 2 ^ (prefixWord ++ tailWord_1313886).sum := by decide
  have hdescent : baseEnd_1313886 < baseStart_1313886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313897 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 5]
def baseStart_1313897 : Nat := 118140960795 + 1313897 * 2 ^ 59
def prefixEnd_1313897 : Nat := 4983230072969 + 3 ^ 40 * 1313897 * 2
def baseEnd_1313897 : Nat := 149924598111233579032223

theorem tailTrace_1313897 : CollatzResearch.WordTrace tailWord_1313897 prefixEnd_1313897 149924598111233579032223 := by
  unfold tailWord_1313897
  simp only [CollatzResearch.WordTrace]
  refine ⟨47921760520983039587651945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31947840347322026391767963 47921760520983039587651945)
  ·
    refine ⟨35941320390737279690738959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47921760520983039587651945 35941320390737279690738959)
    ·
      refine ⟨53911980586105919536108439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35941320390737279690738959 53911980586105919536108439)
      ·
        refine ⟨80867970879158879304162659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53911980586105919536108439 80867970879158879304162659)
        ·
          refine ⟨121301956318738318956243989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80867970879158879304162659 121301956318738318956243989)
          ·
            refine ⟨5686029202440858701073937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121301956318738318956243989 5686029202440858701073937)
            ·
              refine ⟨4264521901830644025805453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5686029202440858701073937 4264521901830644025805453)
              ·
                refine ⟨1599195713186491509677045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4264521901830644025805453 1599195713186491509677045)
                ·
                  refine ⟨149924598111233579032223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1599195713186491509677045 149924598111233579032223)
                  ·
                    rfl

theorem cell22_1313897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_1313897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313897 prefixEnd_1313897 := by exact prefixLift 1313897
  have htrace : WordTrace (prefixWord ++ tailWord_1313897) baseStart_1313897 baseEnd_1313897 := by
    simpa [prefixWord, tailWord_1313897, baseEnd_1313897] using wordTrace_append hprefix tailTrace_1313897
  have hstable : (prefixWord ++ tailWord_1313897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313897).length < 2 ^ (prefixWord ++ tailWord_1313897).sum := by decide
  have hdescent : baseEnd_1313897 < baseStart_1313897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313959 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 6]
def baseStart_1313959 : Nat := 118140960795 + 1313959 * 2 ^ 59
def prefixEnd_1313959 : Nat := 4983230072969 + 3 ^ 40 * 1313959 * 2
def baseEnd_1313959 : Nat := 149931672733584414015493

theorem tailTrace_1313959 : CollatzResearch.WordTrace tailWord_1313959 prefixEnd_1313959 149931672733584414015493 := by
  unfold tailWord_1313959
  simp only [CollatzResearch.WordTrace]
  refine ⟨47924021846758424176408931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31949347897838949450939287 47924021846758424176408931)
  ·
    refine ⟨71886032770137636264613397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47924021846758424176408931 71886032770137636264613397)
    ·
      refine ⟨3369657786100201699903753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71886032770137636264613397 3369657786100201699903753)
      ·
        refine ⟨2527243339575151274927815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369657786100201699903753 2527243339575151274927815)
        ·
          refine ⟨3790865009362726912391723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527243339575151274927815 3790865009362726912391723)
          ·
            refine ⟨5686297514044090368587585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790865009362726912391723 5686297514044090368587585)
            ·
              refine ⟨4264723135533067776440689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5686297514044090368587585 4264723135533067776440689)
              ·
                refine ⟨3198542351649800832330517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4264723135533067776440689 3198542351649800832330517)
                ·
                  refine ⟨149931672733584414015493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3198542351649800832330517 149931672733584414015493)
                  ·
                    rfl

theorem cell22_1313959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 6].length) (baseStart_1313959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1313959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1313959 prefixEnd_1313959 := by exact prefixLift 1313959
  have htrace : WordTrace (prefixWord ++ tailWord_1313959) baseStart_1313959 baseEnd_1313959 := by
    simpa [prefixWord, tailWord_1313959, baseEnd_1313959] using wordTrace_append hprefix tailTrace_1313959
  have hstable : (prefixWord ++ tailWord_1313959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313959).length < 2 ^ (prefixWord ++ tailWord_1313959).sum := by decide
  have hdescent : baseEnd_1313959 < baseStart_1313959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314049 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 5]
def baseStart_1314049 : Nat := 118140960795 + 1314049 * 2 ^ 59
def prefixEnd_1314049 : Nat := 4983230072969 + 3 ^ 40 * 1314049 * 2
def baseEnd_1314049 : Nat := 149941942346674335765401

theorem tailTrace_1314049 : CollatzResearch.WordTrace tailWord_1314049 prefixEnd_1314049 149941942346674335765401 := by
  unfold tailWord_1314049
  simp only [CollatzResearch.WordTrace]
  refine ⟨47927304416432369547185201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31951536277621579698123467 47927304416432369547185201)
  ·
    refine ⟨35945478312324277160388901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47927304416432369547185201 35945478312324277160388901)
    ·
      refine ⟨6739777183560801967572919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35945478312324277160388901 6739777183560801967572919)
      ·
        refine ⟨10109665775341202951359379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6739777183560801967572919 10109665775341202951359379)
        ·
          refine ⟨15164498663011804427039069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10109665775341202951359379 15164498663011804427039069)
          ·
            refine ⟨5686686998629426660139651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15164498663011804427039069 5686686998629426660139651)
            ·
              refine ⟨8530030497944139990209477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5686686998629426660139651 8530030497944139990209477)
              ·
                refine ⟨1599380718364526248164277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8530030497944139990209477 1599380718364526248164277)
                ·
                  refine ⟨149941942346674335765401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1599380718364526248164277 149941942346674335765401)
                  ·
                    rfl

theorem cell22_1314049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_1314049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314049 prefixEnd_1314049 := by exact prefixLift 1314049
  have htrace : WordTrace (prefixWord ++ tailWord_1314049) baseStart_1314049 baseEnd_1314049 := by
    simpa [prefixWord, tailWord_1314049, baseEnd_1314049] using wordTrace_append hprefix tailTrace_1314049
  have hstable : (prefixWord ++ tailWord_1314049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314049).length < 2 ^ (prefixWord ++ tailWord_1314049).sum := by decide
  have hdescent : baseEnd_1314049 < baseStart_1314049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314111 : List Nat := [1, 1, 2, 2, 4, 2, 2, 4, 4]
def baseStart_1314111 : Nat := 118140960795 + 1314111 * 2 ^ 59
def prefixEnd_1314111 : Nat := 4983230072969 + 3 ^ 40 * 1314111 * 2
def baseEnd_1314111 : Nat := 149949016969025170748671

theorem tailTrace_1314111 : CollatzResearch.WordTrace tailWord_1314111 prefixEnd_1314111 149949016969025170748671 := by
  unfold tailWord_1314111
  simp only [CollatzResearch.WordTrace]
  refine ⟨47929565742207754135942187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31953043828138502757294791 47929565742207754135942187)
  ·
    refine ⟨71894348613311631203913281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47929565742207754135942187 71894348613311631203913281)
    ·
      refine ⟨53920761459983723402934961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71894348613311631203913281 53920761459983723402934961)
      ·
        refine ⟨40440571094987792552201221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53920761459983723402934961 40440571094987792552201221)
        ·
          refine ⟨7582607080310211103537729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40440571094987792552201221 7582607080310211103537729)
          ·
            refine ⟨5686955310232658327653297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7582607080310211103537729 5686955310232658327653297)
            ·
              refine ⟨4265216482674493745739973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5686955310232658327653297 4265216482674493745739973)
              ·
                refine ⟨799728090501467577326245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4265216482674493745739973 799728090501467577326245)
                ·
                  refine ⟨149949016969025170748671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 799728090501467577326245 149949016969025170748671)
                  ·
                    rfl

theorem cell22_1314111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 4].length) (baseStart_1314111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314111 prefixEnd_1314111 := by exact prefixLift 1314111
  have htrace : WordTrace (prefixWord ++ tailWord_1314111) baseStart_1314111 baseEnd_1314111 := by
    simpa [prefixWord, tailWord_1314111, baseEnd_1314111] using wordTrace_append hprefix tailTrace_1314111
  have hstable : (prefixWord ++ tailWord_1314111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314111).length < 2 ^ (prefixWord ++ tailWord_1314111).sum := by decide
  have hdescent : baseEnd_1314111 < baseStart_1314111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314124 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1314124 : Nat := 118140960795 + 1314124 * 2 ^ 59
def prefixEnd_1314124 : Nat := 4983230072969 + 3 ^ 40 * 1314124 * 2
def baseEnd_1314124 : Nat := 449851501072747811670973

theorem tailTrace_1314124 : CollatzResearch.WordTrace tailWord_1314124 prefixEnd_1314124 449851501072747811670973 := by
  unfold tailWord_1314124
  simp only [CollatzResearch.WordTrace]
  refine ⟨23965019945580328678082713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31953359927440438237443617 23965019945580328678082713)
  ·
    refine ⟨17973764959185246508562035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23965019945580328678082713 17973764959185246508562035)
    ·
      refine ⟨26960647438777869762843053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17973764959185246508562035 26960647438777869762843053)
      ·
        refine ⟨10110242789541701161066145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26960647438777869762843053 10110242789541701161066145)
        ·
          refine ⟨7582682092156275870799609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10110242789541701161066145 7582682092156275870799609)
          ·
            refine ⟨5687011569117206903099707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7582682092156275870799609 5687011569117206903099707)
            ·
              refine ⟨8530517353675810354649561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5687011569117206903099707 8530517353675810354649561)
              ·
                refine ⟨6397888015256857765987171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8530517353675810354649561 6397888015256857765987171)
                ·
                  refine ⟨9596832022885286648980757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6397888015256857765987171 9596832022885286648980757)
                  ·
                    refine ⟨449851501072747811670973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9596832022885286648980757 449851501072747811670973)
                    ·
                      rfl

theorem cell22_1314124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1314124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314124 prefixEnd_1314124 := by exact prefixLift 1314124
  have htrace : WordTrace (prefixWord ++ tailWord_1314124) baseStart_1314124 baseEnd_1314124 := by
    simpa [prefixWord, tailWord_1314124, baseEnd_1314124] using wordTrace_append hprefix tailTrace_1314124
  have hstable : (prefixWord ++ tailWord_1314124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314124).length < 2 ^ (prefixWord ++ tailWord_1314124).sum := by decide
  have hdescent : baseEnd_1314124 < baseStart_1314124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314177 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1314177 : Nat := 118140960795 + 1314177 * 2 ^ 59
def prefixEnd_1314177 : Nat := 4983230072969 + 3 ^ 40 * 1314177 * 2
def baseEnd_1314177 : Nat := 449869644055873340095811

theorem tailTrace_1314177 : CollatzResearch.WordTrace tailWord_1314177 prefixEnd_1314177 449869644055873340095811 := by
  unfold tailWord_1314177
  simp only [CollatzResearch.WordTrace]
  refine ⟨47931972959968647407844785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31954648639979098271896523 47931972959968647407844785)
  ·
    refine ⟨35948979719976485555883589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47931972959968647407844785 35948979719976485555883589)
    ·
      refine ⟨6740433697495591041728173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35948979719976485555883589 6740433697495591041728173)
      ·
        refine ⟨2527662636560846640648065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6740433697495591041728173 2527662636560846640648065)
        ·
          refine ⟨1895746977420634980486049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2527662636560846640648065 1895746977420634980486049)
          ·
            refine ⟨1421810233065476235364537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895746977420634980486049 1421810233065476235364537)
            ·
              refine ⟨1066357674799107176523403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421810233065476235364537 1066357674799107176523403)
              ·
                refine ⟨1599536512198660764785105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066357674799107176523403 1599536512198660764785105)
                ·
                  refine ⟨1199652384148995573588829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1599536512198660764785105 1199652384148995573588829)
                  ·
                    refine ⟨449869644055873340095811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1199652384148995573588829 449869644055873340095811)
                    ·
                      rfl

theorem cell22_1314177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1314177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314177 prefixEnd_1314177 := by exact prefixLift 1314177
  have htrace : WordTrace (prefixWord ++ tailWord_1314177) baseStart_1314177 baseEnd_1314177 := by
    simpa [prefixWord, tailWord_1314177, baseEnd_1314177] using wordTrace_append hprefix tailTrace_1314177
  have hstable : (prefixWord ++ tailWord_1314177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314177).length < 2 ^ (prefixWord ++ tailWord_1314177).sum := by decide
  have hdescent : baseEnd_1314177 < baseStart_1314177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314199 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 4, 5]
def baseStart_1314199 : Nat := 118140960795 + 1314199 * 2 ^ 59
def prefixEnd_1314199 : Nat := 4983230072969 + 3 ^ 40 * 1314199 * 2
def baseEnd_1314199 : Nat := 449877175105472616045743

theorem tailTrace_1314199 : CollatzResearch.WordTrace tailWord_1314199 prefixEnd_1314199 449877175105472616045743 := by
  unfold tailWord_1314199
  simp only [CollatzResearch.WordTrace]
  refine ⟨47932775365888945165145651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31955183577259296776763767 47932775365888945165145651)
  ·
    refine ⟨71899163048833417747718477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47932775365888945165145651 71899163048833417747718477)
    ·
      refine ⟨26962186143312531655394429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71899163048833417747718477 26962186143312531655394429)
      ·
        refine ⟨10110819803742199370772911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26962186143312531655394429 10110819803742199370772911)
        ·
          refine ⟨15166229705613299056159367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10110819803742199370772911 15166229705613299056159367)
          ·
            refine ⟨22749344558419948584239051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15166229705613299056159367 22749344558419948584239051)
            ·
              refine ⟨34124016837629922876358577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22749344558419948584239051 34124016837629922876358577)
              ·
                refine ⟨25593012628222442157268933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34124016837629922876358577 25593012628222442157268933)
                ·
                  refine ⟨4798689867791707904487925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25593012628222442157268933 4798689867791707904487925)
                  ·
                    refine ⟨449877175105472616045743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4798689867791707904487925 449877175105472616045743)
                    ·
                      rfl

theorem cell22_1314199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_1314199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314199 prefixEnd_1314199 := by exact prefixLift 1314199
  have htrace : WordTrace (prefixWord ++ tailWord_1314199) baseStart_1314199 baseEnd_1314199 := by
    simpa [prefixWord, tailWord_1314199, baseEnd_1314199] using wordTrace_append hprefix tailTrace_1314199
  have hstable : (prefixWord ++ tailWord_1314199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314199).length < 2 ^ (prefixWord ++ tailWord_1314199).sum := by decide
  have hdescent : baseEnd_1314199 < baseStart_1314199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314261 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1314261 : Nat := 118140960795 + 1314261 * 2 ^ 59
def prefixEnd_1314261 : Nat := 4983230072969 + 3 ^ 40 * 1314261 * 2
def baseEnd_1314261 : Nat := 449898398972525120995553

theorem tailTrace_1314261 : CollatzResearch.WordTrace tailWord_1314261 prefixEnd_1314261 449898398972525120995553 := by
  unfold tailWord_1314261
  simp only [CollatzResearch.WordTrace]
  refine ⟨47935036691664329753902637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31956691127776219835935091 47935036691664329753902637)
  ·
    refine ⟨17975638759374123657713489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47935036691664329753902637 17975638759374123657713489)
    ·
      refine ⟨13481729069530592743285117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17975638759374123657713489 13481729069530592743285117)
      ·
        refine ⟨5055648401073972278731919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13481729069530592743285117 5055648401073972278731919)
        ·
          refine ⟨7583472601610958418097879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5055648401073972278731919 7583472601610958418097879)
          ·
            refine ⟨11375208902416437627146819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7583472601610958418097879 11375208902416437627146819)
            ·
              refine ⟨17062813353624656440720229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11375208902416437627146819 17062813353624656440720229)
              ·
                refine ⟨3199277503804623082635043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17062813353624656440720229 3199277503804623082635043)
                ·
                  refine ⟨4798916255706934623952565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199277503804623082635043 4798916255706934623952565)
                  ·
                    refine ⟨449898398972525120995553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4798916255706934623952565 449898398972525120995553)
                    ·
                      rfl

theorem cell22_1314261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1314261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314261 prefixEnd_1314261 := by exact prefixLift 1314261
  have htrace : WordTrace (prefixWord ++ tailWord_1314261) baseStart_1314261 baseEnd_1314261 := by
    simpa [prefixWord, tailWord_1314261, baseEnd_1314261] using wordTrace_append hprefix tailTrace_1314261
  have hstable : (prefixWord ++ tailWord_1314261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314261).length < 2 ^ (prefixWord ++ tailWord_1314261).sum := by decide
  have hdescent : baseEnd_1314261 < baseStart_1314261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314265 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 1, 4]
def baseStart_1314265 : Nat := 118140960795 + 1314265 * 2 ^ 59
def prefixEnd_1314265 : Nat := 4983230072969 + 3 ^ 40 * 1314265 * 2
def baseEnd_1314265 : Nat := 449899768254270443895541

theorem tailTrace_1314265 : CollatzResearch.WordTrace tailWord_1314265 prefixEnd_1314265 449899768254270443895541 := by
  unfold tailWord_1314265
  simp only [CollatzResearch.WordTrace]
  refine ⟨47935182583649838437048249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31956788389099892291365499 47935182583649838437048249)
  ·
    refine ⟨35951386937737378827786187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47935182583649838437048249 35951386937737378827786187)
    ·
      refine ⟨53927080406606068241679281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35951386937737378827786187 53927080406606068241679281)
      ·
        refine ⟨40445310304954551181259461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53927080406606068241679281 40445310304954551181259461)
        ·
          refine ⟨7583495682178978346486149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40445310304954551181259461 7583495682178978346486149)
          ·
            refine ⟨1421905440408558439966153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7583495682178978346486149 1421905440408558439966153)
            ·
              refine ⟨1066429080306418829974615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421905440408558439966153 1066429080306418829974615)
              ·
                refine ⟨1599643620459628244961923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066429080306418829974615 1599643620459628244961923)
                ·
                  refine ⟨2399465430689442367442885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599643620459628244961923 2399465430689442367442885)
                  ·
                    refine ⟨449899768254270443895541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2399465430689442367442885 449899768254270443895541)
                    ·
                      rfl

theorem cell22_1314265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 4].length) (baseStart_1314265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314265 prefixEnd_1314265 := by exact prefixLift 1314265
  have htrace : WordTrace (prefixWord ++ tailWord_1314265) baseStart_1314265 baseEnd_1314265 := by
    simpa [prefixWord, tailWord_1314265, baseEnd_1314265] using wordTrace_append hprefix tailTrace_1314265
  have hstable : (prefixWord ++ tailWord_1314265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314265).length < 2 ^ (prefixWord ++ tailWord_1314265).sum := by decide
  have hdescent : baseEnd_1314265 < baseStart_1314265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314276 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_1314276 : Nat := 118140960795 + 1314276 * 2 ^ 59
def prefixEnd_1314276 : Nat := 4983230072969 + 3 ^ 40 * 1314276 * 2
def baseEnd_1314276 : Nat := 449903533779070081870507

theorem tailTrace_1314276 : CollatzResearch.WordTrace tailWord_1314276 prefixEnd_1314276 449903533779070081870507 := by
  unfold tailWord_1314276
  simp only [CollatzResearch.WordTrace]
  refine ⟨23967791893304993657849341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31957055857739991543799121 23967791893304993657849341)
  ·
    refine ⟨8987921959989372621693503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23967791893304993657849341 8987921959989372621693503)
    ·
      refine ⟨13481882939984058932540255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8987921959989372621693503 13481882939984058932540255)
      ·
        refine ⟨20222824409976088398810383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13481882939984058932540255 20222824409976088398810383)
        ·
          refine ⟨30334236614964132598215575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20222824409976088398810383 30334236614964132598215575)
          ·
            refine ⟨45501354922446198897323363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30334236614964132598215575 45501354922446198897323363)
            ·
              refine ⟨68252032383669298345985045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45501354922446198897323363 68252032383669298345985045)
              ·
                refine ⟨3199314017984498359968049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68252032383669298345985045 3199314017984498359968049)
                ·
                  refine ⟨2399485513488373769976037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3199314017984498359968049 2399485513488373769976037)
                  ·
                    refine ⟨449903533779070081870507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2399485513488373769976037 449903533779070081870507)
                    ·
                      rfl

theorem cell22_1314276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_1314276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314276 prefixEnd_1314276 := by exact prefixLift 1314276
  have htrace : WordTrace (prefixWord ++ tailWord_1314276) baseStart_1314276 baseEnd_1314276 := by
    simpa [prefixWord, tailWord_1314276, baseEnd_1314276] using wordTrace_append hprefix tailTrace_1314276
  have hstable : (prefixWord ++ tailWord_1314276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314276).length < 2 ^ (prefixWord ++ tailWord_1314276).sum := by decide
  have hdescent : baseEnd_1314276 < baseStart_1314276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314293 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1314293 : Nat := 118140960795 + 1314293 * 2 ^ 59
def prefixEnd_1314293 : Nat := 4983230072969 + 3 ^ 40 * 1314293 * 2
def baseEnd_1314293 : Nat := 449909353226487704195455

theorem tailTrace_1314293 : CollatzResearch.WordTrace tailWord_1314293 prefixEnd_1314293 449909353226487704195455 := by
  unfold tailWord_1314293
  simp only [CollatzResearch.WordTrace]
  refine ⟨47936203827548399219067533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31957469218365599479378355 47936203827548399219067533)
  ·
    refine ⟨17976076435330649707150325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47936203827548399219067533 17976076435330649707150325)
    ·
      refine ⟨1685257165812248410045343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17976076435330649707150325 1685257165812248410045343)
      ·
        refine ⟨2527885748718372615068015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685257165812248410045343 2527885748718372615068015)
        ·
          refine ⟨3791828623077558922602023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527885748718372615068015 3791828623077558922602023)
          ·
            refine ⟨5687742934616338383903035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3791828623077558922602023 5687742934616338383903035)
            ·
              refine ⟨8531614401924507575854553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5687742934616338383903035 8531614401924507575854553)
              ·
                refine ⟨6398710801443380681890915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8531614401924507575854553 6398710801443380681890915)
                ·
                  refine ⟨9598066202165071022836373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6398710801443380681890915 9598066202165071022836373)
                  ·
                    refine ⟨449909353226487704195455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9598066202165071022836373 449909353226487704195455)
                    ·
                      rfl

theorem cell22_1314293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1314293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314293 prefixEnd_1314293 := by exact prefixLift 1314293
  have htrace : WordTrace (prefixWord ++ tailWord_1314293) baseStart_1314293 baseEnd_1314293 := by
    simpa [prefixWord, tailWord_1314293, baseEnd_1314293] using wordTrace_append hprefix tailTrace_1314293
  have hstable : (prefixWord ++ tailWord_1314293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314293).length < 2 ^ (prefixWord ++ tailWord_1314293).sum := by decide
  have hdescent : baseEnd_1314293 < baseStart_1314293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314308 : List Nat := [2, 3, 2, 3, 2, 1, 1, 8]
def baseStart_1314308 : Nat := 118140960795 + 1314308 * 2 ^ 59
def prefixEnd_1314308 : Nat := 4983230072969 + 3 ^ 40 * 1314308 * 2
def baseEnd_1314308 : Nat := 49990498670336962785601

theorem tailTrace_1314308 : CollatzResearch.WordTrace tailWord_1314308 prefixEnd_1314308 49990498670336962785601 := by
  unfold tailWord_1314308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23968375461247028390431789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31957833948329371187242385 23968375461247028390431789)
  ·
    refine ⟨8988140797967635646411921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23968375461247028390431789 8988140797967635646411921)
    ·
      refine ⟨6741105598475726734808941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8988140797967635646411921 6741105598475726734808941)
      ·
        refine ⟨2527914599428397525553353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6741105598475726734808941 2527914599428397525553353)
        ·
          refine ⟨1895935949571298144165015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2527914599428397525553353 1895935949571298144165015)
          ·
            refine ⟨2843903924356947216247523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895935949571298144165015 2843903924356947216247523)
            ·
              refine ⟨4265855886535420824371285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843903924356947216247523 4265855886535420824371285)
              ·
                refine ⟨49990498670336962785601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4265855886535420824371285 49990498670336962785601)
                ·
                  rfl

theorem cell22_1314308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 8].length) (baseStart_1314308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314308 prefixEnd_1314308 := by exact prefixLift 1314308
  have htrace : WordTrace (prefixWord ++ tailWord_1314308) baseStart_1314308 baseEnd_1314308 := by
    simpa [prefixWord, tailWord_1314308, baseEnd_1314308] using wordTrace_append hprefix tailTrace_1314308
  have hstable : (prefixWord ++ tailWord_1314308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314308).length < 2 ^ (prefixWord ++ tailWord_1314308).sum := by decide
  have hdescent : baseEnd_1314308 < baseStart_1314308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314509 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1314509 : Nat := 118140960795 + 1314509 * 2 ^ 59
def prefixEnd_1314509 : Nat := 4983230072969 + 3 ^ 40 * 1314509 * 2
def baseEnd_1314509 : Nat := 449983294440735140794793

theorem tailTrace_1314509 : CollatzResearch.WordTrace tailWord_1314509 prefixEnd_1314509 449983294440735140794793 := by
  unfold tailWord_1314509
  simp only [CollatzResearch.WordTrace]
  refine ⟨47944081994765868108930581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31962721329843912072620387 47944081994765868108930581)
  ·
    refine ⟨2247378843504650067606121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47944081994765868108930581 2247378843504650067606121)
    ·
      refine ⟨1685534132628487550704591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2247378843504650067606121 1685534132628487550704591)
      ·
        refine ⟨2528301198942731326056887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685534132628487550704591 2528301198942731326056887)
        ·
          refine ⟨3792451798414096989085331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528301198942731326056887 3792451798414096989085331)
          ·
            refine ⟨5688677697621145483627997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792451798414096989085331 5688677697621145483627997)
            ·
              refine ⟨2133254136607929556360499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5688677697621145483627997 2133254136607929556360499)
              ·
                refine ⟨3199881204911894334540749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133254136607929556360499 3199881204911894334540749)
                ·
                  refine ⟨1199955451841960375452781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3199881204911894334540749 1199955451841960375452781)
                  ·
                    refine ⟨449983294440735140794793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1199955451841960375452781 449983294440735140794793)
                    ·
                      rfl

theorem cell22_1314509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1314509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314509 prefixEnd_1314509 := by exact prefixLift 1314509
  have htrace : WordTrace (prefixWord ++ tailWord_1314509) baseStart_1314509 baseEnd_1314509 := by
    simpa [prefixWord, tailWord_1314509, baseEnd_1314509] using wordTrace_append hprefix tailTrace_1314509
  have hstable : (prefixWord ++ tailWord_1314509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314509).length < 2 ^ (prefixWord ++ tailWord_1314509).sum := by decide
  have hdescent : baseEnd_1314509 < baseStart_1314509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314522 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_1314522 : Nat := 118140960795 + 1314522 * 2 ^ 59
def prefixEnd_1314522 : Nat := 4983230072969 + 3 ^ 40 * 1314522 * 2
def baseEnd_1314522 : Nat := 149995914868802480073251

theorem tailTrace_1314522 : CollatzResearch.WordTrace tailWord_1314522 prefixEnd_1314522 149995914868802480073251 := by
  unfold tailWord_1314522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11986139035929692832288455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31963037429145847552769213 11986139035929692832288455)
  ·
    refine ⟨17979208553894539248432683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11986139035929692832288455 17979208553894539248432683)
    ·
      refine ⟨26968812830841808872649025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17979208553894539248432683 26968812830841808872649025)
      ·
        refine ⟨20226609623131356654486769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26968812830841808872649025 20226609623131356654486769)
        ·
          refine ⟨15169957217348517490865077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20226609623131356654486769 15169957217348517490865077)
          ·
            refine ⟨1422183489126423514768601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15169957217348517490865077 1422183489126423514768601)
            ·
              refine ⟨1066637616844817636076451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422183489126423514768601 1066637616844817636076451)
              ·
                refine ⟨1599956425267226454114677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066637616844817636076451 1599956425267226454114677)
                ·
                  refine ⟨149995914868802480073251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1599956425267226454114677 149995914868802480073251)
                  ·
                    rfl

theorem cell22_1314522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_1314522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314522 prefixEnd_1314522 := by exact prefixLift 1314522
  have htrace : WordTrace (prefixWord ++ tailWord_1314522) baseStart_1314522 baseEnd_1314522 := by
    simpa [prefixWord, tailWord_1314522, baseEnd_1314522] using wordTrace_append hprefix tailTrace_1314522
  have hstable : (prefixWord ++ tailWord_1314522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314522).length < 2 ^ (prefixWord ++ tailWord_1314522).sum := by decide
  have hdescent : baseEnd_1314522 < baseStart_1314522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314533 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 8]
def baseStart_1314533 : Nat := 118140960795 + 1314533 * 2 ^ 59
def prefixEnd_1314533 : Nat := 4983230072969 + 3 ^ 40 * 1314533 * 2
def baseEnd_1314533 : Nat := 149997170043735692731573

theorem tailTrace_1314533 : CollatzResearch.WordTrace tailWord_1314533 prefixEnd_1314533 149997170043735692731573 := by
  unfold tailWord_1314533
  simp only [CollatzResearch.WordTrace]
  refine ⟨47944957346678920207804253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31963304897785946805202835 47944957346678920207804253)
  ·
    refine ⟨17979359005004595077926595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47944957346678920207804253 17979359005004595077926595)
    ·
      refine ⟨26969038507506892616889893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17979359005004595077926595 26969038507506892616889893)
      ·
        refine ⟨5056694720157542365666855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26969038507506892616889893 5056694720157542365666855)
        ·
          refine ⟨7585042080236313548500283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056694720157542365666855 7585042080236313548500283)
          ·
            refine ⟨11377563120354470322750425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7585042080236313548500283 11377563120354470322750425)
            ·
              refine ⟨8533172340265852742062819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11377563120354470322750425 8533172340265852742062819)
              ·
                refine ⟨12799758510398779113094229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8533172340265852742062819 12799758510398779113094229)
                ·
                  refine ⟨149997170043735692731573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12799758510398779113094229 149997170043735692731573)
                  ·
                    rfl

theorem cell22_1314533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_1314533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314533 prefixEnd_1314533 := by exact prefixLift 1314533
  have htrace : WordTrace (prefixWord ++ tailWord_1314533) baseStart_1314533 baseEnd_1314533 := by
    simpa [prefixWord, tailWord_1314533, baseEnd_1314533] using wordTrace_append hprefix tailTrace_1314533
  have hstable : (prefixWord ++ tailWord_1314533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314533).length < 2 ^ (prefixWord ++ tailWord_1314533).sum := by decide
  have hdescent : baseEnd_1314533 < baseStart_1314533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314597 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_1314597 : Nat := 118140960795 + 1314597 * 2 ^ 59
def prefixEnd_1314597 : Nat := 4983230072969 + 3 ^ 40 * 1314597 * 2
def baseEnd_1314597 : Nat := 450013418639132244594523

theorem tailTrace_1314597 : CollatzResearch.WordTrace tailWord_1314597 prefixEnd_1314597 450013418639132244594523 := by
  unfold tailWord_1314597
  simp only [CollatzResearch.WordTrace]
  refine ⟨47947291618447059138134045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31964861078964706092089363 47947291618447059138134045)
  ·
    refine ⟨17980234356917647176800267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47947291618447059138134045 17980234356917647176800267)
    ·
      refine ⟨26970351535376470765200401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17980234356917647176800267 26970351535376470765200401)
      ·
        refine ⟨20227763651532353073900301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26970351535376470765200401 20227763651532353073900301)
        ·
          refine ⟨7585411369324632402712613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20227763651532353073900301 7585411369324632402712613)
          ·
            refine ⟨1422264631748368575508615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7585411369324632402712613 1422264631748368575508615)
            ·
              refine ⟨2133396947622552863262923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422264631748368575508615 2133396947622552863262923)
              ·
                refine ⟨3200095421433829294894385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133396947622552863262923 3200095421433829294894385)
                ·
                  refine ⟨2400071566075371971170789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3200095421433829294894385 2400071566075371971170789)
                  ·
                    refine ⟨450013418639132244594523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400071566075371971170789 450013418639132244594523)
                    ·
                      rfl

theorem cell22_1314597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_1314597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314597 prefixEnd_1314597 := by exact prefixLift 1314597
  have htrace : WordTrace (prefixWord ++ tailWord_1314597) baseStart_1314597 baseEnd_1314597 := by
    simpa [prefixWord, tailWord_1314597, baseEnd_1314597] using wordTrace_append hprefix tailTrace_1314597
  have hstable : (prefixWord ++ tailWord_1314597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314597).length < 2 ^ (prefixWord ++ tailWord_1314597).sum := by decide
  have hdescent : baseEnd_1314597 < baseStart_1314597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314627 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 3, 3]
def baseStart_1314627 : Nat := 118140960795 + 1314627 * 2 ^ 59
def prefixEnd_1314627 : Nat := 4983230072969 + 3 ^ 40 * 1314627 * 2
def baseEnd_1314627 : Nat := 450023688252222166344431

theorem tailTrace_1314627 : CollatzResearch.WordTrace tailWord_1314627 prefixEnd_1314627 450023688252222166344431 := by
  unfold tailWord_1314627
  simp only [CollatzResearch.WordTrace]
  refine ⟨47948385808338374261726135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31965590538892249507817423 47948385808338374261726135)
  ·
    refine ⟨71922578712507561392589203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47948385808338374261726135 71922578712507561392589203)
    ·
      refine ⟨107883868068761342088883805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71922578712507561392589203 107883868068761342088883805)
      ·
        refine ⟨40456450525785503283331427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107883868068761342088883805 40456450525785503283331427)
        ·
          refine ⟨60684675788678254924997141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40456450525785503283331427 60684675788678254924997141)
          ·
            refine ⟨2844594177594293199609241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60684675788678254924997141 2844594177594293199609241)
            ·
              refine ⟨2133445633195719899706931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844594177594293199609241 2133445633195719899706931)
              ·
                refine ⟨3200168449793579849560397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133445633195719899706931 3200168449793579849560397)
                ·
                  refine ⟨1200063168672592443585149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3200168449793579849560397 1200063168672592443585149)
                  ·
                    refine ⟨450023688252222166344431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1200063168672592443585149 450023688252222166344431)
                    ·
                      rfl

theorem cell22_1314627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 3].length) (baseStart_1314627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314627 prefixEnd_1314627 := by exact prefixLift 1314627
  have htrace : WordTrace (prefixWord ++ tailWord_1314627) baseStart_1314627 baseEnd_1314627 := by
    simpa [prefixWord, tailWord_1314627, baseEnd_1314627] using wordTrace_append hprefix tailTrace_1314627
  have hstable : (prefixWord ++ tailWord_1314627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314627).length < 2 ^ (prefixWord ++ tailWord_1314627).sum := by decide
  have hdescent : baseEnd_1314627 < baseStart_1314627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314678 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_1314678 : Nat := 118140960795 + 1314678 * 2 ^ 59
def prefixEnd_1314678 : Nat := 4983230072969 + 3 ^ 40 * 1314678 * 2
def baseEnd_1314678 : Nat := 450041146594475033319275

theorem tailTrace_1314678 : CollatzResearch.WordTrace tailWord_1314678 prefixEnd_1314678 450041146594475033319275 := by
  unfold tailWord_1314678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2996890370697100623239543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31966830620769073314555125 2996890370697100623239543)
  ·
    refine ⟨4495335556045650934859315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2996890370697100623239543 4495335556045650934859315)
    ·
      refine ⟨6743003334068476402288973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4495335556045650934859315 6743003334068476402288973)
      ·
        refine ⟨2528626250275678650858365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6743003334068476402288973 2528626250275678650858365)
        ·
          refine ⟨948234843853379494071887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2528626250275678650858365 948234843853379494071887)
          ·
            refine ⟨1422352265780069241107831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948234843853379494071887 1422352265780069241107831)
            ·
              refine ⟨2133528398670103861661747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422352265780069241107831 2133528398670103861661747)
              ·
                refine ⟨3200292598005155792492621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133528398670103861661747 3200292598005155792492621)
                ·
                  refine ⟨1200109724251933422184733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3200292598005155792492621 1200109724251933422184733)
                  ·
                    refine ⟨450041146594475033319275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1200109724251933422184733 450041146594475033319275)
                    ·
                      rfl

theorem cell22_1314678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_1314678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314678 prefixEnd_1314678 := by exact prefixLift 1314678
  have htrace : WordTrace (prefixWord ++ tailWord_1314678) baseStart_1314678 baseEnd_1314678 := by
    simpa [prefixWord, tailWord_1314678, baseEnd_1314678] using wordTrace_append hprefix tailTrace_1314678
  have hstable : (prefixWord ++ tailWord_1314678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314678).length < 2 ^ (prefixWord ++ tailWord_1314678).sum := by decide
  have hdescent : baseEnd_1314678 < baseStart_1314678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314700 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_1314700 : Nat := 118140960795 + 1314700 * 2 ^ 59
def prefixEnd_1314700 : Nat := 4983230072969 + 3 ^ 40 * 1314700 * 2
def baseEnd_1314700 : Nat := 450048677644074309269207

theorem tailTrace_1314700 : CollatzResearch.WordTrace tailWord_1314700 prefixEnd_1314700 450048677644074309269207 := by
  unfold tailWord_1314700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23975524168536953864566777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31967365558049271819422369 23975524168536953864566777)
  ·
    refine ⟨17981643126402715398425083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23975524168536953864566777 17981643126402715398425083)
    ·
      refine ⟨26972464689604073097637625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17981643126402715398425083 26972464689604073097637625)
      ·
        refine ⟨20229348517203054823228219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26972464689604073097637625 20229348517203054823228219)
        ·
          refine ⟨30344022775804582234842329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20229348517203054823228219 30344022775804582234842329)
          ·
            refine ⟨22758017081853436676131747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30344022775804582234842329 22758017081853436676131747)
            ·
              refine ⟨34137025622780155014197621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22758017081853436676131747 34137025622780155014197621)
              ·
                refine ⟨3200346152135639532581027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34137025622780155014197621 3200346152135639532581027)
                ·
                  refine ⟨4800519228203459298871541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200346152135639532581027 4800519228203459298871541)
                  ·
                    refine ⟨450048677644074309269207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4800519228203459298871541 450048677644074309269207)
                    ·
                      rfl

theorem cell22_1314700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_1314700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314700 prefixEnd_1314700 := by exact prefixLift 1314700
  have htrace : WordTrace (prefixWord ++ tailWord_1314700) baseStart_1314700 baseEnd_1314700 := by
    simpa [prefixWord, tailWord_1314700, baseEnd_1314700] using wordTrace_append hprefix tailTrace_1314700
  have hstable : (prefixWord ++ tailWord_1314700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314700).length < 2 ^ (prefixWord ++ tailWord_1314700).sum := by decide
  have hdescent : baseEnd_1314700 < baseStart_1314700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314717 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1314717 : Nat := 118140960795 + 1314717 * 2 ^ 59
def prefixEnd_1314717 : Nat := 4983230072969 + 3 ^ 40 * 1314717 * 2
def baseEnd_1314717 : Nat := 450054497091491931594155

theorem tailTrace_1314717 : CollatzResearch.WordTrace tailWord_1314717 prefixEnd_1314717 450054497091491931594155 := by
  unfold tailWord_1314717
  simp only [CollatzResearch.WordTrace]
  refine ⟨47951668378012319632502405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31967778918674879755001603 47951668378012319632502405)
  ·
    refine ⟨8990937820877309931094201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47951668378012319632502405 8990937820877309931094201)
    ·
      refine ⟨6743203365657982448320651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8990937820877309931094201 6743203365657982448320651)
      ·
        refine ⟨10114805048486973672480977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6743203365657982448320651 10114805048486973672480977)
        ·
          refine ⟨7586103786365230254360733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10114805048486973672480977 7586103786365230254360733)
          ·
            refine ⟨2844788919886961345385275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7586103786365230254360733 2844788919886961345385275)
            ·
              refine ⟨4267183379830442018077913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844788919886961345385275 4267183379830442018077913)
              ·
                refine ⟨3200387534872831513558435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4267183379830442018077913 3200387534872831513558435)
                ·
                  refine ⟨4800581302309247270337653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200387534872831513558435 4800581302309247270337653)
                  ·
                    refine ⟨450054497091491931594155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4800581302309247270337653 450054497091491931594155)
                    ·
                      rfl

theorem cell22_1314717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1314717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314717 prefixEnd_1314717 := by exact prefixLift 1314717
  have htrace : WordTrace (prefixWord ++ tailWord_1314717) baseStart_1314717 baseEnd_1314717 := by
    simpa [prefixWord, tailWord_1314717, baseEnd_1314717] using wordTrace_append hprefix tailTrace_1314717
  have hstable : (prefixWord ++ tailWord_1314717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314717).length < 2 ^ (prefixWord ++ tailWord_1314717).sum := by decide
  have hdescent : baseEnd_1314717 < baseStart_1314717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314721 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 1, 4]
def baseStart_1314721 : Nat := 118140960795 + 1314721 * 2 ^ 59
def prefixEnd_1314721 : Nat := 4983230072969 + 3 ^ 40 * 1314721 * 2
def baseEnd_1314721 : Nat := 450055866373237254494143

theorem tailTrace_1314721 : CollatzResearch.WordTrace tailWord_1314721 prefixEnd_1314721 450055866373237254494143 := by
  unfold tailWord_1314721
  simp only [CollatzResearch.WordTrace]
  refine ⟨47951814269997828315648017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31967876179998552210432011 47951814269997828315648017)
  ·
    refine ⟨35963860702498371236736013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47951814269997828315648017 35963860702498371236736013)
    ·
      refine ⟨13486447763436889213776005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35963860702498371236736013 13486447763436889213776005)
      ·
        refine ⟨2528708955644416727583001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13486447763436889213776005 2528708955644416727583001)
        ·
          refine ⟨1896531716733312545687251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2528708955644416727583001 1896531716733312545687251)
          ·
            refine ⟨2844797575099968818530877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896531716733312545687251 2844797575099968818530877)
            ·
              refine ⟨1066799090662488306949079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2844797575099968818530877 1066799090662488306949079)
              ·
                refine ⟨1600198635993732460423619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066799090662488306949079 1600198635993732460423619)
                ·
                  refine ⟨2400297953990598690635429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600198635993732460423619 2400297953990598690635429)
                  ·
                    refine ⟨450055866373237254494143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400297953990598690635429 450055866373237254494143)
                    ·
                      rfl

theorem cell22_1314721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_1314721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314721 prefixEnd_1314721 := by exact prefixLift 1314721
  have htrace : WordTrace (prefixWord ++ tailWord_1314721) baseStart_1314721 baseEnd_1314721 := by
    simpa [prefixWord, tailWord_1314721, baseEnd_1314721] using wordTrace_append hprefix tailTrace_1314721
  have hstable : (prefixWord ++ tailWord_1314721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314721).length < 2 ^ (prefixWord ++ tailWord_1314721).sum := by decide
  have hdescent : baseEnd_1314721 < baseStart_1314721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314762 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 5, 3]
def baseStart_1314762 : Nat := 118140960795 + 1314762 * 2 ^ 59
def prefixEnd_1314762 : Nat := 4983230072969 + 3 ^ 40 * 1314762 * 2
def baseEnd_1314762 : Nat := 450069901511126814219017

theorem tailTrace_1314762 : CollatzResearch.WordTrace tailWord_1314762 prefixEnd_1314762 450069901511126814219017 := by
  unfold tailWord_1314762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11988327415712323079472635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31968873108566194878593693 11988327415712323079472635)
  ·
    refine ⟨17982491123568484619208953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11988327415712323079472635 17982491123568484619208953)
    ·
      refine ⟨13486868342676363464406715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17982491123568484619208953 13486868342676363464406715)
      ·
        refine ⟨20230302514014545196610073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13486868342676363464406715 20230302514014545196610073)
        ·
          refine ⟨15172726885510908897457555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20230302514014545196610073 15172726885510908897457555)
          ·
            refine ⟨22759090328266363346186333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15172726885510908897457555 22759090328266363346186333)
            ·
              refine ⟨8534658873099886254819875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22759090328266363346186333 8534658873099886254819875)
              ·
                refine ⟨12801988309649829382229813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8534658873099886254819875 12801988309649829382229813)
                ·
                  refine ⟨1200186404029671504584045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12801988309649829382229813 1200186404029671504584045)
                  ·
                    refine ⟨450069901511126814219017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1200186404029671504584045 450069901511126814219017)
                    ·
                      rfl

theorem cell22_1314762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_1314762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314762 prefixEnd_1314762 := by exact prefixLift 1314762
  have htrace : WordTrace (prefixWord ++ tailWord_1314762) baseStart_1314762 baseEnd_1314762 := by
    simpa [prefixWord, tailWord_1314762, baseEnd_1314762] using wordTrace_append hprefix tailTrace_1314762
  have hstable : (prefixWord ++ tailWord_1314762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314762).length < 2 ^ (prefixWord ++ tailWord_1314762).sum := by decide
  have hdescent : baseEnd_1314762 < baseStart_1314762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314775 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 7]
def baseStart_1314775 : Nat := 118140960795 + 1314775 * 2 ^ 59
def prefixEnd_1314775 : Nat := 4983230072969 + 3 ^ 40 * 1314775 * 2
def baseEnd_1314775 : Nat := 150024783892266371214659

theorem tailTrace_1314775 : CollatzResearch.WordTrace tailWord_1314775 prefixEnd_1314775 150024783892266371214659 := by
  unfold tailWord_1314775
  simp only [CollatzResearch.WordTrace]
  refine ⟨47953783811802195538113779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31969189207868130358742519 47953783811802195538113779)
  ·
    refine ⟨71930675717703293307170669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47953783811802195538113779 71930675717703293307170669)
    ·
      refine ⟨26974003394138734990189001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71930675717703293307170669 26974003394138734990189001)
      ·
        refine ⟨20230502545604051242641751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26974003394138734990189001 20230502545604051242641751)
        ·
          refine ⟨30345753818406076863962627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20230502545604051242641751 30345753818406076863962627)
          ·
            refine ⟨45518630727609115295943941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30345753818406076863962627 45518630727609115295943941)
            ·
              refine ⟨8534743261426709117989489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45518630727609115295943941 8534743261426709117989489)
              ·
                refine ⟨6401057446070031838492117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8534743261426709117989489 6401057446070031838492117)
                ·
                  refine ⟨150024783892266371214659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6401057446070031838492117 150024783892266371214659)
                  ·
                    rfl

theorem cell22_1314775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 7].length) (baseStart_1314775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314775 prefixEnd_1314775 := by exact prefixLift 1314775
  have htrace : WordTrace (prefixWord ++ tailWord_1314775) baseStart_1314775 baseEnd_1314775 := by
    simpa [prefixWord, tailWord_1314775, baseEnd_1314775] using wordTrace_append hprefix tailTrace_1314775
  have hstable : (prefixWord ++ tailWord_1314775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314775).length < 2 ^ (prefixWord ++ tailWord_1314775).sum := by decide
  have hdescent : baseEnd_1314775 < baseStart_1314775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314809 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 5]
def baseStart_1314809 : Nat := 118140960795 + 1314809 * 2 ^ 59
def prefixEnd_1314809 : Nat := 4983230072969 + 3 ^ 40 * 1314809 * 2
def baseEnd_1314809 : Nat := 150028663523878119431291

theorem tailTrace_1314809 : CollatzResearch.WordTrace tailWord_1314809 prefixEnd_1314809 150028663523878119431291 := by
  unfold tailWord_1314809
  simp only [CollatzResearch.WordTrace]
  refine ⟨47955023893679019344851481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31970015929119346229900987 47955023893679019344851481)
  ·
    refine ⟨35966267920259264508638611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47955023893679019344851481 35966267920259264508638611)
    ·
      refine ⟨53949401880388896762957917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35966267920259264508638611 53949401880388896762957917)
      ·
        refine ⟨20231025705145836286109219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53949401880388896762957917 20231025705145836286109219)
        ·
          refine ⟨30346538557718754429163829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20231025705145836286109219 30346538557718754429163829)
          ·
            refine ⟨2844987989786133227734109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30346538557718754429163829 2844987989786133227734109)
            ·
              refine ⟨1066870496169799960400291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2844987989786133227734109 1066870496169799960400291)
              ·
                refine ⟨1600305744254699940600437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066870496169799960400291 1600305744254699940600437)
                ·
                  refine ⟨150028663523878119431291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1600305744254699940600437 150028663523878119431291)
                  ·
                    rfl

theorem cell22_1314809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_1314809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314809 prefixEnd_1314809 := by exact prefixLift 1314809
  have htrace : WordTrace (prefixWord ++ tailWord_1314809) baseStart_1314809 baseEnd_1314809 := by
    simpa [prefixWord, tailWord_1314809, baseEnd_1314809] using wordTrace_append hprefix tailTrace_1314809
  have hstable : (prefixWord ++ tailWord_1314809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314809).length < 2 ^ (prefixWord ++ tailWord_1314809).sum := by decide
  have hdescent : baseEnd_1314809 < baseStart_1314809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314873 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 1, 4]
def baseStart_1314873 : Nat := 118140960795 + 1314873 * 2 ^ 59
def prefixEnd_1314873 : Nat := 4983230072969 + 3 ^ 40 * 1314873 * 2
def baseEnd_1314873 : Nat := 450107899079559524693677

theorem tailTrace_1314873 : CollatzResearch.WordTrace tailWord_1314873 prefixEnd_1314873 450107899079559524693677 := by
  unfold tailWord_1314873
  simp only [CollatzResearch.WordTrace]
  refine ⟨47957358165447158275181273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31971572110298105516787515 47957358165447158275181273)
  ·
    refine ⟨35968018624085368706385955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47957358165447158275181273 35968018624085368706385955)
    ·
      refine ⟨53952027936128053059578933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35968018624085368706385955 53952027936128053059578933)
      ·
        refine ⟨5058002619012004974335525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53952027936128053059578933 5058002619012004974335525)
        ·
          refine ⟨948375491064750932687911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5058002619012004974335525 948375491064750932687911)
          ·
            refine ⟨1422563236597126399031867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948375491064750932687911 1422563236597126399031867)
            ·
              refine ⟨2133844854895689598547801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422563236597126399031867 2133844854895689598547801)
              ·
                refine ⟨1600383641171767198910851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133844854895689598547801 1600383641171767198910851)
                ·
                  refine ⟨2400575461757650798366277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600383641171767198910851 2400575461757650798366277)
                  ·
                    refine ⟨450107899079559524693677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400575461757650798366277 450107899079559524693677)
                    ·
                      rfl

theorem cell22_1314873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 4].length) (baseStart_1314873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314873 prefixEnd_1314873 := by exact prefixLift 1314873
  have htrace : WordTrace (prefixWord ++ tailWord_1314873) baseStart_1314873 baseEnd_1314873 := by
    simpa [prefixWord, tailWord_1314873, baseEnd_1314873] using wordTrace_append hprefix tailTrace_1314873
  have hstable : (prefixWord ++ tailWord_1314873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314873).length < 2 ^ (prefixWord ++ tailWord_1314873).sum := by decide
  have hdescent : baseEnd_1314873 < baseStart_1314873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314886 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1314886 : Nat := 118140960795 + 1314886 * 2 ^ 59
def prefixEnd_1314886 : Nat := 4983230072969 + 3 ^ 40 * 1314886 * 2
def baseEnd_1314886 : Nat := 450112349245231824118637

theorem tailTrace_1314886 : CollatzResearch.WordTrace tailWord_1314886 prefixEnd_1314886 450112349245231824118637 := by
  unfold tailWord_1314886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498682259825001921731391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31971888209600040996936341 1498682259825001921731391)
  ·
    refine ⟨2248023389737502882597087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1498682259825001921731391 2248023389737502882597087)
    ·
      refine ⟨3372035084606254323895631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2248023389737502882597087 3372035084606254323895631)
      ·
        refine ⟨5058052626909381485843447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3372035084606254323895631 5058052626909381485843447)
        ·
          refine ⟨7587078940364072228765171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5058052626909381485843447 7587078940364072228765171)
          ·
            refine ⟨11380618410546108343147757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7587078940364072228765171 11380618410546108343147757)
            ·
              refine ⟨4267731903954790628680409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11380618410546108343147757 4267731903954790628680409)
              ·
                refine ⟨3200798927966092971510307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4267731903954790628680409 3200798927966092971510307)
                ·
                  refine ⟨4801198391949139457265461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200798927966092971510307 4801198391949139457265461)
                  ·
                    refine ⟨450112349245231824118637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4801198391949139457265461 450112349245231824118637)
                    ·
                      rfl

theorem cell22_1314886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1314886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314886 prefixEnd_1314886 := by exact prefixLift 1314886
  have htrace : WordTrace (prefixWord ++ tailWord_1314886) baseStart_1314886 baseEnd_1314886 := by
    simpa [prefixWord, tailWord_1314886, baseEnd_1314886] using wordTrace_append hprefix tailTrace_1314886
  have hstable : (prefixWord ++ tailWord_1314886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314886).length < 2 ^ (prefixWord ++ tailWord_1314886).sum := by decide
  have hdescent : baseEnd_1314886 < baseStart_1314886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314912 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_1314912 : Nat := 118140960795 + 1314912 * 2 ^ 59
def prefixEnd_1314912 : Nat := 4983230072969 + 3 ^ 40 * 1314912 * 2
def baseEnd_1314912 : Nat := 450121249576576422968557

theorem tailTrace_1314912 : CollatzResearch.WordTrace tailWord_1314912 prefixEnd_1314912 450121249576576422968557 := by
  unfold tailWord_1314912
  simp only [CollatzResearch.WordTrace]
  refine ⟨23979390306152933967925495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31972520408203911957233993 23979390306152933967925495)
  ·
    refine ⟨35969085459229400951888243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23979390306152933967925495 35969085459229400951888243)
    ·
      refine ⟨53953628188844101427832365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35969085459229400951888243 53953628188844101427832365)
      ·
        refine ⟨20232610570816538035437137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53953628188844101427832365 20232610570816538035437137)
        ·
          refine ⟨15174457928112403526577853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20232610570816538035437137 15174457928112403526577853)
          ·
            refine ⟨5690421723042151322466695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15174457928112403526577853 5690421723042151322466695)
            ·
              refine ⟨8535632584563226983700043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690421723042151322466695 8535632584563226983700043)
              ·
                refine ⟨12803448876844840475550065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8535632584563226983700043 12803448876844840475550065)
                ·
                  refine ⟨9602586657633630356662549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12803448876844840475550065 9602586657633630356662549)
                  ·
                    refine ⟨450121249576576422968557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9602586657633630356662549 450121249576576422968557)
                    ·
                      rfl

theorem cell22_1314912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_1314912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314912 prefixEnd_1314912 := by exact prefixLift 1314912
  have htrace : WordTrace (prefixWord ++ tailWord_1314912) baseStart_1314912 baseEnd_1314912 := by
    simpa [prefixWord, tailWord_1314912, baseEnd_1314912] using wordTrace_append hprefix tailTrace_1314912
  have hstable : (prefixWord ++ tailWord_1314912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314912).length < 2 ^ (prefixWord ++ tailWord_1314912).sum := by decide
  have hdescent : baseEnd_1314912 < baseStart_1314912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314948 : List Nat := [2, 3, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_1314948 : Nat := 118140960795 + 1314948 * 2 ^ 59
def prefixEnd_1314948 : Nat := 4983230072969 + 3 ^ 40 * 1314948 * 2
def baseEnd_1314948 : Nat := 450133573112284329068447

theorem tailTrace_1314948 : CollatzResearch.WordTrace tailWord_1314948 prefixEnd_1314948 450133573112284329068447 := by
  unfold tailWord_1314948
  simp only [CollatzResearch.WordTrace]
  refine ⟨23980046820087723042080749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31973395760116964056107665 23980046820087723042080749)
  ·
    refine ⟨8992517557532896140780281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23980046820087723042080749 8992517557532896140780281)
    ·
      refine ⟨6744388168149672105585211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8992517557532896140780281 6744388168149672105585211)
      ·
        refine ⟨10116582252224508158377817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744388168149672105585211 10116582252224508158377817)
        ·
          refine ⟨7587436689168381118783363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10116582252224508158377817 7587436689168381118783363)
          ·
            refine ⟨11381155033752571678175045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7587436689168381118783363 11381155033752571678175045)
            ·
              refine ⟨2133966568828607189657821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11381155033752571678175045 2133966568828607189657821)
              ·
                refine ⟨800237463310727696121683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2133966568828607189657821 800237463310727696121683)
                ·
                  refine ⟨1200356194966091544182525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800237463310727696121683 1200356194966091544182525)
                  ·
                    refine ⟨450133573112284329068447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1200356194966091544182525 450133573112284329068447)
                    ·
                      rfl

theorem cell22_1314948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_1314948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314948 prefixEnd_1314948 := by exact prefixLift 1314948
  have htrace : WordTrace (prefixWord ++ tailWord_1314948) baseStart_1314948 baseEnd_1314948 := by
    simpa [prefixWord, tailWord_1314948, baseEnd_1314948] using wordTrace_append hprefix tailTrace_1314948
  have hstable : (prefixWord ++ tailWord_1314948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314948).length < 2 ^ (prefixWord ++ tailWord_1314948).sum := by decide
  have hdescent : baseEnd_1314948 < baseStart_1314948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314978 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1314978 : Nat := 118140960795 + 1314978 * 2 ^ 59
def prefixEnd_1314978 : Nat := 4983230072969 + 3 ^ 40 * 1314978 * 2
def baseEnd_1314978 : Nat := 150047947575124750272785

theorem tailTrace_1314978 : CollatzResearch.WordTrace tailWord_1314978 prefixEnd_1314978 150047947575124750272785 := by
  unfold tailWord_1314978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11990296957516690301938397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31974125220044507471835725 11990296957516690301938397)
  ·
    refine ⟨4496361359068758863226899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11990296957516690301938397 4496361359068758863226899)
    ·
      refine ⟨6744542038603138294840349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496361359068758863226899 6744542038603138294840349)
      ·
        refine ⟨2529203264476176860565131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6744542038603138294840349 2529203264476176860565131)
        ·
          refine ⟨3793804896714265290847697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529203264476176860565131 3793804896714265290847697)
          ·
            refine ⟨2845353672535698968135773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793804896714265290847697 2845353672535698968135773)
            ·
              refine ⟨1067007627200887113050915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2845353672535698968135773 1067007627200887113050915)
              ·
                refine ⟨1600511440801330669576373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067007627200887113050915 1600511440801330669576373)
                ·
                  refine ⟨150047947575124750272785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1600511440801330669576373 150047947575124750272785)
                  ·
                    rfl

theorem cell22_1314978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1314978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1314978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1314978 prefixEnd_1314978 := by exact prefixLift 1314978
  have htrace : WordTrace (prefixWord ++ tailWord_1314978) baseStart_1314978 baseEnd_1314978 := by
    simpa [prefixWord, tailWord_1314978, baseEnd_1314978] using wordTrace_append hprefix tailTrace_1314978
  have hstable : (prefixWord ++ tailWord_1314978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314978).length < 2 ^ (prefixWord ++ tailWord_1314978).sum := by decide
  have hdescent : baseEnd_1314978 < baseStart_1314978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315019 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 2, 4]
def baseStart_1315019 : Nat := 118140960795 + 1315019 * 2 ^ 59
def prefixEnd_1315019 : Nat := 4983230072969 + 3 ^ 40 * 1315019 * 2
def baseEnd_1315019 : Nat := 450157877863263810543229

theorem tailTrace_1315019 : CollatzResearch.WordTrace tailWord_1315019 prefixEnd_1315019 450157877863263810543229 := by
  unfold tailWord_1315019
  simp only [CollatzResearch.WordTrace]
  refine ⟨47962683222918225209996111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31975122148612150139997407 47962683222918225209996111)
  ·
    refine ⟨71944024834377337814994167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47962683222918225209996111 71944024834377337814994167)
    ·
      refine ⟨107916037251566006722491251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71944024834377337814994167 107916037251566006722491251)
      ·
        refine ⟨161874055877349010083736877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107916037251566006722491251 161874055877349010083736877)
        ·
          refine ⟨60702770954005878781401329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161874055877349010083736877 60702770954005878781401329)
          ·
            refine ⟨45527078215504409086050997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60702770954005878781401329 45527078215504409086050997)
            ·
              refine ⟨4268163582703538351817281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45527078215504409086050997 4268163582703538351817281)
              ·
                refine ⟨3201122687027653763862961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4268163582703538351817281 3201122687027653763862961)
                ·
                  refine ⟨2400842015270740322897221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201122687027653763862961 2400842015270740322897221)
                  ·
                    refine ⟨450157877863263810543229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400842015270740322897221 450157877863263810543229)
                    ·
                      rfl

theorem cell22_1315019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 4].length) (baseStart_1315019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315019 prefixEnd_1315019 := by exact prefixLift 1315019
  have htrace : WordTrace (prefixWord ++ tailWord_1315019) baseStart_1315019 baseEnd_1315019 := by
    simpa [prefixWord, tailWord_1315019, baseEnd_1315019] using wordTrace_append hprefix tailTrace_1315019
  have hstable : (prefixWord ++ tailWord_1315019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315019).length < 2 ^ (prefixWord ++ tailWord_1315019).sum := by decide
  have hdescent : baseEnd_1315019 < baseStart_1315019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315053 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_1315053 : Nat := 118140960795 + 1315053 * 2 ^ 59
def prefixEnd_1315053 : Nat := 4983230072969 + 3 ^ 40 * 1315053 * 2
def baseEnd_1315053 : Nat := 450169516758099055193125

theorem tailTrace_1315053 : CollatzResearch.WordTrace tailWord_1315053 prefixEnd_1315053 450169516758099055193125 := by
  unfold tailWord_1315053
  simp only [CollatzResearch.WordTrace]
  refine ⟨47963923304795049016733813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31975948869863366011155875 47963923304795049016733813)
  ·
    refine ⟨4496617809824535845318795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47963923304795049016733813 4496617809824535845318795)
    ·
      refine ⟨6744926714736803767978193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496617809824535845318795 6744926714736803767978193)
      ·
        refine ⟨5058695036052602825983645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6744926714736803767978193 5058695036052602825983645)
        ·
          refine ⟨1897010638519726059743867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5058695036052602825983645 1897010638519726059743867)
          ·
            refine ⟨2845515957779589089615801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897010638519726059743867 2845515957779589089615801)
            ·
              refine ⟨2134136968334691817211851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845515957779589089615801 2134136968334691817211851)
              ·
                refine ⟨3201205452502037725817777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134136968334691817211851 3201205452502037725817777)
                ·
                  refine ⟨2400904089376528294363333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201205452502037725817777 2400904089376528294363333)
                  ·
                    refine ⟨450169516758099055193125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2400904089376528294363333 450169516758099055193125)
                    ·
                      rfl

theorem cell22_1315053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_1315053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315053 prefixEnd_1315053 := by exact prefixLift 1315053
  have htrace : WordTrace (prefixWord ++ tailWord_1315053) baseStart_1315053 baseEnd_1315053 := by
    simpa [prefixWord, tailWord_1315053, baseEnd_1315053] using wordTrace_append hprefix tailTrace_1315053
  have hstable : (prefixWord ++ tailWord_1315053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315053).length < 2 ^ (prefixWord ++ tailWord_1315053).sum := by decide
  have hdescent : baseEnd_1315053 < baseStart_1315053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
