import V185TrunkScan22Chunk220

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1970138 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_1970138 : Nat := 118140960795 + 1970138 * 2 ^ 59
def prefixEnd_1970138 : Nat := 4983230072969 + 3 ^ 40 * 1970138 * 2
def baseEnd_1970138 : Nat := 224806166597270679936557

theorem tailTrace_1970138 : CollatzResearch.WordTrace tailWord_1970138 prefixEnd_1970138 224806166597270679936557 := by
  unfold tailWord_1970138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17964209034133493406885767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47904557424355982418362045 17964209034133493406885767)
  ·
    refine ⟨26946313551200240110328651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17964209034133493406885767 26946313551200240110328651)
    ·
      refine ⟨40419470326800360165492977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26946313551200240110328651 40419470326800360165492977)
      ·
        refine ⟨30314602745100270124119733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40419470326800360165492977 30314602745100270124119733)
        ·
          refine ⟨2841994007353150324136225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30314602745100270124119733 2841994007353150324136225)
          ·
            refine ⟨2131495505514862743102169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2841994007353150324136225 2131495505514862743102169)
            ·
              refine ⟨1598621629136147057326627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131495505514862743102169 1598621629136147057326627)
              ·
                refine ⟨2397932443704220585989941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598621629136147057326627 2397932443704220585989941)
                ·
                  refine ⟨224806166597270679936557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397932443704220585989941 224806166597270679936557)
                  ·
                    rfl

theorem cell22_1970138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_1970138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970138 prefixEnd_1970138 := by exact prefixLift 1970138
  have htrace : WordTrace (prefixWord ++ tailWord_1970138) baseStart_1970138 baseEnd_1970138 := by
    simpa [prefixWord, tailWord_1970138, baseEnd_1970138] using wordTrace_append hprefix tailTrace_1970138
  have hstable : (prefixWord ++ tailWord_1970138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970138).length < 2 ^ (prefixWord ++ tailWord_1970138).sum := by decide
  have hdescent : baseEnd_1970138 < baseStart_1970138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970151 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1970151 : Nat := 118140960795 + 1970151 * 2 ^ 59
def prefixEnd_1970151 : Nat := 4983230072969 + 3 ^ 40 * 1970151 * 2
def baseEnd_1970151 : Nat := 674422949957484339234631

theorem tailTrace_1970151 : CollatzResearch.WordTrace tailWord_1970151 prefixEnd_1970151 674422949957484339234631 := by
  unfold tailWord_1970151
  simp only [CollatzResearch.WordTrace]
  refine ⟨71857310285486876847766307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47904873523657917898510871 71857310285486876847766307)
  ·
    refine ⟨107785965428230315271649461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71857310285486876847766307 107785965428230315271649461)
    ·
      refine ⟨10104934258896592056717137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107785965428230315271649461 10104934258896592056717137)
      ·
        refine ⟨7578700694172444042537853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10104934258896592056717137 7578700694172444042537853)
        ·
          refine ⟨2842012760314666515951695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7578700694172444042537853 2842012760314666515951695)
          ·
            refine ⟨4263019140471999773927543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842012760314666515951695 4263019140471999773927543)
            ·
              refine ⟨6394528710707999660891315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4263019140471999773927543 6394528710707999660891315)
              ·
                refine ⟨9591793066061999491336973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394528710707999660891315 9591793066061999491336973)
                ·
                  refine ⟨3596922399773249809251365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9591793066061999491336973 3596922399773249809251365)
                  ·
                    refine ⟨674422949957484339234631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3596922399773249809251365 674422949957484339234631)
                    ·
                      rfl

theorem cell22_1970151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1970151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970151 prefixEnd_1970151 := by exact prefixLift 1970151
  have htrace : WordTrace (prefixWord ++ tailWord_1970151) baseStart_1970151 baseEnd_1970151 := by
    simpa [prefixWord, tailWord_1970151, baseEnd_1970151] using wordTrace_append hprefix tailTrace_1970151
  have hstable : (prefixWord ++ tailWord_1970151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970151).length < 2 ^ (prefixWord ++ tailWord_1970151).sum := by decide
  have hdescent : baseEnd_1970151 < baseStart_1970151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970181 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_1970181 : Nat := 118140960795 + 1970181 * 2 ^ 59
def prefixEnd_1970181 : Nat := 4983230072969 + 3 ^ 40 * 1970181 * 2
def baseEnd_1970181 : Nat := 674433219570574260984539

theorem tailTrace_1970181 : CollatzResearch.WordTrace tailWord_1970181 prefixEnd_1970181 674433219570574260984539 := by
  unfold tailWord_1970181
  simp only [CollatzResearch.WordTrace]
  refine ⟨71858404475378191971358397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47905602983585461314238931 71858404475378191971358397)
  ·
    refine ⟨26946901678266821989259399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71858404475378191971358397 26946901678266821989259399)
    ·
      refine ⟨40420352517400232983889099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26946901678266821989259399 40420352517400232983889099)
      ·
        refine ⟨60630528776100349475833649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40420352517400232983889099 60630528776100349475833649)
        ·
          refine ⟨45472896582075262106875237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60630528776100349475833649 45472896582075262106875237)
          ·
            refine ⟨8526168109139111645039107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45472896582075262106875237 8526168109139111645039107)
            ·
              refine ⟨12789252163708667467558661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8526168109139111645039107 12789252163708667467558661)
              ·
                refine ⟨2397984780695375150167249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12789252163708667467558661 2397984780695375150167249)
                ·
                  refine ⟨1798488585521531362625437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2397984780695375150167249 1798488585521531362625437)
                  ·
                    refine ⟨674433219570574260984539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1798488585521531362625437 674433219570574260984539)
                    ·
                      rfl

theorem cell22_1970181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_1970181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970181 prefixEnd_1970181 := by exact prefixLift 1970181
  have htrace : WordTrace (prefixWord ++ tailWord_1970181) baseStart_1970181 baseEnd_1970181 := by
    simpa [prefixWord, tailWord_1970181, baseEnd_1970181] using wordTrace_append hprefix tailTrace_1970181
  have hstable : (prefixWord ++ tailWord_1970181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970181).length < 2 ^ (prefixWord ++ tailWord_1970181).sum := by decide
  have hdescent : baseEnd_1970181 < baseStart_1970181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970183 : List Nat := [1, 1, 4, 3, 1, 2, 4, 2, 4]
def baseStart_1970183 : Nat := 118140960795 + 1970183 * 2 ^ 59
def prefixEnd_1970183 : Nat := 4983230072969 + 3 ^ 40 * 1970183 * 2
def baseEnd_1970183 : Nat := 224811301403815640811511

theorem tailTrace_1970183 : CollatzResearch.WordTrace tailWord_1970183 prefixEnd_1970183 224811301403815640811511 := by
  unfold tailWord_1970183
  simp only [CollatzResearch.WordTrace]
  refine ⟨71858477421370946312931203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47905651614247297541954135 71858477421370946312931203)
  ·
    refine ⟨107787716132056419469396805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71858477421370946312931203 107787716132056419469396805)
    ·
      refine ⟨20210196774760578650511901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107787716132056419469396805 20210196774760578650511901)
      ·
        refine ⟨7578823790535216993941963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20210196774760578650511901 7578823790535216993941963)
        ·
          refine ⟨11368235685802825490912945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578823790535216993941963 11368235685802825490912945)
          ·
            refine ⟨8526176764352119118184709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368235685802825490912945 8526176764352119118184709)
            ·
              refine ⟨1598658143316022334659633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8526176764352119118184709 1598658143316022334659633)
              ·
                refine ⟨1198993607487016750994725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1598658143316022334659633 1198993607487016750994725)
                ·
                  refine ⟨224811301403815640811511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1198993607487016750994725 224811301403815640811511)
                  ·
                    rfl

theorem cell22_1970183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 4].length) (baseStart_1970183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970183 prefixEnd_1970183 := by exact prefixLift 1970183
  have htrace : WordTrace (prefixWord ++ tailWord_1970183) baseStart_1970183 baseEnd_1970183 := by
    simpa [prefixWord, tailWord_1970183, baseEnd_1970183] using wordTrace_append hprefix tailTrace_1970183
  have hstable : (prefixWord ++ tailWord_1970183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970183).length < 2 ^ (prefixWord ++ tailWord_1970183).sum := by decide
  have hdescent : baseEnd_1970183 < baseStart_1970183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970301 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1970301 : Nat := 118140960795 + 1970301 * 2 ^ 59
def prefixEnd_1970301 : Nat := 4983230072969 + 3 ^ 40 * 1970301 * 2
def baseEnd_1970301 : Nat := 224824766007644649328057

theorem tailTrace_1970301 : CollatzResearch.WordTrace tailWord_1970301 prefixEnd_1970301 224824766007644649328057 := by
  unfold tailWord_1970301
  simp only [CollatzResearch.WordTrace]
  refine ⟨71862781234943452465726757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47908520823295634977151171 71862781234943452465726757)
  ·
    refine ⟨13474271481551897337323767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71862781234943452465726757 13474271481551897337323767)
    ·
      refine ⟨20211407222327846005985651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13474271481551897337323767 20211407222327846005985651)
      ·
        refine ⟨30317110833491769008978477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20211407222327846005985651 30317110833491769008978477)
        ·
          refine ⟨11368916562559413378366929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30317110833491769008978477 11368916562559413378366929)
          ·
            refine ⟨8526687421919560033775197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368916562559413378366929 8526687421919560033775197)
            ·
              refine ⟨3197507783219835012665699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8526687421919560033775197 3197507783219835012665699)
              ·
                refine ⟨4796261674829752518998549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197507783219835012665699 4796261674829752518998549)
                ·
                  refine ⟨224824766007644649328057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4796261674829752518998549 224824766007644649328057)
                  ·
                    rfl

theorem cell22_1970301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1970301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970301 prefixEnd_1970301 := by exact prefixLift 1970301
  have htrace : WordTrace (prefixWord ++ tailWord_1970301) baseStart_1970301 baseEnd_1970301 := by
    simpa [prefixWord, tailWord_1970301, baseEnd_1970301] using wordTrace_append hprefix tailTrace_1970301
  have hstable : (prefixWord ++ tailWord_1970301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970301).length < 2 ^ (prefixWord ++ tailWord_1970301).sum := by decide
  have hdescent : baseEnd_1970301 < baseStart_1970301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970346 : List Nat := [3, 1, 5, 1, 12]
def baseStart_1970346 : Nat := 118140960795 + 1970346 * 2 ^ 59
def prefixEnd_1970346 : Nat := 4983230072969 + 3 ^ 40 * 1970346 * 2
def baseEnd_1970346 : Nat := 2775677787829501360531

theorem tailTrace_1970346 : CollatzResearch.WordTrace tailWord_1970346 prefixEnd_1970346 2775677787829501360531 := by
  unfold tailWord_1970346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17966105629945106287778723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47909615013186950100743261 17966105629945106287778723)
  ·
    refine ⟨26949158444917659431668085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17966105629945106287778723 26949158444917659431668085)
    ·
      refine ⟨2526483604211030571718883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26949158444917659431668085 2526483604211030571718883)
      ·
        refine ⟨3789725406316545857578325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526483604211030571718883 3789725406316545857578325)
        ·
          refine ⟨2775677787829501360531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3789725406316545857578325 2775677787829501360531)
          ·
            rfl

theorem cell22_1970346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 12].length) (baseStart_1970346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970346 prefixEnd_1970346 := by exact prefixLift 1970346
  have htrace : WordTrace (prefixWord ++ tailWord_1970346) baseStart_1970346 baseEnd_1970346 := by
    simpa [prefixWord, tailWord_1970346, baseEnd_1970346] using wordTrace_append hprefix tailTrace_1970346
  have hstable : (prefixWord ++ tailWord_1970346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970346).length < 2 ^ (prefixWord ++ tailWord_1970346).sum := by decide
  have hdescent : baseEnd_1970346 < baseStart_1970346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970378 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_1970378 : Nat := 118140960795 + 1970378 * 2 ^ 59
def prefixEnd_1970378 : Nat := 4983230072969 + 3 ^ 40 * 1970378 * 2
def baseEnd_1970378 : Nat := 674500656696531413808935

theorem tailTrace_1970378 : CollatzResearch.WordTrace tailWord_1970378 prefixEnd_1970378 674500656696531413808935 := by
  unfold tailWord_1970378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17966397413916123654069947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47910393103776329744186525 17966397413916123654069947)
  ·
    refine ⟨26949596120874185481104921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17966397413916123654069947 26949596120874185481104921)
    ·
      refine ⟨20212197090655639110828691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26949596120874185481104921 20212197090655639110828691)
      ·
        refine ⟨30318295635983458666243037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20212197090655639110828691 30318295635983458666243037)
        ·
          refine ⟨11369360863493796999841139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30318295635983458666243037 11369360863493796999841139)
          ·
            refine ⟨17054041295240695499761709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11369360863493796999841139 17054041295240695499761709)
            ·
              refine ⟨6395265485715260812410641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17054041295240695499761709 6395265485715260812410641)
              ·
                refine ⟨4796449114286445609307981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6395265485715260812410641 4796449114286445609307981)
                ·
                  refine ⟨1798668417857417103490493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4796449114286445609307981 1798668417857417103490493)
                  ·
                    refine ⟨674500656696531413808935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1798668417857417103490493 674500656696531413808935)
                    ·
                      rfl

theorem cell22_1970378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_1970378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970378 prefixEnd_1970378 := by exact prefixLift 1970378
  have htrace : WordTrace (prefixWord ++ tailWord_1970378) baseStart_1970378 baseEnd_1970378 := by
    simpa [prefixWord, tailWord_1970378, baseEnd_1970378] using wordTrace_append hprefix tailTrace_1970378
  have hstable : (prefixWord ++ tailWord_1970378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970378).length < 2 ^ (prefixWord ++ tailWord_1970378).sum := by decide
  have hdescent : baseEnd_1970378 < baseStart_1970378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970380 : List Nat := [2, 2, 1, 6, 1, 1, 3, 6]
def baseStart_1970380 : Nat := 118140960795 + 1970380 * 2 ^ 59
def prefixEnd_1970380 : Nat := 4983230072969 + 3 ^ 40 * 1970380 * 2
def baseEnd_1970380 : Nat := 74944593481933786139881

theorem tailTrace_1970380 : CollatzResearch.WordTrace tailWord_1970380 prefixEnd_1970380 74944593481933786139881 := by
  unfold tailWord_1970380
  simp only [CollatzResearch.WordTrace]
  refine ⟨35932831300828624478926297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47910441734438165971901729 35932831300828624478926297)
  ·
    refine ⟨26949623475621468359194723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35932831300828624478926297 26949623475621468359194723)
    ·
      refine ⟨40424435213432202538792085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26949623475621468359194723 40424435213432202538792085)
      ·
        refine ⟨1894895400629634494005879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40424435213432202538792085 1894895400629634494005879)
        ·
          refine ⟨2842343100944451741008819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894895400629634494005879 2842343100944451741008819)
          ·
            refine ⟨4263514651416677611513229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2842343100944451741008819 4263514651416677611513229)
            ·
              refine ⟨1598817994281254104317461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4263514651416677611513229 1598817994281254104317461)
              ·
                refine ⟨74944593481933786139881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1598817994281254104317461 74944593481933786139881)
                ·
                  rfl

theorem cell22_1970380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 6].length) (baseStart_1970380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970380 prefixEnd_1970380 := by exact prefixLift 1970380
  have htrace : WordTrace (prefixWord ++ tailWord_1970380) baseStart_1970380 baseEnd_1970380 := by
    simpa [prefixWord, tailWord_1970380, baseEnd_1970380] using wordTrace_append hprefix tailTrace_1970380
  have hstable : (prefixWord ++ tailWord_1970380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970380).length < 2 ^ (prefixWord ++ tailWord_1970380).sum := by decide
  have hdescent : baseEnd_1970380 < baseStart_1970380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970408 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 5]
def baseStart_1970408 : Nat := 118140960795 + 1970408 * 2 ^ 59
def prefixEnd_1970408 : Nat := 4983230072969 + 3 ^ 40 * 1970408 * 2
def baseEnd_1970408 : Nat := 224836975436540445186281

theorem tailTrace_1970408 : CollatzResearch.WordTrace tailWord_1970408 prefixEnd_1970408 224836975436540445186281 := by
  unfold tailWord_1970408
  simp only [CollatzResearch.WordTrace]
  refine ⟨35933341922777904869935939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47911122563703873159914585 35933341922777904869935939)
  ·
    refine ⟨53900012884166857304903909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35933341922777904869935939 53900012884166857304903909)
    ·
      refine ⟨10106252415781285744669483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53900012884166857304903909 10106252415781285744669483)
      ·
        refine ⟨15159378623671928617004225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106252415781285744669483 15159378623671928617004225)
        ·
          refine ⟨11369533967753946462753169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15159378623671928617004225 11369533967753946462753169)
          ·
            refine ⟨8527150475815459847064877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11369533967753946462753169 8527150475815459847064877)
            ·
              refine ⟨3197681428430797442649329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8527150475815459847064877 3197681428430797442649329)
              ·
                refine ⟨2398261071323098081986997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3197681428430797442649329 2398261071323098081986997)
                ·
                  refine ⟨224836975436540445186281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2398261071323098081986997 224836975436540445186281)
                  ·
                    rfl

theorem cell22_1970408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_1970408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970408 prefixEnd_1970408 := by exact prefixLift 1970408
  have htrace : WordTrace (prefixWord ++ tailWord_1970408) baseStart_1970408 baseEnd_1970408 := by
    simpa [prefixWord, tailWord_1970408, baseEnd_1970408] using wordTrace_append hprefix tailTrace_1970408
  have hstable : (prefixWord ++ tailWord_1970408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970408).length < 2 ^ (prefixWord ++ tailWord_1970408).sum := by decide
  have hdescent : baseEnd_1970408 < baseStart_1970408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970451 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 1, 5]
def baseStart_1970451 : Nat := 118140960795 + 1970451 * 2 ^ 59
def prefixEnd_1970451 : Nat := 4983230072969 + 3 ^ 40 * 1970451 * 2
def baseEnd_1970451 : Nat := 674525646088383556733711

theorem tailTrace_1970451 : CollatzResearch.WordTrace tailWord_1970451 prefixEnd_1970451 674525646088383556733711 := by
  unfold tailWord_1970451
  simp only [CollatzResearch.WordTrace]
  refine ⟨71868252184400028083687207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47912168122933352055791471 71868252184400028083687207)
  ·
    refine ⟨107802378276600042125530811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71868252184400028083687207 107802378276600042125530811)
    ·
      refine ⟨161703567414900063188296217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107802378276600042125530811 161703567414900063188296217)
      ·
        refine ⟨121277675561175047391222163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161703567414900063188296217 121277675561175047391222163)
        ·
          refine ⟨181916513341762571086833245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121277675561175047391222163 181916513341762571086833245)
          ·
            refine ⟨68218692503160964157562467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181916513341762571086833245 68218692503160964157562467)
            ·
              refine ⟨102328038754741446236343701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68218692503160964157562467 102328038754741446236343701)
              ·
                refine ⟨4796626816628505292328611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102328038754741446236343701 4796626816628505292328611)
                ·
                  refine ⟨7194940224942757938492917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4796626816628505292328611 7194940224942757938492917)
                  ·
                    refine ⟨674525646088383556733711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7194940224942757938492917 674525646088383556733711)
                    ·
                      rfl

theorem cell22_1970451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_1970451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970451 prefixEnd_1970451 := by exact prefixLift 1970451
  have htrace : WordTrace (prefixWord ++ tailWord_1970451) baseStart_1970451 baseEnd_1970451 := by
    simpa [prefixWord, tailWord_1970451, baseEnd_1970451] using wordTrace_append hprefix tailTrace_1970451
  have hstable : (prefixWord ++ tailWord_1970451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970451).length < 2 ^ (prefixWord ++ tailWord_1970451).sum := by decide
  have hdescent : baseEnd_1970451 < baseStart_1970451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970485 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1970485 : Nat := 118140960795 + 1970485 * 2 ^ 59
def prefixEnd_1970485 : Nat := 4983230072969 + 3 ^ 40 * 1970485 * 2
def baseEnd_1970485 : Nat := 674537284983218801383607

theorem tailTrace_1970485 : CollatzResearch.WordTrace tailWord_1970485 prefixEnd_1970485 674537284983218801383607 := by
  unfold tailWord_1970485
  simp only [CollatzResearch.WordTrace]
  refine ⟨71869492266276851890424909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47912994844184567926949939 71869492266276851890424909)
  ·
    refine ⟨26951059599853819458909341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71869492266276851890424909 26951059599853819458909341)
    ·
      refine ⟨10106647349945182297091003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26951059599853819458909341 10106647349945182297091003)
      ·
        refine ⟨15159971024917773445636505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106647349945182297091003 15159971024917773445636505)
        ·
          refine ⟨11369978268688330084227379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15159971024917773445636505 11369978268688330084227379)
          ·
            refine ⟨17054967403032495126341069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11369978268688330084227379 17054967403032495126341069)
            ·
              refine ⟨6395612776137185672377901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17054967403032495126341069 6395612776137185672377901)
              ·
                refine ⟨2398354791051444627141713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6395612776137185672377901 2398354791051444627141713)
                ·
                  refine ⟨1798766093288583470356285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2398354791051444627141713 1798766093288583470356285)
                  ·
                    refine ⟨674537284983218801383607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1798766093288583470356285 674537284983218801383607)
                    ·
                      rfl

theorem cell22_1970485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1970485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970485 prefixEnd_1970485 := by exact prefixLift 1970485
  have htrace : WordTrace (prefixWord ++ tailWord_1970485) baseStart_1970485 baseEnd_1970485 := by
    simpa [prefixWord, tailWord_1970485, baseEnd_1970485] using wordTrace_append hprefix tailTrace_1970485
  have hstable : (prefixWord ++ tailWord_1970485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970485).length < 2 ^ (prefixWord ++ tailWord_1970485).sum := by decide
  have hdescent : baseEnd_1970485 < baseStart_1970485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970618 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_1970618 : Nat := 118140960795 + 1970618 * 2 ^ 59
def prefixEnd_1970618 : Nat := 4983230072969 + 3 ^ 40 * 1970618 * 2
def baseEnd_1970618 : Nat := 674582813601250787808199

theorem tailTrace_1970618 : CollatzResearch.WordTrace tailWord_1970618 prefixEnd_1970618 674582813601250787808199 := by
  unfold tailWord_1970618
  simp only [CollatzResearch.WordTrace]
  refine ⟨17968585793698753901254127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47916228783196677070011005 17968585793698753901254127)
  ·
    refine ⟨26952878690548130851881191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17968585793698753901254127 26952878690548130851881191)
    ·
      refine ⟨40429318035822196277821787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26952878690548130851881191 40429318035822196277821787)
      ·
        refine ⟨60643977053733294416732681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40429318035822196277821787 60643977053733294416732681)
        ·
          refine ⟨45482982790299970812549511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60643977053733294416732681 45482982790299970812549511)
          ·
            refine ⟨68224474185449956218824267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45482982790299970812549511 68224474185449956218824267)
            ·
              refine ⟨102336711278174934328236401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68224474185449956218824267 102336711278174934328236401)
              ·
                refine ⟨76752533458631200746177301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102336711278174934328236401 76752533458631200746177301)
                ·
                  refine ⟨3597775005873337534977061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76752533458631200746177301 3597775005873337534977061)
                  ·
                    refine ⟨674582813601250787808199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3597775005873337534977061 674582813601250787808199)
                    ·
                      rfl

theorem cell22_1970618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_1970618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970618 prefixEnd_1970618 := by exact prefixLift 1970618
  have htrace : WordTrace (prefixWord ++ tailWord_1970618) baseStart_1970618 baseEnd_1970618 := by
    simpa [prefixWord, tailWord_1970618, baseEnd_1970618] using wordTrace_append hprefix tailTrace_1970618
  have hstable : (prefixWord ++ tailWord_1970618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970618).length < 2 ^ (prefixWord ++ tailWord_1970618).sum := by decide
  have hdescent : baseEnd_1970618 < baseStart_1970618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970622 : List Nat := [4, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1970622 : Nat := 118140960795 + 1970622 * 2 ^ 59
def prefixEnd_1970622 : Nat := 4983230072969 + 3 ^ 40 * 1970622 * 2
def baseEnd_1970622 : Nat := 224861394294332036902729

theorem tailTrace_1970622 : CollatzResearch.WordTrace tailWord_1970622 prefixEnd_1970622 224861394294332036902729 := by
  unfold tailWord_1970622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984311133347565536020265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47916326044520349525441413 8984311133347565536020265)
  ·
    refine ⟨6738233350010674152015199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8984311133347565536020265 6738233350010674152015199)
    ·
      refine ⟨10107350025016011228022799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738233350010674152015199 10107350025016011228022799)
      ·
        refine ⟨15161025037524016842034199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10107350025016011228022799 15161025037524016842034199)
        ·
          refine ⟨22741537556286025263051299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15161025037524016842034199 22741537556286025263051299)
          ·
            refine ⟨34112306334429037894576949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22741537556286025263051299 34112306334429037894576949)
            ·
              refine ⟨3198028718852722302616589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34112306334429037894576949 3198028718852722302616589)
              ·
                refine ⟨1199260769569770863481221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3198028718852722302616589 1199260769569770863481221)
                ·
                  refine ⟨224861394294332036902729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199260769569770863481221 224861394294332036902729)
                  ·
                    rfl

theorem cell22_1970622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1970622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970622 prefixEnd_1970622 := by exact prefixLift 1970622
  have htrace : WordTrace (prefixWord ++ tailWord_1970622) baseStart_1970622 baseEnd_1970622 := by
    simpa [prefixWord, tailWord_1970622, baseEnd_1970622] using wordTrace_append hprefix tailTrace_1970622
  have hstable : (prefixWord ++ tailWord_1970622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970622).length < 2 ^ (prefixWord ++ tailWord_1970622).sum := by decide
  have hdescent : baseEnd_1970622 < baseStart_1970622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970658 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1970658 : Nat := 118140960795 + 1970658 * 2 ^ 59
def prefixEnd_1970658 : Nat := 4983230072969 + 3 ^ 40 * 1970658 * 2
def baseEnd_1970658 : Nat := 674596506418704016808077

theorem tailTrace_1970658 : CollatzResearch.WordTrace tailWord_1970658 prefixEnd_1970658 674596506418704016808077 := by
  unfold tailWord_1970658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17968950523662525609118157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47917201396433401624315085 17968950523662525609118157)
  ·
    refine ⟨6738356446373447103419309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17968950523662525609118157 6738356446373447103419309)
    ·
      refine ⟨2526883667390042663782241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6738356446373447103419309 2526883667390042663782241)
      ·
        refine ⟨1895162750542531997836681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2526883667390042663782241 1895162750542531997836681)
        ·
          refine ⟨1421372062906898998377511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1895162750542531997836681 1421372062906898998377511)
          ·
            refine ⟨2132058094360348497566267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421372062906898998377511 2132058094360348497566267)
            ·
              refine ⟨3198087141540522746349401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132058094360348497566267 3198087141540522746349401)
              ·
                refine ⟨2398565356155392059762051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3198087141540522746349401 2398565356155392059762051)
                ·
                  refine ⟨3597848034233088089643077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398565356155392059762051 3597848034233088089643077)
                  ·
                    refine ⟨674596506418704016808077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3597848034233088089643077 674596506418704016808077)
                    ·
                      rfl

theorem cell22_1970658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1970658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970658 prefixEnd_1970658 := by exact prefixLift 1970658
  have htrace : WordTrace (prefixWord ++ tailWord_1970658) baseStart_1970658 baseEnd_1970658 := by
    simpa [prefixWord, tailWord_1970658, baseEnd_1970658] using wordTrace_append hprefix tailTrace_1970658
  have hstable : (prefixWord ++ tailWord_1970658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970658).length < 2 ^ (prefixWord ++ tailWord_1970658).sum := by decide
  have hdescent : baseEnd_1970658 < baseStart_1970658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970699 : List Nat := [1, 1, 1, 1, 7, 2, 1, 4, 1, 3]
def baseStart_1970699 : Nat := 118140960795 + 1970699 * 2 ^ 59
def prefixEnd_1970699 : Nat := 4983230072969 + 3 ^ 40 * 1970699 * 2
def baseEnd_1970699 : Nat := 674610541556593576532951

theorem tailTrace_1970699 : CollatzResearch.WordTrace tailWord_1970699 prefixEnd_1970699 674610541556593576532951 := by
  unfold tailWord_1970699
  simp only [CollatzResearch.WordTrace]
  refine ⟨71877297487501566438715151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47918198325001044292476767 71877297487501566438715151)
  ·
    refine ⟨107815946231252349658072727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71877297487501566438715151 107815946231252349658072727)
    ·
      refine ⟨161723919346878524487109091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107815946231252349658072727 161723919346878524487109091)
      ·
        refine ⟨242585879020317786730663637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161723919346878524487109091 242585879020317786730663637)
        ·
          refine ⟨5685606539538698126499929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 242585879020317786730663637 5685606539538698126499929)
          ·
            refine ⟨4264204904654023594874947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5685606539538698126499929 4264204904654023594874947)
            ·
              refine ⟨6396307356981035392312421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264204904654023594874947 6396307356981035392312421)
              ·
                refine ⟨1199307629433944136058579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6396307356981035392312421 1199307629433944136058579)
                ·
                  refine ⟨1798961444150916204087869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199307629433944136058579 1798961444150916204087869)
                  ·
                    refine ⟨674610541556593576532951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1798961444150916204087869 674610541556593576532951)
                    ·
                      rfl

theorem cell22_1970699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 3].length) (baseStart_1970699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970699 prefixEnd_1970699 := by exact prefixLift 1970699
  have htrace : WordTrace (prefixWord ++ tailWord_1970699) baseStart_1970699 baseEnd_1970699 := by
    simpa [prefixWord, tailWord_1970699, baseEnd_1970699] using wordTrace_append hprefix tailTrace_1970699
  have hstable : (prefixWord ++ tailWord_1970699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970699).length < 2 ^ (prefixWord ++ tailWord_1970699).sum := by decide
  have hdescent : baseEnd_1970699 < baseStart_1970699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970725 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1970725 : Nat := 118140960795 + 1970725 * 2 ^ 59
def prefixEnd_1970725 : Nat := 4983230072969 + 3 ^ 40 * 1970725 * 2
def baseEnd_1970725 : Nat := 674619441887938175382871

theorem tailTrace_1970725 : CollatzResearch.WordTrace tailWord_1970725 prefixEnd_1970725 674619441887938175382871 := by
  unfold tailWord_1970725
  simp only [CollatzResearch.WordTrace]
  refine ⟨71878245785407372879161629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47918830523604915252774419 71878245785407372879161629)
  ·
    refine ⟨26954342169527764829685611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71878245785407372879161629 26954342169527764829685611)
    ·
      refine ⟨40431513254291647244528417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26954342169527764829685611 40431513254291647244528417)
      ·
        refine ⟨30323634940718735433396313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40431513254291647244528417 30323634940718735433396313)
        ·
          refine ⟨22742726205539051575047235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30323634940718735433396313 22742726205539051575047235)
          ·
            refine ⟨34114089308308577362570853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22742726205539051575047235 34114089308308577362570853)
            ·
              refine ⟨6396391745307858255482035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34114089308308577362570853 6396391745307858255482035)
              ·
                refine ⟨9594587617961787383223053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6396391745307858255482035 9594587617961787383223053)
                ·
                  refine ⟨3597970356735670268708645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9594587617961787383223053 3597970356735670268708645)
                  ·
                    refine ⟨674619441887938175382871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3597970356735670268708645 674619441887938175382871)
                    ·
                      rfl

theorem cell22_1970725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1970725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970725 prefixEnd_1970725 := by exact prefixLift 1970725
  have htrace : WordTrace (prefixWord ++ tailWord_1970725) baseStart_1970725 baseEnd_1970725 := by
    simpa [prefixWord, tailWord_1970725, baseEnd_1970725] using wordTrace_append hprefix tailTrace_1970725
  have hstable : (prefixWord ++ tailWord_1970725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970725).length < 2 ^ (prefixWord ++ tailWord_1970725).sum := by decide
  have hdescent : baseEnd_1970725 < baseStart_1970725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970757 : List Nat := [1, 3, 1, 1, 1, 5, 2, 4, 4]
def baseStart_1970757 : Nat := 118140960795 + 1970757 * 2 ^ 59
def prefixEnd_1970757 : Nat := 4983230072969 + 3 ^ 40 * 1970757 * 2
def baseEnd_1970757 : Nat := 224876798713966919527591

theorem tailTrace_1970757 : CollatzResearch.WordTrace tailWord_1970757 prefixEnd_1970757 224876798713966919527591 := by
  unfold tailWord_1970757
  simp only [CollatzResearch.WordTrace]
  refine ⟨71879412921291442344326525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47919608614194294896217683 71879412921291442344326525)
  ·
    refine ⟨26954779845484290879122447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71879412921291442344326525 26954779845484290879122447)
    ·
      refine ⟨40432169768226436318683671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26954779845484290879122447 40432169768226436318683671)
      ·
        refine ⟨60648254652339654478025507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40432169768226436318683671 60648254652339654478025507)
        ·
          refine ⟨90972381978509481717038261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60648254652339654478025507 90972381978509481717038261)
          ·
            refine ⟨8528660810485263910972337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90972381978509481717038261 8528660810485263910972337)
            ·
              refine ⟨6396495607863947933229253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8528660810485263910972337 6396495607863947933229253)
              ·
                refine ⟨1199342926474490237480485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6396495607863947933229253 1199342926474490237480485)
                ·
                  refine ⟨224876798713966919527591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199342926474490237480485 224876798713966919527591)
                  ·
                    rfl

theorem cell22_1970757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_1970757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970757 prefixEnd_1970757 := by exact prefixLift 1970757
  have htrace : WordTrace (prefixWord ++ tailWord_1970757) baseStart_1970757 baseEnd_1970757 := by
    simpa [prefixWord, tailWord_1970757, baseEnd_1970757] using wordTrace_append hprefix tailTrace_1970757
  have hstable : (prefixWord ++ tailWord_1970757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970757).length < 2 ^ (prefixWord ++ tailWord_1970757).sum := by decide
  have hdescent : baseEnd_1970757 < baseStart_1970757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970770 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1970770 : Nat := 118140960795 + 1970770 * 2 ^ 59
def prefixEnd_1970770 : Nat := 4983230072969 + 3 ^ 40 * 1970770 * 2
def baseEnd_1970770 : Nat := 674634846307573058007733

theorem tailTrace_1970770 : CollatzResearch.WordTrace tailWord_1970770 prefixEnd_1970770 674634846307573058007733 := by
  unfold tailWord_1970770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17969971767561086391137441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47919924713496230376366509 17969971767561086391137441)
  ·
    refine ⟨13477478825670814793353081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17969971767561086391137441 13477478825670814793353081)
    ·
      refine ⟨10108109119253111095014811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13477478825670814793353081 10108109119253111095014811)
      ·
        refine ⟨15162163678879666642522217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108109119253111095014811 15162163678879666642522217)
        ·
          refine ⟨11371622759159749981891663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15162163678879666642522217 11371622759159749981891663)
          ·
            refine ⟨17057434138739624972837495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11371622759159749981891663 17057434138739624972837495)
            ·
              refine ⟨25586151208109437459256243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17057434138739624972837495 25586151208109437459256243)
              ·
                refine ⟨38379226812164156188884365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25586151208109437459256243 38379226812164156188884365)
                ·
                  refine ⟨14392210054561558570831637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38379226812164156188884365 14392210054561558570831637)
                  ·
                    refine ⟨674634846307573058007733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14392210054561558570831637 674634846307573058007733)
                    ·
                      rfl

theorem cell22_1970770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1970770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970770 prefixEnd_1970770 := by exact prefixLift 1970770
  have htrace : WordTrace (prefixWord ++ tailWord_1970770) baseStart_1970770 baseEnd_1970770 := by
    simpa [prefixWord, tailWord_1970770, baseEnd_1970770] using wordTrace_append hprefix tailTrace_1970770
  have hstable : (prefixWord ++ tailWord_1970770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970770).length < 2 ^ (prefixWord ++ tailWord_1970770).sum := by decide
  have hdescent : baseEnd_1970770 < baseStart_1970770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970772 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1970772 : Nat := 118140960795 + 1970772 * 2 ^ 59
def prefixEnd_1970772 : Nat := 4983230072969 + 3 ^ 40 * 1970772 * 2
def baseEnd_1970772 : Nat := 674635530948445719457727

theorem tailTrace_1970772 : CollatzResearch.WordTrace tailWord_1970772 prefixEnd_1970772 674635530948445719457727 := by
  unfold tailWord_1970772
  simp only [CollatzResearch.WordTrace]
  refine ⟨35939980008118549953061285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47919973344158066604081713 35939980008118549953061285)
  ·
    refine ⟨6738746251522228116198991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35939980008118549953061285 6738746251522228116198991)
    ·
      refine ⟨10108119377283342174298487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738746251522228116198991 10108119377283342174298487)
      ·
        refine ⟨15162179065925013261447731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108119377283342174298487 15162179065925013261447731)
        ·
          refine ⟨22743268598887519892171597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15162179065925013261447731 22743268598887519892171597)
          ·
            refine ⟨8528725724582819959564349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22743268598887519892171597 8528725724582819959564349)
            ·
              refine ⟨3198272146718557484836631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8528725724582819959564349 3198272146718557484836631)
              ·
                refine ⟨4797408220077836227254947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3198272146718557484836631 4797408220077836227254947)
                ·
                  refine ⟨7196112330116754340882421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4797408220077836227254947 7196112330116754340882421)
                  ·
                    refine ⟨674635530948445719457727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7196112330116754340882421 674635530948445719457727)
                    ·
                      rfl

theorem cell22_1970772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1970772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970772 prefixEnd_1970772 := by exact prefixLift 1970772
  have htrace : WordTrace (prefixWord ++ tailWord_1970772) baseStart_1970772 baseEnd_1970772 := by
    simpa [prefixWord, tailWord_1970772, baseEnd_1970772] using wordTrace_append hprefix tailTrace_1970772
  have hstable : (prefixWord ++ tailWord_1970772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970772).length < 2 ^ (prefixWord ++ tailWord_1970772).sum := by decide
  have hdescent : baseEnd_1970772 < baseStart_1970772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970785 : List Nat := [1, 2, 3, 1, 1, 5, 1, 8]
def baseStart_1970785 : Nat := 118140960795 + 1970785 * 2 ^ 59
def prefixEnd_1970785 : Nat := 4983230072969 + 3 ^ 40 * 1970785 * 2
def baseEnd_1970785 : Nat := 74959997901568668764743

theorem tailTrace_1970785 : CollatzResearch.WordTrace tailWord_1970785 prefixEnd_1970785 74959997901568668764743 := by
  unfold tailWord_1970785
  simp only [CollatzResearch.WordTrace]
  refine ⟨71880434165190003126345809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47920289443460002084230539 71880434165190003126345809)
  ·
    refine ⟨53910325623892502344759357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71880434165190003126345809 53910325623892502344759357)
    ·
      refine ⟨20216372108959688379284759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53910325623892502344759357 20216372108959688379284759)
      ·
        refine ⟨30324558163439532568927139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20216372108959688379284759 30324558163439532568927139)
        ·
          refine ⟨45486837245159298853390709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30324558163439532568927139 45486837245159298853390709)
          ·
            refine ⟨4264390991733684267505379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45486837245159298853390709 4264390991733684267505379)
            ·
              refine ⟨6396586487600526401258069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264390991733684267505379 6396586487600526401258069)
              ·
                refine ⟨74959997901568668764743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6396586487600526401258069 74959997901568668764743)
                ·
                  rfl

theorem cell22_1970785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 8].length) (baseStart_1970785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970785 prefixEnd_1970785 := by exact prefixLift 1970785
  have htrace : WordTrace (prefixWord ++ tailWord_1970785) baseStart_1970785 baseEnd_1970785 := by
    simpa [prefixWord, tailWord_1970785, baseEnd_1970785] using wordTrace_append hprefix tailTrace_1970785
  have hstable : (prefixWord ++ tailWord_1970785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970785).length < 2 ^ (prefixWord ++ tailWord_1970785).sum := by decide
  have hdescent : baseEnd_1970785 < baseStart_1970785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970802 : List Nat := [3, 2, 1, 2, 4, 2, 8]
def baseStart_1970802 : Nat := 118140960795 + 1970802 * 2 ^ 59
def prefixEnd_1970802 : Nat := 4983230072969 + 3 ^ 40 * 1970802 * 2
def baseEnd_1970802 : Nat := 24986881502279097822505

theorem tailTrace_1970802 : CollatzResearch.WordTrace tailWord_1970802 prefixEnd_1970802 24986881502279097822505 := by
  unfold tailWord_1970802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17970263551532103757428665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47920702804085610019809773 17970263551532103757428665)
  ·
    refine ⟨13477697663649077818071499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17970263551532103757428665 13477697663649077818071499)
    ·
      refine ⟨20216546495473616727107249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13477697663649077818071499 20216546495473616727107249)
      ·
        refine ⟨15162409871605212545330437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20216546495473616727107249 15162409871605212545330437)
        ·
          refine ⟨2842951850925977352249457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15162409871605212545330437 2842951850925977352249457)
          ·
            refine ⟨2132213888194483014187093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2842951850925977352249457 2132213888194483014187093)
            ·
              refine ⟨24986881502279097822505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2132213888194483014187093 24986881502279097822505)
              ·
                rfl

theorem cell22_1970802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 8].length) (baseStart_1970802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970802 prefixEnd_1970802 := by exact prefixLift 1970802
  have htrace : WordTrace (prefixWord ++ tailWord_1970802) baseStart_1970802 baseEnd_1970802 := by
    simpa [prefixWord, tailWord_1970802, baseEnd_1970802] using wordTrace_append hprefix tailTrace_1970802
  have hstable : (prefixWord ++ tailWord_1970802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970802).length < 2 ^ (prefixWord ++ tailWord_1970802).sum := by decide
  have hdescent : baseEnd_1970802 < baseStart_1970802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970877 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1970877 : Nat := 118140960795 + 1970877 * 2 ^ 59
def prefixEnd_1970877 : Nat := 4983230072969 + 3 ^ 40 * 1970877 * 2
def baseEnd_1970877 : Nat := 674671474594260445582405

theorem tailTrace_1970877 : CollatzResearch.WordTrace tailWord_1970877 prefixEnd_1970877 674671474594260445582405 := by
  unfold tailWord_1970877
  simp only [CollatzResearch.WordTrace]
  refine ⟨71883789680856702838694885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47922526453904468559129923 71883789680856702838694885)
  ·
    refine ⟨13478210565160631782255291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71883789680856702838694885 13478210565160631782255291)
    ·
      refine ⟨20217315847740947673382937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13478210565160631782255291 20217315847740947673382937)
      ·
        refine ⟨15162986885805710755037203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20217315847740947673382937 15162986885805710755037203)
        ·
          refine ⟨22744480328708566132555805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15162986885805710755037203 22744480328708566132555805)
          ·
            refine ⟨8529180123265712299708427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22744480328708566132555805 8529180123265712299708427)
            ·
              refine ⟨12793770184898568449562641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529180123265712299708427 12793770184898568449562641)
              ·
                refine ⟨9595327638673926337171981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12793770184898568449562641 9595327638673926337171981)
                ·
                  refine ⟨3598247864502722376439493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9595327638673926337171981 3598247864502722376439493)
                  ·
                    refine ⟨674671474594260445582405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3598247864502722376439493 674671474594260445582405)
                    ·
                      rfl

theorem cell22_1970877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1970877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970877 prefixEnd_1970877 := by exact prefixLift 1970877
  have htrace : WordTrace (prefixWord ++ tailWord_1970877) baseStart_1970877 baseEnd_1970877 := by
    simpa [prefixWord, tailWord_1970877, baseEnd_1970877] using wordTrace_append hprefix tailTrace_1970877
  have hstable : (prefixWord ++ tailWord_1970877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970877).length < 2 ^ (prefixWord ++ tailWord_1970877).sum := by decide
  have hdescent : baseEnd_1970877 < baseStart_1970877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970892 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 8]
def baseStart_1970892 : Nat := 118140960795 + 1970892 * 2 ^ 59
def prefixEnd_1970892 : Nat := 4983230072969 + 3 ^ 40 * 1970892 * 2
def baseEnd_1970892 : Nat := 224892203133601802152453

theorem tailTrace_1970892 : CollatzResearch.WordTrace tailWord_1970892 prefixEnd_1970892 224892203133601802152453 := by
  unfold tailWord_1970892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35942168387901180200245465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47922891183868240266993953 35942168387901180200245465)
  ·
    refine ⟨26956626290925885150184099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35942168387901180200245465 26956626290925885150184099)
    ·
      refine ⟨40434939436388827725276149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26956626290925885150184099 40434939436388827725276149)
      ·
        refine ⟨3790775572161452599244639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40434939436388827725276149 3790775572161452599244639)
        ·
          refine ⟨5686163358242178898866959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790775572161452599244639 5686163358242178898866959)
          ·
            refine ⟨8529245037363268348300439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5686163358242178898866959 8529245037363268348300439)
            ·
              refine ⟨12793867556044902522450659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8529245037363268348300439 12793867556044902522450659)
              ·
                refine ⟨19190801334067353783675989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12793867556044902522450659 19190801334067353783675989)
                ·
                  refine ⟨224892203133601802152453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19190801334067353783675989 224892203133601802152453)
                  ·
                    rfl

theorem cell22_1970892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_1970892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970892 prefixEnd_1970892 := by exact prefixLift 1970892
  have htrace : WordTrace (prefixWord ++ tailWord_1970892) baseStart_1970892 baseEnd_1970892 := by
    simpa [prefixWord, tailWord_1970892, baseEnd_1970892] using wordTrace_append hprefix tailTrace_1970892
  have hstable : (prefixWord ++ tailWord_1970892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970892).length < 2 ^ (prefixWord ++ tailWord_1970892).sum := by decide
  have hdescent : baseEnd_1970892 < baseStart_1970892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970911 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 1, 4]
def baseStart_1970911 : Nat := 118140960795 + 1970911 * 2 ^ 59
def prefixEnd_1970911 : Nat := 4983230072969 + 3 ^ 40 * 1970911 * 2
def baseEnd_1970911 : Nat := 674683113489095690232301

theorem tailTrace_1970911 : CollatzResearch.WordTrace tailWord_1970911 prefixEnd_1970911 674683113489095690232301 := by
  unfold tailWord_1970911
  simp only [CollatzResearch.WordTrace]
  refine ⟨71885029762733526645432587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47923353175155684430288391 71885029762733526645432587)
  ·
    refine ⟨107827544644100289968148881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71885029762733526645432587 107827544644100289968148881)
    ·
      refine ⟨80870658483075217476111661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107827544644100289968148881 80870658483075217476111661)
      ·
        refine ⟨30326496931153206553541873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80870658483075217476111661 30326496931153206553541873)
        ·
          refine ⟨22744872698364904915156405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30326496931153206553541873 22744872698364904915156405)
          ·
            refine ⟨2132331815471709835795913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22744872698364904915156405 2132331815471709835795913)
            ·
              refine ⟨1599248861603782376846935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132331815471709835795913 1599248861603782376846935)
              ·
                refine ⟨2398873292405673565270403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599248861603782376846935 2398873292405673565270403)
                ·
                  refine ⟨3598309938608510347905605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2398873292405673565270403 3598309938608510347905605)
                  ·
                    refine ⟨674683113489095690232301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3598309938608510347905605 674683113489095690232301)
                    ·
                      rfl

theorem cell22_1970911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 4].length) (baseStart_1970911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970911 prefixEnd_1970911 := by exact prefixLift 1970911
  have htrace : WordTrace (prefixWord ++ tailWord_1970911) baseStart_1970911 baseEnd_1970911 := by
    simpa [prefixWord, tailWord_1970911, baseEnd_1970911] using wordTrace_append hprefix tailTrace_1970911
  have hstable : (prefixWord ++ tailWord_1970911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970911).length < 2 ^ (prefixWord ++ tailWord_1970911).sum := by decide
  have hdescent : baseEnd_1970911 < baseStart_1970911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970922 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1970922 : Nat := 118140960795 + 1970922 * 2 ^ 59
def prefixEnd_1970922 : Nat := 4983230072969 + 3 ^ 40 * 1970922 * 2
def baseEnd_1970922 : Nat := 674686879013895328207267

theorem tailTrace_1970922 : CollatzResearch.WordTrace tailWord_1970922 prefixEnd_1970922 674686879013895328207267 := by
  unfold tailWord_1970922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17971357741423418881020755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47923620643795783682722013 17971357741423418881020755)
  ·
    refine ⟨26957036612135128321531133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17971357741423418881020755 26957036612135128321531133)
    ·
      refine ⟨10108888729550673120574175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26957036612135128321531133 10108888729550673120574175)
      ·
        refine ⟨15163333094326009680861263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108888729550673120574175 15163333094326009680861263)
        ·
          refine ⟨22744999641489014521291895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15163333094326009680861263 22744999641489014521291895)
          ·
            refine ⟨34117499462233521781937843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22744999641489014521291895 34117499462233521781937843)
            ·
              refine ⟨51176249193350282672906765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34117499462233521781937843 51176249193350282672906765)
              ·
                refine ⟨19191093447506356002340037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51176249193350282672906765 19191093447506356002340037)
                ·
                  refine ⟨3598330021407441750438757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19191093447506356002340037 3598330021407441750438757)
                  ·
                    refine ⟨674686879013895328207267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3598330021407441750438757 674686879013895328207267)
                    ·
                      rfl

theorem cell22_1970922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1970922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970922 prefixEnd_1970922 := by exact prefixLift 1970922
  have htrace : WordTrace (prefixWord ++ tailWord_1970922) baseStart_1970922 baseEnd_1970922 := by
    simpa [prefixWord, tailWord_1970922, baseEnd_1970922] using wordTrace_append hprefix tailTrace_1970922
  have hstable : (prefixWord ++ tailWord_1970922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970922).length < 2 ^ (prefixWord ++ tailWord_1970922).sum := by decide
  have hdescent : baseEnd_1970922 < baseStart_1970922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970941 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_1970941 : Nat := 118140960795 + 1970941 * 2 ^ 59
def prefixEnd_1970941 : Nat := 4983230072969 + 3 ^ 40 * 1970941 * 2
def baseEnd_1970941 : Nat := 674693383102185611982209

theorem tailTrace_1970941 : CollatzResearch.WordTrace tailWord_1970941 prefixEnd_1970941 674693383102185611982209 := by
  unfold tailWord_1970941
  simp only [CollatzResearch.WordTrace]
  refine ⟨71886123952624841769024677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47924082635083227846016451 71886123952624841769024677)
  ·
    refine ⟨13478648241117157831692127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71886123952624841769024677 13478648241117157831692127)
    ·
      refine ⟨20217972361675736747538191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13478648241117157831692127 20217972361675736747538191)
      ·
        refine ⟨30326958542513605121307287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20217972361675736747538191 30326958542513605121307287)
        ·
          refine ⟨45490437813770407681960931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30326958542513605121307287 45490437813770407681960931)
          ·
            refine ⟨68235656720655611522941397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45490437813770407681960931 68235656720655611522941397)
            ·
              refine ⟨1599273204390365895068939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 68235656720655611522941397 1599273204390365895068939)
              ·
                refine ⟨2398909806585548842603409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599273204390365895068939 2398909806585548842603409)
                ·
                  refine ⟨1799182354939161631952557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2398909806585548842603409 1799182354939161631952557)
                  ·
                    refine ⟨674693383102185611982209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1799182354939161631952557 674693383102185611982209)
                    ·
                      rfl

theorem cell22_1970941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_1970941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970941 prefixEnd_1970941 := by exact prefixLift 1970941
  have htrace : WordTrace (prefixWord ++ tailWord_1970941) baseStart_1970941 baseEnd_1970941 := by
    simpa [prefixWord, tailWord_1970941, baseEnd_1970941] using wordTrace_append hprefix tailTrace_1970941
  have hstable : (prefixWord ++ tailWord_1970941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970941).length < 2 ^ (prefixWord ++ tailWord_1970941).sum := by decide
  have hdescent : baseEnd_1970941 < baseStart_1970941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971093 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_1971093 : Nat := 118140960795 + 1971093 * 2 ^ 59
def prefixEnd_1971093 : Nat := 4983230072969 + 3 ^ 40 * 1971093 * 2
def baseEnd_1971093 : Nat := 674745415808507882181743

theorem tailTrace_1971093 : CollatzResearch.WordTrace tailWord_1971093 prefixEnd_1971093 674745415808507882181743 := by
  unfold tailWord_1971093
  simp only [CollatzResearch.WordTrace]
  refine ⟨71891667848074171728557933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47927778565382781152371955 71891667848074171728557933)
  ·
    refine ⟨26959375443027814398209225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71891667848074171728557933 26959375443027814398209225)
    ·
      refine ⟨20219531582270860798656919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26959375443027814398209225 20219531582270860798656919)
      ·
        refine ⟨30329297373406291197985379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20219531582270860798656919 30329297373406291197985379)
        ·
          refine ⟨45493946060109436796978069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30329297373406291197985379 45493946060109436796978069)
          ·
            refine ⟨2132528721567629849858347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45493946060109436796978069 2132528721567629849858347)
            ·
              refine ⟨3198793082351444774787521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132528721567629849858347 3198793082351444774787521)
              ·
                refine ⟨2399094811763583581090641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3198793082351444774787521 2399094811763583581090641)
                ·
                  refine ⟨1799321108822687685817981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2399094811763583581090641 1799321108822687685817981)
                  ·
                    refine ⟨674745415808507882181743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1799321108822687685817981 674745415808507882181743)
                    ·
                      rfl

theorem cell22_1971093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_1971093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971093 prefixEnd_1971093 := by exact prefixLift 1971093
  have htrace : WordTrace (prefixWord ++ tailWord_1971093) baseStart_1971093 baseEnd_1971093 := by
    simpa [prefixWord, tailWord_1971093, baseEnd_1971093] using wordTrace_append hprefix tailTrace_1971093
  have hstable : (prefixWord ++ tailWord_1971093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971093).length < 2 ^ (prefixWord ++ tailWord_1971093).sum := by decide
  have hdescent : baseEnd_1971093 < baseStart_1971093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971134 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1971134 : Nat := 118140960795 + 1971134 * 2 ^ 59
def prefixEnd_1971134 : Nat := 4983230072969 + 3 ^ 40 * 1971134 * 2
def baseEnd_1971134 : Nat := 224919816982132480635539

theorem tailTrace_1971134 : CollatzResearch.WordTrace tailWord_1971134 prefixEnd_1971134 224919816982132480635539 := by
  unfold tailWord_1971134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8986645405115704466350057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47928775493950423820533637 8986645405115704466350057)
  ·
    refine ⟨6739984053836778349762543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8986645405115704466350057 6739984053836778349762543)
    ·
      refine ⟨10109976080755167524643815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739984053836778349762543 10109976080755167524643815)
      ·
        refine ⟨15164964121132751286965723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10109976080755167524643815 15164964121132751286965723)
        ·
          refine ⟨22747446181699126930448585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15164964121132751286965723 22747446181699126930448585)
          ·
            refine ⟨17060584636274345197836439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22747446181699126930448585 17060584636274345197836439)
            ·
              refine ⟨25590876954411517796754659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17060584636274345197836439 25590876954411517796754659)
              ·
                refine ⟨38386315431617276695131989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25590876954411517796754659 38386315431617276695131989)
                ·
                  refine ⟨224919816982132480635539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38386315431617276695131989 224919816982132480635539)
                  ·
                    rfl

theorem cell22_1971134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1971134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971134 prefixEnd_1971134 := by exact prefixLift 1971134
  have htrace : WordTrace (prefixWord ++ tailWord_1971134) baseStart_1971134 baseEnd_1971134 := by
    simpa [prefixWord, tailWord_1971134, baseEnd_1971134] using wordTrace_append hprefix tailTrace_1971134
  have hstable : (prefixWord ++ tailWord_1971134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971134).length < 2 ^ (prefixWord ++ tailWord_1971134).sum := by decide
  have hdescent : baseEnd_1971134 < baseStart_1971134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971228 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1971228 : Nat := 118140960795 + 1971228 * 2 ^ 59
def prefixEnd_1971228 : Nat := 4983230072969 + 3 ^ 40 * 1971228 * 2
def baseEnd_1971228 : Nat := 674791629067412530056329

theorem tailTrace_1971228 : CollatzResearch.WordTrace tailWord_1971228 prefixEnd_1971228 674791629067412530056329 := by
  unfold tailWord_1971228
  simp only [CollatzResearch.WordTrace]
  refine ⟨35948295851292544892361169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47931061135056726523148225 35948295851292544892361169)
  ·
    refine ⟨26961221888469408669270877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35948295851292544892361169 26961221888469408669270877)
    ·
      refine ⟨10110458208176028250976579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26961221888469408669270877 10110458208176028250976579)
      ·
        refine ⟨15165687312264042376464869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10110458208176028250976579 15165687312264042376464869)
        ·
          refine ⟨2843566371049507945587163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15165687312264042376464869 2843566371049507945587163)
          ·
            refine ⟨4265349556574261918380745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843566371049507945587163 4265349556574261918380745)
            ·
              refine ⟨3199012167430696438785559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4265349556574261918380745 3199012167430696438785559)
              ·
                refine ⟨4798518251146044658178339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199012167430696438785559 4798518251146044658178339)
                ·
                  refine ⟨7197777376719066987267509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798518251146044658178339 7197777376719066987267509)
                  ·
                    refine ⟨674791629067412530056329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7197777376719066987267509 674791629067412530056329)
                    ·
                      rfl

theorem cell22_1971228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1971228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971228 prefixEnd_1971228 := by exact prefixLift 1971228
  have htrace : WordTrace (prefixWord ++ tailWord_1971228) baseStart_1971228 baseEnd_1971228 := by
    simpa [prefixWord, tailWord_1971228, baseEnd_1971228] using wordTrace_append hprefix tailTrace_1971228
  have hstable : (prefixWord ++ tailWord_1971228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971228).length < 2 ^ (prefixWord ++ tailWord_1971228).sum := by decide
  have hdescent : baseEnd_1971228 < baseStart_1971228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971262 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_1971262 : Nat := 118140960795 + 1971262 * 2 ^ 59
def prefixEnd_1971262 : Nat := 4983230072969 + 3 ^ 40 * 1971262 * 2
def baseEnd_1971262 : Nat := 674803267962247774706225

theorem tailTrace_1971262 : CollatzResearch.WordTrace tailWord_1971262 prefixEnd_1971262 674803267962247774706225 := by
  unfold tailWord_1971262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987228973057739198932505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47931887856307942394306693 8987228973057739198932505)
  ·
    refine ⟨6740421729793304399199379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8987228973057739198932505 6740421729793304399199379)
    ·
      refine ⟨10110632594689956598799069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6740421729793304399199379 10110632594689956598799069)
      ·
        refine ⟨3791487223008733724549651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10110632594689956598799069 3791487223008733724549651)
        ·
          refine ⟨5687230834513100586824477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791487223008733724549651 5687230834513100586824477)
          ·
            refine ⟨2132711562942412720059179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5687230834513100586824477 2132711562942412720059179)
            ·
              refine ⟨3199067344413619080088769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132711562942412720059179 3199067344413619080088769)
              ·
                refine ⟨2399300508310214310066577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3199067344413619080088769 2399300508310214310066577)
                ·
                  refine ⟨1799475381232660732549933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2399300508310214310066577 1799475381232660732549933)
                  ·
                    refine ⟨674803267962247774706225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1799475381232660732549933 674803267962247774706225)
                    ·
                      rfl

theorem cell22_1971262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_1971262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971262 prefixEnd_1971262 := by exact prefixLift 1971262
  have htrace : WordTrace (prefixWord ++ tailWord_1971262) baseStart_1971262 baseEnd_1971262 := by
    simpa [prefixWord, tailWord_1971262, baseEnd_1971262] using wordTrace_append hprefix tailTrace_1971262
  have hstable : (prefixWord ++ tailWord_1971262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971262).length < 2 ^ (prefixWord ++ tailWord_1971262).sum := by decide
  have hdescent : baseEnd_1971262 < baseStart_1971262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971367 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1971367 : Nat := 118140960795 + 1971367 * 2 ^ 59
def prefixEnd_1971367 : Nat := 4983230072969 + 3 ^ 40 * 1971367 * 2
def baseEnd_1971367 : Nat := 674839211608062500830903

theorem tailTrace_1971367 : CollatzResearch.WordTrace tailWord_1971367 prefixEnd_1971367 674839211608062500830903 := by
  unfold tailWord_1971367
  simp only [CollatzResearch.WordTrace]
  refine ⟨71901661449081516524032355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47934440966054344349354903 71901661449081516524032355)
  ·
    refine ⟨107852492173622274786048533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71901661449081516524032355 107852492173622274786048533)
    ·
      refine ⟨5055585570638544130596025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107852492173622274786048533 5055585570638544130596025)
      ·
        refine ⟨3791689177978908097947019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5055585570638544130596025 3791689177978908097947019)
        ·
          refine ⟨5687533766968362146920529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791689177978908097947019 5687533766968362146920529)
          ·
            refine ⟨4265650325226271610190397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5687533766968362146920529 4265650325226271610190397)
            ·
              refine ⟨1599618871959851853821399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4265650325226271610190397 1599618871959851853821399)
              ·
                refine ⟨2399428307939777780732099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599618871959851853821399 2399428307939777780732099)
                ·
                  refine ⟨3599142461909666671098149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399428307939777780732099 3599142461909666671098149)
                  ·
                    refine ⟨674839211608062500830903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3599142461909666671098149 674839211608062500830903)
                    ·
                      rfl

theorem cell22_1971367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1971367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971367 prefixEnd_1971367 := by exact prefixLift 1971367
  have htrace : WordTrace (prefixWord ++ tailWord_1971367) baseStart_1971367 baseEnd_1971367 := by
    simpa [prefixWord, tailWord_1971367, baseEnd_1971367] using wordTrace_append hprefix tailTrace_1971367
  have hstable : (prefixWord ++ tailWord_1971367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971367).length < 2 ^ (prefixWord ++ tailWord_1971367).sum := by decide
  have hdescent : baseEnd_1971367 < baseStart_1971367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971378 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1971378 : Nat := 118140960795 + 1971378 * 2 ^ 59
def prefixEnd_1971378 : Nat := 4983230072969 + 3 ^ 40 * 1971378 * 2
def baseEnd_1971378 : Nat := 674842977132862138805869

theorem tailTrace_1971378 : CollatzResearch.WordTrace tailWord_1971378 prefixEnd_1971378 674842977132862138805869 := by
  unfold tailWord_1971378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17975515663010416350670697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47934708434694443601788525 17975515663010416350670697)
  ·
    refine ⟨13481636747257812263003023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17975515663010416350670697 13481636747257812263003023)
    ·
      refine ⟨20222455120886718394504535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13481636747257812263003023 20222455120886718394504535)
      ·
        refine ⟨30333682681330077591756803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20222455120886718394504535 30333682681330077591756803)
        ·
          refine ⟨45500524021995116387635205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30333682681330077591756803 45500524021995116387635205)
          ·
            refine ⟨8531348254124084322681601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45500524021995116387635205 8531348254124084322681601)
            ·
              refine ⟨6398511190593063242011201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8531348254124084322681601 6398511190593063242011201)
              ·
                refine ⟨4798883392944797431508401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6398511190593063242011201 4798883392944797431508401)
                ·
                  refine ⟨3599162544708598073631301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4798883392944797431508401 3599162544708598073631301)
                  ·
                    refine ⟨674842977132862138805869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3599162544708598073631301 674842977132862138805869)
                    ·
                      rfl

theorem cell22_1971378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1971378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971378 prefixEnd_1971378 := by exact prefixLift 1971378
  have htrace : WordTrace (prefixWord ++ tailWord_1971378) baseStart_1971378 baseEnd_1971378 := by
    simpa [prefixWord, tailWord_1971378, baseEnd_1971378] using wordTrace_append hprefix tailTrace_1971378
  have hstable : (prefixWord ++ tailWord_1971378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971378).length < 2 ^ (prefixWord ++ tailWord_1971378).sum := by decide
  have hdescent : baseEnd_1971378 < baseStart_1971378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971442 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_1971442 : Nat := 118140960795 + 1971442 * 2 ^ 59
def prefixEnd_1971442 : Nat := 4983230072969 + 3 ^ 40 * 1971442 * 2
def baseEnd_1971442 : Nat := 674864885640787305205673

theorem tailTrace_1971442 : CollatzResearch.WordTrace tailWord_1971442 prefixEnd_1971442 674864885640787305205673 := by
  unfold tailWord_1971442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17976099230952451083253145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47936264615873202888675053 17976099230952451083253145)
  ·
    refine ⟨13482074423214338312439859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17976099230952451083253145 13482074423214338312439859)
    ·
      refine ⟨20223111634821507468659789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13482074423214338312439859 20223111634821507468659789)
      ·
        refine ⟨7583666863058065300747421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20223111634821507468659789 7583666863058065300747421)
        ·
          refine ⟨2843875073646774487780283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7583666863058065300747421 2843875073646774487780283)
          ·
            refine ⟨4265812610470161731670425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843875073646774487780283 4265812610470161731670425)
            ·
              refine ⟨3199359457852621298752819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4265812610470161731670425 3199359457852621298752819)
              ·
                refine ⟨4799039186778931948129229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199359457852621298752819 4799039186778931948129229)
                ·
                  refine ⟨1799639695042099480548461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4799039186778931948129229 1799639695042099480548461)
                  ·
                    refine ⟨674864885640787305205673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1799639695042099480548461 674864885640787305205673)
                    ·
                      rfl

theorem cell22_1971442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_1971442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971442 prefixEnd_1971442 := by exact prefixLift 1971442
  have htrace : WordTrace (prefixWord ++ tailWord_1971442) baseStart_1971442 baseEnd_1971442 := by
    simpa [prefixWord, tailWord_1971442, baseEnd_1971442] using wordTrace_append hprefix tailTrace_1971442
  have hstable : (prefixWord ++ tailWord_1971442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971442).length < 2 ^ (prefixWord ++ tailWord_1971442).sum := by decide
  have hdescent : baseEnd_1971442 < baseStart_1971442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971455 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 5]
def baseStart_1971455 : Nat := 118140960795 + 1971455 * 2 ^ 59
def prefixEnd_1971455 : Nat := 4983230072969 + 3 ^ 40 * 1971455 * 2
def baseEnd_1971455 : Nat := 224956445268819868210211

theorem tailTrace_1971455 : CollatzResearch.WordTrace tailWord_1971455 prefixEnd_1971455 224956445268819868210211 := by
  unfold tailWord_1971455
  simp only [CollatzResearch.WordTrace]
  refine ⟨71904871072762707553235819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47936580715175138368823879 71904871072762707553235819)
  ·
    refine ⟨107857306609144061329853729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71904871072762707553235819 107857306609144061329853729)
    ·
      refine ⟨80892979956858045997390297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107857306609144061329853729 80892979956858045997390297)
      ·
        refine ⟨60669734967643534498042723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80892979956858045997390297 60669734967643534498042723)
        ·
          refine ⟨91004602451465301747064085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60669734967643534498042723 91004602451465301747064085)
          ·
            refine ⟨4265840739912436019393629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91004602451465301747064085 4265840739912436019393629)
            ·
              refine ⟨1599690277467163507272611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4265840739912436019393629 1599690277467163507272611)
              ·
                refine ⟨2399535416200745260908917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599690277467163507272611 2399535416200745260908917)
                ·
                  refine ⟨224956445268819868210211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2399535416200745260908917 224956445268819868210211)
                  ·
                    rfl

theorem cell22_1971455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 5].length) (baseStart_1971455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971455 prefixEnd_1971455 := by exact prefixLift 1971455
  have htrace : WordTrace (prefixWord ++ tailWord_1971455) baseStart_1971455 baseEnd_1971455 := by
    simpa [prefixWord, tailWord_1971455, baseEnd_1971455] using wordTrace_append hprefix tailTrace_1971455
  have hstable : (prefixWord ++ tailWord_1971455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971455).length < 2 ^ (prefixWord ++ tailWord_1971455).sum := by decide
  have hdescent : baseEnd_1971455 < baseStart_1971455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971562 : List Nat := [3, 1, 3, 3, 2, 2, 1, 7]
def baseStart_1971562 : Nat := 118140960795 + 1971562 * 2 ^ 59
def prefixEnd_1971562 : Nat := 4983230072969 + 3 ^ 40 * 1971562 * 2
def baseEnd_1971562 : Nat := 74989551565905221356145

theorem tailTrace_1971562 : CollatzResearch.WordTrace tailWord_1971562 prefixEnd_1971562 74989551565905221356145 := by
  unfold tailWord_1971562
  simp only [CollatzResearch.WordTrace]
  refine ⟨17977193420843766206845235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47939182455583376551587293 17977193420843766206845235)
  ·
    refine ⟨26965790131265649310267853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17977193420843766206845235 26965790131265649310267853)
    ·
      refine ⟨10112171299224618491350445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26965790131265649310267853 10112171299224618491350445)
      ·
        refine ⟨3792064237209231934256417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10112171299224618491350445 3792064237209231934256417)
        ·
          refine ⟨2844048177906923950692313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3792064237209231934256417 2844048177906923950692313)
          ·
            refine ⟨2133036133430192963019235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844048177906923950692313 2133036133430192963019235)
            ·
              refine ⟨3199554200145289444528853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133036133430192963019235 3199554200145289444528853)
              ·
                refine ⟨74989551565905221356145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3199554200145289444528853 74989551565905221356145)
                ·
                  rfl

theorem cell22_1971562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_1971562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971562 prefixEnd_1971562 := by exact prefixLift 1971562
  have htrace : WordTrace (prefixWord ++ tailWord_1971562) baseStart_1971562 baseEnd_1971562 := by
    simpa [prefixWord, tailWord_1971562, baseEnd_1971562] using wordTrace_append hprefix tailTrace_1971562
  have hstable : (prefixWord ++ tailWord_1971562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971562).length < 2 ^ (prefixWord ++ tailWord_1971562).sum := by decide
  have hdescent : baseEnd_1971562 < baseStart_1971562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971637 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1971637 : Nat := 118140960795 + 1971637 * 2 ^ 59
def prefixEnd_1971637 : Nat := 4983230072969 + 3 ^ 40 * 1971637 * 2
def baseEnd_1971637 : Nat := 674931638125871796580075

theorem tailTrace_1971637 : CollatzResearch.WordTrace tailWord_1971637 prefixEnd_1971637 674931638125871796580075 := by
  unfold tailWord_1971637
  simp only [CollatzResearch.WordTrace]
  refine ⟨71911509158103352636361165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47941006105402235090907443 71911509158103352636361165)
  ·
    refine ⟨26966815934288757238635437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71911509158103352636361165 26966815934288757238635437)
    ·
      refine ⟨10112555975358283964488289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26966815934288757238635437 10112555975358283964488289)
      ·
        refine ⟨7584416981518712973366217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10112555975358283964488289 7584416981518712973366217)
        ·
          refine ⟨5688312736139034730024663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7584416981518712973366217 5688312736139034730024663)
          ·
            refine ⟨8532469104208552095036995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688312736139034730024663 8532469104208552095036995)
            ·
              refine ⟨12798703656312828142555493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532469104208552095036995 12798703656312828142555493)
              ·
                refine ⟨2399756935558655276729155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12798703656312828142555493 2399756935558655276729155)
                ·
                  refine ⟨3599635403337982915093733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2399756935558655276729155 3599635403337982915093733)
                  ·
                    refine ⟨674931638125871796580075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3599635403337982915093733 674931638125871796580075)
                    ·
                      rfl

theorem cell22_1971637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1971637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971637 prefixEnd_1971637 := by exact prefixLift 1971637
  have htrace : WordTrace (prefixWord ++ tailWord_1971637) baseStart_1971637 baseEnd_1971637 := by
    simpa [prefixWord, tailWord_1971637, baseEnd_1971637] using wordTrace_append hprefix tailTrace_1971637
  have hstable : (prefixWord ++ tailWord_1971637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971637).length < 2 ^ (prefixWord ++ tailWord_1971637).sum := by decide
  have hdescent : baseEnd_1971637 < baseStart_1971637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971663 : List Nat := [1, 1, 2, 1, 1, 4, 12]
def baseStart_1971663 : Nat := 118140960795 + 1971663 * 2 ^ 59
def prefixEnd_1971663 : Nat := 4983230072969 + 3 ^ 40 * 1971663 * 2
def baseEnd_1971663 : Nat := 24997797720637644275185

theorem tailTrace_1971663 : CollatzResearch.WordTrace tailWord_1971663 prefixEnd_1971663 24997797720637644275185 := by
  unfold tailWord_1971663
  simp only [CollatzResearch.WordTrace]
  refine ⟨71912457456009159076807643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47941638304006106051205095 71912457456009159076807643)
  ·
    refine ⟨107868686184013738615211465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71912457456009159076807643 107868686184013738615211465)
    ·
      refine ⟨80901514638010303961408599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107868686184013738615211465 80901514638010303961408599)
      ·
        refine ⟨121352271957015455942112899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80901514638010303961408599 121352271957015455942112899)
        ·
          refine ⟨182028407935523183913169349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121352271957015455942112899 182028407935523183913169349)
          ·
            refine ⟨34130326487910596983719253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182028407935523183913169349 34130326487910596983719253)
            ·
              refine ⟨24997797720637644275185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34130326487910596983719253 24997797720637644275185)
              ·
                rfl

theorem cell22_1971663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 12].length) (baseStart_1971663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971663 prefixEnd_1971663 := by exact prefixLift 1971663
  have htrace : WordTrace (prefixWord ++ tailWord_1971663) baseStart_1971663 baseEnd_1971663 := by
    simpa [prefixWord, tailWord_1971663, baseEnd_1971663] using wordTrace_append hprefix tailTrace_1971663
  have hstable : (prefixWord ++ tailWord_1971663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971663).length < 2 ^ (prefixWord ++ tailWord_1971663).sum := by decide
  have hdescent : baseEnd_1971663 < baseStart_1971663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971669 : List Nat := [1, 3, 2, 3, 1, 1, 5, 2, 4]
def baseStart_1971669 : Nat := 118140960795 + 1971669 * 2 ^ 59
def prefixEnd_1971669 : Nat := 4983230072969 + 3 ^ 40 * 1971669 * 2
def baseEnd_1971669 : Nat := 224980864126611459926659

theorem tailTrace_1971669 : CollatzResearch.WordTrace tailWord_1971669 prefixEnd_1971669 224980864126611459926659 := by
  unfold tailWord_1971669
  simp only [CollatzResearch.WordTrace]
  refine ⟨71912676293987422101526061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47941784195991614734350707 71912676293987422101526061)
  ·
    refine ⟨26967253610245283288072273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71912676293987422101526061 26967253610245283288072273)
    ·
      refine ⟨20225440207683962466054205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26967253610245283288072273 20225440207683962466054205)
      ·
        refine ⟨7584540077881485924770327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20225440207683962466054205 7584540077881485924770327)
        ·
          refine ⟨11376810116822228887155491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7584540077881485924770327 11376810116822228887155491)
          ·
            refine ⟨17065215175233343330733237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11376810116822228887155491 17065215175233343330733237)
            ·
              refine ⟨1599863922678125937256241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17065215175233343330733237 1599863922678125937256241)
              ·
                refine ⟨1199897942008594452942181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599863922678125937256241 1199897942008594452942181)
                ·
                  refine ⟨224980864126611459926659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1199897942008594452942181 224980864126611459926659)
                  ·
                    rfl

theorem cell22_1971669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_1971669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971669 prefixEnd_1971669 := by exact prefixLift 1971669
  have htrace : WordTrace (prefixWord ++ tailWord_1971669) baseStart_1971669 baseEnd_1971669 := by
    simpa [prefixWord, tailWord_1971669, baseEnd_1971669] using wordTrace_append hprefix tailTrace_1971669
  have hstable : (prefixWord ++ tailWord_1971669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971669).length < 2 ^ (prefixWord ++ tailWord_1971669).sum := by decide
  have hdescent : baseEnd_1971669 < baseStart_1971669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971729 : List Nat := [1, 2, 2, 1, 1, 2, 5, 4, 1, 3]
def baseStart_1971729 : Nat := 118140960795 + 1971729 * 2 ^ 59
def prefixEnd_1971729 : Nat := 4983230072969 + 3 ^ 40 * 1971729 * 2
def baseEnd_1971729 : Nat := 674963131606014223279793

theorem tailTrace_1971729 : CollatzResearch.WordTrace tailWord_1971729 prefixEnd_1971729 674963131606014223279793 := by
  unfold tailWord_1971729
  simp only [CollatzResearch.WordTrace]
  refine ⟨71914864673770052348710241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47943243115846701565806827 71914864673770052348710241)
  ·
    refine ⟨53936148505327539261532681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71914864673770052348710241 53936148505327539261532681)
    ·
      refine ⟨40452111378995654446149511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53936148505327539261532681 40452111378995654446149511)
      ·
        refine ⟨60678167068493481669224267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40452111378995654446149511 60678167068493481669224267)
        ·
          refine ⟨91017250602740222503836401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60678167068493481669224267 91017250602740222503836401)
          ·
            refine ⟨68262937952055166877877301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91017250602740222503836401 68262937952055166877877301)
            ·
              refine ⟨6399650433005171894800997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68262937952055166877877301 6399650433005171894800997)
              ·
                refine ⟨1199934456188469730275187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6399650433005171894800997 1199934456188469730275187)
                ·
                  refine ⟨1799901684282704595412781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199934456188469730275187 1799901684282704595412781)
                  ·
                    refine ⟨674963131606014223279793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1799901684282704595412781 674963131606014223279793)
                    ·
                      rfl

theorem cell22_1971729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_1971729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971729 prefixEnd_1971729 := by exact prefixLift 1971729
  have htrace : WordTrace (prefixWord ++ tailWord_1971729) baseStart_1971729 baseEnd_1971729 := by
    simpa [prefixWord, tailWord_1971729, baseEnd_1971729] using wordTrace_append hprefix tailTrace_1971729
  have hstable : (prefixWord ++ tailWord_1971729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971729).length < 2 ^ (prefixWord ++ tailWord_1971729).sum := by decide
  have hdescent : baseEnd_1971729 < baseStart_1971729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971770 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_1971770 : Nat := 118140960795 + 1971770 * 2 ^ 59
def prefixEnd_1971770 : Nat := 4983230072969 + 3 ^ 40 * 1971770 * 2
def baseEnd_1971770 : Nat := 224992388914634594334889

theorem tailTrace_1971770 : CollatzResearch.WordTrace tailWord_1971770 prefixEnd_1971770 224992388914634594334889 := by
  unfold tailWord_1971770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17979090016655379087738191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47944240044414344233968509 17979090016655379087738191)
  ·
    refine ⟨26968635024983068631607287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17979090016655379087738191 26968635024983068631607287)
    ·
      refine ⟨40452952537474602947410931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26968635024983068631607287 40452952537474602947410931)
      ·
        refine ⟨60679428806211904421116397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40452952537474602947410931 60679428806211904421116397)
        ·
          refine ⟨22754785802329464157918649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60679428806211904421116397 22754785802329464157918649)
          ·
            refine ⟨17066089351747098118438987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22754785802329464157918649 17066089351747098118438987)
            ·
              refine ⟨25599134027620647177658481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17066089351747098118438987 25599134027620647177658481)
              ·
                refine ⟨19199350520715485383243861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25599134027620647177658481 19199350520715485383243861)
                ·
                  refine ⟨224992388914634594334889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19199350520715485383243861 224992388914634594334889)
                  ·
                    rfl

theorem cell22_1971770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_1971770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971770 prefixEnd_1971770 := by exact prefixLift 1971770
  have htrace : WordTrace (prefixWord ++ tailWord_1971770) baseStart_1971770 baseEnd_1971770 := by
    simpa [prefixWord, tailWord_1971770, baseEnd_1971770] using wordTrace_append hprefix tailTrace_1971770
  have hstable : (prefixWord ++ tailWord_1971770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971770).length < 2 ^ (prefixWord ++ tailWord_1971770).sum := by decide
  have hdescent : baseEnd_1971770 < baseStart_1971770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971785 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_1971785 : Nat := 118140960795 + 1971785 * 2 ^ 59
def prefixEnd_1971785 : Nat := 4983230072969 + 3 ^ 40 * 1971785 * 2
def baseEnd_1971785 : Nat := 674982301550448743879621

theorem tailTrace_1971785 : CollatzResearch.WordTrace tailWord_1971785 prefixEnd_1971785 674982301550448743879621 := by
  unfold tailWord_1971785
  simp only [CollatzResearch.WordTrace]
  refine ⟨71916907161567173912748809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47944604774378115941832539 71916907161567173912748809)
  ·
    refine ⟨53937680371175380434561607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71916907161567173912748809 53937680371175380434561607)
    ·
      refine ⟨80906520556763070651842411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53937680371175380434561607 80906520556763070651842411)
      ·
        refine ⟨121359780835144605977763617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80906520556763070651842411 121359780835144605977763617)
        ·
          refine ⟨91019835626358454483322713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121359780835144605977763617 91019835626358454483322713)
          ·
            refine ⟨68264876719768840862492035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91019835626358454483322713 68264876719768840862492035)
            ·
              refine ⟨102397315079653261293738053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68264876719768840862492035 102397315079653261293738053)
              ·
                refine ⟨19199496577434986492575885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102397315079653261293738053 19199496577434986492575885)
                ·
                  refine ⟨7199811216538119934715957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19199496577434986492575885 7199811216538119934715957)
                  ·
                    refine ⟨674982301550448743879621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7199811216538119934715957 674982301550448743879621)
                    ·
                      rfl

theorem cell22_1971785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_1971785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971785 prefixEnd_1971785 := by exact prefixLift 1971785
  have htrace : WordTrace (prefixWord ++ tailWord_1971785) baseStart_1971785 baseEnd_1971785 := by
    simpa [prefixWord, tailWord_1971785, baseEnd_1971785] using wordTrace_append hprefix tailTrace_1971785
  have hstable : (prefixWord ++ tailWord_1971785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971785).length < 2 ^ (prefixWord ++ tailWord_1971785).sum := by decide
  have hdescent : baseEnd_1971785 < baseStart_1971785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971898 : List Nat := [3, 1, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_1971898 : Nat := 118140960795 + 1971898 * 2 ^ 59
def prefixEnd_1971898 : Nat := 4983230072969 + 3 ^ 40 * 1971898 * 2
def baseEnd_1971898 : Nat := 675020983759754115804275

theorem tailTrace_1971898 : CollatzResearch.WordTrace tailWord_1971898 prefixEnd_1971898 675020983759754115804275 := by
  unfold tailWord_1971898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17980257152539448552903087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47947352406771862807741565 17980257152539448552903087)
  ·
    refine ⟨26970385728809172829354631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17980257152539448552903087 26970385728809172829354631)
    ·
      refine ⟨40455578593213759244031947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26970385728809172829354631 40455578593213759244031947)
      ·
        refine ⟨60683367889820638866047921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40455578593213759244031947 60683367889820638866047921)
        ·
          refine ⟨45512525917365479149535941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60683367889820638866047921 45512525917365479149535941)
          ·
            refine ⟨8533598609506027340537989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45512525917365479149535941 8533598609506027340537989)
            ·
              refine ⟨1600049739282380126350873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8533598609506027340537989 1600049739282380126350873)
              ·
                refine ⟨1200037304461785094763155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600049739282380126350873 1200037304461785094763155)
                ·
                  refine ⟨1800055956692677642144733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200037304461785094763155 1800055956692677642144733)
                  ·
                    refine ⟨675020983759754115804275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800055956692677642144733 675020983759754115804275)
                    ·
                      rfl

theorem cell22_1971898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_1971898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971898 prefixEnd_1971898 := by exact prefixLift 1971898
  have htrace : WordTrace (prefixWord ++ tailWord_1971898) baseStart_1971898 baseEnd_1971898 := by
    simpa [prefixWord, tailWord_1971898, baseEnd_1971898] using wordTrace_append hprefix tailTrace_1971898
  have hstable : (prefixWord ++ tailWord_1971898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971898).length < 2 ^ (prefixWord ++ tailWord_1971898).sum := by decide
  have hdescent : baseEnd_1971898 < baseStart_1971898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1971986 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1971986 : Nat := 118140960795 + 1971986 * 2 ^ 59
def prefixEnd_1971986 : Nat := 4983230072969 + 3 ^ 40 * 1971986 * 2
def baseEnd_1971986 : Nat := 675051107958151219604005

theorem tailTrace_1971986 : CollatzResearch.WordTrace tailWord_1971986 prefixEnd_1971986 675051107958151219604005 := by
  unfold tailWord_1971986
  simp only [CollatzResearch.WordTrace]
  refine ⟨17981059558459746310203953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47949492155892656827210541 17981059558459746310203953)
  ·
    refine ⟨13485794668844809732652965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17981059558459746310203953 13485794668844809732652965)
    ·
      refine ⟨2528586500408401824872431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13485794668844809732652965 2528586500408401824872431)
      ·
        refine ⟨3792879750612602737308647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528586500408401824872431 3792879750612602737308647)
        ·
          refine ⟨5689319625918904105962971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792879750612602737308647 5689319625918904105962971)
          ·
            refine ⟨8533979438878356158944457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689319625918904105962971 8533979438878356158944457)
            ·
              refine ⟨6400484579158767119208343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8533979438878356158944457 6400484579158767119208343)
              ·
                refine ⟨9600726868738150678812515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6400484579158767119208343 9600726868738150678812515)
                ·
                  refine ⟨14401090303107226018218773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9600726868738150678812515 14401090303107226018218773)
                  ·
                    refine ⟨675051107958151219604005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14401090303107226018218773 675051107958151219604005)
                    ·
                      rfl

theorem cell22_1971986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1971986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1971986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1971986 prefixEnd_1971986 := by exact prefixLift 1971986
  have htrace : WordTrace (prefixWord ++ tailWord_1971986) baseStart_1971986 baseEnd_1971986 := by
    simpa [prefixWord, tailWord_1971986, baseEnd_1971986] using wordTrace_append hprefix tailTrace_1971986
  have hstable : (prefixWord ++ tailWord_1971986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1971986).length < 2 ^ (prefixWord ++ tailWord_1971986).sum := by decide
  have hdescent : baseEnd_1971986 < baseStart_1971986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1971986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972022 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1972022 : Nat := 118140960795 + 1972022 * 2 ^ 59
def prefixEnd_1972022 : Nat := 4983230072969 + 3 ^ 40 * 1972022 * 2
def baseEnd_1972022 : Nat := 675063431493859125703895

theorem tailTrace_1972022 : CollatzResearch.WordTrace tailWord_1972022 prefixEnd_1972022 675063431493859125703895 := by
  unfold tailWord_1972022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495346953856785211820395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47950367507805708926084213 4495346953856785211820395)
  ·
    refine ⟨6743020430785177817730593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4495346953856785211820395 6743020430785177817730593)
    ·
      refine ⟨5057265323088883363297945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6743020430785177817730593 5057265323088883363297945)
      ·
        refine ⟨3792948992316662522473459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057265323088883363297945 3792948992316662522473459)
        ·
          refine ⟨5689423488474993783710189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792948992316662522473459 5689423488474993783710189)
          ·
            refine ⟨2133533808178122668891321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5689423488474993783710189 2133533808178122668891321)
            ·
              refine ⟨1600150356133592001668491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133533808178122668891321 1600150356133592001668491)
              ·
                refine ⟨2400225534200388002502737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600150356133592001668491 2400225534200388002502737)
                ·
                  refine ⟨1800169150650291001877053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2400225534200388002502737 1800169150650291001877053)
                  ·
                    refine ⟨675063431493859125703895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800169150650291001877053 675063431493859125703895)
                    ·
                      rfl

theorem cell22_1972022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1972022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972022 prefixEnd_1972022 := by exact prefixLift 1972022
  have htrace : WordTrace (prefixWord ++ tailWord_1972022) baseStart_1972022 baseEnd_1972022 := by
    simpa [prefixWord, tailWord_1972022, baseEnd_1972022] using wordTrace_append hprefix tailTrace_1972022
  have hstable : (prefixWord ++ tailWord_1972022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972022).length < 2 ^ (prefixWord ++ tailWord_1972022).sum := by decide
  have hdescent : baseEnd_1972022 < baseStart_1972022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972067 : List Nat := [1, 1, 1, 5, 4, 2, 2, 2, 1, 3]
def baseStart_1972067 : Nat := 118140960795 + 1972067 * 2 ^ 59
def prefixEnd_1972067 : Nat := 4983230072969 + 3 ^ 40 * 1972067 * 2
def baseEnd_1972067 : Nat := 675078835913494008328757

theorem tailTrace_1972067 : CollatzResearch.WordTrace tailWord_1972067 prefixEnd_1972067 675078835913494008328757 := by
  unfold tailWord_1972067
  simp only [CollatzResearch.WordTrace]
  refine ⟨71927192546545536074514455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47951461697697024049676303 71927192546545536074514455)
  ·
    refine ⟨107890788819818304111771683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71927192546545536074514455 107890788819818304111771683)
    ·
      refine ⟨161836183229727456167657525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107890788819818304111771683 161836183229727456167657525)
      ·
        refine ⟨15172142177786949015717893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161836183229727456167657525 15172142177786949015717893)
        ·
          refine ⟨2844776658335052940447105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15172142177786949015717893 2844776658335052940447105)
          ·
            refine ⟨2133582493751289705335329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844776658335052940447105 2133582493751289705335329)
            ·
              refine ⟨1600186870313467279001497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133582493751289705335329 1600186870313467279001497)
              ·
                refine ⟨1200140152735100459251123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600186870313467279001497 1200140152735100459251123)
                ·
                  refine ⟨1800210229102650688876685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200140152735100459251123 1800210229102650688876685)
                  ·
                    refine ⟨675078835913494008328757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800210229102650688876685 675078835913494008328757)
                    ·
                      rfl

theorem cell22_1972067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 3].length) (baseStart_1972067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972067 prefixEnd_1972067 := by exact prefixLift 1972067
  have htrace : WordTrace (prefixWord ++ tailWord_1972067) baseStart_1972067 baseEnd_1972067 := by
    simpa [prefixWord, tailWord_1972067, baseEnd_1972067] using wordTrace_append hprefix tailTrace_1972067
  have hstable : (prefixWord ++ tailWord_1972067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972067).length < 2 ^ (prefixWord ++ tailWord_1972067).sum := by decide
  have hdescent : baseEnd_1972067 < baseStart_1972067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972110 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_1972110 : Nat := 118140960795 + 1972110 * 2 ^ 59
def prefixEnd_1972110 : Nat := 4983230072969 + 3 ^ 40 * 1972110 * 2
def baseEnd_1972110 : Nat := 675093555692256229503625

theorem tailTrace_1972110 : CollatzResearch.WordTrace tailWord_1972110 prefixEnd_1972110 675093555692256229503625 := by
  unfold tailWord_1972110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8991095110673719302291223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47952507256926502945553189 8991095110673719302291223)
  ·
    refine ⟨13486642666010578953436835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8991095110673719302291223 13486642666010578953436835)
    ·
      refine ⟨20229963999015868430155253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13486642666010578953436835 20229963999015868430155253)
      ·
        refine ⟨1896559124907737665327055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20229963999015868430155253 1896559124907737665327055)
        ·
          refine ⟨2844838687361606497990583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896559124907737665327055 2844838687361606497990583)
          ·
            refine ⟨4267258031042409746985875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844838687361606497990583 4267258031042409746985875)
            ·
              refine ⟨6400887046563614620478813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267258031042409746985875 6400887046563614620478813)
              ·
                refine ⟨2400332642461355482679555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6400887046563614620478813 2400332642461355482679555)
                ·
                  refine ⟨3600498963692033224019333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400332642461355482679555 3600498963692033224019333)
                  ·
                    refine ⟨675093555692256229503625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3600498963692033224019333 675093555692256229503625)
                    ·
                      rfl

theorem cell22_1972110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_1972110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972110 prefixEnd_1972110 := by exact prefixLift 1972110
  have htrace : WordTrace (prefixWord ++ tailWord_1972110) baseStart_1972110 baseEnd_1972110 := by
    simpa [prefixWord, tailWord_1972110, baseEnd_1972110] using wordTrace_append hprefix tailTrace_1972110
  have hstable : (prefixWord ++ tailWord_1972110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972110).length < 2 ^ (prefixWord ++ tailWord_1972110).sum := by decide
  have hdescent : baseEnd_1972110 < baseStart_1972110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972119 : List Nat := [1, 1, 3, 3, 1, 4, 9]
def baseStart_1972119 : Nat := 118140960795 + 1972119 * 2 ^ 59
def prefixEnd_1972119 : Nat := 4983230072969 + 3 ^ 40 * 1972119 * 2
def baseEnd_1972119 : Nat := 25003579132451229852911

theorem tailTrace_1972119 : CollatzResearch.WordTrace tailWord_1972119 prefixEnd_1972119 25003579132451229852911 := by
  unfold tailWord_1972119
  simp only [CollatzResearch.WordTrace]
  refine ⟨71929089142357148955407411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47952726094904765970271607 71929089142357148955407411)
  ·
    refine ⟨107893633713535723433111117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71929089142357148955407411 107893633713535723433111117)
    ·
      refine ⟨40460112642575896287416669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107893633713535723433111117 40460112642575896287416669)
      ·
        refine ⟨15172542240965961107781251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40460112642575896287416669 15172542240965961107781251)
        ·
          refine ⟨22758813361448941661671877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15172542240965961107781251 22758813361448941661671877)
          ·
            refine ⟨4267277505271676561563477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22758813361448941661671877 4267277505271676561563477)
            ·
              refine ⟨25003579132451229852911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4267277505271676561563477 25003579132451229852911)
              ·
                rfl

theorem cell22_1972119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 9].length) (baseStart_1972119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972119 prefixEnd_1972119 := by exact prefixLift 1972119
  have htrace : WordTrace (prefixWord ++ tailWord_1972119) baseStart_1972119 baseEnd_1972119 := by
    simpa [prefixWord, tailWord_1972119, baseEnd_1972119] using wordTrace_append hprefix tailTrace_1972119
  have hstable : (prefixWord ++ tailWord_1972119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972119).length < 2 ^ (prefixWord ++ tailWord_1972119).sum := by decide
  have hdescent : baseEnd_1972119 < baseStart_1972119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972181 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 7]
def baseStart_1972181 : Nat := 118140960795 + 1972181 * 2 ^ 59
def prefixEnd_1972181 : Nat := 4983230072969 + 3 ^ 40 * 1972181 * 2
def baseEnd_1972181 : Nat := 225039286814411903659469

theorem tailTrace_1972181 : CollatzResearch.WordTrace tailWord_1972181 prefixEnd_1972181 225039286814411903659469 := by
  unfold tailWord_1972181
  simp only [CollatzResearch.WordTrace]
  refine ⟨71931350468132533544164397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47954233645421689029442931 71931350468132533544164397)
  ·
    refine ⟨26974256425549700079061649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71931350468132533544164397 26974256425549700079061649)
    ·
      refine ⟨20230692319162275059296237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26974256425549700079061649 20230692319162275059296237)
      ·
        refine ⟨7586509619685853147236089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20230692319162275059296237 7586509619685853147236089)
        ·
          refine ⟨5689882214764389860427067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7586509619685853147236089 5689882214764389860427067)
          ·
            refine ⟨8534823322146584790640601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689882214764389860427067 8534823322146584790640601)
            ·
              refine ⟨6401117491609938592980451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8534823322146584790640601 6401117491609938592980451)
              ·
                refine ⟨9601676237414907889470677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6401117491609938592980451 9601676237414907889470677)
                ·
                  refine ⟨225039286814411903659469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9601676237414907889470677 225039286814411903659469)
                  ·
                    rfl

theorem cell22_1972181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_1972181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972181 prefixEnd_1972181 := by exact prefixLift 1972181
  have htrace : WordTrace (prefixWord ++ tailWord_1972181) baseStart_1972181 baseEnd_1972181 := by
    simpa [prefixWord, tailWord_1972181, baseEnd_1972181] using wordTrace_append hprefix tailTrace_1972181
  have hstable : (prefixWord ++ tailWord_1972181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972181).length < 2 ^ (prefixWord ++ tailWord_1972181).sum := by decide
  have hdescent : baseEnd_1972181 < baseStart_1972181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972185 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 3, 3]
def baseStart_1972185 : Nat := 118140960795 + 1972185 * 2 ^ 59
def prefixEnd_1972185 : Nat := 4983230072969 + 3 ^ 40 * 1972185 * 2
def baseEnd_1972185 : Nat := 675119229724981033878395

theorem tailTrace_1972185 : CollatzResearch.WordTrace tailWord_1972185 prefixEnd_1972185 675119229724981033878395 := by
  unfold tailWord_1972185
  simp only [CollatzResearch.WordTrace]
  refine ⟨71931496360118042227310009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47954330906745361484873339 71931496360118042227310009)
  ·
    refine ⟨53948622270088531670482507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71931496360118042227310009 53948622270088531670482507)
    ·
      refine ⟨80922933405132797505723761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53948622270088531670482507 80922933405132797505723761)
      ·
        refine ⟨60692200053849598129292821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80922933405132797505723761 60692200053849598129292821)
        ·
          refine ⟨2844946877524199912310601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60692200053849598129292821 2844946877524199912310601)
          ·
            refine ⟨2133710158143149934232951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844946877524199912310601 2133710158143149934232951)
            ·
              refine ⟨3200565237214724901349427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133710158143149934232951 3200565237214724901349427)
              ·
                refine ⟨4800847855822087352024141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200565237214724901349427 4800847855822087352024141)
                ·
                  refine ⟨1800317945933282757009053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4800847855822087352024141 1800317945933282757009053)
                  ·
                    refine ⟨675119229724981033878395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800317945933282757009053 675119229724981033878395)
                    ·
                      rfl

theorem cell22_1972185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_1972185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972185 prefixEnd_1972185 := by exact prefixLift 1972185
  have htrace : WordTrace (prefixWord ++ tailWord_1972185) baseStart_1972185 baseEnd_1972185 := by
    simpa [prefixWord, tailWord_1972185, baseEnd_1972185] using wordTrace_append hprefix tailTrace_1972185
  have hstable : (prefixWord ++ tailWord_1972185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972185).length < 2 ^ (prefixWord ++ tailWord_1972185).sum := by decide
  have hdescent : baseEnd_1972185 < baseStart_1972185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972258 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1972258 : Nat := 118140960795 + 1972258 * 2 ^ 59
def prefixEnd_1972258 : Nat := 4983230072969 + 3 ^ 40 * 1972258 * 2
def baseEnd_1972258 : Nat := 675144219116833176803171

theorem tailTrace_1972258 : CollatzResearch.WordTrace tailWord_1972258 prefixEnd_1972258 675144219116833176803171 := by
  unfold tailWord_1972258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983539722213393923679357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47956105925902383796478285 17983539722213393923679357)
  ·
    refine ⟨6743827395830022721379759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17983539722213393923679357 6743827395830022721379759)
    ·
      refine ⟨10115741093745034082069639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6743827395830022721379759 10115741093745034082069639)
      ·
        refine ⟨15173611640617551123104459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10115741093745034082069639 15173611640617551123104459)
        ·
          refine ⟨22760417460926326684656689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15173611640617551123104459 22760417460926326684656689)
          ·
            refine ⟨17070313095694745013492517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22760417460926326684656689 17070313095694745013492517)
            ·
              refine ⟨3200683705442764690029847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17070313095694745013492517 3200683705442764690029847)
              ·
                refine ⟨4801025558164147035044771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200683705442764690029847 4801025558164147035044771)
                ·
                  refine ⟨7201538337246220552567157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4801025558164147035044771 7201538337246220552567157)
                  ·
                    refine ⟨675144219116833176803171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7201538337246220552567157 675144219116833176803171)
                    ·
                      rfl

theorem cell22_1972258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1972258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972258 prefixEnd_1972258 := by exact prefixLift 1972258
  have htrace : WordTrace (prefixWord ++ tailWord_1972258) baseStart_1972258 baseEnd_1972258 := by
    simpa [prefixWord, tailWord_1972258, baseEnd_1972258] using wordTrace_append hprefix tailTrace_1972258
  have hstable : (prefixWord ++ tailWord_1972258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972258).length < 2 ^ (prefixWord ++ tailWord_1972258).sum := by decide
  have hdescent : baseEnd_1972258 < baseStart_1972258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972273 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1972273 : Nat := 118140960795 + 1972273 * 2 ^ 59
def prefixEnd_1972273 : Nat := 4983230072969 + 3 ^ 40 * 1972273 * 2
def baseEnd_1972273 : Nat := 675149353923378137678125

theorem tailTrace_1972273 : CollatzResearch.WordTrace tailWord_1972273 prefixEnd_1972273 675149353923378137678125 := by
  unfold tailWord_1972273
  simp only [CollatzResearch.WordTrace]
  refine ⟨71934705983799233256513473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47956470655866155504342315 71934705983799233256513473)
  ·
    refine ⟨53951029487849424942385105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71934705983799233256513473 53951029487849424942385105)
    ·
      refine ⟨40463272115887068706788829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53951029487849424942385105 40463272115887068706788829)
      ·
        refine ⟨15173727043457650765045811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40463272115887068706788829 15173727043457650765045811)
        ·
          refine ⟨22760590565186476147568717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15173727043457650765045811 22760590565186476147568717)
          ·
            refine ⟨8535221461944928555338269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22760590565186476147568717 8535221461944928555338269)
            ·
              refine ⟨3200708048229348208251851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8535221461944928555338269 3200708048229348208251851)
              ·
                refine ⟨4801062072344022312377777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200708048229348208251851 4801062072344022312377777)
                ·
                  refine ⟨3600796554258016734283333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4801062072344022312377777 3600796554258016734283333)
                  ·
                    refine ⟨675149353923378137678125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3600796554258016734283333 675149353923378137678125)
                    ·
                      rfl

theorem cell22_1972273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1972273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972273 prefixEnd_1972273 := by exact prefixLift 1972273
  have htrace : WordTrace (prefixWord ++ tailWord_1972273) baseStart_1972273 baseEnd_1972273 := by
    simpa [prefixWord, tailWord_1972273, baseEnd_1972273] using wordTrace_append hprefix tailTrace_1972273
  have hstable : (prefixWord ++ tailWord_1972273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972273).length < 2 ^ (prefixWord ++ tailWord_1972273).sum := by decide
  have hdescent : baseEnd_1972273 < baseStart_1972273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972322 : List Nat := [3, 3, 2, 2, 2, 2, 2, 6]
def baseStart_1972322 : Nat := 118140960795 + 1972322 * 2 ^ 59
def prefixEnd_1972322 : Nat := 4983230072969 + 3 ^ 40 * 1972322 * 2
def baseEnd_1972322 : Nat := 75018458624973149244775

theorem tailTrace_1972322 : CollatzResearch.WordTrace tailWord_1972322 prefixEnd_1972322 75018458624973149244775 := by
  unfold tailWord_1972322
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984123290155428656261805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47957662107081143083364813 17984123290155428656261805)
  ·
    refine ⟨6744046233808285746098177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17984123290155428656261805 6744046233808285746098177)
    ·
      refine ⟨5058034675356214309573633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6744046233808285746098177 5058034675356214309573633)
      ·
        refine ⟨3793526006517160732180225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5058034675356214309573633 3793526006517160732180225)
        ·
          refine ⟨2845144504887870549135169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3793526006517160732180225 2845144504887870549135169)
          ·
            refine ⟨2133858378665902911851377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845144504887870549135169 2133858378665902911851377)
            ·
              refine ⟨1600393783999427183888533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133858378665902911851377 1600393783999427183888533)
              ·
                refine ⟨75018458624973149244775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1600393783999427183888533 75018458624973149244775)
                ·
                  rfl

theorem cell22_1972322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 6].length) (baseStart_1972322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972322 prefixEnd_1972322 := by exact prefixLift 1972322
  have htrace : WordTrace (prefixWord ++ tailWord_1972322) baseStart_1972322 baseEnd_1972322 := by
    simpa [prefixWord, tailWord_1972322, baseEnd_1972322] using wordTrace_append hprefix tailTrace_1972322
  have hstable : (prefixWord ++ tailWord_1972322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972322).length < 2 ^ (prefixWord ++ tailWord_1972322).sum := by decide
  have hdescent : baseEnd_1972322 < baseStart_1972322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972408 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_1972408 : Nat := 118140960795 + 1972408 * 2 ^ 59
def prefixEnd_1972408 : Nat := 4983230072969 + 3 ^ 40 * 1972408 * 2
def baseEnd_1972408 : Nat := 675195567182282785552711

theorem tailTrace_1972408 : CollatzResearch.WordTrace tailWord_1972408 prefixEnd_1972408 675195567182282785552711 := by
  unfold tailWord_1972408
  simp only [CollatzResearch.WordTrace]
  refine ⟨35969814919155075656338939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47959753225540100875118585 35969814919155075656338939)
  ·
    refine ⟨53954722378732613484508409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35969814919155075656338939 53954722378732613484508409)
    ·
      refine ⟨40466041784049460113381307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53954722378732613484508409 40466041784049460113381307)
      ·
        refine ⟨60699062676074190170071961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40466041784049460113381307 60699062676074190170071961)
        ·
          refine ⟨45524297007055642627553971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60699062676074190170071961 45524297007055642627553971)
          ·
            refine ⟨68286445510583463941330957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45524297007055642627553971 68286445510583463941330957)
            ·
              refine ⟨25607417066468798977999109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68286445510583463941330957 25607417066468798977999109)
              ·
                refine ⟨4801390699962899808374833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25607417066468798977999109 4801390699962899808374833)
                ·
                  refine ⟨3601043024972174856281125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4801390699962899808374833 3601043024972174856281125)
                  ·
                    refine ⟨675195567182282785552711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601043024972174856281125 675195567182282785552711)
                    ·
                      rfl

theorem cell22_1972408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_1972408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972408 prefixEnd_1972408 := by exact prefixLift 1972408
  have htrace : WordTrace (prefixWord ++ tailWord_1972408) baseStart_1972408 baseEnd_1972408 := by
    simpa [prefixWord, tailWord_1972408, baseEnd_1972408] using wordTrace_append hprefix tailTrace_1972408
  have hstable : (prefixWord ++ tailWord_1972408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972408).length < 2 ^ (prefixWord ++ tailWord_1972408).sum := by decide
  have hdescent : baseEnd_1972408 < baseStart_1972408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972410 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_1972410 : Nat := 118140960795 + 1972410 * 2 ^ 59
def prefixEnd_1972410 : Nat := 4983230072969 + 3 ^ 40 * 1972410 * 2
def baseEnd_1972410 : Nat := 675196251823155447002705

theorem tailTrace_1972410 : CollatzResearch.WordTrace tailWord_1972410 prefixEnd_1972410 675196251823155447002705 := by
  unfold tailWord_1972410
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984925696075726413562671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47959801856201937102833789 17984925696075726413562671)
  ·
    refine ⟨26977388544113589620344007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17984925696075726413562671 26977388544113589620344007)
    ·
      refine ⟨40466082816170384430516011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26977388544113589620344007 40466082816170384430516011)
      ·
        refine ⟨60699124224255576645774017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40466082816170384430516011 60699124224255576645774017)
        ·
          refine ⟨45524343168191682484330513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60699124224255576645774017 45524343168191682484330513)
          ·
            refine ⟨34143257376143761863247885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45524343168191682484330513 34143257376143761863247885)
            ·
              refine ⟨12803721516053910698717957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34143257376143761863247885 12803721516053910698717957)
              ·
                refine ⟨2400697784260108256009617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12803721516053910698717957 2400697784260108256009617)
                ·
                  refine ⟨1800523338195081192007213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2400697784260108256009617 1800523338195081192007213)
                  ·
                    refine ⟨675196251823155447002705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800523338195081192007213 675196251823155447002705)
                    ·
                      rfl

theorem cell22_1972410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_1972410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972410 prefixEnd_1972410 := by exact prefixLift 1972410
  have htrace : WordTrace (prefixWord ++ tailWord_1972410) baseStart_1972410 baseEnd_1972410 := by
    simpa [prefixWord, tailWord_1972410, baseEnd_1972410] using wordTrace_append hprefix tailTrace_1972410
  have hstable : (prefixWord ++ tailWord_1972410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972410).length < 2 ^ (prefixWord ++ tailWord_1972410).sum := by decide
  have hdescent : baseEnd_1972410 < baseStart_1972410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972412 : List Nat := [2, 2, 2, 3, 3, 1, 1, 4, 4]
def baseStart_1972412 : Nat := 118140960795 + 1972412 * 2 ^ 59
def prefixEnd_1972412 : Nat := 4983230072969 + 3 ^ 40 * 1972412 * 2
def baseEnd_1972412 : Nat := 225065645488009369484233

theorem tailTrace_1972412 : CollatzResearch.WordTrace tailWord_1972412 prefixEnd_1972412 225065645488009369484233 := by
  unfold tailWord_1972412
  simp only [CollatzResearch.WordTrace]
  refine ⟨35969887865147829997911745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47959850486863773330548993 35969887865147829997911745)
  ·
    refine ⟨26977415898860872498433809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35969887865147829997911745 26977415898860872498433809)
    ·
      refine ⟨20233061924145654373825357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26977415898860872498433809 20233061924145654373825357)
      ·
        refine ⟨7587398221554620390184509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20233061924145654373825357 7587398221554620390184509)
        ·
          refine ⟨2845274333082982646319191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7587398221554620390184509 2845274333082982646319191)
          ·
            refine ⟨4267911499624473969478787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845274333082982646319191 4267911499624473969478787)
            ·
              refine ⟨6401867249436710954218181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267911499624473969478787 6401867249436710954218181)
              ·
                refine ⟨1200350109269383303915909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6401867249436710954218181 1200350109269383303915909)
                ·
                  refine ⟨225065645488009369484233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200350109269383303915909 225065645488009369484233)
                  ·
                    rfl

theorem cell22_1972412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_1972412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972412 prefixEnd_1972412 := by exact prefixLift 1972412
  have htrace : WordTrace (prefixWord ++ tailWord_1972412) baseStart_1972412 baseEnd_1972412 := by
    simpa [prefixWord, tailWord_1972412, baseEnd_1972412] using wordTrace_append hprefix tailTrace_1972412
  have hstable : (prefixWord ++ tailWord_1972412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972412).length < 2 ^ (prefixWord ++ tailWord_1972412).sum := by decide
  have hdescent : baseEnd_1972412 < baseStart_1972412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972440 : List Nat := [2, 1, 2, 2, 4, 2, 3, 6]
def baseStart_1972440 : Nat := 118140960795 + 1972440 * 2 ^ 59
def prefixEnd_1972440 : Nat := 4983230072969 + 3 ^ 40 * 1972440 * 2
def baseEnd_1972440 : Nat := 75022946826249485416957

theorem tailTrace_1972440 : CollatzResearch.WordTrace tailWord_1972440 prefixEnd_1972440 75022946826249485416957 := by
  unfold tailWord_1972440
  simp only [CollatzResearch.WordTrace]
  refine ⟨35970398487097110388921387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47960531316129480518561849 35970398487097110388921387)
  ·
    refine ⟨53955597730645665583382081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35970398487097110388921387 53955597730645665583382081)
    ·
      refine ⟨40466698297984249187536561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53955597730645665583382081 40466698297984249187536561)
      ·
        refine ⟨30350023723488186890652421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40466698297984249187536561 30350023723488186890652421)
        ·
          refine ⟨5690629448154035041997329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30350023723488186890652421 5690629448154035041997329)
          ·
            refine ⟨4267972086115526281497997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5690629448154035041997329 4267972086115526281497997)
            ·
              refine ⟨1600489532293322355561749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4267972086115526281497997 1600489532293322355561749)
              ·
                refine ⟨75022946826249485416957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1600489532293322355561749 75022946826249485416957)
                ·
                  rfl

theorem cell22_1972440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 6].length) (baseStart_1972440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972440 prefixEnd_1972440 := by exact prefixLift 1972440
  have htrace : WordTrace (prefixWord ++ tailWord_1972440) baseStart_1972440 baseEnd_1972440 := by
    simpa [prefixWord, tailWord_1972440, baseEnd_1972440] using wordTrace_append hprefix tailTrace_1972440
  have hstable : (prefixWord ++ tailWord_1972440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972440).length < 2 ^ (prefixWord ++ tailWord_1972440).sum := by decide
  have hdescent : baseEnd_1972440 < baseStart_1972440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972461 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_1972461 : Nat := 118140960795 + 1972461 * 2 ^ 59
def prefixEnd_1972461 : Nat := 4983230072969 + 3 ^ 40 * 1972461 * 2
def baseEnd_1972461 : Nat := 675213710165408313977549

theorem tailTrace_1972461 : CollatzResearch.WordTrace tailWord_1972461 prefixEnd_1972461 675213710165408313977549 := by
  unfold tailWord_1972461
  simp only [CollatzResearch.WordTrace]
  refine ⟨71941562907118141364357237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47961041938078760909571491 71941562907118141364357237)
  ·
    refine ⟨6744521522542325752908491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71941562907118141364357237 6744521522542325752908491)
    ·
      refine ⟨10116782283813488629362737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6744521522542325752908491 10116782283813488629362737)
      ·
        refine ⟨7587586712860116472022053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10116782283813488629362737 7587586712860116472022053)
        ·
          refine ⟨1422672508661271838504135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7587586712860116472022053 1422672508661271838504135)
          ·
            refine ⟨2134008762991907757756203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422672508661271838504135 2134008762991907757756203)
            ·
              refine ⟨3201013144487861636634305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134008762991907757756203 3201013144487861636634305)
              ·
                refine ⟨2400759858365896227475729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201013144487861636634305 2400759858365896227475729)
                ·
                  refine ⟨1800569893774422170606797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2400759858365896227475729 1800569893774422170606797)
                  ·
                    refine ⟨675213710165408313977549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800569893774422170606797 675213710165408313977549)
                    ·
                      rfl

theorem cell22_1972461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_1972461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972461 prefixEnd_1972461 := by exact prefixLift 1972461
  have htrace : WordTrace (prefixWord ++ tailWord_1972461) baseStart_1972461 baseEnd_1972461 := by
    simpa [prefixWord, tailWord_1972461, baseEnd_1972461] using wordTrace_append hprefix tailTrace_1972461
  have hstable : (prefixWord ++ tailWord_1972461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972461).length < 2 ^ (prefixWord ++ tailWord_1972461).sum := by decide
  have hdescent : baseEnd_1972461 < baseStart_1972461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972483 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 2, 5]
def baseStart_1972483 : Nat := 118140960795 + 1972483 * 2 ^ 59
def prefixEnd_1972483 : Nat := 4983230072969 + 3 ^ 40 * 1972483 * 2
def baseEnd_1972483 : Nat := 675221241215007589927481

theorem tailTrace_1972483 : CollatzResearch.WordTrace tailWord_1972483 prefixEnd_1972483 675221241215007589927481 := by
  unfold tailWord_1972483
  simp only [CollatzResearch.WordTrace]
  refine ⟨71942365313038439121658103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47961576875358959414438735 71942365313038439121658103)
  ·
    refine ⟨107913547969557658682487155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71942365313038439121658103 107913547969557658682487155)
    ·
      refine ⟨161870321954336488023730733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107913547969557658682487155 161870321954336488023730733)
      ·
        refine ⟨60701370732876183008899025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161870321954336488023730733 60701370732876183008899025)
        ·
          refine ⟨45526028049657137256674269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60701370732876183008899025 45526028049657137256674269)
          ·
            refine ⟨17072260518621426471252851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45526028049657137256674269 17072260518621426471252851)
            ·
              refine ⟨25608390777932139706879277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17072260518621426471252851 25608390777932139706879277)
              ·
                refine ⟨9603146541724552390079729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25608390777932139706879277 9603146541724552390079729)
                ·
                  refine ⟨7202359906293414292559797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9603146541724552390079729 7202359906293414292559797)
                  ·
                    refine ⟨675221241215007589927481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7202359906293414292559797 675221241215007589927481)
                    ·
                      rfl

theorem cell22_1972483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_1972483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972483 prefixEnd_1972483 := by exact prefixLift 1972483
  have htrace : WordTrace (prefixWord ++ tailWord_1972483) baseStart_1972483 baseEnd_1972483 := by
    simpa [prefixWord, tailWord_1972483, baseEnd_1972483] using wordTrace_append hprefix tailTrace_1972483
  have hstable : (prefixWord ++ tailWord_1972483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972483).length < 2 ^ (prefixWord ++ tailWord_1972483).sum := by decide
  have hdescent : baseEnd_1972483 < baseStart_1972483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972506 : List Nat := [3, 1, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_1972506 : Nat := 118140960795 + 1972506 * 2 ^ 59
def prefixEnd_1972506 : Nat := 4983230072969 + 3 ^ 40 * 1972506 * 2
def baseEnd_1972506 : Nat := 675229114585043196602411

theorem tailTrace_1972506 : CollatzResearch.WordTrace tailWord_1972506 prefixEnd_1972506 675229114585043196602411 := by
  unfold tailWord_1972506
  simp only [CollatzResearch.WordTrace]
  refine ⟨17985801047988778512436343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47962136127970076033163581 17985801047988778512436343)
  ·
    refine ⟨26978701571983167768654515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17985801047988778512436343 26978701571983167768654515)
    ·
      refine ⟨40468052357974751652981773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26978701571983167768654515 40468052357974751652981773)
      ·
        refine ⟨15175519634240531869868165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40468052357974751652981773 15175519634240531869868165)
        ·
          refine ⟨2845409931420099725600281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15175519634240531869868165 2845409931420099725600281)
          ·
            refine ⟨2134057448565074794200211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845409931420099725600281 2134057448565074794200211)
            ·
              refine ⟨3201086172847612191300317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134057448565074794200211 3201086172847612191300317)
              ·
                refine ⟨1200407314817854571737619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3201086172847612191300317 1200407314817854571737619)
                ·
                  refine ⟨1800610972226781857606429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200407314817854571737619 1800610972226781857606429)
                  ·
                    refine ⟨675229114585043196602411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800610972226781857606429 675229114585043196602411)
                    ·
                      rfl

theorem cell22_1972506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_1972506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972506 prefixEnd_1972506 := by exact prefixLift 1972506
  have htrace : WordTrace (prefixWord ++ tailWord_1972506) baseStart_1972506 baseEnd_1972506 := by
    simpa [prefixWord, tailWord_1972506, baseEnd_1972506] using wordTrace_append hprefix tailTrace_1972506
  have hstable : (prefixWord ++ tailWord_1972506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972506).length < 2 ^ (prefixWord ++ tailWord_1972506).sum := by decide
  have hdescent : baseEnd_1972506 < baseStart_1972506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972513 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 8]
def baseStart_1972513 : Nat := 118140960795 + 1972513 * 2 ^ 59
def prefixEnd_1972513 : Nat := 4983230072969 + 3 ^ 40 * 1972513 * 2
def baseEnd_1972513 : Nat := 225077170276032503892463

theorem tailTrace_1972513 : CollatzResearch.WordTrace tailWord_1972513 prefixEnd_1972513 225077170276032503892463 := by
  unfold tailWord_1972513
  simp only [CollatzResearch.WordTrace]
  refine ⟨71943459502929754245250193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47962306335286502830166795 71943459502929754245250193)
  ·
    refine ⟨53957594627197315683937645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71943459502929754245250193 53957594627197315683937645)
    ·
      refine ⟨20234097985198993381476617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53957594627197315683937645 20234097985198993381476617)
      ·
        refine ⟨15175573488899245036107463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20234097985198993381476617 15175573488899245036107463)
        ·
          refine ⟨22763360233348867554161195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15175573488899245036107463 22763360233348867554161195)
          ·
            refine ⟨34145040350023301331241793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22763360233348867554161195 34145040350023301331241793)
            ·
              refine ⟨25608780262517475998431345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34145040350023301331241793 25608780262517475998431345)
              ·
                refine ⟨19206585196888106998823509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25608780262517475998431345 19206585196888106998823509)
                ·
                  refine ⟨225077170276032503892463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19206585196888106998823509 225077170276032503892463)
                  ·
                    rfl

theorem cell22_1972513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_1972513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972513 prefixEnd_1972513 := by exact prefixLift 1972513
  have htrace : WordTrace (prefixWord ++ tailWord_1972513) baseStart_1972513 baseEnd_1972513 := by
    simpa [prefixWord, tailWord_1972513, baseEnd_1972513] using wordTrace_append hprefix tailTrace_1972513
  have hstable : (prefixWord ++ tailWord_1972513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972513).length < 2 ^ (prefixWord ++ tailWord_1972513).sum := by decide
  have hdescent : baseEnd_1972513 < baseStart_1972513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972515 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 1, 4]
def baseStart_1972515 : Nat := 118140960795 + 1972515 * 2 ^ 59
def prefixEnd_1972515 : Nat := 4983230072969 + 3 ^ 40 * 1972515 * 2
def baseEnd_1972515 : Nat := 675232195468970173127383

theorem tailTrace_1972515 : CollatzResearch.WordTrace tailWord_1972515 prefixEnd_1972515 675232195468970173127383 := by
  unfold tailWord_1972515
  simp only [CollatzResearch.WordTrace]
  refine ⟨71943532448922508586822999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47962354965948339057881999 71943532448922508586822999)
  ·
    refine ⟨107915298673383762880234499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71943532448922508586822999 107915298673383762880234499)
    ·
      refine ⟨161872948010075644320351749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107915298673383762880234499 161872948010075644320351749)
      ·
        refine ⟨30351177751889183310065953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161872948010075644320351749 30351177751889183310065953)
        ·
          refine ⟨22763383313916887482549465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30351177751889183310065953 22763383313916887482549465)
          ·
            refine ⟨17072537485437665611912099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22763383313916887482549465 17072537485437665611912099)
            ·
              refine ⟨25608806228156498417868149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17072537485437665611912099 25608806228156498417868149)
              ·
                refine ⟨2400825583889671726675139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25608806228156498417868149 2400825583889671726675139)
                ·
                  refine ⟨3601238375834507590012709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400825583889671726675139 3601238375834507590012709)
                  ·
                    refine ⟨675232195468970173127383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601238375834507590012709 675232195468970173127383)
                    ·
                      rfl

theorem cell22_1972515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 4].length) (baseStart_1972515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972515 prefixEnd_1972515 := by exact prefixLift 1972515
  have htrace : WordTrace (prefixWord ++ tailWord_1972515) baseStart_1972515 baseEnd_1972515 := by
    simpa [prefixWord, tailWord_1972515, baseEnd_1972515] using wordTrace_append hprefix tailTrace_1972515
  have hstable : (prefixWord ++ tailWord_1972515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972515).length < 2 ^ (prefixWord ++ tailWord_1972515).sum := by decide
  have hdescent : baseEnd_1972515 < baseStart_1972515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972528 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_1972528 : Nat := 118140960795 + 1972528 * 2 ^ 59
def prefixEnd_1972528 : Nat := 4983230072969 + 3 ^ 40 * 1972528 * 2
def baseEnd_1972528 : Nat := 675236645634642472552343

theorem tailTrace_1972528 : CollatzResearch.WordTrace tailWord_1972528 prefixEnd_1972528 675236645634642472552343 := by
  unfold tailWord_1972528
  simp only [CollatzResearch.WordTrace]
  refine ⟨35972003298937705903523119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47962671065250274538030825 35972003298937705903523119)
  ·
    refine ⟨53958004948406558855284679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35972003298937705903523119 53958004948406558855284679)
    ·
      refine ⟨80937007422609838282927019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53958004948406558855284679 80937007422609838282927019)
      ·
        refine ⟨121405511133914757424390529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80937007422609838282927019 121405511133914757424390529)
        ·
          refine ⟨91054133350436068068292897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121405511133914757424390529 91054133350436068068292897)
          ·
            refine ⟨68290600012827051051219673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91054133350436068068292897 68290600012827051051219673)
            ·
              refine ⟨51217950009620288288414755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68290600012827051051219673 51217950009620288288414755)
              ·
                refine ⟨76826925014430432432622133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51217950009620288288414755 76826925014430432432622133)
                ·
                  refine ⟨7202524220102853040558325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76826925014430432432622133 7202524220102853040558325)
                  ·
                    refine ⟨675236645634642472552343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7202524220102853040558325 675236645634642472552343)
                    ·
                      rfl

theorem cell22_1972528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_1972528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972528 prefixEnd_1972528 := by exact prefixLift 1972528
  have htrace : WordTrace (prefixWord ++ tailWord_1972528) baseStart_1972528 baseEnd_1972528 := by
    simpa [prefixWord, tailWord_1972528, baseEnd_1972528] using wordTrace_append hprefix tailTrace_1972528
  have hstable : (prefixWord ++ tailWord_1972528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972528).length < 2 ^ (prefixWord ++ tailWord_1972528).sum := by decide
  have hdescent : baseEnd_1972528 < baseStart_1972528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972560 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_1972560 : Nat := 118140960795 + 1972560 * 2 ^ 59
def prefixEnd_1972560 : Nat := 4983230072969 + 3 ^ 40 * 1972560 * 2
def baseEnd_1972560 : Nat := 675247599888605055752245

theorem tailTrace_1972560 : CollatzResearch.WordTrace tailWord_1972560 prefixEnd_1972560 675247599888605055752245 := by
  unfold tailWord_1972560
  simp only [CollatzResearch.WordTrace]
  refine ⟨35972586866879740636105567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47963449155839654181474089 35972586866879740636105567)
  ·
    refine ⟨53958880300319610954158351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35972586866879740636105567 53958880300319610954158351)
    ·
      refine ⟨80938320450479416431237527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53958880300319610954158351 80938320450479416431237527)
      ·
        refine ⟨121407480675719124646856291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80938320450479416431237527 121407480675719124646856291)
        ·
          refine ⟨182111221013578686970284437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121407480675719124646856291 182111221013578686970284437)
          ·
            refine ⟨8536463485011500951732083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182111221013578686970284437 8536463485011500951732083)
            ·
              refine ⟨12804695227517251427598125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8536463485011500951732083 12804695227517251427598125)
              ·
                refine ⟨4801760710318969285349297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12804695227517251427598125 4801760710318969285349297)
                ·
                  refine ⟨3601320532739226964011973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4801760710318969285349297 3601320532739226964011973)
                  ·
                    refine ⟨675247599888605055752245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601320532739226964011973 675247599888605055752245)
                    ·
                      rfl

theorem cell22_1972560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_1972560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972560 prefixEnd_1972560 := by exact prefixLift 1972560
  have htrace : WordTrace (prefixWord ++ tailWord_1972560) baseStart_1972560 baseEnd_1972560 := by
    simpa [prefixWord, tailWord_1972560, baseEnd_1972560] using wordTrace_append hprefix tailTrace_1972560
  have hstable : (prefixWord ++ tailWord_1972560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972560).length < 2 ^ (prefixWord ++ tailWord_1972560).sum := by decide
  have hdescent : baseEnd_1972560 < baseStart_1972560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972574 : List Nat := [4, 4, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1972574 : Nat := 118140960795 + 1972574 * 2 ^ 59
def prefixEnd_1972574 : Nat := 4983230072969 + 3 ^ 40 * 1972574 * 2
def baseEnd_1972574 : Nat := 675252392374713685902203

theorem tailTrace_1972574 : CollatzResearch.WordTrace tailWord_1972574 prefixEnd_1972574 675252392374713685902203 := by
  unfold tailWord_1972574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993210544463595207902597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47963789570472507775480517 8993210544463595207902597)
  ·
    refine ⟨1686226977086924101481737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8993210544463595207902597 1686226977086924101481737)
    ·
      refine ⟨1264670232815193076111303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1686226977086924101481737 1264670232815193076111303)
      ·
        refine ⟨1897005349222789614166955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264670232815193076111303 1897005349222789614166955)
        ·
          refine ⟨2845508023834184421250433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897005349222789614166955 2845508023834184421250433)
          ·
            refine ⟨2134131017875638315937825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845508023834184421250433 2134131017875638315937825)
            ·
              refine ⟨1600598263406728736953369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134131017875638315937825 1600598263406728736953369)
              ·
                refine ⟨1200448697555046552715027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600598263406728736953369 1200448697555046552715027)
                ·
                  refine ⟨1800673046332569829072541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200448697555046552715027 1800673046332569829072541)
                  ·
                    refine ⟨675252392374713685902203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800673046332569829072541 675252392374713685902203)
                    ·
                      rfl

theorem cell22_1972574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1972574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972574 prefixEnd_1972574 := by exact prefixLift 1972574
  have htrace : WordTrace (prefixWord ++ tailWord_1972574) baseStart_1972574 baseEnd_1972574 := by
    simpa [prefixWord, tailWord_1972574, baseEnd_1972574] using wordTrace_append hprefix tailTrace_1972574
  have hstable : (prefixWord ++ tailWord_1972574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972574).length < 2 ^ (prefixWord ++ tailWord_1972574).sum := by decide
  have hdescent : baseEnd_1972574 < baseStart_1972574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972637 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 7]
def baseStart_1972637 : Nat := 118140960795 + 1972637 * 2 ^ 59
def prefixEnd_1972637 : Nat := 4983230072969 + 3 ^ 40 * 1972637 * 2
def baseEnd_1972637 : Nat := 225091319520734173859003

theorem tailTrace_1972637 : CollatzResearch.WordTrace tailWord_1972637 prefixEnd_1972637 225091319520734173859003 := by
  unfold tailWord_1972637
  simp only [CollatzResearch.WordTrace]
  refine ⟨71947982154480523422764165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47965321436320348948509443 71947982154480523422764165)
  ·
    refine ⟨13490246653965098141768281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71947982154480523422764165 13490246653965098141768281)
    ·
      refine ⟨10117684990473823606326211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13490246653965098141768281 10117684990473823606326211)
      ·
        refine ⟨15176527485710735409489317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10117684990473823606326211 15176527485710735409489317)
        ·
          refine ⟨2845598903570762889279247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15176527485710735409489317 2845598903570762889279247)
          ·
            refine ⟨4268398355356144333918871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845598903570762889279247 4268398355356144333918871)
            ·
              refine ⟨6402597533034216500878307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268398355356144333918871 6402597533034216500878307)
              ·
                refine ⟨9603896299551324751317461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6402597533034216500878307 9603896299551324751317461)
                ·
                  refine ⟨225091319520734173859003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9603896299551324751317461 225091319520734173859003)
                  ·
                    rfl

theorem cell22_1972637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_1972637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972637 prefixEnd_1972637 := by exact prefixLift 1972637
  have htrace : WordTrace (prefixWord ++ tailWord_1972637) baseStart_1972637 baseEnd_1972637 := by
    simpa [prefixWord, tailWord_1972637, baseEnd_1972637] using wordTrace_append hprefix tailTrace_1972637
  have hstable : (prefixWord ++ tailWord_1972637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972637).length < 2 ^ (prefixWord ++ tailWord_1972637).sum := by decide
  have hdescent : baseEnd_1972637 < baseStart_1972637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972641 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 3, 3]
def baseStart_1972641 : Nat := 118140960795 + 1972641 * 2 ^ 59
def prefixEnd_1972641 : Nat := 4983230072969 + 3 ^ 40 * 1972641 * 2
def baseEnd_1972641 : Nat := 675275327843947844476997

theorem tailTrace_1972641 : CollatzResearch.WordTrace tailWord_1972641 prefixEnd_1972641 675275327843947844476997 := by
  unfold tailWord_1972641
  simp only [CollatzResearch.WordTrace]
  refine ⟨71948128046466032105909777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47965418697644021403939851 71948128046466032105909777)
  ·
    refine ⟨53961096034849524079432333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71948128046466032105909777 53961096034849524079432333)
    ·
      refine ⟨20235411013068571529787125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53961096034849524079432333 20235411013068571529787125)
      ·
        refine ⟨1897069782475178580917543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20235411013068571529787125 1897069782475178580917543)
        ·
          refine ⟨2845604673712767871376315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897069782475178580917543 2845604673712767871376315)
          ·
            refine ⟨4268407010569151807064473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845604673712767871376315 4268407010569151807064473)
            ·
              refine ⟨3201305257926863855298355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4268407010569151807064473 3201305257926863855298355)
              ·
                refine ⟨4801957886890295782947533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201305257926863855298355 4801957886890295782947533)
                ·
                  refine ⟨1800734207583860918605325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4801957886890295782947533 1800734207583860918605325)
                  ·
                    refine ⟨675275327843947844476997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800734207583860918605325 675275327843947844476997)
                    ·
                      rfl

theorem cell22_1972641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_1972641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972641 prefixEnd_1972641 := by exact prefixLift 1972641
  have htrace : WordTrace (prefixWord ++ tailWord_1972641) baseStart_1972641 baseEnd_1972641 := by
    simpa [prefixWord, tailWord_1972641, baseEnd_1972641] using wordTrace_append hprefix tailTrace_1972641
  have hstable : (prefixWord ++ tailWord_1972641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972641).length < 2 ^ (prefixWord ++ tailWord_1972641).sum := by decide
  have hdescent : baseEnd_1972641 < baseStart_1972641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972697 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 4, 3]
def baseStart_1972697 : Nat := 118140960795 + 1972697 * 2 ^ 59
def prefixEnd_1972697 : Nat := 4983230072969 + 3 ^ 40 * 1972697 * 2
def baseEnd_1972697 : Nat := 675294497788382365076825

theorem tailTrace_1972697 : CollatzResearch.WordTrace tailWord_1972697 prefixEnd_1972697 675294497788382365076825 := by
  unfold tailWord_1972697
  simp only [CollatzResearch.WordTrace]
  refine ⟨71950170534263153669948345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47966780356175435779965563 71950170534263153669948345)
  ·
    refine ⟨53962627900697365252461259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71950170534263153669948345 53962627900697365252461259)
    ·
      refine ⟨80943941851046047878691889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53962627900697365252461259 80943941851046047878691889)
      ·
        refine ⟨60707956388284535909018917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80943941851046047878691889 60707956388284535909018917)
        ·
          refine ⟨11382741822803350482941047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60707956388284535909018917 11382741822803350482941047)
          ·
            refine ⟨17074112734205025724411571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382741822803350482941047 17074112734205025724411571)
            ·
              refine ⟨25611169101307538586617357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17074112734205025724411571 25611169101307538586617357)
              ·
                refine ⟨9604188412990326969981509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25611169101307538586617357 9604188412990326969981509)
                ·
                  refine ⟨1800785327435686306871533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9604188412990326969981509 1800785327435686306871533)
                  ·
                    refine ⟨675294497788382365076825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800785327435686306871533 675294497788382365076825)
                    ·
                      rfl

theorem cell22_1972697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_1972697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972697 prefixEnd_1972697 := by exact prefixLift 1972697
  have htrace : WordTrace (prefixWord ++ tailWord_1972697) baseStart_1972697 baseEnd_1972697 := by
    simpa [prefixWord, tailWord_1972697, baseEnd_1972697] using wordTrace_append hprefix tailTrace_1972697
  have hstable : (prefixWord ++ tailWord_1972697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972697).length < 2 ^ (prefixWord ++ tailWord_1972697).sum := by decide
  have hdescent : baseEnd_1972697 < baseStart_1972697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972776 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1972776 : Nat := 118140960795 + 1972776 * 2 ^ 59
def prefixEnd_1972776 : Nat := 4983230072969 + 3 ^ 40 * 1972776 * 2
def baseEnd_1972776 : Nat := 675321541102852492351583

theorem tailTrace_1972776 : CollatzResearch.WordTrace tailWord_1972776 prefixEnd_1972776 675321541102852492351583 := by
  unfold tailWord_1972776
  simp only [CollatzResearch.WordTrace]
  refine ⟨35976525950488475081037091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47968701267317966774716121 35976525950488475081037091)
  ·
    refine ⟨53964788925732712621555637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35976525950488475081037091 53964788925732712621555637)
    ·
      refine ⟨5059198961787441808270841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53964788925732712621555637 5059198961787441808270841)
      ·
        refine ⟨3794399221340581356203131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5059198961787441808270841 3794399221340581356203131)
        ·
          refine ⟨5691598832010872034304697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794399221340581356203131 5691598832010872034304697)
          ·
            refine ⟨4268699124008154025728523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5691598832010872034304697 4268699124008154025728523)
            ·
              refine ⟨6403048686012231038592785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268699124008154025728523 6403048686012231038592785)
              ·
                refine ⟨4802286514509173278944589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403048686012231038592785 4802286514509173278944589)
                ·
                  refine ⟨1800857442940939979604221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4802286514509173278944589 1800857442940939979604221)
                  ·
                    refine ⟨675321541102852492351583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800857442940939979604221 675321541102852492351583)
                    ·
                      rfl

theorem cell22_1972776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1972776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972776 prefixEnd_1972776 := by exact prefixLift 1972776
  have htrace : WordTrace (prefixWord ++ tailWord_1972776) baseStart_1972776 baseEnd_1972776 := by
    simpa [prefixWord, tailWord_1972776, baseEnd_1972776] using wordTrace_append hprefix tailTrace_1972776
  have hstable : (prefixWord ++ tailWord_1972776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972776).length < 2 ^ (prefixWord ++ tailWord_1972776).sum := by decide
  have hdescent : baseEnd_1972776 < baseStart_1972776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972806 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1972806 : Nat := 118140960795 + 1972806 * 2 ^ 59
def prefixEnd_1972806 : Nat := 4983230072969 + 3 ^ 40 * 1972806 * 2
def baseEnd_1972806 : Nat := 225110603571980804700497

theorem tailTrace_1972806 : CollatzResearch.WordTrace tailWord_1972806 prefixEnd_1972806 225110603571980804700497 := by
  unfold tailWord_1972806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248567065339633290177071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47969430727245510190444181 2248567065339633290177071)
  ·
    refine ⟨3372850598009449935265607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2248567065339633290177071 3372850598009449935265607)
    ·
      refine ⟨5059275897014174902898411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372850598009449935265607 5059275897014174902898411)
      ·
        refine ⟨7588913845521262354347617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059275897014174902898411 7588913845521262354347617)
        ·
          refine ⟨5691685384140946765760713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7588913845521262354347617 5691685384140946765760713)
          ·
            refine ⟨4268764038105710074320535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5691685384140946765760713 4268764038105710074320535)
            ·
              refine ⟨6403146057158565111480803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268764038105710074320535 6403146057158565111480803)
              ·
                refine ⟨9604719085737847667221205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403146057158565111480803 9604719085737847667221205)
                ·
                  refine ⟨225110603571980804700497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9604719085737847667221205 225110603571980804700497)
                  ·
                    rfl

theorem cell22_1972806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1972806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972806 prefixEnd_1972806 := by exact prefixLift 1972806
  have htrace : WordTrace (prefixWord ++ tailWord_1972806) baseStart_1972806 baseEnd_1972806 := by
    simpa [prefixWord, tailWord_1972806, baseEnd_1972806] using wordTrace_append hprefix tailTrace_1972806
  have hstable : (prefixWord ++ tailWord_1972806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972806).length < 2 ^ (prefixWord ++ tailWord_1972806).sum := by decide
  have hdescent : baseEnd_1972806 < baseStart_1972806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972817 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 6]
def baseStart_1972817 : Nat := 118140960795 + 1972817 * 2 ^ 59
def prefixEnd_1972817 : Nat := 4983230072969 + 3 ^ 40 * 1972817 * 2
def baseEnd_1972817 : Nat := 225111858746914017358819

theorem tailTrace_1972817 : CollatzResearch.WordTrace tailWord_1972817 prefixEnd_1972817 225111858746914017358819 := by
  unfold tailWord_1972817
  simp only [CollatzResearch.WordTrace]
  refine ⟨71954547293828414164316705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47969698195885609442877803 71954547293828414164316705)
  ·
    refine ⟨53965910470371310623237529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71954547293828414164316705 53965910470371310623237529)
    ·
      refine ⟨40474432852778482967428147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53965910470371310623237529 40474432852778482967428147)
      ·
        refine ⟨60711649279167724451142221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40474432852778482967428147 60711649279167724451142221)
        ·
          refine ⟨22766868479687896669178333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60711649279167724451142221 22766868479687896669178333)
          ·
            refine ⟨8537575679882961250941875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22766868479687896669178333 8537575679882961250941875)
            ·
              refine ⟨12806363519824441876412813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8537575679882961250941875 12806363519824441876412813)
              ·
                refine ⟨4802386319934165703654805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12806363519824441876412813 4802386319934165703654805)
                ·
                  refine ⟨225111858746914017358819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4802386319934165703654805 225111858746914017358819)
                  ·
                    rfl

theorem cell22_1972817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_1972817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972817 prefixEnd_1972817 := by exact prefixLift 1972817
  have htrace : WordTrace (prefixWord ++ tailWord_1972817) baseStart_1972817 baseEnd_1972817 := by
    simpa [prefixWord, tailWord_1972817, baseEnd_1972817] using wordTrace_append hprefix tailTrace_1972817
  have hstable : (prefixWord ++ tailWord_1972817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972817).length < 2 ^ (prefixWord ++ tailWord_1972817).sum := by decide
  have hdescent : baseEnd_1972817 < baseStart_1972817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972847 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 1, 6]
def baseStart_1972847 : Nat := 118140960795 + 1972847 * 2 ^ 59
def prefixEnd_1972847 : Nat := 4983230072969 + 3 ^ 40 * 1972847 * 2
def baseEnd_1972847 : Nat := 675345845853831973826365

theorem tailTrace_1972847 : CollatzResearch.WordTrace tailWord_1972847 prefixEnd_1972847 675345845853831973826365 := by
  unfold tailWord_1972847
  simp only [CollatzResearch.WordTrace]
  refine ⟨71955641483719729287908795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47970427655813152858605863 71955641483719729287908795)
  ·
    refine ⟨107933462225579593931863193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71955641483719729287908795 107933462225579593931863193)
    ·
      refine ⟨80950096669184695448897395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107933462225579593931863193 80950096669184695448897395)
      ·
        refine ⟨121425145003777043173346093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80950096669184695448897395 121425145003777043173346093)
        ·
          refine ⟨45534429376416391190004785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121425145003777043173346093 45534429376416391190004785)
          ·
            refine ⟨34150822032312293392503589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45534429376416391190004785 34150822032312293392503589)
            ·
              refine ⟨6403279131058555011094423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34150822032312293392503589 6403279131058555011094423)
              ·
                refine ⟨9604918696587832516641635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403279131058555011094423 9604918696587832516641635)
                ·
                  refine ⟨14407378044881748774962453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9604918696587832516641635 14407378044881748774962453)
                  ·
                    refine ⟨675345845853831973826365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14407378044881748774962453 675345845853831973826365)
                    ·
                      rfl

theorem cell22_1972847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_1972847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972847 prefixEnd_1972847 := by exact prefixLift 1972847
  have htrace : WordTrace (prefixWord ++ tailWord_1972847) baseStart_1972847 baseEnd_1972847 := by
    simpa [prefixWord, tailWord_1972847, baseEnd_1972847] using wordTrace_append hprefix tailTrace_1972847
  have hstable : (prefixWord ++ tailWord_1972847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972847).length < 2 ^ (prefixWord ++ tailWord_1972847).sum := by decide
  have hdescent : baseEnd_1972847 < baseStart_1972847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972864 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_1972864 : Nat := 118140960795 + 1972864 * 2 ^ 59
def prefixEnd_1972864 : Nat := 4983230072969 + 3 ^ 40 * 1972864 * 2
def baseEnd_1972864 : Nat := 675351665301249596151313

theorem tailTrace_1972864 : CollatzResearch.WordTrace tailWord_1972864 prefixEnd_1972864 675351665301249596151313 := by
  unfold tailWord_1972864
  simp only [CollatzResearch.WordTrace]
  refine ⟨35978130762329070595638823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47970841016438760794185097 35978130762329070595638823)
  ·
    refine ⟨53967196143493605893458235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35978130762329070595638823 53967196143493605893458235)
    ·
      refine ⟨80950794215240408840187353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53967196143493605893458235 80950794215240408840187353)
      ·
        refine ⟨60713095661430306630140515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80950794215240408840187353 60713095661430306630140515)
        ·
          refine ⟨91069643492145459945210773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60713095661430306630140515 91069643492145459945210773)
          ·
            refine ⟨4268889538694318434931755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91069643492145459945210773 4268889538694318434931755)
            ·
              refine ⟨6403334308041477652397633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268889538694318434931755 6403334308041477652397633)
              ·
                refine ⟨4802500731031108239298225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6403334308041477652397633 4802500731031108239298225)
                ·
                  refine ⟨3601875548273331179473669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4802500731031108239298225 3601875548273331179473669)
                  ·
                    refine ⟨675351665301249596151313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3601875548273331179473669 675351665301249596151313)
                    ·
                      rfl

theorem cell22_1972864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_1972864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972864 prefixEnd_1972864 := by exact prefixLift 1972864
  have htrace : WordTrace (prefixWord ++ tailWord_1972864) baseStart_1972864 baseEnd_1972864 := by
    simpa [prefixWord, tailWord_1972864, baseEnd_1972864] using wordTrace_append hprefix tailTrace_1972864
  have hstable : (prefixWord ++ tailWord_1972864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972864).length < 2 ^ (prefixWord ++ tailWord_1972864).sum := by decide
  have hdescent : baseEnd_1972864 < baseStart_1972864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972868 : List Nat := [2, 3, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1972868 : Nat := 118140960795 + 1972868 * 2 ^ 59
def prefixEnd_1972868 : Nat := 4983230072969 + 3 ^ 40 * 1972868 * 2
def baseEnd_1972868 : Nat := 225117678194331639683767

theorem tailTrace_1972868 : CollatzResearch.WordTrace tailWord_1972868 prefixEnd_1972868 225117678194331639683767 := by
  unfold tailWord_1972868
  simp only [CollatzResearch.WordTrace]
  refine ⟨35978203708321824937211629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47970938277762433249615505 35978203708321824937211629)
  ·
    refine ⟨13491826390620684351454361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35978203708321824937211629 13491826390620684351454361)
    ·
      refine ⟨10118869792965513263590771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13491826390620684351454361 10118869792965513263590771)
      ·
        refine ⟨15178304689448269895386157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10118869792965513263590771 15178304689448269895386157)
        ·
          refine ⟨5691864258543101210769809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15178304689448269895386157 5691864258543101210769809)
          ·
            refine ⟨4268898193907325908077357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5691864258543101210769809 4268898193907325908077357)
            ·
              refine ⟨1600836822715247215529009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4268898193907325908077357 1600836822715247215529009)
              ·
                refine ⟨1200627617036435411646757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600836822715247215529009 1200627617036435411646757)
                ·
                  refine ⟨225117678194331639683767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200627617036435411646757 225117678194331639683767)
                  ·
                    rfl

theorem cell22_1972868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1972868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972868 prefixEnd_1972868 := by exact prefixLift 1972868
  have htrace : WordTrace (prefixWord ++ tailWord_1972868) baseStart_1972868 baseEnd_1972868 := by
    simpa [prefixWord, tailWord_1972868, baseEnd_1972868] using wordTrace_append hprefix tailTrace_1972868
  have hstable : (prefixWord ++ tailWord_1972868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972868).length < 2 ^ (prefixWord ++ tailWord_1972868).sum := by decide
  have hdescent : baseEnd_1972868 < baseStart_1972868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972928 : List Nat := [2, 1, 1, 2, 4, 3, 1, 4, 1, 3]
def baseStart_1972928 : Nat := 118140960795 + 1972928 * 2 ^ 59
def prefixEnd_1972928 : Nat := 4983230072969 + 3 ^ 40 * 1972928 * 2
def baseEnd_1972928 : Nat := 675373573809174762551117

theorem tailTrace_1972928 : CollatzResearch.WordTrace tailWord_1972928 prefixEnd_1972928 675373573809174762551117 := by
  unfold tailWord_1972928
  simp only [CollatzResearch.WordTrace]
  refine ⟨35979297898213140060803719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47972397197617520081071625 35979297898213140060803719)
  ·
    refine ⟨53968946847319710091205579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35979297898213140060803719 53968946847319710091205579)
    ·
      refine ⟨80953420270979565136808369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53968946847319710091205579 80953420270979565136808369)
      ·
        refine ⟨60715065203234673852606277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80953420270979565136808369 60715065203234673852606277)
        ·
          refine ⟨11384074725606501347363677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60715065203234673852606277 11384074725606501347363677)
          ·
            refine ⟨4269028022102438005261379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11384074725606501347363677 4269028022102438005261379)
            ·
              refine ⟨6403542033153657007892069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269028022102438005261379 6403542033153657007892069)
              ·
                refine ⟨1200664131216310688979763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6403542033153657007892069 1200664131216310688979763)
                ·
                  refine ⟨1800996196824466033469645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1200664131216310688979763 1800996196824466033469645)
                  ·
                    refine ⟨675373573809174762551117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1800996196824466033469645 675373573809174762551117)
                    ·
                      rfl

theorem cell22_1972928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 3].length) (baseStart_1972928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972928 prefixEnd_1972928 := by exact prefixLift 1972928
  have htrace : WordTrace (prefixWord ++ tailWord_1972928) baseStart_1972928 baseEnd_1972928 := by
    simpa [prefixWord, tailWord_1972928, baseEnd_1972928] using wordTrace_append hprefix tailTrace_1972928
  have hstable : (prefixWord ++ tailWord_1972928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972928).length < 2 ^ (prefixWord ++ tailWord_1972928).sum := by decide
  have hdescent : baseEnd_1972928 < baseStart_1972928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972954 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_1972954 : Nat := 118140960795 + 1972954 * 2 ^ 59
def prefixEnd_1972954 : Nat := 4983230072969 + 3 ^ 40 * 1972954 * 2
def baseEnd_1972954 : Nat := 675382474140519361401037

theorem tailTrace_1972954 : CollatzResearch.WordTrace tailWord_1972954 prefixEnd_1972954 675382474140519361401037 := by
  unfold tailWord_1972954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989886023583021640513479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47973029396221391041369277 17989886023583021640513479)
  ·
    refine ⟨26984829035374532460770219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17989886023583021640513479 26984829035374532460770219)
    ·
      refine ⟨40477243553061798691155329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26984829035374532460770219 40477243553061798691155329)
      ·
        refine ⟨30357932664796349018366497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40477243553061798691155329 30357932664796349018366497)
        ·
          refine ⟨22768449498597261763774873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30357932664796349018366497 22768449498597261763774873)
          ·
            refine ⟨17076337123947946322831155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22768449498597261763774873 17076337123947946322831155)
            ·
              refine ⟨25614505685921919484246733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17076337123947946322831155 25614505685921919484246733)
              ·
                refine ⟨9605439632220719806592525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25614505685921919484246733 9605439632220719806592525)
                ·
                  refine ⟨3602039862082769927472197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9605439632220719806592525 3602039862082769927472197)
                  ·
                    refine ⟨675382474140519361401037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602039862082769927472197 675382474140519361401037)
                    ·
                      rfl

theorem cell22_1972954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_1972954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972954 prefixEnd_1972954 := by exact prefixLift 1972954
  have htrace : WordTrace (prefixWord ++ tailWord_1972954) baseStart_1972954 baseEnd_1972954 := by
    simpa [prefixWord, tailWord_1972954, baseEnd_1972954] using wordTrace_append hprefix tailTrace_1972954
  have hstable : (prefixWord ++ tailWord_1972954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972954).length < 2 ^ (prefixWord ++ tailWord_1972954).sum := by decide
  have hdescent : baseEnd_1972954 < baseStart_1972954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1972986 : List Nat := [3, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_1972986 : Nat := 118140960795 + 1972986 * 2 ^ 59
def prefixEnd_1972986 : Nat := 4983230072969 + 3 ^ 40 * 1972986 * 2
def baseEnd_1972986 : Nat := 225131142798160648200313

theorem tailTrace_1972986 : CollatzResearch.WordTrace tailWord_1972986 prefixEnd_1972986 225131142798160648200313 := by
  unfold tailWord_1972986
  simp only [CollatzResearch.WordTrace]
  refine ⟨17990177807554039006804703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47973807486810770684812541 17990177807554039006804703)
  ·
    refine ⟨26985266711331058510207055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17990177807554039006804703 26985266711331058510207055)
    ·
      refine ⟨40477900066996587765310583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26985266711331058510207055 40477900066996587765310583)
      ·
        refine ⟨60716850100494881647965875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40477900066996587765310583 60716850100494881647965875)
        ·
          refine ⟨91075275150742322471948813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60716850100494881647965875 91075275150742322471948813)
          ·
            refine ⟨34153228181528370926980805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91075275150742322471948813 34153228181528370926980805)
            ·
              refine ⟨6403730284036569548808901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34153228181528370926980805 6403730284036569548808901)
              ·
                refine ⟨1200699428256856790401669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6403730284036569548808901 1200699428256856790401669)
                ·
                  refine ⟨225131142798160648200313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200699428256856790401669 225131142798160648200313)
                  ·
                    rfl

theorem cell22_1972986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_1972986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1972986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1972986 prefixEnd_1972986 := by exact prefixLift 1972986
  have htrace : WordTrace (prefixWord ++ tailWord_1972986) baseStart_1972986 baseEnd_1972986 := by
    simpa [prefixWord, tailWord_1972986, baseEnd_1972986] using wordTrace_append hprefix tailTrace_1972986
  have hstable : (prefixWord ++ tailWord_1972986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1972986).length < 2 ^ (prefixWord ++ tailWord_1972986).sum := by decide
  have hdescent : baseEnd_1972986 < baseStart_1972986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1972986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973001 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 2, 3]
def baseStart_1973001 : Nat := 118140960795 + 1973001 * 2 ^ 59
def prefixEnd_1973001 : Nat := 4983230072969 + 3 ^ 40 * 1973001 * 2
def baseEnd_1973001 : Nat := 675398563201026905475893

theorem tailTrace_1973001 : CollatzResearch.WordTrace tailWord_1973001 prefixEnd_1973001 675398563201026905475893 := by
  unfold tailWord_1973001
  simp only [CollatzResearch.WordTrace]
  refine ⟨71961258325161813589014857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47974172216774542392676571 71961258325161813589014857)
  ·
    refine ⟨53970943743871360191761143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71961258325161813589014857 53970943743871360191761143)
    ·
      refine ⟨80956415615807040287641715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53970943743871360191761143 80956415615807040287641715)
      ·
        refine ⟨121434623423710560431462573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80956415615807040287641715 121434623423710560431462573)
        ·
          refine ⟨45537983783891460161798465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121434623423710560431462573 45537983783891460161798465)
          ·
            refine ⟨34153487837918595121348849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45537983783891460161798465 34153487837918595121348849)
            ·
              refine ⟨25615115878438946341011637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34153487837918595121348849 25615115878438946341011637)
              ·
                refine ⟨2401417113603651219469841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25615115878438946341011637 2401417113603651219469841)
                ·
                  refine ⟨1801062835202738414602381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2401417113603651219469841 1801062835202738414602381)
                  ·
                    refine ⟨675398563201026905475893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801062835202738414602381 675398563201026905475893)
                    ·
                      rfl

theorem cell22_1973001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_1973001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973001 prefixEnd_1973001 := by exact prefixLift 1973001
  have htrace : WordTrace (prefixWord ++ tailWord_1973001) baseStart_1973001 baseEnd_1973001 := by
    simpa [prefixWord, tailWord_1973001, baseEnd_1973001] using wordTrace_append hprefix tailTrace_1973001
  have hstable : (prefixWord ++ tailWord_1973001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973001).length < 2 ^ (prefixWord ++ tailWord_1973001).sum := by decide
  have hdescent : baseEnd_1973001 < baseStart_1973001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973037 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1973037 : Nat := 118140960795 + 1973037 * 2 ^ 59
def prefixEnd_1973037 : Nat := 4983230072969 + 3 ^ 40 * 1973037 * 2
def baseEnd_1973037 : Nat := 225136962245578270525261

theorem tailTrace_1973037 : CollatzResearch.WordTrace tailWord_1973037 prefixEnd_1973037 225136962245578270525261 := by
  unfold tailWord_1973037
  simp only [CollatzResearch.WordTrace]
  refine ⟨71962571353031391737325365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47975047568687594491550243 71962571353031391737325365)
  ·
    refine ⟨6746491064346692975374253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71962571353031391737325365 6746491064346692975374253)
    ·
      refine ⟨2529934149130009865765345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6746491064346692975374253 2529934149130009865765345)
      ·
        refine ⟨1897450611847507399324009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529934149130009865765345 1897450611847507399324009)
        ·
          refine ⟨1423087958885630549493007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1897450611847507399324009 1423087958885630549493007)
          ·
            refine ⟨2134631938328445824239511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423087958885630549493007 2134631938328445824239511)
            ·
              refine ⟨3201947907492668736359267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134631938328445824239511 3201947907492668736359267)
              ·
                refine ⟨4802921861239003104538901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3201947907492668736359267 4802921861239003104538901)
                ·
                  refine ⟨225136962245578270525261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4802921861239003104538901 225136962245578270525261)
                  ·
                    rfl

theorem cell22_1973037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1973037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973037 prefixEnd_1973037 := by exact prefixLift 1973037
  have htrace : WordTrace (prefixWord ++ tailWord_1973037) baseStart_1973037 baseEnd_1973037 := by
    simpa [prefixWord, tailWord_1973037, baseEnd_1973037] using wordTrace_append hprefix tailTrace_1973037
  have hstable : (prefixWord ++ tailWord_1973037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973037).length < 2 ^ (prefixWord ++ tailWord_1973037).sum := by decide
  have hdescent : baseEnd_1973037 < baseStart_1973037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973106 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1973106 : Nat := 118140960795 + 1973106 * 2 ^ 59
def prefixEnd_1973106 : Nat := 4983230072969 + 3 ^ 40 * 1973106 * 2
def baseEnd_1973106 : Nat := 675434506846841631600571

theorem tailTrace_1973106 : CollatzResearch.WordTrace tailWord_1973106 prefixEnd_1973106 675434506846841631600571 := by
  unfold tailWord_1973106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17991271997445354130396793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47976725326520944347724781 17991271997445354130396793)
  ·
    refine ⟨13493453998084015597797595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17991271997445354130396793 13493453998084015597797595)
    ·
      refine ⟨20240180997126023396696393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13493453998084015597797595 20240180997126023396696393)
      ·
        refine ⟨15180135747844517547522295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20240180997126023396696393 15180135747844517547522295)
        ·
          refine ⟨22770203621766776321283443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15180135747844517547522295 22770203621766776321283443)
          ·
            refine ⟨34155305432650164481925165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22770203621766776321283443 34155305432650164481925165)
            ·
              refine ⟨12808239537243811680721937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34155305432650164481925165 12808239537243811680721937)
              ·
                refine ⟨9606179652932858760541453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12808239537243811680721937 9606179652932858760541453)
                ·
                  refine ⟨3602317369849822035203045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9606179652932858760541453 3602317369849822035203045)
                  ·
                    refine ⟨675434506846841631600571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602317369849822035203045 675434506846841631600571)
                    ·
                      rfl

theorem cell22_1973106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1973106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973106 prefixEnd_1973106 := by exact prefixLift 1973106
  have htrace : WordTrace (prefixWord ++ tailWord_1973106) baseStart_1973106 baseEnd_1973106 := by
    simpa [prefixWord, tailWord_1973106, baseEnd_1973106] using wordTrace_append hprefix tailTrace_1973106
  have hstable : (prefixWord ++ tailWord_1973106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973106).length < 2 ^ (prefixWord ++ tailWord_1973106).sum := by decide
  have hdescent : baseEnd_1973106 < baseStart_1973106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973221 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_1973221 : Nat := 118140960795 + 1973221 * 2 ^ 59
def prefixEnd_1973221 : Nat := 4983230072969 + 3 ^ 40 * 1973221 * 2
def baseEnd_1973221 : Nat := 675473873697019664975219

theorem tailTrace_1973221 : CollatzResearch.WordTrace tailWord_1973221 prefixEnd_1973221 675473873697019664975219 := by
  unfold tailWord_1973221
  simp only [CollatzResearch.WordTrace]
  refine ⟨71969282384364791162023517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47979521589576527441349011 71969282384364791162023517)
  ·
    refine ⟨26988480894136796685758819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71969282384364791162023517 26988480894136796685758819)
    ·
      refine ⟨40482721341205195028638229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26988480894136796685758819 40482721341205195028638229)
      ·
        refine ⟨1897627562868993516967417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40482721341205195028638229 1897627562868993516967417)
        ·
          refine ⟨1423220672151745137725563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1897627562868993516967417 1423220672151745137725563)
          ·
            refine ⟨2134831008227617706588345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423220672151745137725563 2134831008227617706588345)
            ·
              refine ⟨1601123256170713279941259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134831008227617706588345 1601123256170713279941259)
              ·
                refine ⟨2401684884256069919911889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601123256170713279941259 2401684884256069919911889)
                ·
                  refine ⟨1801263663192052439933917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2401684884256069919911889 1801263663192052439933917)
                  ·
                    refine ⟨675473873697019664975219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801263663192052439933917 675473873697019664975219)
                    ·
                      rfl

theorem cell22_1973221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_1973221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973221 prefixEnd_1973221 := by exact prefixLift 1973221
  have htrace : WordTrace (prefixWord ++ tailWord_1973221) baseStart_1973221 baseEnd_1973221 := by
    simpa [prefixWord, tailWord_1973221, baseEnd_1973221] using wordTrace_append hprefix tailTrace_1973221
  have hstable : (prefixWord ++ tailWord_1973221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973221).length < 2 ^ (prefixWord ++ tailWord_1973221).sum := by decide
  have hdescent : baseEnd_1973221 < baseStart_1973221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973236 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1973236 : Nat := 118140960795 + 1973236 * 2 ^ 59
def prefixEnd_1973236 : Nat := 4983230072969 + 3 ^ 40 * 1973236 * 2
def baseEnd_1973236 : Nat := 675479008503564625850173

theorem tailTrace_1973236 : CollatzResearch.WordTrace tailWord_1973236 prefixEnd_1973236 675479008503564625850173 := by
  unfold tailWord_1973236
  simp only [CollatzResearch.WordTrace]
  refine ⟨35984914739655224361909781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47979886319540299149213041 35984914739655224361909781)
  ·
    refine ⟨1686792878421338641964521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35984914739655224361909781 1686792878421338641964521)
    ·
      refine ⟨1265094658816003981473391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1686792878421338641964521 1265094658816003981473391)
      ·
        refine ⟨1897641988224005972210087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265094658816003981473391 1897641988224005972210087)
        ·
          refine ⟨2846462982336008958315131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897641988224005972210087 2846462982336008958315131)
          ·
            refine ⟨4269694473504013437472697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846462982336008958315131 4269694473504013437472697)
            ·
              refine ⟨3202270855128010078104523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4269694473504013437472697 3202270855128010078104523)
              ·
                refine ⟨4803406282692015117156785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202270855128010078104523 4803406282692015117156785)
                ·
                  refine ⟨3602554712019011337867589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803406282692015117156785 3602554712019011337867589)
                  ·
                    refine ⟨675479008503564625850173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602554712019011337867589 675479008503564625850173)
                    ·
                      rfl

theorem cell22_1973236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1973236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973236 prefixEnd_1973236 := by exact prefixLift 1973236
  have htrace : WordTrace (prefixWord ++ tailWord_1973236) baseStart_1973236 baseEnd_1973236 := by
    simpa [prefixWord, tailWord_1973236, baseEnd_1973236] using wordTrace_append hprefix tailTrace_1973236
  have hstable : (prefixWord ++ tailWord_1973236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973236).length < 2 ^ (prefixWord ++ tailWord_1973236).sum := by decide
  have hdescent : baseEnd_1973236 < baseStart_1973236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973290 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_1973290 : Nat := 118140960795 + 1973290 * 2 ^ 59
def prefixEnd_1973290 : Nat := 4983230072969 + 3 ^ 40 * 1973290 * 2
def baseEnd_1973290 : Nat := 225165831269042161666669

theorem tailTrace_1973290 : CollatzResearch.WordTrace tailWord_1973290 prefixEnd_1973290 225165831269042161666669 := by
  unfold tailWord_1973290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17992949755278703986571331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47981199347409877297523549 17992949755278703986571331)
  ·
    refine ⟨26989424632918055979856997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17992949755278703986571331 26989424632918055979856997)
    ·
      refine ⟨5060517118672135496223187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26989424632918055979856997 5060517118672135496223187)
      ·
        refine ⟨7590775678008203244334781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5060517118672135496223187 7590775678008203244334781)
        ·
          refine ⟨2846540879253076216625543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7590775678008203244334781 2846540879253076216625543)
          ·
            refine ⟨4269811318879614324938315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846540879253076216625543 4269811318879614324938315)
            ·
              refine ⟨6404716978319421487407473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269811318879614324938315 6404716978319421487407473)
              ·
                refine ⟨4803537733739566115555605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6404716978319421487407473 4803537733739566115555605)
                ·
                  refine ⟨225165831269042161666669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4803537733739566115555605 225165831269042161666669)
                  ·
                    rfl

theorem cell22_1973290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_1973290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973290 prefixEnd_1973290 := by exact prefixLift 1973290
  have htrace : WordTrace (prefixWord ++ tailWord_1973290) baseStart_1973290 baseEnd_1973290 := by
    simpa [prefixWord, tailWord_1973290, baseEnd_1973290] using wordTrace_append hprefix tailTrace_1973290
  have hstable : (prefixWord ++ tailWord_1973290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973290).length < 2 ^ (prefixWord ++ tailWord_1973290).sum := by decide
  have hdescent : baseEnd_1973290 < baseStart_1973290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973384 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 3, 3]
def baseStart_1973384 : Nat := 118140960795 + 1973384 * 2 ^ 59
def prefixEnd_1973384 : Nat := 4983230072969 + 3 ^ 40 * 1973384 * 2
def baseEnd_1973384 : Nat := 675529671928141573149719

theorem tailTrace_1973384 : CollatzResearch.WordTrace tailWord_1973384 prefixEnd_1973384 675529671928141573149719 := by
  unfold tailWord_1973384
  simp only [CollatzResearch.WordTrace]
  refine ⟨35987613741387135000103603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47983484988516180000138137 35987613741387135000103603)
  ·
    refine ⟨53981420612080702500155405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35987613741387135000103603 53981420612080702500155405)
    ·
      refine ⟨20243032729530263437558277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53981420612080702500155405 20243032729530263437558277)
      ·
        refine ⟨3795568636786924394542177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20243032729530263437558277 3795568636786924394542177)
        ·
          refine ⟨2846676477590193295906633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3795568636786924394542177 2846676477590193295906633)
          ·
            refine ⟨2135007358192644971929975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2846676477590193295906633 2135007358192644971929975)
            ·
              refine ⟨3202511037288967457894963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135007358192644971929975 3202511037288967457894963)
              ·
                refine ⟨4803766555933451186842445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202511037288967457894963 4803766555933451186842445)
                ·
                  refine ⟨1801412458475044195065917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4803766555933451186842445 1801412458475044195065917)
                  ·
                    refine ⟨675529671928141573149719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801412458475044195065917 675529671928141573149719)
                    ·
                      rfl

theorem cell22_1973384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_1973384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973384 prefixEnd_1973384 := by exact prefixLift 1973384
  have htrace : WordTrace (prefixWord ++ tailWord_1973384) baseStart_1973384 baseEnd_1973384 := by
    simpa [prefixWord, tailWord_1973384, baseEnd_1973384] using wordTrace_append hprefix tailTrace_1973384
  have hstable : (prefixWord ++ tailWord_1973384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973384).length < 2 ^ (prefixWord ++ tailWord_1973384).sum := by decide
  have hdescent : baseEnd_1973384 < baseStart_1973384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973408 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 8]
def baseStart_1973408 : Nat := 118140960795 + 1973408 * 2 ^ 59
def prefixEnd_1973408 : Nat := 4983230072969 + 3 ^ 40 * 1973408 * 2
def baseEnd_1973408 : Nat := 225179295872871170183215

theorem tailTrace_1973408 : CollatzResearch.WordTrace tailWord_1973408 prefixEnd_1973408 225179295872871170183215 := by
  unfold tailWord_1973408
  simp only [CollatzResearch.WordTrace]
  refine ⟨35988051417343661049540439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47984068556458214732720585 35988051417343661049540439)
  ·
    refine ⟨53982077126015491574310659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35988051417343661049540439 53982077126015491574310659)
    ·
      refine ⟨80973115689023237361465989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53982077126015491574310659 80973115689023237361465989)
      ·
        refine ⟨15182459191691857005274873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80973115689023237361465989 15182459191691857005274873)
        ·
          refine ⟨11386844393768892753956155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15182459191691857005274873 11386844393768892753956155)
          ·
            refine ⟨17080266590653339130934233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11386844393768892753956155 17080266590653339130934233)
            ·
              refine ⟨12810199942990004348200675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17080266590653339130934233 12810199942990004348200675)
              ·
                refine ⟨19215299914485006522301013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12810199942990004348200675 19215299914485006522301013)
                ·
                  refine ⟨225179295872871170183215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19215299914485006522301013 225179295872871170183215)
                  ·
                    rfl

theorem cell22_1973408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_1973408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973408 prefixEnd_1973408 := by exact prefixLift 1973408
  have htrace : WordTrace (prefixWord ++ tailWord_1973408) baseStart_1973408 baseEnd_1973408 := by
    simpa [prefixWord, tailWord_1973408, baseEnd_1973408] using wordTrace_append hprefix tailTrace_1973408
  have hstable : (prefixWord ++ tailWord_1973408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973408).length < 2 ^ (prefixWord ++ tailWord_1973408).sum := by decide
  have hdescent : baseEnd_1973408 < baseStart_1973408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973423 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 3, 5]
def baseStart_1973423 : Nat := 118140960795 + 1973423 * 2 ^ 59
def prefixEnd_1973423 : Nat := 4983230072969 + 3 ^ 40 * 1973423 * 2
def baseEnd_1973423 : Nat := 675543022425158471424599

theorem tailTrace_1973423 : CollatzResearch.WordTrace tailWord_1973423 prefixEnd_1973423 675543022425158471424599 := by
  unfold tailWord_1973423
  simp only [CollatzResearch.WordTrace]
  refine ⟨71976649929632979660876923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47984433286421986440584615 71976649929632979660876923)
  ·
    refine ⟨107964974894449469491315385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71976649929632979660876923 107964974894449469491315385)
    ·
      refine ⟨80973731170837102118486539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107964974894449469491315385 80973731170837102118486539)
      ·
        refine ⟨121460596756255653177729809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80973731170837102118486539 121460596756255653177729809)
        ·
          refine ⟨91095447567191739883297357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121460596756255653177729809 91095447567191739883297357)
          ·
            refine ⟨34160792837696902456236509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91095447567191739883297357 34160792837696902456236509)
            ·
              refine ⟨12810297314136338421088691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34160792837696902456236509 12810297314136338421088691)
              ·
                refine ⟨19215445971204507631633037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12810297314136338421088691 19215445971204507631633037)
                ·
                  refine ⟨7205792239201690361862389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19215445971204507631633037 7205792239201690361862389)
                  ·
                    refine ⟨675543022425158471424599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7205792239201690361862389 675543022425158471424599)
                    ·
                      rfl

theorem cell22_1973423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_1973423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973423 prefixEnd_1973423 := by exact prefixLift 1973423
  have htrace : WordTrace (prefixWord ++ tailWord_1973423) baseStart_1973423 baseEnd_1973423 := by
    simpa [prefixWord, tailWord_1973423, baseEnd_1973423] using wordTrace_append hprefix tailTrace_1973423
  have hstable : (prefixWord ++ tailWord_1973423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973423).length < 2 ^ (prefixWord ++ tailWord_1973423).sum := by decide
  have hdescent : baseEnd_1973423 < baseStart_1973423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973446 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1973446 : Nat := 118140960795 + 1973446 * 2 ^ 59
def prefixEnd_1973446 : Nat := 4983230072969 + 3 ^ 40 * 1973446 * 2
def baseEnd_1973446 : Nat := 675550895795194078099529

theorem tailTrace_1973446 : CollatzResearch.WordTrace tailWord_1973446 prefixEnd_1973446 675550895795194078099529 := by
  unfold tailWord_1973446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249296525267176705905131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47984992539033103059309461 2249296525267176705905131)
  ·
    refine ⟨3373944787900765058857697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2249296525267176705905131 3373944787900765058857697)
    ·
      refine ⟨2530458590925573794143273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3373944787900765058857697 2530458590925573794143273)
      ·
        refine ⟨1897843943194180345607455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2530458590925573794143273 1897843943194180345607455)
        ·
          refine ⟨2846765914791270518411183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897843943194180345607455 2846765914791270518411183)
          ·
            refine ⟨4270148872186905777616775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846765914791270518411183 4270148872186905777616775)
            ·
              refine ⟨6405223308280358666425163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4270148872186905777616775 6405223308280358666425163)
              ·
                refine ⟨9607834962420537999637745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6405223308280358666425163 9607834962420537999637745)
                ·
                  refine ⟨7205876221815403499728309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9607834962420537999637745 7205876221815403499728309)
                  ·
                    refine ⟨675550895795194078099529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7205876221815403499728309 675550895795194078099529)
                    ·
                      rfl

theorem cell22_1973446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1973446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973446 prefixEnd_1973446 := by exact prefixLift 1973446
  have htrace : WordTrace (prefixWord ++ tailWord_1973446) baseStart_1973446 baseEnd_1973446 := by
    simpa [prefixWord, tailWord_1973446, baseEnd_1973446] using wordTrace_append hprefix tailTrace_1973446
  have hstable : (prefixWord ++ tailWord_1973446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973446).length < 2 ^ (prefixWord ++ tailWord_1973446).sum := by decide
  have hdescent : baseEnd_1973446 < baseStart_1973446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973472 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 2, 4]
def baseStart_1973472 : Nat := 118140960795 + 1973472 * 2 ^ 59
def prefixEnd_1973472 : Nat := 4983230072969 + 3 ^ 40 * 1973472 * 2
def baseEnd_1973472 : Nat := 675559796126538676949449

theorem tailTrace_1973472 : CollatzResearch.WordTrace tailWord_1973472 prefixEnd_1973472 675559796126538676949449 := by
  unfold tailWord_1973472
  simp only [CollatzResearch.WordTrace]
  refine ⟨35989218553227730514705335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47985624737636974019607113 35989218553227730514705335)
  ·
    refine ⟨53983827829841595772058003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35989218553227730514705335 53983827829841595772058003)
    ·
      refine ⟨80975741744762393658087005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53983827829841595772058003 80975741744762393658087005)
      ·
        refine ⟨30365903154285897621782627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80975741744762393658087005 30365903154285897621782627)
        ·
          refine ⟨45548854731428846432673941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30365903154285897621782627 45548854731428846432673941)
          ·
            refine ⟨2135102565535727176531591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45548854731428846432673941 2135102565535727176531591)
            ·
              refine ⟨3202653848303590764797387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135102565535727176531591 3202653848303590764797387)
              ·
                refine ⟨4803980772455386147196081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202653848303590764797387 4803980772455386147196081)
                ·
                  refine ⟨3602985579341539610397061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4803980772455386147196081 3602985579341539610397061)
                  ·
                    refine ⟨675559796126538676949449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3602985579341539610397061 675559796126538676949449)
                    ·
                      rfl

theorem cell22_1973472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_1973472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973472 prefixEnd_1973472 := by exact prefixLift 1973472
  have htrace : WordTrace (prefixWord ++ tailWord_1973472) baseStart_1973472 baseEnd_1973472 := by
    simpa [prefixWord, tailWord_1973472, baseEnd_1973472] using wordTrace_append hprefix tailTrace_1973472
  have hstable : (prefixWord ++ tailWord_1973472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973472).length < 2 ^ (prefixWord ++ tailWord_1973472).sum := by decide
  have hdescent : baseEnd_1973472 < baseStart_1973472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973637 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_1973637 : Nat := 118140960795 + 1973637 * 2 ^ 59
def prefixEnd_1973637 : Nat := 4983230072969 + 3 ^ 40 * 1973637 * 2
def baseEnd_1973637 : Nat := 675616278998533246573943

theorem tailTrace_1973637 : CollatzResearch.WordTrace tailWord_1973637 prefixEnd_1973637 675616278998533246573943 := by
  unfold tailWord_1973637
  simp only [CollatzResearch.WordTrace]
  refine ⟨71984455150857694209167165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47989636767238462806111443 71984455150857694209167165)
  ·
    refine ⟨26994170681571635328437687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71984455150857694209167165 26994170681571635328437687)
    ·
      refine ⟨40491256022357452992656531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26994170681571635328437687 40491256022357452992656531)
      ·
        refine ⟨60736884033536179488984797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40491256022357452992656531 60736884033536179488984797)
        ·
          refine ⟨22776331512576067308369299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60736884033536179488984797 22776331512576067308369299)
          ·
            refine ⟨34164497268864100962553949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22776331512576067308369299 34164497268864100962553949)
            ·
              refine ⟨12811686475824037860957731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34164497268864100962553949 12811686475824037860957731)
              ·
                refine ⟨19217529713736056791436597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12811686475824037860957731 19217529713736056791436597)
                ·
                  refine ⟨1801643410662755324197181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19217529713736056791436597 1801643410662755324197181)
                  ·
                    refine ⟨675616278998533246573943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801643410662755324197181 675616278998533246573943)
                    ·
                      rfl

theorem cell22_1973637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_1973637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973637 prefixEnd_1973637 := by exact prefixLift 1973637
  have htrace : WordTrace (prefixWord ++ tailWord_1973637) baseStart_1973637 baseEnd_1973637 := by
    simpa [prefixWord, tailWord_1973637, baseEnd_1973637] using wordTrace_append hprefix tailTrace_1973637
  have hstable : (prefixWord ++ tailWord_1973637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973637).length < 2 ^ (prefixWord ++ tailWord_1973637).sum := by decide
  have hdescent : baseEnd_1973637 < baseStart_1973637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973641 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 2, 4]
def baseStart_1973641 : Nat := 118140960795 + 1973641 * 2 ^ 59
def prefixEnd_1973641 : Nat := 4983230072969 + 3 ^ 40 * 1973641 * 2
def baseEnd_1973641 : Nat := 675617648280278569473931

theorem tailTrace_1973641 : CollatzResearch.WordTrace tailWord_1973641 prefixEnd_1973641 675617648280278569473931 := by
  unfold tailWord_1973641
  simp only [CollatzResearch.WordTrace]
  refine ⟨71984601042843202892312777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47989734028562135261541851 71984601042843202892312777)
  ·
    refine ⟨53988450782132402169234583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71984601042843202892312777 53988450782132402169234583)
    ·
      refine ⟨80982676173198603253851875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53988450782132402169234583 80982676173198603253851875)
      ·
        refine ⟨121474014259797904880777813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80982676173198603253851875 121474014259797904880777813)
        ·
          refine ⟨1423523604607006697821615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 121474014259797904880777813 1423523604607006697821615)
          ·
            refine ⟨2135285406910510046732423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423523604607006697821615 2135285406910510046732423)
            ·
              refine ⟨3202928110365765070098635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135285406910510046732423 3202928110365765070098635)
              ·
                refine ⟨4804392165548647605147953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202928110365765070098635 4804392165548647605147953)
                ·
                  refine ⟨3603294124161485703860965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4804392165548647605147953 3603294124161485703860965)
                  ·
                    refine ⟨675617648280278569473931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3603294124161485703860965 675617648280278569473931)
                    ·
                      rfl

theorem cell22_1973641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 4].length) (baseStart_1973641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973641 prefixEnd_1973641 := by exact prefixLift 1973641
  have htrace : WordTrace (prefixWord ++ tailWord_1973641) baseStart_1973641 baseEnd_1973641 := by
    simpa [prefixWord, tailWord_1973641, baseEnd_1973641] using wordTrace_append hprefix tailTrace_1973641
  have hstable : (prefixWord ++ tailWord_1973641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973641).length < 2 ^ (prefixWord ++ tailWord_1973641).sum := by decide
  have hdescent : baseEnd_1973641 < baseStart_1973641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973660 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_1973660 : Nat := 118140960795 + 1973660 * 2 ^ 59
def prefixEnd_1973660 : Nat := 4983230072969 + 3 ^ 40 * 1973660 * 2
def baseEnd_1973660 : Nat := 675624152368568853248873

theorem tailTrace_1973660 : CollatzResearch.WordTrace tailWord_1973660 prefixEnd_1973660 675624152368568853248873 := by
  unfold tailWord_1973660
  simp only [CollatzResearch.WordTrace]
  refine ⟨35992647014887184568627217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47990196019849579424836289 35992647014887184568627217)
  ·
    refine ⟨26994485261165388426470413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35992647014887184568627217 26994485261165388426470413)
    ·
      refine ⟨10122931972937020659926405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26994485261165388426470413 10122931972937020659926405)
      ·
        refine ⟨1898049744925691373736201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10122931972937020659926405 1898049744925691373736201)
        ·
          refine ⟨1423537308694268530302151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898049744925691373736201 1423537308694268530302151)
          ·
            refine ⟨2135305963041402795453227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423537308694268530302151 2135305963041402795453227)
            ·
              refine ⟨3202958944562104193179841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135305963041402795453227 3202958944562104193179841)
              ·
                refine ⟨2402219208421578144884881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202958944562104193179841 2402219208421578144884881)
                ·
                  refine ⟨1801664406316183608663661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2402219208421578144884881 1801664406316183608663661)
                  ·
                    refine ⟨675624152368568853248873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801664406316183608663661 675624152368568853248873)
                    ·
                      rfl

theorem cell22_1973660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_1973660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973660 prefixEnd_1973660 := by exact prefixLift 1973660
  have htrace : WordTrace (prefixWord ++ tailWord_1973660) baseStart_1973660 baseEnd_1973660 := by
    simpa [prefixWord, tailWord_1973660, baseEnd_1973660] using wordTrace_append hprefix tailTrace_1973660
  have hstable : (prefixWord ++ tailWord_1973660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973660).length < 2 ^ (prefixWord ++ tailWord_1973660).sum := by decide
  have hdescent : baseEnd_1973660 < baseStart_1973660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973671 : List Nat := [1, 1, 6, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1973671 : Nat := 118140960795 + 1973671 * 2 ^ 59
def prefixEnd_1973671 : Nat := 4983230072969 + 3 ^ 40 * 1973671 * 2
def baseEnd_1973671 : Nat := 675627917893368491223839

theorem tailTrace_1973671 : CollatzResearch.WordTrace tailWord_1973671 prefixEnd_1973671 675627917893368491223839 := by
  unfold tailWord_1973671
  simp only [CollatzResearch.WordTrace]
  refine ⟨71985695232734518015904867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47990463488489678677269911 71985695232734518015904867)
  ·
    refine ⟨107978542849101777023857301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71985695232734518015904867 107978542849101777023857301)
    ·
      refine ⟨5061494196051645797993311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107978542849101777023857301 5061494196051645797993311)
      ·
        refine ⟨7592241294077468696989967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061494196051645797993311 7592241294077468696989967)
        ·
          refine ⟨11388361941116203045484951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592241294077468696989967 11388361941116203045484951)
          ·
            refine ⟨17082542911674304568227427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11388361941116203045484951 17082542911674304568227427)
            ·
              refine ⟨25623814367511456852341141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17082542911674304568227427 25623814367511456852341141)
              ·
                refine ⟨1201116298477099539953491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25623814367511456852341141 1201116298477099539953491)
                ·
                  refine ⟨1801674447715649309930237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201116298477099539953491 1801674447715649309930237)
                  ·
                    refine ⟨675627917893368491223839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801674447715649309930237 675627917893368491223839)
                    ·
                      rfl

theorem cell22_1973671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1973671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973671 prefixEnd_1973671 := by exact prefixLift 1973671
  have htrace : WordTrace (prefixWord ++ tailWord_1973671) baseStart_1973671 baseEnd_1973671 := by
    simpa [prefixWord, tailWord_1973671, baseEnd_1973671] using wordTrace_append hprefix tailTrace_1973671
  have hstable : (prefixWord ++ tailWord_1973671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973671).length < 2 ^ (prefixWord ++ tailWord_1973671).sum := by decide
  have hdescent : baseEnd_1973671 < baseStart_1973671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973680 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_1973680 : Nat := 118140960795 + 1973680 * 2 ^ 59
def prefixEnd_1973680 : Nat := 4983230072969 + 3 ^ 40 * 1973680 * 2
def baseEnd_1973680 : Nat := 675630998777295467748811

theorem tailTrace_1973680 : CollatzResearch.WordTrace tailWord_1973680 prefixEnd_1973680 675630998777295467748811 := by
  unfold tailWord_1973680
  simp only [CollatzResearch.WordTrace]
  refine ⟨35993011744850956276491247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47990682326467941701988329 35993011744850956276491247)
  ·
    refine ⟨53989517617276434414736871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35993011744850956276491247 53989517617276434414736871)
    ·
      refine ⟨80984276425914651622105307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53989517617276434414736871 80984276425914651622105307)
      ·
        refine ⟨121476414638871977433157961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80984276425914651622105307 121476414638871977433157961)
        ·
          refine ⟨91107310979153983074868471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121476414638871977433157961 91107310979153983074868471)
          ·
            refine ⟨136660966468730974612302707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91107310979153983074868471 136660966468730974612302707)
            ·
              refine ⟨204991449703096461918454061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136660966468730974612302707 204991449703096461918454061)
              ·
                refine ⟨76871793638661173219420273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204991449703096461918454061 76871793638661173219420273)
                ·
                  refine ⟨57653845228995879914565205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76871793638661173219420273 57653845228995879914565205)
                  ·
                    refine ⟨675630998777295467748811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57653845228995879914565205 675630998777295467748811)
                    ·
                      rfl

theorem cell22_1973680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_1973680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973680 prefixEnd_1973680 := by exact prefixLift 1973680
  have htrace : WordTrace (prefixWord ++ tailWord_1973680) baseStart_1973680 baseEnd_1973680 := by
    simpa [prefixWord, tailWord_1973680, baseEnd_1973680] using wordTrace_append hprefix tailTrace_1973680
  have hstable : (prefixWord ++ tailWord_1973680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973680).length < 2 ^ (prefixWord ++ tailWord_1973680).sum := by decide
  have hdescent : baseEnd_1973680 < baseStart_1973680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973729 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 6]
def baseStart_1973729 : Nat := 118140960795 + 1973729 * 2 ^ 59
def prefixEnd_1973729 : Nat := 4983230072969 + 3 ^ 40 * 1973729 * 2
def baseEnd_1973729 : Nat := 225215924159558557757887

theorem tailTrace_1973729 : CollatzResearch.WordTrace tailWord_1973729 prefixEnd_1973729 225215924159558557757887 := by
  unfold tailWord_1973729
  simp only [CollatzResearch.WordTrace]
  refine ⟨71987810666524393921516241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47991873777682929281010827 71987810666524393921516241)
  ·
    refine ⟨53990857999893295441137181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71987810666524393921516241 53990857999893295441137181)
    ·
      refine ⟨20246571749959985790426443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53990857999893295441137181 20246571749959985790426443)
      ·
        refine ⟨30369857624939978685639665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20246571749959985790426443 30369857624939978685639665)
        ·
          refine ⟨22777393218704984014229749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30369857624939978685639665 22777393218704984014229749)
          ·
            refine ⟨2135380614253592251334039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22777393218704984014229749 2135380614253592251334039)
            ·
              refine ⟨3203070921380388377001059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135380614253592251334039 3203070921380388377001059)
              ·
                refine ⟨4804606382070582565501589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203070921380388377001059 4804606382070582565501589)
                ·
                  refine ⟨225215924159558557757887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4804606382070582565501589 225215924159558557757887)
                  ·
                    rfl

theorem cell22_1973729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_1973729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973729 prefixEnd_1973729 := by exact prefixLift 1973729
  have htrace : WordTrace (prefixWord ++ tailWord_1973729) baseStart_1973729 baseEnd_1973729 := by
    simpa [prefixWord, tailWord_1973729, baseEnd_1973729] using wordTrace_append hprefix tailTrace_1973729
  have hstable : (prefixWord ++ tailWord_1973729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973729).length < 2 ^ (prefixWord ++ tailWord_1973729).sum := by decide
  have hdescent : baseEnd_1973729 < baseStart_1973729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973757 : List Nat := [1, 4, 1, 1, 1, 4, 2, 8]
def baseStart_1973757 : Nat := 118140960795 + 1973757 * 2 ^ 59
def prefixEnd_1973757 : Nat := 4983230072969 + 3 ^ 40 * 1973757 * 2
def baseEnd_1973757 : Nat := 75073039716765881508175

theorem tailTrace_1973757 : CollatzResearch.WordTrace tailWord_1973757 prefixEnd_1973757 75073039716765881508175 := by
  unfold tailWord_1973757
  simp only [CollatzResearch.WordTrace]
  refine ⟨71988831910422954703535525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47992554606948636469023683 71988831910422954703535525)
  ·
    refine ⟨13497905983204304006912911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71988831910422954703535525 13497905983204304006912911)
    ·
      refine ⟨20246858974806456010369367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13497905983204304006912911 20246858974806456010369367)
      ·
        refine ⟨30370288462209684015554051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20246858974806456010369367 30370288462209684015554051)
        ·
          refine ⟨45555432693314526023331077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30370288462209684015554051 45555432693314526023331077)
          ·
            refine ⟨8541643629996473629374577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45555432693314526023331077 8541643629996473629374577)
            ·
              refine ⟨6406232722497355222030933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8541643629996473629374577 6406232722497355222030933)
              ·
                refine ⟨75073039716765881508175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6406232722497355222030933 75073039716765881508175)
                ·
                  rfl

theorem cell22_1973757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 8].length) (baseStart_1973757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973757 prefixEnd_1973757 := by exact prefixLift 1973757
  have htrace : WordTrace (prefixWord ++ tailWord_1973757) baseStart_1973757 baseEnd_1973757 := by
    simpa [prefixWord, tailWord_1973757, baseEnd_1973757] using wordTrace_append hprefix tailTrace_1973757
  have hstable : (prefixWord ++ tailWord_1973757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973757).length < 2 ^ (prefixWord ++ tailWord_1973757).sum := by decide
  have hdescent : baseEnd_1973757 < baseStart_1973757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973774 : List Nat := [4, 1, 1, 2, 5, 9]
def baseStart_1973774 : Nat := 118140960795 + 1973774 * 2 ^ 59
def prefixEnd_1973774 : Nat := 4983230072969 + 3 ^ 40 * 1973774 * 2
def baseEnd_1973774 : Nat := 8341520702448278467883

theorem tailTrace_1973774 : CollatzResearch.WordTrace tailWord_1973774 prefixEnd_1973774 8341520702448278467883 := by
  unfold tailWord_1973774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8998681493920170825863047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47992967967574244404602917 8998681493920170825863047)
  ·
    refine ⟨13498022240880256238794571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8998681493920170825863047 13498022240880256238794571)
    ·
      refine ⟨20247033361320384358191857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13498022240880256238794571 20247033361320384358191857)
      ·
        refine ⟨15185275020990288268643893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20247033361320384358191857 15185275020990288268643893)
        ·
          refine ⟨1423619533217839525185365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15185275020990288268643893 1423619533217839525185365)
          ·
            refine ⟨8341520702448278467883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1423619533217839525185365 8341520702448278467883)
            ·
              rfl

theorem cell22_1973774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 9].length) (baseStart_1973774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973774 prefixEnd_1973774 := by exact prefixLift 1973774
  have htrace : WordTrace (prefixWord ++ tailWord_1973774) baseStart_1973774 baseEnd_1973774 := by
    simpa [prefixWord, tailWord_1973774, baseEnd_1973774] using wordTrace_append hprefix tailTrace_1973774
  have hstable : (prefixWord ++ tailWord_1973774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973774).length < 2 ^ (prefixWord ++ tailWord_1973774).sum := by decide
  have hdescent : baseEnd_1973774 < baseStart_1973774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973806 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1973806 : Nat := 118140960795 + 1973806 * 2 ^ 59
def prefixEnd_1973806 : Nat := 4983230072969 + 3 ^ 40 * 1973806 * 2
def baseEnd_1973806 : Nat := 675674131152273139098425

theorem tailTrace_1973806 : CollatzResearch.WordTrace tailWord_1973806 prefixEnd_1973806 675674131152273139098425 := by
  unfold tailWord_1973806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8998827385905679509008659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47993746058163624048046181 8998827385905679509008659)
  ·
    refine ⟨13498241078858519263512989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8998827385905679509008659 13498241078858519263512989)
    ·
      refine ⟨5061840404571944723817371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13498241078858519263512989 5061840404571944723817371)
      ·
        refine ⟨7592760606857917085726057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061840404571944723817371 7592760606857917085726057)
        ·
          refine ⟨5694570455143437814294543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7592760606857917085726057 5694570455143437814294543)
          ·
            refine ⟨8541855682715156721441815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694570455143437814294543 8541855682715156721441815)
            ·
              refine ⟨12812783524072735082162723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541855682715156721441815 12812783524072735082162723)
              ·
                refine ⟨19219175286109102623244085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12812783524072735082162723 19219175286109102623244085)
                ·
                  refine ⟨1801797683072728370929133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19219175286109102623244085 1801797683072728370929133)
                  ·
                    refine ⟨675674131152273139098425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801797683072728370929133 675674131152273139098425)
                    ·
                      rfl

theorem cell22_1973806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1973806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973806 prefixEnd_1973806 := by exact prefixLift 1973806
  have htrace : WordTrace (prefixWord ++ tailWord_1973806) baseStart_1973806 baseEnd_1973806 := by
    simpa [prefixWord, tailWord_1973806, baseEnd_1973806] using wordTrace_append hprefix tailTrace_1973806
  have hstable : (prefixWord ++ tailWord_1973806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973806).length < 2 ^ (prefixWord ++ tailWord_1973806).sum := by decide
  have hdescent : baseEnd_1973806 < baseStart_1973806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973823 : List Nat := [1, 1, 2, 2, 3, 4, 2, 3, 1, 3]
def baseStart_1973823 : Nat := 118140960795 + 1973823 * 2 ^ 59
def prefixEnd_1973823 : Nat := 4983230072969 + 3 ^ 40 * 1973823 * 2
def baseEnd_1973823 : Nat := 675679950599690761423373

theorem tailTrace_1973823 : CollatzResearch.WordTrace tailWord_1973823 prefixEnd_1973823 675679950599690761423373 := by
  unfold tailWord_1973823
  simp only [CollatzResearch.WordTrace]
  refine ⟨71991239128183847975438123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47994159418789231983625415 71991239128183847975438123)
  ·
    refine ⟨107986858692275771963157185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71991239128183847975438123 107986858692275771963157185)
    ·
      refine ⟨80990144019206828972367889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107986858692275771963157185 80990144019206828972367889)
      ·
        refine ⟨60742608014405121729275917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80990144019206828972367889 60742608014405121729275917)
        ·
          refine ⟨22778478005401920648478469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60742608014405121729275917 22778478005401920648478469)
          ·
            refine ⟨4270964626012860121589713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22778478005401920648478469 4270964626012860121589713)
            ·
              refine ⟨3203223469509645091192285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270964626012860121589713 3203223469509645091192285)
              ·
                refine ⟨1201208801066116909197107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3203223469509645091192285 1201208801066116909197107)
                ·
                  refine ⟨1801813201599175363795661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201208801066116909197107 1801813201599175363795661)
                  ·
                    refine ⟨675679950599690761423373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801813201599175363795661 675679950599690761423373)
                    ·
                      rfl

theorem cell22_1973823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 3].length) (baseStart_1973823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973823 prefixEnd_1973823 := by exact prefixLift 1973823
  have htrace : WordTrace (prefixWord ++ tailWord_1973823) baseStart_1973823 baseEnd_1973823 := by
    simpa [prefixWord, tailWord_1973823, baseEnd_1973823] using wordTrace_append hprefix tailTrace_1973823
  have hstable : (prefixWord ++ tailWord_1973823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973823).length < 2 ^ (prefixWord ++ tailWord_1973823).sum := by decide
  have hdescent : baseEnd_1973823 < baseStart_1973823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973836 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 5]
def baseStart_1973836 : Nat := 118140960795 + 1973836 * 2 ^ 59
def prefixEnd_1973836 : Nat := 4983230072969 + 3 ^ 40 * 1973836 * 2
def baseEnd_1973836 : Nat := 225228133588454353616111

theorem tailTrace_1973836 : CollatzResearch.WordTrace tailWord_1973836 prefixEnd_1973836 225228133588454353616111 := by
  unfold tailWord_1973836
  simp only [CollatzResearch.WordTrace]
  refine ⟨35995856638568375597830681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47994475518091167463774241 35995856638568375597830681)
  ·
    refine ⟨26996892478926281698373011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35995856638568375597830681 26996892478926281698373011)
    ·
      refine ⟨40495338718389422547559517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26996892478926281698373011 40495338718389422547559517)
      ·
        refine ⟨15185752019396033455334819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40495338718389422547559517 15185752019396033455334819)
        ·
          refine ⟨22778628029094050183002229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15185752019396033455334819 22778628029094050183002229)
          ·
            refine ⟨2135496377727567204656459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22778628029094050183002229 2135496377727567204656459)
            ·
              refine ⟨3203244566591350806984689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135496377727567204656459 3203244566591350806984689)
              ·
                refine ⟨2402433424943513105238517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203244566591350806984689 2402433424943513105238517)
                ·
                  refine ⟨225228133588454353616111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2402433424943513105238517 225228133588454353616111)
                  ·
                    rfl

theorem cell22_1973836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_1973836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973836 prefixEnd_1973836 := by exact prefixLift 1973836
  have htrace : WordTrace (prefixWord ++ tailWord_1973836) baseStart_1973836 baseEnd_1973836 := by
    simpa [prefixWord, tailWord_1973836, baseEnd_1973836] using wordTrace_append hprefix tailTrace_1973836
  have hstable : (prefixWord ++ tailWord_1973836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973836).length < 2 ^ (prefixWord ++ tailWord_1973836).sum := by decide
  have hdescent : baseEnd_1973836 < baseStart_1973836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973866 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1973866 : Nat := 118140960795 + 1973866 * 2 ^ 59
def prefixEnd_1973866 : Nat := 4983230072969 + 3 ^ 40 * 1973866 * 2
def baseEnd_1973866 : Nat := 675694670378452982598241

theorem tailTrace_1973866 : CollatzResearch.WordTrace tailWord_1973866 prefixEnd_1973866 675694670378452982598241 := by
  unfold tailWord_1973866
  simp only [CollatzResearch.WordTrace]
  refine ⟨17998201866757016579813363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47995204978018710879502301 17998201866757016579813363)
  ·
    refine ⟨26997302800135524869720045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17998201866757016579813363 26997302800135524869720045)
    ·
      refine ⟨10123988550050821826145017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26997302800135524869720045 10123988550050821826145017)
      ·
        refine ⟨7592991412538116369608763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10123988550050821826145017 7592991412538116369608763)
        ·
          refine ⟨11389487118807174554413145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592991412538116369608763 11389487118807174554413145)
          ·
            refine ⟨8542115339105380915809859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11389487118807174554413145 8542115339105380915809859)
            ·
              refine ⟨12813173008658071373714789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8542115339105380915809859 12813173008658071373714789)
              ·
                refine ⟨2402469939123388382571523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12813173008658071373714789 2402469939123388382571523)
                ·
                  refine ⟨3603704908685082573857285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402469939123388382571523 3603704908685082573857285)
                  ·
                    refine ⟨675694670378452982598241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3603704908685082573857285 675694670378452982598241)
                    ·
                      rfl

theorem cell22_1973866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1973866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973866 prefixEnd_1973866 := by exact prefixLift 1973866
  have htrace : WordTrace (prefixWord ++ tailWord_1973866) baseStart_1973866 baseEnd_1973866 := by
    simpa [prefixWord, tailWord_1973866, baseEnd_1973866] using wordTrace_append hprefix tailTrace_1973866
  have hstable : (prefixWord ++ tailWord_1973866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973866).length < 2 ^ (prefixWord ++ tailWord_1973866).sum := by decide
  have hdescent : baseEnd_1973866 < baseStart_1973866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973969 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_1973969 : Nat := 118140960795 + 1973969 * 2 ^ 59
def prefixEnd_1973969 : Nat := 4983230072969 + 3 ^ 40 * 1973969 * 2
def baseEnd_1973969 : Nat := 675729929383395047272925

theorem tailTrace_1973969 : CollatzResearch.WordTrace tailWord_1973969 prefixEnd_1973969 675729929383395047272925 := by
  unfold tailWord_1973969
  simp only [CollatzResearch.WordTrace]
  refine ⟨71996564185654914910252961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47997709457103276606835307 71996564185654914910252961)
  ·
    refine ⟨53997423139241186182689721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71996564185654914910252961 53997423139241186182689721)
    ·
      refine ⟨40498067354430889637017291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53997423139241186182689721 40498067354430889637017291)
      ·
        refine ⟨60747101031646334455525937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40498067354430889637017291 60747101031646334455525937)
        ·
          refine ⟨45560325773734750841644453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60747101031646334455525937 45560325773734750841644453)
          ·
            refine ⟨8542561082575265782808335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45560325773734750841644453 8542561082575265782808335)
            ·
              refine ⟨12813841623862898674212503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8542561082575265782808335 12813841623862898674212503)
              ·
                refine ⟨19220762435794348011318755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12813841623862898674212503 19220762435794348011318755)
                ·
                  refine ⟨28831143653691522016978133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19220762435794348011318755 28831143653691522016978133)
                  ·
                    refine ⟨675729929383395047272925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28831143653691522016978133 675729929383395047272925)
                    ·
                      rfl

theorem cell22_1973969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_1973969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973969 prefixEnd_1973969 := by exact prefixLift 1973969
  have htrace : WordTrace (prefixWord ++ tailWord_1973969) baseStart_1973969 baseEnd_1973969 := by
    simpa [prefixWord, tailWord_1973969, baseEnd_1973969] using wordTrace_append hprefix tailTrace_1973969
  have hstable : (prefixWord ++ tailWord_1973969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973969).length < 2 ^ (prefixWord ++ tailWord_1973969).sum := by decide
  have hdescent : baseEnd_1973969 < baseStart_1973969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973999 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 8]
def baseStart_1973999 : Nat := 118140960795 + 1973999 * 2 ^ 59
def prefixEnd_1973999 : Nat := 4983230072969 + 3 ^ 40 * 1973999 * 2
def baseEnd_1973999 : Nat := 225246732998828323007611

theorem tailTrace_1973999 : CollatzResearch.WordTrace tailWord_1973999 prefixEnd_1973999 225246732998828323007611 := by
  unfold tailWord_1973999
  simp only [CollatzResearch.WordTrace]
  refine ⟨71997658375546230033845051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47998438917030820022563367 71997658375546230033845051)
  ·
    refine ⟨107996487563319345050767577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71997658375546230033845051 107996487563319345050767577)
    ·
      refine ⟨80997365672489508788075683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107996487563319345050767577 80997365672489508788075683)
      ·
        refine ⟨121496048508734263182113525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80997365672489508788075683 121496048508734263182113525)
        ·
          refine ⟨11390254547693837173323143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121496048508734263182113525 11390254547693837173323143)
          ·
            refine ⟨17085381821540755759984715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11390254547693837173323143 17085381821540755759984715)
            ·
              refine ⟨25628072732311133639977073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17085381821540755759984715 25628072732311133639977073)
              ·
                refine ⟨19221054549233350229982805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25628072732311133639977073 19221054549233350229982805)
                ·
                  refine ⟨225246732998828323007611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19221054549233350229982805 225246732998828323007611)
                  ·
                    rfl

theorem cell22_1973999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 8].length) (baseStart_1973999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1973999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1973999 prefixEnd_1973999 := by exact prefixLift 1973999
  have htrace : WordTrace (prefixWord ++ tailWord_1973999) baseStart_1973999 baseEnd_1973999 := by
    simpa [prefixWord, tailWord_1973999, baseEnd_1973999] using wordTrace_append hprefix tailTrace_1973999
  have hstable : (prefixWord ++ tailWord_1973999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973999).length < 2 ^ (prefixWord ++ tailWord_1973999).sum := by decide
  have hdescent : baseEnd_1973999 < baseStart_1973999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974059 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 4, 7]
def baseStart_1974059 : Nat := 118140960795 + 1974059 * 2 ^ 59
def prefixEnd_1974059 : Nat := 4983230072969 + 3 ^ 40 * 1974059 * 2
def baseEnd_1974059 : Nat := 675760738222664812522649

theorem tailTrace_1974059 : CollatzResearch.WordTrace tailWord_1974059 prefixEnd_1974059 675760738222664812522649 := by
  unfold tailWord_1974059
  simp only [CollatzResearch.WordTrace]
  refine ⟨71999846755328860281029231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47999897836885906854019487 71999846755328860281029231)
  ·
    refine ⟨107999770132993290421543847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71999846755328860281029231 107999770132993290421543847)
    ·
      refine ⟨161999655199489935632315771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107999770132993290421543847 161999655199489935632315771)
      ·
        refine ⟨242999482799234903448473657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161999655199489935632315771 242999482799234903448473657)
        ·
          refine ⟨182249612099426177586355243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242999482799234903448473657 182249612099426177586355243)
          ·
            refine ⟨273374418149139266379532865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182249612099426177586355243 273374418149139266379532865)
            ·
              refine ⟨205030813611854449784649649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273374418149139266379532865 205030813611854449784649649)
              ·
                refine ⟨153773110208890837338487237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205030813611854449784649649 153773110208890837338487237)
                ·
                  refine ⟨28832458164167032000966357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153773110208890837338487237 28832458164167032000966357)
                  ·
                    refine ⟨675760738222664812522649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28832458164167032000966357 675760738222664812522649)
                    ·
                      rfl

theorem cell22_1974059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_1974059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974059 prefixEnd_1974059 := by exact prefixLift 1974059
  have htrace : WordTrace (prefixWord ++ tailWord_1974059) baseStart_1974059 baseEnd_1974059 := by
    simpa [prefixWord, tailWord_1974059, baseEnd_1974059] using wordTrace_append hprefix tailTrace_1974059
  have hstable : (prefixWord ++ tailWord_1974059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974059).length < 2 ^ (prefixWord ++ tailWord_1974059).sum := by decide
  have hdescent : baseEnd_1974059 < baseStart_1974059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974078 : List Nat := [4, 2, 1, 2, 2, 2, 2, 7]
def baseStart_1974078 : Nat := 118140960795 + 1974078 * 2 ^ 59
def prefixEnd_1974078 : Nat := 4983230072969 + 3 ^ 40 * 1974078 * 2
def baseEnd_1974078 : Nat := 75085249145661677366399

theorem tailTrace_1974078 : CollatzResearch.WordTrace tailWord_1974078 prefixEnd_1974078 75085249145661677366399 := by
  unfold tailWord_1974078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000067467782503315746361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48000359828173351017313925 9000067467782503315746361)
  ·
    refine ⟨6750050600836877486809771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9000067467782503315746361 6750050600836877486809771)
    ·
      refine ⟨10125075901255316230214657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6750050600836877486809771 10125075901255316230214657)
      ·
        refine ⟨7593806925941487172660993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10125075901255316230214657 7593806925941487172660993)
        ·
          refine ⟨5695355194456115379495745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7593806925941487172660993 5695355194456115379495745)
          ·
            refine ⟨4271516395842086534621809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5695355194456115379495745 4271516395842086534621809)
            ·
              refine ⟨3203637296881564900966357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271516395842086534621809 3203637296881564900966357)
              ·
                refine ⟨75085249145661677366399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3203637296881564900966357 75085249145661677366399)
                ·
                  rfl

theorem cell22_1974078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_1974078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974078 prefixEnd_1974078 := by exact prefixLift 1974078
  have htrace : WordTrace (prefixWord ++ tailWord_1974078) baseStart_1974078 baseEnd_1974078 := by
    simpa [prefixWord, tailWord_1974078, baseEnd_1974078] using wordTrace_append hprefix tailTrace_1974078
  have hstable : (prefixWord ++ tailWord_1974078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974078).length < 2 ^ (prefixWord ++ tailWord_1974078).sum := by decide
  have hdescent : baseEnd_1974078 < baseStart_1974078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974153 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_1974153 : Nat := 118140960795 + 1974153 * 2 ^ 59
def prefixEnd_1974153 : Nat := 4983230072969 + 3 ^ 40 * 1974153 * 2
def baseEnd_1974153 : Nat := 675792916343679900672361

theorem tailTrace_1974153 : CollatzResearch.WordTrace tailWord_1974153 prefixEnd_1974153 675792916343679900672361 := by
  unfold tailWord_1974153
  simp only [CollatzResearch.WordTrace]
  refine ⟨72003275216988314334951113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48002183477992209556634075 72003275216988314334951113)
  ·
    refine ⟨54002456412741235751213335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72003275216988314334951113 54002456412741235751213335)
    ·
      refine ⟨81003684619111853626820003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54002456412741235751213335 81003684619111853626820003)
      ·
        refine ⟨121505526928667780440230005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81003684619111853626820003 121505526928667780440230005)
        ·
          refine ⟨11391143149562604416271563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121505526928667780440230005 11391143149562604416271563)
          ·
            refine ⟨17086714724343906624407345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11391143149562604416271563 17086714724343906624407345)
            ·
              refine ⟨12815036043257929968305509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17086714724343906624407345 12815036043257929968305509)
              ·
                refine ⟨2402819258110861869057283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12815036043257929968305509 2402819258110861869057283)
                ·
                  refine ⟨3604228887166292803585925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402819258110861869057283 3604228887166292803585925)
                  ·
                    refine ⟨675792916343679900672361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3604228887166292803585925 675792916343679900672361)
                    ·
                      rfl

theorem cell22_1974153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_1974153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974153 prefixEnd_1974153 := by exact prefixLift 1974153
  have htrace : WordTrace (prefixWord ++ tailWord_1974153) baseStart_1974153 baseEnd_1974153 := by
    simpa [prefixWord, tailWord_1974153, baseEnd_1974153] using wordTrace_append hprefix tailTrace_1974153
  have hstable : (prefixWord ++ tailWord_1974153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974153).length < 2 ^ (prefixWord ++ tailWord_1974153).sum := by decide
  have hdescent : baseEnd_1974153 < baseStart_1974153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974170 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_1974170 : Nat := 118140960795 + 1974170 * 2 ^ 59
def prefixEnd_1974170 : Nat := 4983230072969 + 3 ^ 40 * 1974170 * 2
def baseEnd_1974170 : Nat := 675798735791097522997309

theorem tailTrace_1974170 : CollatzResearch.WordTrace tailWord_1974170 prefixEnd_1974170 675798735791097522997309 := by
  unfold tailWord_1974170
  simp only [CollatzResearch.WordTrace]
  refine ⟨18000973814481681559579991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48002596838617817492213309 18000973814481681559579991)
  ·
    refine ⟨27001460721722522339369987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18000973814481681559579991 27001460721722522339369987)
    ·
      refine ⟨40502191082583783509054981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27001460721722522339369987 40502191082583783509054981)
      ·
        refine ⟨7594160827984459407947809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40502191082583783509054981 7594160827984459407947809)
        ·
          refine ⟨5695620620988344555960857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7594160827984459407947809 5695620620988344555960857)
          ·
            refine ⟨4271715465741258416970643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5695620620988344555960857 4271715465741258416970643)
            ·
              refine ⟨6407573198611887625455965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271715465741258416970643 6407573198611887625455965)
              ·
                refine ⟨2402839949479457859545987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6407573198611887625455965 2402839949479457859545987)
                ·
                  refine ⟨3604259924219186789318981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402839949479457859545987 3604259924219186789318981)
                  ·
                    refine ⟨675798735791097522997309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3604259924219186789318981 675798735791097522997309)
                    ·
                      rfl

theorem cell22_1974170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_1974170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974170 prefixEnd_1974170 := by exact prefixLift 1974170
  have htrace : WordTrace (prefixWord ++ tailWord_1974170) baseStart_1974170 baseEnd_1974170 := by
    simpa [prefixWord, tailWord_1974170, baseEnd_1974170] using wordTrace_append hprefix tailTrace_1974170
  have hstable : (prefixWord ++ tailWord_1974170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974170).length < 2 ^ (prefixWord ++ tailWord_1974170).sum := by decide
  have hdescent : baseEnd_1974170 < baseStart_1974170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974174 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1974174 : Nat := 118140960795 + 1974174 * 2 ^ 59
def prefixEnd_1974174 : Nat := 4983230072969 + 3 ^ 40 * 1974174 * 2
def baseEnd_1974174 : Nat := 225266701690947615299099

theorem tailTrace_1974174 : CollatzResearch.WordTrace tailWord_1974174 prefixEnd_1974174 225266701690947615299099 := by
  unfold tailWord_1974174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000505143739029365183197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48002694099941489947643717 9000505143739029365183197)
  ·
    refine ⟨3375189428902136011943699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9000505143739029365183197 3375189428902136011943699)
    ·
      refine ⟨5062784143353204017915549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375189428902136011943699 5062784143353204017915549)
      ·
        refine ⟨1898544053757451506718331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5062784143353204017915549 1898544053757451506718331)
        ·
          refine ⟨2847816080636177260077497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898544053757451506718331 2847816080636177260077497)
          ·
            refine ⟨2135862060477132945058123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2847816080636177260077497 2135862060477132945058123)
            ·
              refine ⟨3203793090715699417587185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135862060477132945058123 3203793090715699417587185)
              ·
                refine ⟨2402844818036774563190389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203793090715699417587185 2402844818036774563190389)
                ·
                  refine ⟨225266701690947615299099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2402844818036774563190389 225266701690947615299099)
                  ·
                    rfl

theorem cell22_1974174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1974174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974174 prefixEnd_1974174 := by exact prefixLift 1974174
  have htrace : WordTrace (prefixWord ++ tailWord_1974174) baseStart_1974174 baseEnd_1974174 := by
    simpa [prefixWord, tailWord_1974174, baseEnd_1974174] using wordTrace_append hprefix tailTrace_1974174
  have hstable : (prefixWord ++ tailWord_1974174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974174).length < 2 ^ (prefixWord ++ tailWord_1974174).sum := by decide
  have hdescent : baseEnd_1974174 < baseStart_1974174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974236 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 6]
def baseStart_1974236 : Nat := 118140960795 + 1974236 * 2 ^ 59
def prefixEnd_1974236 : Nat := 4983230072969 + 3 ^ 40 * 1974236 * 2
def baseEnd_1974236 : Nat := 225273776313298450282369

theorem tailTrace_1974236 : CollatzResearch.WordTrace tailWord_1974236 prefixEnd_1974236 225273776313298450282369 := by
  unfold tailWord_1974236
  simp only [CollatzResearch.WordTrace]
  refine ⟨36003151237843809755111281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48004201650458413006815041 36003151237843809755111281)
  ·
    refine ⟨27002363428382857316333461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36003151237843809755111281 27002363428382857316333461)
    ·
      refine ⟨1265735785705446436703131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27002363428382857316333461 1265735785705446436703131)
      ·
        refine ⟨1898603678558169655054697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265735785705446436703131 1898603678558169655054697)
        ·
          refine ⟨1423952758918627241291023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898603678558169655054697 1423952758918627241291023)
          ·
            refine ⟨2135929138377940861936535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423952758918627241291023 2135929138377940861936535)
            ·
              refine ⟨3203893707566911292904803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135929138377940861936535 3203893707566911292904803)
              ·
                refine ⟨4805840561350366939357205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203893707566911292904803 4805840561350366939357205)
                ·
                  refine ⟨225273776313298450282369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4805840561350366939357205 225273776313298450282369)
                  ·
                    rfl

theorem cell22_1974236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_1974236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974236 prefixEnd_1974236 := by exact prefixLift 1974236
  have htrace : WordTrace (prefixWord ++ tailWord_1974236) baseStart_1974236 baseEnd_1974236 := by
    simpa [prefixWord, tailWord_1974236, baseEnd_1974236] using wordTrace_append hprefix tailTrace_1974236
  have hstable : (prefixWord ++ tailWord_1974236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974236).length < 2 ^ (prefixWord ++ tailWord_1974236).sum := by decide
  have hdescent : baseEnd_1974236 < baseStart_1974236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974303 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 6]
def baseStart_1974303 : Nat := 118140960795 + 1974303 * 2 ^ 59
def prefixEnd_1974303 : Nat := 4983230072969 + 3 ^ 40 * 1974303 * 2
def baseEnd_1974303 : Nat := 225281421469709836473967

theorem tailTrace_1974303 : CollatzResearch.WordTrace tailWord_1974303 prefixEnd_1974303 225281421469709836473967 := by
  unfold tailWord_1974303
  simp only [CollatzResearch.WordTrace]
  refine ⟨72008746166444889952911563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48005830777629926635274375 72008746166444889952911563)
  ·
    refine ⟨108013119249667334929367345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72008746166444889952911563 108013119249667334929367345)
    ·
      refine ⟨81009839437250501197025509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108013119249667334929367345 81009839437250501197025509)
      ·
        refine ⟨15189344894484468974442283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81009839437250501197025509 15189344894484468974442283)
        ·
          refine ⟨22784017341726703461663425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15189344894484468974442283 22784017341726703461663425)
          ·
            refine ⟨17088013006295027596247569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22784017341726703461663425 17088013006295027596247569)
            ·
              refine ⟨12816009754721270697185677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17088013006295027596247569 12816009754721270697185677)
              ·
                refine ⟨4806003658020476511444629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12816009754721270697185677 4806003658020476511444629)
                ·
                  refine ⟨225281421469709836473967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4806003658020476511444629 225281421469709836473967)
                  ·
                    rfl

theorem cell22_1974303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 6].length) (baseStart_1974303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974303 prefixEnd_1974303 := by exact prefixLift 1974303
  have htrace : WordTrace (prefixWord ++ tailWord_1974303) baseStart_1974303 baseEnd_1974303 := by
    simpa [prefixWord, tailWord_1974303, baseEnd_1974303] using wordTrace_append hprefix tailTrace_1974303
  have hstable : (prefixWord ++ tailWord_1974303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974303).length < 2 ^ (prefixWord ++ tailWord_1974303).sum := by decide
  have hdescent : baseEnd_1974303 < baseStart_1974303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974337 : List Nat := [1, 2, 5, 1, 2, 1, 1, 5, 4]
def baseStart_1974337 : Nat := 118140960795 + 1974337 * 2 ^ 59
def prefixEnd_1974337 : Nat := 4983230072969 + 3 ^ 40 * 1974337 * 2
def baseEnd_1974337 : Nat := 225285301101321584690599

theorem tailTrace_1974337 : CollatzResearch.WordTrace tailWord_1974337 prefixEnd_1974337 225285301101321584690599 := by
  unfold tailWord_1974337
  simp only [CollatzResearch.WordTrace]
  refine ⟨72009986248321713759649265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48006657498881142506432843 72009986248321713759649265)
  ·
    refine ⟨54007489686241285319736949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72009986248321713759649265 54007489686241285319736949)
    ·
      refine ⟨5063202158085120498725339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54007489686241285319736949 5063202158085120498725339)
      ·
        refine ⟨7594803237127680748088009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063202158085120498725339 7594803237127680748088009)
        ·
          refine ⟨5696102427845760561066007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7594803237127680748088009 5696102427845760561066007)
          ·
            refine ⟨8544153641768640841599011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696102427845760561066007 8544153641768640841599011)
            ·
              refine ⟨12816230462652961262398517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8544153641768640841599011 12816230462652961262398517)
              ·
                refine ⟨1201521605873715118349861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12816230462652961262398517 1201521605873715118349861)
                ·
                  refine ⟨225285301101321584690599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1201521605873715118349861 225285301101321584690599)
                  ·
                    rfl

theorem cell22_1974337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 4].length) (baseStart_1974337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974337 prefixEnd_1974337 := by exact prefixLift 1974337
  have htrace : WordTrace (prefixWord ++ tailWord_1974337) baseStart_1974337 baseEnd_1974337 := by
    simpa [prefixWord, tailWord_1974337, baseEnd_1974337] using wordTrace_append hprefix tailTrace_1974337
  have hstable : (prefixWord ++ tailWord_1974337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974337).length < 2 ^ (prefixWord ++ tailWord_1974337).sum := by decide
  have hdescent : baseEnd_1974337 < baseStart_1974337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974410 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 7]
def baseStart_1974410 : Nat := 118140960795 + 1974410 * 2 ^ 59
def prefixEnd_1974410 : Nat := 4983230072969 + 3 ^ 40 * 1974410 * 2
def baseEnd_1974410 : Nat := 225293630898605632332191

theorem tailTrace_1974410 : CollatzResearch.WordTrace tailWord_1974410 prefixEnd_1974410 225293630898605632332191 := by
  unfold tailWord_1974410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18003162194264311806764171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48008432518038164818037789 18003162194264311806764171)
  ·
    refine ⟨27004743291396467710146257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18003162194264311806764171 27004743291396467710146257)
    ·
      refine ⟨20253557468547350782609693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27004743291396467710146257 20253557468547350782609693)
      ·
        refine ⟨7595084050705256543478635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20253557468547350782609693 7595084050705256543478635)
        ·
          refine ⟨11392626076057884815217953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595084050705256543478635 11392626076057884815217953)
          ·
            refine ⟨8544469557043413611413465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11392626076057884815217953 8544469557043413611413465)
            ·
              refine ⟨6408352167782560208560099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8544469557043413611413465 6408352167782560208560099)
              ·
                refine ⟨9612528251673840312840149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408352167782560208560099 9612528251673840312840149)
                ·
                  refine ⟨225293630898605632332191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9612528251673840312840149 225293630898605632332191)
                  ·
                    rfl

theorem cell22_1974410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_1974410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974410 prefixEnd_1974410 := by exact prefixLift 1974410
  have htrace : WordTrace (prefixWord ++ tailWord_1974410) baseStart_1974410 baseEnd_1974410 := by
    simpa [prefixWord, tailWord_1974410, baseEnd_1974410] using wordTrace_append hprefix tailTrace_1974410
  have hstable : (prefixWord ++ tailWord_1974410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974410).length < 2 ^ (prefixWord ++ tailWord_1974410).sum := by decide
  have hdescent : baseEnd_1974410 < baseStart_1974410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974420 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1974420 : Nat := 118140960795 + 1974420 * 2 ^ 59
def prefixEnd_1974420 : Nat := 4983230072969 + 3 ^ 40 * 1974420 * 2
def baseEnd_1974420 : Nat := 675884315900180204246543

theorem tailTrace_1974420 : CollatzResearch.WordTrace tailWord_1974420 prefixEnd_1974420 675884315900180204246543 := by
  unfold tailWord_1974420
  simp only [CollatzResearch.WordTrace]
  refine ⟨36006506753510509467460357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48008675671347345956613809 36006506753510509467460357)
  ·
    refine ⟨6751220016283220525148817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36006506753510509467460357 6751220016283220525148817)
    ·
      refine ⟨5063415012212415393861613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6751220016283220525148817 5063415012212415393861613)
      ·
        refine ⟨1898780629579655772698105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5063415012212415393861613 1898780629579655772698105)
        ·
          refine ⟨1424085472184741829523579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898780629579655772698105 1424085472184741829523579)
          ·
            refine ⟨2136128208277112744285369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424085472184741829523579 2136128208277112744285369)
            ·
              refine ⟨1602096156207834558214027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136128208277112744285369 1602096156207834558214027)
              ·
                refine ⟨2403144234311751837321041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602096156207834558214027 2403144234311751837321041)
                ·
                  refine ⟨1802358175733813877990781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2403144234311751837321041 1802358175733813877990781)
                  ·
                    refine ⟨675884315900180204246543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1802358175733813877990781 675884315900180204246543)
                    ·
                      rfl

theorem cell22_1974420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1974420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974420 prefixEnd_1974420 := by exact prefixLift 1974420
  have htrace : WordTrace (prefixWord ++ tailWord_1974420) baseStart_1974420 baseEnd_1974420 := by
    simpa [prefixWord, tailWord_1974420, baseEnd_1974420] using wordTrace_append hprefix tailTrace_1974420
  have hstable : (prefixWord ++ tailWord_1974420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974420).length < 2 ^ (prefixWord ++ tailWord_1974420).sum := by decide
  have hdescent : baseEnd_1974420 < baseStart_1974420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974465 : List Nat := [1, 2, 6, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1974465 : Nat := 118140960795 + 1974465 * 2 ^ 59
def prefixEnd_1974465 : Nat := 4983230072969 + 3 ^ 40 * 1974465 * 2
def baseEnd_1974465 : Nat := 675899720319815086871405

theorem tailTrace_1974465 : CollatzResearch.WordTrace tailWord_1974465 prefixEnd_1974465 675899720319815086871405 := by
  unfold tailWord_1974465
  simp only [CollatzResearch.WordTrace]
  refine ⟨72014654791857991620308849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48009769861238661080205899 72014654791857991620308849)
  ·
    refine ⟨54010991093893493715231637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72014654791857991620308849 54010991093893493715231637)
    ·
      refine ⟨2531765207526257517901483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54010991093893493715231637 2531765207526257517901483)
      ·
        refine ⟨3797647811289386276852225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531765207526257517901483 3797647811289386276852225)
        ·
          refine ⟨2848235858467039707639169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797647811289386276852225 2848235858467039707639169)
          ·
            refine ⟨2136176893850279780729377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2848235858467039707639169 2136176893850279780729377)
            ·
              refine ⟨1602132670387709835547033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136176893850279780729377 1602132670387709835547033)
              ·
                refine ⟨1201599502790782376660275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602132670387709835547033 1201599502790782376660275)
                ·
                  refine ⟨1802399254186173564990413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201599502790782376660275 1802399254186173564990413)
                  ·
                    refine ⟨675899720319815086871405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1802399254186173564990413 675899720319815086871405)
                    ·
                      rfl

theorem cell22_1974465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1974465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974465 prefixEnd_1974465 := by exact prefixLift 1974465
  have htrace : WordTrace (prefixWord ++ tailWord_1974465) baseStart_1974465 baseEnd_1974465 := by
    simpa [prefixWord, tailWord_1974465, baseEnd_1974465] using wordTrace_append hprefix tailTrace_1974465
  have hstable : (prefixWord ++ tailWord_1974465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974465).length < 2 ^ (prefixWord ++ tailWord_1974465).sum := by decide
  have hdescent : baseEnd_1974465 < baseStart_1974465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974562 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1974562 : Nat := 118140960795 + 1974562 * 2 ^ 59
def prefixEnd_1974562 : Nat := 4983230072969 + 3 ^ 40 * 1974562 * 2
def baseEnd_1974562 : Nat := 225310975134046389065369

theorem tailTrace_1974562 : CollatzResearch.WordTrace tailWord_1974562 prefixEnd_1974562 225310975134046389065369 := by
  unfold tailWord_1974562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18004548168126644296647485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48012128448337718124393293 18004548168126644296647485)
  ·
    refine ⟨6751705563047491611242807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18004548168126644296647485 6751705563047491611242807)
    ·
      refine ⟨10127558344571237416864211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6751705563047491611242807 10127558344571237416864211)
      ·
        refine ⟨15191337516856856125296317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10127558344571237416864211 15191337516856856125296317)
        ·
          refine ⟨5696751568821321046986119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15191337516856856125296317 5696751568821321046986119)
          ·
            refine ⟨8545127353231981570479179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696751568821321046986119 8545127353231981570479179)
            ·
              refine ⟨12817691029847972355718769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8545127353231981570479179 12817691029847972355718769)
              ·
                refine ⟨9613268272385979266789077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12817691029847972355718769 9613268272385979266789077)
                ·
                  refine ⟨225310975134046389065369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9613268272385979266789077 225310975134046389065369)
                  ·
                    rfl

theorem cell22_1974562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1974562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974562 prefixEnd_1974562 := by exact prefixLift 1974562
  have htrace : WordTrace (prefixWord ++ tailWord_1974562) baseStart_1974562 baseEnd_1974562 := by
    simpa [prefixWord, tailWord_1974562, baseEnd_1974562] using wordTrace_append hprefix tailTrace_1974562
  have hstable : (prefixWord ++ tailWord_1974562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974562).length < 2 ^ (prefixWord ++ tailWord_1974562).sum := by decide
  have hdescent : baseEnd_1974562 < baseStart_1974562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974596 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1974596 : Nat := 118140960795 + 1974596 * 2 ^ 59
def prefixEnd_1974596 : Nat := 4983230072969 + 3 ^ 40 * 1974596 * 2
def baseEnd_1974596 : Nat := 225314854765658137282001

theorem tailTrace_1974596 : CollatzResearch.WordTrace tailWord_1974596 prefixEnd_1974596 225314854765658137282001 := by
  unfold tailWord_1974596
  simp only [CollatzResearch.WordTrace]
  refine ⟨36009716377191700496663821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48012955169588933995551761 36009716377191700496663821)
  ·
    refine ⟨13503643641446887686248933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36009716377191700496663821 13503643641446887686248933)
    ·
      refine ⟨2531933182771291441171675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13503643641446887686248933 2531933182771291441171675)
      ·
        refine ⟨3797899774156937161757513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531933182771291441171675 3797899774156937161757513)
        ·
          refine ⟨2848424830617702871318135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797899774156937161757513 2848424830617702871318135)
          ·
            refine ⟨4272637245926554306977203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848424830617702871318135 4272637245926554306977203)
            ·
              refine ⟨6408955868889831460465805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272637245926554306977203 6408955868889831460465805)
              ·
                refine ⟨2403358450833686797674677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6408955868889831460465805 2403358450833686797674677)
                ·
                  refine ⟨225314854765658137282001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2403358450833686797674677 225314854765658137282001)
                  ·
                    rfl

theorem cell22_1974596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1974596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974596 prefixEnd_1974596 := by exact prefixLift 1974596
  have htrace : WordTrace (prefixWord ++ tailWord_1974596) baseStart_1974596 baseEnd_1974596 := by
    simpa [prefixWord, tailWord_1974596, baseEnd_1974596] using wordTrace_append hprefix tailTrace_1974596
  have hstable : (prefixWord ++ tailWord_1974596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974596).length < 2 ^ (prefixWord ++ tailWord_1974596).sum := by decide
  have hdescent : baseEnd_1974596 < baseStart_1974596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974609 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_1974609 : Nat := 118140960795 + 1974609 * 2 ^ 59
def prefixEnd_1974609 : Nat := 4983230072969 + 3 ^ 40 * 1974609 * 2
def baseEnd_1974609 : Nat := 675949014462646711270963

theorem tailTrace_1974609 : CollatzResearch.WordTrace tailWord_1974609 prefixEnd_1974609 675949014462646711270963 := by
  unfold tailWord_1974609
  simp only [CollatzResearch.WordTrace]
  refine ⟨72019906903336304213550881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48013271268890869475700587 72019906903336304213550881)
  ·
    refine ⟨54014930177502228160163161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72019906903336304213550881 54014930177502228160163161)
    ·
      refine ⟨40511197633126671120122371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54014930177502228160163161 40511197633126671120122371)
      ·
        refine ⟨60766796449690006680183557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40511197633126671120122371 60766796449690006680183557)
        ·
          refine ⟨11393774334316876252534417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60766796449690006680183557 11393774334316876252534417)
          ·
            refine ⟨8545330750737657189400813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11393774334316876252534417 8545330750737657189400813)
            ·
              refine ⟨3204499031526621446025305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8545330750737657189400813 3204499031526621446025305)
              ·
                refine ⟨2403374273644966084518979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3204499031526621446025305 2403374273644966084518979)
                ·
                  refine ⟨3605061410467449126778469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403374273644966084518979 3605061410467449126778469)
                  ·
                    refine ⟨675949014462646711270963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3605061410467449126778469 675949014462646711270963)
                    ·
                      rfl

theorem cell22_1974609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_1974609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974609 prefixEnd_1974609 := by exact prefixLift 1974609
  have htrace : WordTrace (prefixWord ++ tailWord_1974609) baseStart_1974609 baseEnd_1974609 := by
    simpa [prefixWord, tailWord_1974609, baseEnd_1974609] using wordTrace_append hprefix tailTrace_1974609
  have hstable : (prefixWord ++ tailWord_1974609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974609).length < 2 ^ (prefixWord ++ tailWord_1974609).sum := by decide
  have hdescent : baseEnd_1974609 < baseStart_1974609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974787 : List Nat := [1, 1, 1, 3, 2, 1, 3, 10]
def baseStart_1974787 : Nat := 118140960795 + 1974787 * 2 ^ 59
def prefixEnd_1974787 : Nat := 4983230072969 + 3 ^ 40 * 1974787 * 2
def baseEnd_1974787 : Nat := 75112216388923731146713

theorem tailTrace_1974787 : CollatzResearch.WordTrace tailWord_1974787 prefixEnd_1974787 75112216388923731146713 := by
  unfold tailWord_1974787
  simp only [CollatzResearch.WordTrace]
  refine ⟨72026399096691440613530615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48017599397794293742353743 72026399096691440613530615)
  ·
    refine ⟨108039598645037160920295923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72026399096691440613530615 108039598645037160920295923)
    ·
      refine ⟨162059397967555741380443885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108039598645037160920295923 162059397967555741380443885)
      ·
        refine ⟨60772274237833403017666457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162059397967555741380443885 60772274237833403017666457)
        ·
          refine ⟨45579205678375052263249843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60772274237833403017666457 45579205678375052263249843)
          ·
            refine ⟨68368808517562578394874765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45579205678375052263249843 68368808517562578394874765)
            ·
              refine ⟨25638303194085966898078037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68368808517562578394874765 25638303194085966898078037)
              ·
                refine ⟨75112216388923731146713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25638303194085966898078037 75112216388923731146713)
                ·
                  rfl

theorem cell22_1974787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 10].length) (baseStart_1974787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974787 prefixEnd_1974787 := by exact prefixLift 1974787
  have htrace : WordTrace (prefixWord ++ tailWord_1974787) baseStart_1974787 baseEnd_1974787 := by
    simpa [prefixWord, tailWord_1974787, baseEnd_1974787] using wordTrace_append hprefix tailTrace_1974787
  have hstable : (prefixWord ++ tailWord_1974787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974787).length < 2 ^ (prefixWord ++ tailWord_1974787).sum := by decide
  have hdescent : baseEnd_1974787 < baseStart_1974787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974789 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_1974789 : Nat := 118140960795 + 1974789 * 2 ^ 59
def prefixEnd_1974789 : Nat := 4983230072969 + 3 ^ 40 * 1974789 * 2
def baseEnd_1974789 : Nat := 676010632141186241770411

theorem tailTrace_1974789 : CollatzResearch.WordTrace tailWord_1974789 prefixEnd_1974789 676010632141186241770411 := by
  unfold tailWord_1974789
  simp only [CollatzResearch.WordTrace]
  refine ⟨72026472042684194955103421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48017648028456129970068947 72026472042684194955103421)
  ·
    refine ⟨27009927016006573108163783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72026472042684194955103421 27009927016006573108163783)
    ·
      refine ⟨40514890524009859662245675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27009927016006573108163783 40514890524009859662245675)
      ·
        refine ⟨60772335786014789493368513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40514890524009859662245675 60772335786014789493368513)
        ·
          refine ⟨45579251839511092120026385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60772335786014789493368513 45579251839511092120026385)
          ·
            refine ⟨34184438879633319090019789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45579251839511092120026385 34184438879633319090019789)
            ·
              refine ⟨12819164579862494658757421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34184438879633319090019789 12819164579862494658757421)
              ·
                refine ⟨4807186717448435497034033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12819164579862494658757421 4807186717448435497034033)
                ·
                  refine ⟨3605390038086326622775525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4807186717448435497034033 3605390038086326622775525)
                  ·
                    refine ⟨676010632141186241770411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3605390038086326622775525 676010632141186241770411)
                    ·
                      rfl

theorem cell22_1974789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_1974789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974789 prefixEnd_1974789 := by exact prefixLift 1974789
  have htrace : WordTrace (prefixWord ++ tailWord_1974789) baseStart_1974789 baseEnd_1974789 := by
    simpa [prefixWord, tailWord_1974789, baseEnd_1974789] using wordTrace_append hprefix tailTrace_1974789
  have hstable : (prefixWord ++ tailWord_1974789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974789).length < 2 ^ (prefixWord ++ tailWord_1974789).sum := by decide
  have hdescent : baseEnd_1974789 < baseStart_1974789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974791 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1974791 : Nat := 118140960795 + 1974791 * 2 ^ 59
def prefixEnd_1974791 : Nat := 4983230072969 + 3 ^ 40 * 1974791 * 2
def baseEnd_1974791 : Nat := 676011316782058903220405

theorem tailTrace_1974791 : CollatzResearch.WordTrace tailWord_1974791 prefixEnd_1974791 676011316782058903220405 := by
  unfold tailWord_1974791
  simp only [CollatzResearch.WordTrace]
  refine ⟨72026544988676949296676227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48017696659117966197784151 72026544988676949296676227)
  ·
    refine ⟨108039817483015423945014341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72026544988676949296676227 108039817483015423945014341)
    ·
      refine ⟨20257465778065391989690189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108039817483015423945014341 20257465778065391989690189)
      ·
        refine ⟨7596549666774521996133821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20257465778065391989690189 7596549666774521996133821)
        ·
          refine ⟨2848706125040445748550183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7596549666774521996133821 2848706125040445748550183)
          ·
            refine ⟨4273059187560668622825275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848706125040445748550183 4273059187560668622825275)
            ·
              refine ⟨6409588781341002934237913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273059187560668622825275 6409588781341002934237913)
              ·
                refine ⟨4807191586005752200678435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6409588781341002934237913 4807191586005752200678435)
                ·
                  refine ⟨7210787379008628301017653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807191586005752200678435 7210787379008628301017653)
                  ·
                    refine ⟨676011316782058903220405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7210787379008628301017653 676011316782058903220405)
                    ·
                      rfl

theorem cell22_1974791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1974791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974791 prefixEnd_1974791 := by exact prefixLift 1974791
  have htrace : WordTrace (prefixWord ++ tailWord_1974791) baseStart_1974791 baseEnd_1974791 := by
    simpa [prefixWord, tailWord_1974791, baseEnd_1974791] using wordTrace_append hprefix tailTrace_1974791
  have hstable : (prefixWord ++ tailWord_1974791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974791).length < 2 ^ (prefixWord ++ tailWord_1974791).sum := by decide
  have hdescent : baseEnd_1974791 < baseStart_1974791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974808 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 2, 3]
def baseStart_1974808 : Nat := 118140960795 + 1974808 * 2 ^ 59
def prefixEnd_1974808 : Nat := 4983230072969 + 3 ^ 40 * 1974808 * 2
def baseEnd_1974808 : Nat := 676017136229476525545353

theorem tailTrace_1974808 : CollatzResearch.WordTrace tailWord_1974808 prefixEnd_1974808 676017136229476525545353 := by
  unfold tailWord_1974808
  simp only [CollatzResearch.WordTrace]
  refine ⟨36013582514807680600022539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48018110019743574133363385 36013582514807680600022539)
  ·
    refine ⟨54020373772211520900033809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36013582514807680600022539 54020373772211520900033809)
    ·
      refine ⟨40515280329158640675025357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54020373772211520900033809 40515280329158640675025357)
      ·
        refine ⟨15193230123434490253134509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40515280329158640675025357 15193230123434490253134509)
        ·
          refine ⟨5697461296287933844925441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15193230123434490253134509 5697461296287933844925441)
          ·
            refine ⟨4273095972215950383694081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5697461296287933844925441 4273095972215950383694081)
            ·
              refine ⟨3204821979161962787770561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4273095972215950383694081 3204821979161962787770561)
              ·
                refine ⟨2403616484371472090827921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3204821979161962787770561 2403616484371472090827921)
                ·
                  refine ⟨1802712363278604068120941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2403616484371472090827921 1802712363278604068120941)
                  ·
                    refine ⟨676017136229476525545353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1802712363278604068120941 676017136229476525545353)
                    ·
                      rfl

theorem cell22_1974808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_1974808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974808 prefixEnd_1974808 := by exact prefixLift 1974808
  have htrace : WordTrace (prefixWord ++ tailWord_1974808) baseStart_1974808 baseEnd_1974808 := by
    simpa [prefixWord, tailWord_1974808, baseEnd_1974808] using wordTrace_append hprefix tailTrace_1974808
  have hstable : (prefixWord ++ tailWord_1974808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974808).length < 2 ^ (prefixWord ++ tailWord_1974808).sum := by decide
  have hdescent : baseEnd_1974808 < baseStart_1974808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974838 : List Nat := [5, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1974838 : Nat := 118140960795 + 1974838 * 2 ^ 59
def prefixEnd_1974838 : Nat := 4983230072969 + 3 ^ 40 * 1974838 * 2
def baseEnd_1974838 : Nat := 75114156204729605255029

theorem tailTrace_1974838 : CollatzResearch.WordTrace tailWord_1974838 prefixEnd_1974838 75114156204729605255029 := by
  unfold tailWord_1974838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501766201219167270227323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48018839479671117549091445 4501766201219167270227323)
  ·
    refine ⟨6752649301828750905340985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4501766201219167270227323 6752649301828750905340985)
    ·
      refine ⟨5064486976371563179005739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6752649301828750905340985 5064486976371563179005739)
      ·
        refine ⟨7596730464557344768508609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064486976371563179005739 7596730464557344768508609)
        ·
          refine ⟨5697547848418008576381457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7596730464557344768508609 5697547848418008576381457)
          ·
            refine ⟨4273160886313506432286093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5697547848418008576381457 4273160886313506432286093)
            ·
              refine ⟨1602435332367564912107285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4273160886313506432286093 1602435332367564912107285)
              ·
                refine ⟨75114156204729605255029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1602435332367564912107285 75114156204729605255029)
                ·
                  rfl

theorem cell22_1974838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1974838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974838 prefixEnd_1974838 := by exact prefixLift 1974838
  have htrace : WordTrace (prefixWord ++ tailWord_1974838) baseStart_1974838 baseEnd_1974838 := by
    simpa [prefixWord, tailWord_1974838, baseEnd_1974838] using wordTrace_append hprefix tailTrace_1974838
  have hstable : (prefixWord ++ tailWord_1974838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974838).length < 2 ^ (prefixWord ++ tailWord_1974838).sum := by decide
  have hdescent : baseEnd_1974838 < baseStart_1974838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974853 : List Nat := [1, 3, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_1974853 : Nat := 118140960795 + 1974853 * 2 ^ 59
def prefixEnd_1974853 : Nat := 4983230072969 + 3 ^ 40 * 1974853 * 2
def baseEnd_1974853 : Nat := 676032540649111408170215

theorem tailTrace_1974853 : CollatzResearch.WordTrace tailWord_1974853 prefixEnd_1974853 676032540649111408170215 := by
  unfold tailWord_1974853
  simp only [CollatzResearch.WordTrace]
  refine ⟨72028806314452333885433213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48019204209634889256955475 72028806314452333885433213)
  ·
    refine ⟨27010802367919625207037455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72028806314452333885433213 27010802367919625207037455)
    ·
      refine ⟨40516203551879437810556183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27010802367919625207037455 40516203551879437810556183)
      ·
        refine ⟨60774305327819156715834275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40516203551879437810556183 60774305327819156715834275)
        ·
          refine ⟨91161457991728735073751413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60774305327819156715834275 91161457991728735073751413)
          ·
            refine ⟨8546386686724568913164195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91161457991728735073751413 8546386686724568913164195)
            ·
              refine ⟨12819580030086853369746293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546386686724568913164195 12819580030086853369746293)
              ·
                refine ⟨1201835627820642503413715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12819580030086853369746293 1201835627820642503413715)
                ·
                  refine ⟨1802753441730963755120573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201835627820642503413715 1802753441730963755120573)
                  ·
                    refine ⟨676032540649111408170215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1802753441730963755120573 676032540649111408170215)
                    ·
                      rfl

theorem cell22_1974853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_1974853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974853 prefixEnd_1974853 := by exact prefixLift 1974853
  have htrace : WordTrace (prefixWord ++ tailWord_1974853) baseStart_1974853 baseEnd_1974853 := by
    simpa [prefixWord, tailWord_1974853, baseEnd_1974853] using wordTrace_append hprefix tailTrace_1974853
  have hstable : (prefixWord ++ tailWord_1974853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974853).length < 2 ^ (prefixWord ++ tailWord_1974853).sum := by decide
  have hdescent : baseEnd_1974853 < baseStart_1974853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974879 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 5, 4]
def baseStart_1974879 : Nat := 118140960795 + 1974879 * 2 ^ 59
def prefixEnd_1974879 : Nat := 4983230072969 + 3 ^ 40 * 1974879 * 2
def baseEnd_1974879 : Nat := 676041440980456007020135

theorem tailTrace_1974879 : CollatzResearch.WordTrace tailWord_1974879 prefixEnd_1974879 676041440980456007020135 := by
  unfold tailWord_1974879
  simp only [CollatzResearch.WordTrace]
  refine ⟨72029754612358140325879691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48019836408238760217253127 72029754612358140325879691)
  ·
    refine ⟨108044631918537210488819537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72029754612358140325879691 108044631918537210488819537)
    ·
      refine ⟨81033473938902907866614653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108044631918537210488819537 81033473938902907866614653)
      ·
        refine ⟨30387552727088590449980495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81033473938902907866614653 30387552727088590449980495)
        ·
          refine ⟨45581329090632885674970743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30387552727088590449980495 45581329090632885674970743)
          ·
            refine ⟨68371993635949328512456115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45581329090632885674970743 68371993635949328512456115)
            ·
              refine ⟨102557990453923992768684173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68371993635949328512456115 102557990453923992768684173)
              ·
                refine ⟨38459246420221497288256565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102557990453923992768684173 38459246420221497288256565)
                ·
                  refine ⟨3605554351895765370774053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38459246420221497288256565 3605554351895765370774053)
                  ·
                    refine ⟨676041440980456007020135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3605554351895765370774053 676041440980456007020135)
                    ·
                      rfl

theorem cell22_1974879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_1974879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974879 prefixEnd_1974879 := by exact prefixLift 1974879
  have htrace : WordTrace (prefixWord ++ tailWord_1974879) baseStart_1974879 baseEnd_1974879 := by
    simpa [prefixWord, tailWord_1974879, baseEnd_1974879] using wordTrace_append hprefix tailTrace_1974879
  have hstable : (prefixWord ++ tailWord_1974879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974879).length < 2 ^ (prefixWord ++ tailWord_1974879).sum := by decide
  have hdescent : baseEnd_1974879 < baseStart_1974879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974911 : List Nat := [1, 1, 2, 2, 1, 1, 1, 9, 4]
def baseStart_1974911 : Nat := 118140960795 + 1974911 * 2 ^ 59
def prefixEnd_1974911 : Nat := 4983230072969 + 3 ^ 40 * 1974911 * 2
def baseEnd_1974911 : Nat := 225350798411472863406679

theorem tailTrace_1974911 : CollatzResearch.WordTrace tailWord_1974911 prefixEnd_1974911 225350798411472863406679 := by
  unfold tailWord_1974911
  simp only [CollatzResearch.WordTrace]
  refine ⟨72030921748242209791044587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48020614498828139860696391 72030921748242209791044587)
  ·
    refine ⟨108046382622363314686566881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72030921748242209791044587 108046382622363314686566881)
    ·
      refine ⟨81034786966772486014925161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108046382622363314686566881 81034786966772486014925161)
      ·
        refine ⟨60776090225079364511193871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81034786966772486014925161 60776090225079364511193871)
        ·
          refine ⟨91164135337619046766790807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60776090225079364511193871 91164135337619046766790807)
          ·
            refine ⟨136746203006428570150186211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91164135337619046766790807 136746203006428570150186211)
            ·
              refine ⟨205119304509642855225279317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136746203006428570150186211 205119304509642855225279317)
              ·
                refine ⟨1201870924861188604835621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 205119304509642855225279317 1201870924861188604835621)
                ·
                  refine ⟨225350798411472863406679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1201870924861188604835621 225350798411472863406679)
                  ·
                    rfl

theorem cell22_1974911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 4].length) (baseStart_1974911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974911 prefixEnd_1974911 := by exact prefixLift 1974911
  have htrace : WordTrace (prefixWord ++ tailWord_1974911) baseStart_1974911 baseEnd_1974911 := by
    simpa [prefixWord, tailWord_1974911, baseEnd_1974911] using wordTrace_append hprefix tailTrace_1974911
  have hstable : (prefixWord ++ tailWord_1974911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974911).length < 2 ^ (prefixWord ++ tailWord_1974911).sum := by decide
  have hdescent : baseEnd_1974911 < baseStart_1974911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974924 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_1974924 : Nat := 118140960795 + 1974924 * 2 ^ 59
def prefixEnd_1974924 : Nat := 4983230072969 + 3 ^ 40 * 1974924 * 2
def baseEnd_1974924 : Nat := 676056845400090889644997

theorem tailTrace_1974924 : CollatzResearch.WordTrace tailWord_1974924 prefixEnd_1974924 676056845400090889644997 := by
  unfold tailWord_1974924
  simp only [CollatzResearch.WordTrace]
  refine ⟨36015697948597556505633913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48020930598130075340845217 36015697948597556505633913)
  ·
    refine ⟨27011773461448167379225435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36015697948597556505633913 27011773461448167379225435)
    ·
      refine ⟨40517660192172251068838153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27011773461448167379225435 40517660192172251068838153)
      ·
        refine ⟨30388245144129188301628615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40517660192172251068838153 30388245144129188301628615)
        ·
          refine ⟨45582367716193782452442923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30388245144129188301628615 45582367716193782452442923)
          ·
            refine ⟨68373551574290673678664385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45582367716193782452442923 68373551574290673678664385)
            ·
              refine ⟨51280163680718005258998289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68373551574290673678664385 51280163680718005258998289)
              ·
                refine ⟨38460122760538503944248717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51280163680718005258998289 38460122760538503944248717)
                ·
                  refine ⟨14422546035201938979093269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38460122760538503944248717 14422546035201938979093269)
                  ·
                    refine ⟨676056845400090889644997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14422546035201938979093269 676056845400090889644997)
                    ·
                      rfl

theorem cell22_1974924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_1974924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974924 prefixEnd_1974924 := by exact prefixLift 1974924
  have htrace : WordTrace (prefixWord ++ tailWord_1974924) baseStart_1974924 baseEnd_1974924 := by
    simpa [prefixWord, tailWord_1974924, baseEnd_1974924] using wordTrace_append hprefix tailTrace_1974924
  have hstable : (prefixWord ++ tailWord_1974924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974924).length < 2 ^ (prefixWord ++ tailWord_1974924).sum := by decide
  have hdescent : baseEnd_1974924 < baseStart_1974924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974986 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_1974986 : Nat := 118140960795 + 1974986 * 2 ^ 59
def prefixEnd_1974986 : Nat := 4983230072969 + 3 ^ 40 * 1974986 * 2
def baseEnd_1974986 : Nat := 676078069267143394594807

theorem tailTrace_1974986 : CollatzResearch.WordTrace tailWord_1974986 prefixEnd_1974986 676078069267143394594807 := by
  unfold tailWord_1974986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008414305742624400006203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48022438148646998400016541 18008414305742624400006203)
  ·
    refine ⟨27012621458613936600009305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18008414305742624400006203 27012621458613936600009305)
    ·
      refine ⟨20259466093960452450006979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27012621458613936600009305 20259466093960452450006979)
      ·
        refine ⟨30389199140940678675010469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20259466093960452450006979 30389199140940678675010469)
        ·
          refine ⟨5697974838926377251564463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30389199140940678675010469 5697974838926377251564463)
          ·
            refine ⟨8546962258389565877346695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697974838926377251564463 8546962258389565877346695)
            ·
              refine ⟨12820443387584348816020043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546962258389565877346695 12820443387584348816020043)
              ·
                refine ⟨19230665081376523224030065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12820443387584348816020043 19230665081376523224030065)
                ·
                  refine ⟨14422998811032392418022549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19230665081376523224030065 14422998811032392418022549)
                  ·
                    refine ⟨676078069267143394594807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14422998811032392418022549 676078069267143394594807)
                    ·
                      rfl

theorem cell22_1974986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_1974986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1974986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1974986 prefixEnd_1974986 := by exact prefixLift 1974986
  have htrace : WordTrace (prefixWord ++ tailWord_1974986) baseStart_1974986 baseEnd_1974986 := by
    simpa [prefixWord, tailWord_1974986, baseEnd_1974986] using wordTrace_append hprefix tailTrace_1974986
  have hstable : (prefixWord ++ tailWord_1974986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974986).length < 2 ^ (prefixWord ++ tailWord_1974986).sum := by decide
  have hdescent : baseEnd_1974986 < baseStart_1974986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975001 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 5]
def baseStart_1975001 : Nat := 118140960795 + 1975001 * 2 ^ 59
def prefixEnd_1975001 : Nat := 4983230072969 + 3 ^ 40 * 1975001 * 2
def baseEnd_1975001 : Nat := 225361068024562785156587

theorem tailTrace_1975001 : CollatzResearch.WordTrace tailWord_1975001 prefixEnd_1975001 225361068024562785156587 := by
  unfold tailWord_1975001
  simp only [CollatzResearch.WordTrace]
  refine ⟨72034204317916155161820857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48022802878610770107880571 72034204317916155161820857)
  ·
    refine ⟨54025653238437116371365643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72034204317916155161820857 54025653238437116371365643)
    ·
      refine ⟨81038479857655674557048465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54025653238437116371365643 81038479857655674557048465)
      ·
        refine ⟨60778859893241755917786349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81038479857655674557048465 60778859893241755917786349)
        ·
          refine ⟨22792072459965658469169881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60778859893241755917786349 22792072459965658469169881)
          ·
            refine ⟨17094054344974243851877411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22792072459965658469169881 17094054344974243851877411)
            ·
              refine ⟨25641081517461365777816117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17094054344974243851877411 25641081517461365777816117)
              ·
                refine ⟨2403851392262003041670261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25641081517461365777816117 2403851392262003041670261)
                ·
                  refine ⟨225361068024562785156587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2403851392262003041670261 225361068024562785156587)
                  ·
                    rfl

theorem cell22_1975001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_1975001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975001 prefixEnd_1975001 := by exact prefixLift 1975001
  have htrace : WordTrace (prefixWord ++ tailWord_1975001) baseStart_1975001 baseEnd_1975001 := by
    simpa [prefixWord, tailWord_1975001, baseEnd_1975001] using wordTrace_append hprefix tailTrace_1975001
  have hstable : (prefixWord ++ tailWord_1975001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975001).length < 2 ^ (prefixWord ++ tailWord_1975001).sum := by decide
  have hdescent : baseEnd_1975001 < baseStart_1975001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975022 : List Nat := [4, 1, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_1975022 : Nat := 118140960795 + 1975022 * 2 ^ 59
def prefixEnd_1975022 : Nat := 4983230072969 + 3 ^ 40 * 1975022 * 2
def baseEnd_1975022 : Nat := 676090392802851300694697

theorem tailTrace_1975022 : CollatzResearch.WordTrace tailWord_1975022 prefixEnd_1975022 676090392802851300694697 := by
  unfold tailWord_1975022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9004371281355009468541915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48023313500560050498890213 9004371281355009468541915)
  ·
    refine ⟨13506556922032514202812873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9004371281355009468541915 13506556922032514202812873)
    ·
      refine ⟨10129917691524385652109655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13506556922032514202812873 10129917691524385652109655)
      ·
        refine ⟨15194876537286578478164483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10129917691524385652109655 15194876537286578478164483)
        ·
          refine ⟨22792314805929867717246725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15194876537286578478164483 22792314805929867717246725)
          ·
            refine ⟨4273559026111850196983761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22792314805929867717246725 4273559026111850196983761)
            ·
              refine ⟨3205169269583887647737821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4273559026111850196983761 3205169269583887647737821)
              ·
                refine ⟨1201938476093957867901683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3205169269583887647737821 1201938476093957867901683)
                ·
                  refine ⟨1802907714140936801852525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201938476093957867901683 1802907714140936801852525)
                  ·
                    refine ⟨676090392802851300694697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1802907714140936801852525 676090392802851300694697)
                    ·
                      rfl

theorem cell22_1975022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_1975022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975022 prefixEnd_1975022 := by exact prefixLift 1975022
  have htrace : WordTrace (prefixWord ++ tailWord_1975022) baseStart_1975022 baseEnd_1975022 := by
    simpa [prefixWord, tailWord_1975022, baseEnd_1975022] using wordTrace_append hprefix tailTrace_1975022
  have hstable : (prefixWord ++ tailWord_1975022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975022).length < 2 ^ (prefixWord ++ tailWord_1975022).sum := by decide
  have hdescent : baseEnd_1975022 < baseStart_1975022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975091 : List Nat := [1, 1, 1, 2, 6, 1, 10]
def baseStart_1975091 : Nat := 118140960795 + 1975091 * 2 ^ 59
def prefixEnd_1975091 : Nat := 4983230072969 + 3 ^ 40 * 1975091 * 2
def baseEnd_1975091 : Nat := 25041259737516967434055

theorem tailTrace_1975091 : CollatzResearch.WordTrace tailWord_1975091 prefixEnd_1975091 25041259737516967434055 := by
  unfold tailWord_1975091
  simp only [CollatzResearch.WordTrace]
  refine ⟨72037486887590100532597127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48024991258393400355064751 72037486887590100532597127)
  ·
    refine ⟨108056230331385150798895691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72037486887590100532597127 108056230331385150798895691)
    ·
      refine ⟨162084345497077726198343537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108056230331385150798895691 162084345497077726198343537)
      ·
        refine ⟨121563259122808294648757653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162084345497077726198343537 121563259122808294648757653)
        ·
          refine ⟨5698277771381638811660515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121563259122808294648757653 5698277771381638811660515)
          ·
            refine ⟨8547416657072458217490773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698277771381638811660515 8547416657072458217490773)
            ·
              refine ⟨25041259737516967434055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8547416657072458217490773 25041259737516967434055)
              ·
                rfl

theorem cell22_1975091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 10].length) (baseStart_1975091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975091 prefixEnd_1975091 := by exact prefixLift 1975091
  have htrace : WordTrace (prefixWord ++ tailWord_1975091) baseStart_1975091 baseEnd_1975091 := by
    simpa [prefixWord, tailWord_1975091, baseEnd_1975091] using wordTrace_append hprefix tailTrace_1975091
  have hstable : (prefixWord ++ tailWord_1975091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975091).length < 2 ^ (prefixWord ++ tailWord_1975091).sum := by decide
  have hdescent : baseEnd_1975091 < baseStart_1975091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975093 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1975093 : Nat := 118140960795 + 1975093 * 2 ^ 59
def prefixEnd_1975093 : Nat := 4983230072969 + 3 ^ 40 * 1975093 * 2
def baseEnd_1975093 : Nat := 676114697553830782169479

theorem tailTrace_1975093 : CollatzResearch.WordTrace tailWord_1975093 prefixEnd_1975093 676114697553830782169479 := by
  unfold tailWord_1975093
  simp only [CollatzResearch.WordTrace]
  refine ⟨72037559833582854874169933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48025039889055236582779955 72037559833582854874169933)
  ·
    refine ⟨27014084937593570577813725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72037559833582854874169933 27014084937593570577813725)
    ·
      refine ⟨10130281851597588966680147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27014084937593570577813725 10130281851597588966680147)
      ·
        refine ⟨15195422777396383450020221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10130281851597588966680147 15195422777396383450020221)
        ·
          refine ⟨5698283541523643793757583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15195422777396383450020221 5698283541523643793757583)
          ·
            refine ⟨8547425312285465690636375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698283541523643793757583 8547425312285465690636375)
            ·
              refine ⟨12821137968428198535954563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547425312285465690636375 12821137968428198535954563)
              ·
                refine ⟨19231706952642297803931845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821137968428198535954563 19231706952642297803931845)
                ·
                  refine ⟨3605945053620430838237221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19231706952642297803931845 3605945053620430838237221)
                  ·
                    refine ⟨676114697553830782169479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3605945053620430838237221 676114697553830782169479)
                    ·
                      rfl

theorem cell22_1975093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1975093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975093 prefixEnd_1975093 := by exact prefixLift 1975093
  have htrace : WordTrace (prefixWord ++ tailWord_1975093) baseStart_1975093 baseEnd_1975093 := by
    simpa [prefixWord, tailWord_1975093, baseEnd_1975093] using wordTrace_append hprefix tailTrace_1975093
  have hstable : (prefixWord ++ tailWord_1975093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975093).length < 2 ^ (prefixWord ++ tailWord_1975093).sum := by decide
  have hdescent : baseEnd_1975093 < baseStart_1975093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975123 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 3, 3]
def baseStart_1975123 : Nat := 118140960795 + 1975123 * 2 ^ 59
def prefixEnd_1975123 : Nat := 4983230072969 + 3 ^ 40 * 1975123 * 2
def baseEnd_1975123 : Nat := 676124967166920703919387

theorem tailTrace_1975123 : CollatzResearch.WordTrace tailWord_1975123 prefixEnd_1975123 676124967166920703919387 := by
  unfold tailWord_1975123
  simp only [CollatzResearch.WordTrace]
  refine ⟨72038654023474169997762023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48025769348982779998508015 72038654023474169997762023)
  ·
    refine ⟨108057981035211254996643035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72038654023474169997762023 108057981035211254996643035)
    ·
      refine ⟨162086971552816882494964553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108057981035211254996643035 162086971552816882494964553)
      ·
        refine ⟨121565228664612661871223415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162086971552816882494964553 121565228664612661871223415)
        ·
          refine ⟨182347842996918992806835123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121565228664612661871223415 182347842996918992806835123)
          ·
            refine ⟨273521764495378489210252685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182347842996918992806835123 273521764495378489210252685)
            ·
              refine ⟨102570661685766933453844757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273521764495378489210252685 102570661685766933453844757)
              ·
                refine ⟨4807999766520325005648973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102570661685766933453844757 4807999766520325005648973)
                ·
                  refine ⟨1802999912445121877118365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4807999766520325005648973 1802999912445121877118365)
                  ·
                    refine ⟨676124967166920703919387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1802999912445121877118365 676124967166920703919387)
                    ·
                      rfl

theorem cell22_1975123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3, 3].length) (baseStart_1975123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975123 prefixEnd_1975123 := by exact prefixLift 1975123
  have htrace : WordTrace (prefixWord ++ tailWord_1975123) baseStart_1975123 baseEnd_1975123 := by
    simpa [prefixWord, tailWord_1975123, baseEnd_1975123] using wordTrace_append hprefix tailTrace_1975123
  have hstable : (prefixWord ++ tailWord_1975123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975123).length < 2 ^ (prefixWord ++ tailWord_1975123).sum := by decide
  have hdescent : baseEnd_1975123 < baseStart_1975123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975151 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 3, 7]
def baseStart_1975151 : Nat := 118140960795 + 1975151 * 2 ^ 59
def prefixEnd_1975151 : Nat := 4983230072969 + 3 ^ 40 * 1975151 * 2
def baseEnd_1975151 : Nat := 676134552139137964219301

theorem tailTrace_1975151 : CollatzResearch.WordTrace tailWord_1975151 prefixEnd_1975151 676134552139137964219301 := by
  unfold tailWord_1975151
  simp only [CollatzResearch.WordTrace]
  refine ⟨72039675267372730779781307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48026450178248487186520871 72039675267372730779781307)
  ·
    refine ⟨108059512901059096169671961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72039675267372730779781307 108059512901059096169671961)
    ·
      refine ⟨81044634675794322127253971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108059512901059096169671961 81044634675794322127253971)
      ·
        refine ⟨121566952013691483190880957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81044634675794322127253971 121566952013691483190880957)
        ·
          refine ⟨45587607005134306196580359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121566952013691483190880957 45587607005134306196580359)
          ·
            refine ⟨68381410507701459294870539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45587607005134306196580359 68381410507701459294870539)
            ·
              refine ⟨102572115761552188942305809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68381410507701459294870539 102572115761552188942305809)
              ·
                refine ⟨76929086821164141706729357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102572115761552188942305809 76929086821164141706729357)
                ·
                  refine ⟨28848407557936553140023509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76929086821164141706729357 28848407557936553140023509)
                  ·
                    refine ⟨676134552139137964219301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28848407557936553140023509 676134552139137964219301)
                    ·
                      rfl

theorem cell22_1975151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_1975151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975151 prefixEnd_1975151 := by exact prefixLift 1975151
  have htrace : WordTrace (prefixWord ++ tailWord_1975151) baseStart_1975151 baseEnd_1975151 := by
    simpa [prefixWord, tailWord_1975151, baseEnd_1975151] using wordTrace_append hprefix tailTrace_1975151
  have hstable : (prefixWord ++ tailWord_1975151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975151).length < 2 ^ (prefixWord ++ tailWord_1975151).sum := by decide
  have hdescent : baseEnd_1975151 < baseStart_1975151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975153 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 5]
def baseStart_1975153 : Nat := 118140960795 + 1975153 * 2 ^ 59
def prefixEnd_1975153 : Nat := 4983230072969 + 3 ^ 40 * 1975153 * 2
def baseEnd_1975153 : Nat := 225378412260003541889765

theorem tailTrace_1975153 : CollatzResearch.WordTrace tailWord_1975153 prefixEnd_1975153 225378412260003541889765 := by
  unfold tailWord_1975153
  simp only [CollatzResearch.WordTrace]
  refine ⟨72039748213365485121354113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48026498808910323414236075 72039748213365485121354113)
  ·
    refine ⟨54029811160024113841015585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72039748213365485121354113 54029811160024113841015585)
    ·
      refine ⟨40522358370018085380761689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54029811160024113841015585 40522358370018085380761689)
      ·
        refine ⟨30391768777513564035571267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40522358370018085380761689 30391768777513564035571267)
        ·
          refine ⟨45587653166270346053356901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30391768777513564035571267 45587653166270346053356901)
          ·
            refine ⟨8547684968675689885004419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45587653166270346053356901 8547684968675689885004419)
            ·
              refine ⟨12821527453013534827506629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547684968675689885004419 12821527453013534827506629)
              ·
                refine ⟨2404036397440037780157493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12821527453013534827506629 2404036397440037780157493)
                ·
                  refine ⟨225378412260003541889765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2404036397440037780157493 225378412260003541889765)
                  ·
                    rfl

theorem cell22_1975153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_1975153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975153 prefixEnd_1975153 := by exact prefixLift 1975153
  have htrace : WordTrace (prefixWord ++ tailWord_1975153) baseStart_1975153 baseEnd_1975153 := by
    simpa [prefixWord, tailWord_1975153, baseEnd_1975153] using wordTrace_append hprefix tailTrace_1975153
  have hstable : (prefixWord ++ tailWord_1975153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975153).length < 2 ^ (prefixWord ++ tailWord_1975153).sum := by decide
  have hdescent : baseEnd_1975153 < baseStart_1975153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975243 : List Nat := [1, 1, 1, 1, 3, 6, 1, 8]
def baseStart_1975243 : Nat := 118140960795 + 1975243 * 2 ^ 59
def prefixEnd_1975243 : Nat := 4983230072969 + 3 ^ 40 * 1975243 * 2
def baseEnd_1975243 : Nat := 75129560624364487879891

theorem tailTrace_1975243 : CollatzResearch.WordTrace tailWord_1975243 prefixEnd_1975243 75129560624364487879891 := by
  unfold tailWord_1975243
  simp only [CollatzResearch.WordTrace]
  refine ⟨72043030783039430492130383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48028687188692953661420255 72043030783039430492130383)
  ·
    refine ⟨108064546174559145738195575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72043030783039430492130383 108064546174559145738195575)
    ·
      refine ⟨162096819261838718607293363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108064546174559145738195575 162096819261838718607293363)
      ·
        refine ⟨243145228892758077910940045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162096819261838718607293363 243145228892758077910940045)
        ·
          refine ⟨91179460834784279216602517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243145228892758077910940045 91179460834784279216602517)
          ·
            refine ⟨4274037226630513088278243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91179460834784279216602517 4274037226630513088278243)
            ·
              refine ⟨6411055839945769632417365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274037226630513088278243 6411055839945769632417365)
              ·
                refine ⟨75129560624364487879891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6411055839945769632417365 75129560624364487879891)
                ·
                  rfl

theorem cell22_1975243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 8].length) (baseStart_1975243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975243 prefixEnd_1975243 := by exact prefixLift 1975243
  have htrace : WordTrace (prefixWord ++ tailWord_1975243) baseStart_1975243 baseEnd_1975243 := by
    simpa [prefixWord, tailWord_1975243, baseEnd_1975243] using wordTrace_append hprefix tailTrace_1975243
  have hstable : (prefixWord ++ tailWord_1975243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975243).length < 2 ^ (prefixWord ++ tailWord_1975243).sum := by decide
  have hdescent : baseEnd_1975243 < baseStart_1975243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975266 : List Nat := [3, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1975266 : Nat := 118140960795 + 1975266 * 2 ^ 59
def prefixEnd_1975266 : Nat := 4983230072969 + 3 ^ 40 * 1975266 * 2
def baseEnd_1975266 : Nat := 225391306329771999197983

theorem tailTrace_1975266 : CollatzResearch.WordTrace tailWord_1975266 prefixEnd_1975266 225391306329771999197983 := by
  unfold tailWord_1975266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18010967415489026355054413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48029246441304070280145101 18010967415489026355054413)
  ·
    refine ⟨6754112780808384883145405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18010967415489026355054413 6754112780808384883145405)
    ·
      refine ⟨2532792292803144331179527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6754112780808384883145405 2532792292803144331179527)
      ·
        refine ⟨3799188439204716496769291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532792292803144331179527 3799188439204716496769291)
        ·
          refine ⟨5698782658807074745153937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799188439204716496769291 5698782658807074745153937)
          ·
            refine ⟨4274086994105306058865453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5698782658807074745153937 4274086994105306058865453)
            ·
              refine ⟨1602782622789489772074545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4274086994105306058865453 1602782622789489772074545)
              ·
                refine ⟨1202086967092117329055909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602782622789489772074545 1202086967092117329055909)
                ·
                  refine ⟨225391306329771999197983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202086967092117329055909 225391306329771999197983)
                  ·
                    rfl

theorem cell22_1975266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1975266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975266 prefixEnd_1975266 := by exact prefixLift 1975266
  have htrace : WordTrace (prefixWord ++ tailWord_1975266) baseStart_1975266 baseEnd_1975266 := by
    simpa [prefixWord, tailWord_1975266, baseEnd_1975266] using wordTrace_append hprefix tailTrace_1975266
  have hstable : (prefixWord ++ tailWord_1975266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975266).length < 2 ^ (prefixWord ++ tailWord_1975266).sum := by decide
  have hdescent : baseEnd_1975266 < baseStart_1975266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975365 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_1975365 : Nat := 118140960795 + 1975365 * 2 ^ 59
def prefixEnd_1975365 : Nat := 4983230072969 + 3 ^ 40 * 1975365 * 2
def baseEnd_1975365 : Nat := 676207808712512739368645

theorem tailTrace_1975365 : CollatzResearch.WordTrace tailWord_1975365 prefixEnd_1975365 676207808712512739368645 := by
  unfold tailWord_1975365
  simp only [CollatzResearch.WordTrace]
  refine ⟨72047480488597445328071549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48031653659064963552047699 72047480488597445328071549)
  ·
    refine ⟨27017805183224041998026831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72047480488597445328071549 27017805183224041998026831)
    ·
      refine ⟨40526707774836062997040247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27017805183224041998026831 40526707774836062997040247)
      ·
        refine ⟨60790061662254094495560371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40526707774836062997040247 60790061662254094495560371)
        ·
          refine ⟨91185092493381141743340557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60790061662254094495560371 91185092493381141743340557)
          ·
            refine ⟨34194409685017928153752709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91185092493381141743340557 34194409685017928153752709)
            ·
              refine ⟨6411451815940861528828633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34194409685017928153752709 6411451815940861528828633)
              ·
                refine ⟨4808588861955646146621475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6411451815940861528828633 4808588861955646146621475)
                ·
                  refine ⟨7212883292933469219932213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808588861955646146621475 7212883292933469219932213)
                  ·
                    refine ⟨676207808712512739368645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7212883292933469219932213 676207808712512739368645)
                    ·
                      rfl

theorem cell22_1975365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_1975365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975365 prefixEnd_1975365 := by exact prefixLift 1975365
  have htrace : WordTrace (prefixWord ++ tailWord_1975365) baseStart_1975365 baseEnd_1975365 := by
    simpa [prefixWord, tailWord_1975365, baseEnd_1975365] using wordTrace_append hprefix tailTrace_1975365
  have hstable : (prefixWord ++ tailWord_1975365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975365).length < 2 ^ (prefixWord ++ tailWord_1975365).sum := by decide
  have hdescent : baseEnd_1975365 < baseStart_1975365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975367 : List Nat := [1, 1, 4, 1, 3, 2, 1, 5, 4]
def baseStart_1975367 : Nat := 118140960795 + 1975367 * 2 ^ 59
def prefixEnd_1975367 : Nat := 4983230072969 + 3 ^ 40 * 1975367 * 2
def baseEnd_1975367 : Nat := 225402831117795133606213

theorem tailTrace_1975367 : CollatzResearch.WordTrace tailWord_1975367 prefixEnd_1975367 225402831117795133606213 := by
  unfold tailWord_1975367
  simp only [CollatzResearch.WordTrace]
  refine ⟨72047553434590199669644355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48031702289726799779762903 72047553434590199669644355)
  ·
    refine ⟨108071330151885299504466533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72047553434590199669644355 108071330151885299504466533)
    ·
      refine ⟨20263374403478493657087475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108071330151885299504466533 20263374403478493657087475)
      ·
        refine ⟨30395061605217740485631213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20263374403478493657087475 30395061605217740485631213)
        ·
          refine ⟨11398148101956652682111705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30395061605217740485631213 11398148101956652682111705)
          ·
            refine ⟨8548611076467489511583779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11398148101956652682111705 8548611076467489511583779)
            ·
              refine ⟨12822916614701234267375669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548611076467489511583779 12822916614701234267375669)
              ·
                refine ⟨1202148432628240712566469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12822916614701234267375669 1202148432628240712566469)
                ·
                  refine ⟨225402831117795133606213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202148432628240712566469 225402831117795133606213)
                  ·
                    rfl

theorem cell22_1975367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 4].length) (baseStart_1975367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975367 prefixEnd_1975367 := by exact prefixLift 1975367
  have htrace : WordTrace (prefixWord ++ tailWord_1975367) baseStart_1975367 baseEnd_1975367 := by
    simpa [prefixWord, tailWord_1975367, baseEnd_1975367] using wordTrace_append hprefix tailTrace_1975367
  have hstable : (prefixWord ++ tailWord_1975367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975367).length < 2 ^ (prefixWord ++ tailWord_1975367).sum := by decide
  have hdescent : baseEnd_1975367 < baseStart_1975367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975410 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1975410 : Nat := 118140960795 + 1975410 * 2 ^ 59
def prefixEnd_1975410 : Nat := 4983230072969 + 3 ^ 40 * 1975410 * 2
def baseEnd_1975410 : Nat := 676223213132147621993507

theorem tailTrace_1975410 : CollatzResearch.WordTrace tailWord_1975410 prefixEnd_1975410 676223213132147621993507 := by
  unfold tailWord_1975410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18012280443358604503364921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48032747848956278675639789 18012280443358604503364921)
  ·
    refine ⟨13509210332518953377523691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18012280443358604503364921 13509210332518953377523691)
    ·
      refine ⟨20263815498778430066285537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13509210332518953377523691 20263815498778430066285537)
      ·
        refine ⟨15197861624083822549714153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20263815498778430066285537 15197861624083822549714153)
        ·
          refine ⟨11398396218062866912285615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15197861624083822549714153 11398396218062866912285615)
          ·
            refine ⟨17097594327094300368428423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11398396218062866912285615 17097594327094300368428423)
            ·
              refine ⟨25646391490641450552642635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17097594327094300368428423 25646391490641450552642635)
              ·
                refine ⟨38469587235962175828963953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25646391490641450552642635 38469587235962175828963953)
                ·
                  refine ⟨28852190426971631871722965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38469587235962175828963953 28852190426971631871722965)
                  ·
                    refine ⟨676223213132147621993507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28852190426971631871722965 676223213132147621993507)
                    ·
                      rfl

theorem cell22_1975410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1975410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975410 prefixEnd_1975410 := by exact prefixLift 1975410
  have htrace : WordTrace (prefixWord ++ tailWord_1975410) baseStart_1975410 baseEnd_1975410 := by
    simpa [prefixWord, tailWord_1975410, baseEnd_1975410] using wordTrace_append hprefix tailTrace_1975410
  have hstable : (prefixWord ++ tailWord_1975410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975410).length < 2 ^ (prefixWord ++ tailWord_1975410).sum := by decide
  have hdescent : baseEnd_1975410 < baseStart_1975410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975457 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 5]
def baseStart_1975457 : Nat := 118140960795 + 1975457 * 2 ^ 59
def prefixEnd_1975457 : Nat := 4983230072969 + 3 ^ 40 * 1975457 * 2
def baseEnd_1975457 : Nat := 225413100730885055356121

theorem tailTrace_1975457 : CollatzResearch.WordTrace tailWord_1975457 prefixEnd_1975457 225413100730885055356121 := by
  unfold tailWord_1975457
  simp only [CollatzResearch.WordTrace]
  refine ⟨72050836004264145040420625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48033890669509430026947083 72050836004264145040420625)
  ·
    refine ⟨54038127003198108780315469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72050836004264145040420625 54038127003198108780315469)
    ·
      refine ⟨20264297626199290792618301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54038127003198108780315469 20264297626199290792618301)
      ·
        refine ⟨7599111609824734047231863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20264297626199290792618301 7599111609824734047231863)
        ·
          refine ⟨11398667414737101070847795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7599111609824734047231863 11398667414737101070847795)
          ·
            refine ⟨17098001122105651606271693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11398667414737101070847795 17098001122105651606271693)
            ·
              refine ⟨6411750420789619352351885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17098001122105651606271693 6411750420789619352351885)
              ·
                refine ⟨2404406407796107257131957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6411750420789619352351885 2404406407796107257131957)
                ·
                  refine ⟨225413100730885055356121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2404406407796107257131957 225413100730885055356121)
                  ·
                    rfl

theorem cell22_1975457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_1975457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975457 prefixEnd_1975457 := by exact prefixLift 1975457
  have htrace : WordTrace (prefixWord ++ tailWord_1975457) baseStart_1975457 baseEnd_1975457 := by
    simpa [prefixWord, tailWord_1975457, baseEnd_1975457] using wordTrace_append hprefix tailTrace_1975457
  have hstable : (prefixWord ++ tailWord_1975457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975457).length < 2 ^ (prefixWord ++ tailWord_1975457).sum := by decide
  have hdescent : baseEnd_1975457 < baseStart_1975457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975487 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 1, 4]
def baseStart_1975487 : Nat := 118140960795 + 1975487 * 2 ^ 59
def prefixEnd_1975487 : Nat := 4983230072969 + 3 ^ 40 * 1975487 * 2
def baseEnd_1975487 : Nat := 676249571805745087818271

theorem tailTrace_1975487 : CollatzResearch.WordTrace tailWord_1975487 prefixEnd_1975487 676249571805745087818271 := by
  unfold tailWord_1975487
  simp only [CollatzResearch.WordTrace]
  refine ⟨72051930194155460164012715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48034620129436973442675143 72051930194155460164012715)
  ·
    refine ⟨108077895291233190246019073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72051930194155460164012715 108077895291233190246019073)
    ·
      refine ⟨81058421468424892684514305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108077895291233190246019073 81058421468424892684514305)
      ·
        refine ⟨60793816101318669513385729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81058421468424892684514305 60793816101318669513385729)
        ·
          refine ⟨45595362075989002135039297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60793816101318669513385729 45595362075989002135039297)
          ·
            refine ⟨34196521556991751601279473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45595362075989002135039297 34196521556991751601279473)
            ·
              refine ⟨25647391167743813700959605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34196521556991751601279473 25647391167743813700959605)
              ·
                refine ⟨2404442921975982534464963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25647391167743813700959605 2404442921975982534464963)
                ·
                  refine ⟨3606664382963973801697445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404442921975982534464963 3606664382963973801697445)
                  ·
                    refine ⟨676249571805745087818271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3606664382963973801697445 676249571805745087818271)
                    ·
                      rfl

theorem cell22_1975487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_1975487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975487 prefixEnd_1975487 := by exact prefixLift 1975487
  have htrace : WordTrace (prefixWord ++ tailWord_1975487) baseStart_1975487 baseEnd_1975487 := by
    simpa [prefixWord, tailWord_1975487, baseEnd_1975487] using wordTrace_append hprefix tailTrace_1975487
  have hstable : (prefixWord ++ tailWord_1975487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975487).length < 2 ^ (prefixWord ++ tailWord_1975487).sum := by decide
  have hdescent : baseEnd_1975487 < baseStart_1975487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975532 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_1975532 : Nat := 118140960795 + 1975532 * 2 ^ 59
def prefixEnd_1975532 : Nat := 4983230072969 + 3 ^ 40 * 1975532 * 2
def baseEnd_1975532 : Nat := 676264976225379970443133

theorem tailTrace_1975532 : CollatzResearch.WordTrace tailWord_1975532 prefixEnd_1975532 676264976225379970443133 := by
  unfold tailWord_1975532
  simp only [CollatzResearch.WordTrace]
  refine ⟨36026785739496216424700425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48035714319328288566267233 36026785739496216424700425)
  ·
    refine ⟨27020089304622162318525319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36026785739496216424700425 27020089304622162318525319)
    ·
      refine ⟨40530133956933243477787979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27020089304622162318525319 40530133956933243477787979)
      ·
        refine ⟨60795200935399865216681969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40530133956933243477787979 60795200935399865216681969)
        ·
          refine ⟨45596400701549898912511477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60795200935399865216681969 45596400701549898912511477)
          ·
            refine ⟨4274662565770303023047951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45596400701549898912511477 4274662565770303023047951)
            ·
              refine ⟨6411993848655454534571927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274662565770303023047951 6411993848655454534571927)
              ·
                refine ⟨9617990772983181801857891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6411993848655454534571927 9617990772983181801857891)
                ·
                  refine ⟨14426986159474772702786837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9617990772983181801857891 14426986159474772702786837)
                  ·
                    refine ⟨676264976225379970443133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14426986159474772702786837 676264976225379970443133)
                    ·
                      rfl

theorem cell22_1975532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_1975532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975532 prefixEnd_1975532 := by exact prefixLift 1975532
  have htrace : WordTrace (prefixWord ++ tailWord_1975532) baseStart_1975532 baseEnd_1975532 := by
    simpa [prefixWord, tailWord_1975532, baseEnd_1975532] using wordTrace_append hprefix tailTrace_1975532
  have hstable : (prefixWord ++ tailWord_1975532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975532).length < 2 ^ (prefixWord ++ tailWord_1975532).sum := by decide
  have hdescent : baseEnd_1975532 < baseStart_1975532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975538 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_1975538 : Nat := 118140960795 + 1975538 * 2 ^ 59
def prefixEnd_1975538 : Nat := 4983230072969 + 3 ^ 40 * 1975538 * 2
def baseEnd_1975538 : Nat := 676267030147997954793115

theorem tailTrace_1975538 : CollatzResearch.WordTrace tailWord_1975538 prefixEnd_1975538 676267030147997954793115 := by
  unfold tailWord_1975538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013447579242673968529817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48035860211313797249412845 18013447579242673968529817)
  ·
    refine ⟨13510085684432005476397363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18013447579242673968529817 13510085684432005476397363)
    ·
      refine ⟨20265128526648008214596045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13510085684432005476397363 20265128526648008214596045)
      ·
        refine ⟨7599423197493003080473517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20265128526648008214596045 7599423197493003080473517)
        ·
          refine ⟨2849783699059876155177569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7599423197493003080473517 2849783699059876155177569)
          ·
            refine ⟨2137337774294907116383177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2849783699059876155177569 2137337774294907116383177)
            ·
              refine ⟨1603003330721180337287383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137337774294907116383177 1603003330721180337287383)
              ·
                refine ⟨2404504996081770505931075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603003330721180337287383 2404504996081770505931075)
                ·
                  refine ⟨3606757494122655758896613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404504996081770505931075 3606757494122655758896613)
                  ·
                    refine ⟨676267030147997954793115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3606757494122655758896613 676267030147997954793115)
                    ·
                      rfl

theorem cell22_1975538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_1975538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975538 prefixEnd_1975538 := by exact prefixLift 1975538
  have htrace : WordTrace (prefixWord ++ tailWord_1975538) baseStart_1975538 baseEnd_1975538 := by
    simpa [prefixWord, tailWord_1975538, baseEnd_1975538] using wordTrace_append hprefix tailTrace_1975538
  have hstable : (prefixWord ++ tailWord_1975538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975538).length < 2 ^ (prefixWord ++ tailWord_1975538).sum := by decide
  have hdescent : baseEnd_1975538 < baseStart_1975538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975551 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 2, 3]
def baseStart_1975551 : Nat := 118140960795 + 1975551 * 2 ^ 59
def prefixEnd_1975551 : Nat := 4983230072969 + 3 ^ 40 * 1975551 * 2
def baseEnd_1975551 : Nat := 676271480313670254218075

theorem tailTrace_1975551 : CollatzResearch.WordTrace tailWord_1975551 prefixEnd_1975551 676271480313670254218075 := by
  unfold tailWord_1975551
  simp only [CollatzResearch.WordTrace]
  refine ⟨72054264465923599094342507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48036176310615732729561671 72054264465923599094342507)
  ·
    refine ⟨108081396698885398641513761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72054264465923599094342507 108081396698885398641513761)
    ·
      refine ⟨81061047524164048981135321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108081396698885398641513761 81061047524164048981135321)
      ·
        refine ⟨60795785643123036735851491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81061047524164048981135321 60795785643123036735851491)
        ·
          refine ⟨91193678464684555103777237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60795785643123036735851491 91193678464684555103777237)
          ·
            refine ⟨2137351839016044260244779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 91193678464684555103777237 2137351839016044260244779)
            ·
              refine ⟨3206027758524066390367169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137351839016044260244779 3206027758524066390367169)
              ·
                refine ⟨2404520818893049792775377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206027758524066390367169 2404520818893049792775377)
                ·
                  refine ⟨1803390614169787344581533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404520818893049792775377 1803390614169787344581533)
                  ·
                    refine ⟨676271480313670254218075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1803390614169787344581533 676271480313670254218075)
                    ·
                      rfl

theorem cell22_1975551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_1975551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975551 prefixEnd_1975551 := by exact prefixLift 1975551
  have htrace : WordTrace (prefixWord ++ tailWord_1975551) baseStart_1975551 baseEnd_1975551 := by
    simpa [prefixWord, tailWord_1975551, baseEnd_1975551] using wordTrace_append hprefix tailTrace_1975551
  have hstable : (prefixWord ++ tailWord_1975551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975551).length < 2 ^ (prefixWord ++ tailWord_1975551).sum := by decide
  have hdescent : baseEnd_1975551 < baseStart_1975551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975581 : List Nat := [1, 4, 2, 3, 1, 3, 2, 6]
def baseStart_1975581 : Nat := 118140960795 + 1975581 * 2 ^ 59
def prefixEnd_1975581 : Nat := 4983230072969 + 3 ^ 40 * 1975581 * 2
def baseEnd_1975581 : Nat := 75142416658528908440887

theorem tailTrace_1975581 : CollatzResearch.WordTrace tailWord_1975581 prefixEnd_1975581 75142416658528908440887 := by
  unfold tailWord_1975581
  simp only [CollatzResearch.WordTrace]
  refine ⟨72055358655814914217934597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48036905770543276145289731 72055358655814914217934597)
  ·
    refine ⟨13510379747965296415862737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72055358655814914217934597 13510379747965296415862737)
    ·
      refine ⟨10132784810973972311897053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13510379747965296415862737 10132784810973972311897053)
      ·
        refine ⟨3799794304115239616961395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10132784810973972311897053 3799794304115239616961395)
        ·
          refine ⟨5699691456172859425442093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799794304115239616961395 5699691456172859425442093)
          ·
            refine ⟨2137384296064822284540785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5699691456172859425442093 2137384296064822284540785)
            ·
              refine ⟨1603038222048616713405589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137384296064822284540785 1603038222048616713405589)
              ·
                refine ⟨75142416658528908440887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1603038222048616713405589 75142416658528908440887)
                ·
                  rfl

theorem cell22_1975581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 6].length) (baseStart_1975581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975581 prefixEnd_1975581 := by exact prefixLift 1975581
  have htrace : WordTrace (prefixWord ++ tailWord_1975581) baseStart_1975581 baseEnd_1975581 := by
    simpa [prefixWord, tailWord_1975581, baseEnd_1975581] using wordTrace_append hprefix tailTrace_1975581
  have hstable : (prefixWord ++ tailWord_1975581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975581).length < 2 ^ (prefixWord ++ tailWord_1975581).sum := by decide
  have hdescent : baseEnd_1975581 < baseStart_1975581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975639 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 3, 4]
def baseStart_1975639 : Nat := 118140960795 + 1975639 * 2 ^ 59
def prefixEnd_1975639 : Nat := 4983230072969 + 3 ^ 40 * 1975639 * 2
def baseEnd_1975639 : Nat := 676301604512067358017805

theorem tailTrace_1975639 : CollatzResearch.WordTrace tailWord_1975639 prefixEnd_1975639 676301604512067358017805 := by
  unfold tailWord_1975639
  simp only [CollatzResearch.WordTrace]
  refine ⟨72057474089604790123545971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48038316059736526749030647 72057474089604790123545971)
  ·
    refine ⟨108086211134407185185318957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72057474089604790123545971 108086211134407185185318957)
    ·
      refine ⟨40532329175402694444494609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108086211134407185185318957 40532329175402694444494609)
      ·
        refine ⟨30399246881552020833370957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40532329175402694444494609 30399246881552020833370957)
        ·
          refine ⟨11399717580582007812514109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30399246881552020833370957 11399717580582007812514109)
          ·
            refine ⟨4274894092718252929692791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11399717580582007812514109 4274894092718252929692791)
            ·
              refine ⟨6412341139077379394539187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274894092718252929692791 6412341139077379394539187)
              ·
                refine ⟨9618511708616069091808781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412341139077379394539187 9618511708616069091808781)
                ·
                  refine ⟨3606941890731025909428293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9618511708616069091808781 3606941890731025909428293)
                  ·
                    refine ⟨676301604512067358017805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3606941890731025909428293 676301604512067358017805)
                    ·
                      rfl

theorem cell22_1975639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_1975639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975639 prefixEnd_1975639 := by exact prefixLift 1975639
  have htrace : WordTrace (prefixWord ++ tailWord_1975639) baseStart_1975639 baseEnd_1975639 := by
    simpa [prefixWord, tailWord_1975639, baseEnd_1975639] using wordTrace_append hprefix tailTrace_1975639
  have hstable : (prefixWord ++ tailWord_1975639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975639).length < 2 ^ (prefixWord ++ tailWord_1975639).sum := by decide
  have hdescent : baseEnd_1975639 < baseStart_1975639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975697 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1975697 : Nat := 118140960795 + 1975697 * 2 ^ 59
def prefixEnd_1975697 : Nat := 4983230072969 + 3 ^ 40 * 1975697 * 2
def baseEnd_1975697 : Nat := 676321459097374540067627

theorem tailTrace_1975697 : CollatzResearch.WordTrace tailWord_1975697 prefixEnd_1975697 676321459097374540067627 := by
  unfold tailWord_1975697
  simp only [CollatzResearch.WordTrace]
  refine ⟨72059589523394666029157345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48039726348929777352771563 72059589523394666029157345)
  ·
    refine ⟨54044692142545999521868009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72059589523394666029157345 54044692142545999521868009)
    ·
      refine ⟨40533519106909499641401007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54044692142545999521868009 40533519106909499641401007)
      ·
        refine ⟨60800278660364249462101511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40533519106909499641401007 60800278660364249462101511)
        ·
          refine ⟨91200417990546374193152267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60800278660364249462101511 91200417990546374193152267)
          ·
            refine ⟨136800626985819561289728401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91200417990546374193152267 136800626985819561289728401)
            ·
              refine ⟨102600470239364670967296301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136800626985819561289728401 102600470239364670967296301)
              ·
                refine ⟨38475176339761751612736113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102600470239364670967296301 38475176339761751612736113)
                ·
                  refine ⟨28856382254821313709552085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38475176339761751612736113 28856382254821313709552085)
                  ·
                    refine ⟨676321459097374540067627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28856382254821313709552085 676321459097374540067627)
                    ·
                      rfl

theorem cell22_1975697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1975697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975697 prefixEnd_1975697 := by exact prefixLift 1975697
  have htrace : WordTrace (prefixWord ++ tailWord_1975697) baseStart_1975697 baseEnd_1975697 := by
    simpa [prefixWord, tailWord_1975697, baseEnd_1975697] using wordTrace_append hprefix tailTrace_1975697
  have hstable : (prefixWord ++ tailWord_1975697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975697).length < 2 ^ (prefixWord ++ tailWord_1975697).sum := by decide
  have hdescent : baseEnd_1975697 < baseStart_1975697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975744 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 5]
def baseStart_1975744 : Nat := 118140960795 + 1975744 * 2 ^ 59
def prefixEnd_1975744 : Nat := 4983230072969 + 3 ^ 40 * 1975744 * 2
def baseEnd_1975744 : Nat := 225445849385960694714161

theorem tailTrace_1975744 : CollatzResearch.WordTrace tailWord_1975744 prefixEnd_1975744 225445849385960694714161 := by
  unfold tailWord_1975744
  simp only [CollatzResearch.WordTrace]
  refine ⟨36030651877112196528059143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48040869169482928704078857 36030651877112196528059143)
  ·
    refine ⟨54045977815668294792088715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36030651877112196528059143 54045977815668294792088715)
    ·
      refine ⟨81068966723502442188133073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54045977815668294792088715 81068966723502442188133073)
      ·
        refine ⟨60801725042626831641099805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81068966723502442188133073 60801725042626831641099805)
        ·
          refine ⟨22800646890985061865412427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60801725042626831641099805 22800646890985061865412427)
          ·
            refine ⟨34200970336477592798118641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22800646890985061865412427 34200970336477592798118641)
            ·
              refine ⟨25650727752358194598588981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34200970336477592798118641 25650727752358194598588981)
              ·
                refine ⟨2404755726783580743617717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25650727752358194598588981 2404755726783580743617717)
                ·
                  refine ⟨225445849385960694714161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2404755726783580743617717 225445849385960694714161)
                  ·
                    rfl

theorem cell22_1975744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_1975744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975744 prefixEnd_1975744 := by exact prefixLift 1975744
  have htrace : WordTrace (prefixWord ++ tailWord_1975744) baseStart_1975744 baseEnd_1975744 := by
    simpa [prefixWord, tailWord_1975744, baseEnd_1975744] using wordTrace_append hprefix tailTrace_1975744
  have hstable : (prefixWord ++ tailWord_1975744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975744).length < 2 ^ (prefixWord ++ tailWord_1975744).sum := by decide
  have hdescent : baseEnd_1975744 < baseStart_1975744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975748 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1975748 : Nat := 118140960795 + 1975748 * 2 ^ 59
def prefixEnd_1975748 : Nat := 4983230072969 + 3 ^ 40 * 1975748 * 2
def baseEnd_1975748 : Nat := 676338917439627407042471

theorem tailTrace_1975748 : CollatzResearch.WordTrace tailWord_1975748 prefixEnd_1975748 676338917439627407042471 := by
  unfold tailWord_1975748
  simp only [CollatzResearch.WordTrace]
  refine ⟨36030724823104950869631949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48040966430806601159509265 36030724823104950869631949)
  ·
    refine ⟨13511521808664356576111981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36030724823104950869631949 13511521808664356576111981)
    ·
      refine ⟨5066820678249133716041993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13511521808664356576111981 5066820678249133716041993)
      ·
        refine ⟨3800115508686850287031495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5066820678249133716041993 3800115508686850287031495)
        ·
          refine ⟨5700173263030275430547243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800115508686850287031495 5700173263030275430547243)
          ·
            refine ⟨8550259894545413145820865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700173263030275430547243 8550259894545413145820865)
            ·
              refine ⟨6412694920909059859365649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550259894545413145820865 6412694920909059859365649)
              ·
                refine ⟨4809521190681794894524237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412694920909059859365649 4809521190681794894524237)
                ·
                  refine ⟨1803570446505673085446589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4809521190681794894524237 1803570446505673085446589)
                  ·
                    refine ⟨676338917439627407042471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1803570446505673085446589 676338917439627407042471)
                    ·
                      rfl

theorem cell22_1975748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1975748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975748 prefixEnd_1975748 := by exact prefixLift 1975748
  have htrace : WordTrace (prefixWord ++ tailWord_1975748) baseStart_1975748 baseEnd_1975748 := by
    simpa [prefixWord, tailWord_1975748, baseEnd_1975748] using wordTrace_append hprefix tailTrace_1975748
  have hstable : (prefixWord ++ tailWord_1975748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975748).length < 2 ^ (prefixWord ++ tailWord_1975748).sum := by decide
  have hdescent : baseEnd_1975748 < baseStart_1975748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975836 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1975836 : Nat := 118140960795 + 1975836 * 2 ^ 59
def prefixEnd_1975836 : Nat := 4983230072969 + 3 ^ 40 * 1975836 * 2
def baseEnd_1975836 : Nat := 676369041638024510842201

theorem tailTrace_1975836 : CollatzResearch.WordTrace tailWord_1975836 prefixEnd_1975836 676369041638024510842201 := by
  unfold tailWord_1975836
  simp only [CollatzResearch.WordTrace]
  refine ⟨36032329634945546384233681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48043106179927395178978241 36032329634945546384233681)
  ·
    refine ⟨27024247226209159788175261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36032329634945546384233681 27024247226209159788175261)
    ·
      refine ⟨10134092709828434920565723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27024247226209159788175261 10134092709828434920565723)
      ·
        refine ⟨15201139064742652380848585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10134092709828434920565723 15201139064742652380848585)
        ·
          refine ⟨11400854298556989285636439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15201139064742652380848585 11400854298556989285636439)
          ·
            refine ⟨17101281447835483928454659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400854298556989285636439 17101281447835483928454659)
            ·
              refine ⟨25651922171753225892681989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17101281447835483928454659 25651922171753225892681989)
              ·
                refine ⟨4809735407203729854877873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25651922171753225892681989 4809735407203729854877873)
                ·
                  refine ⟨3607301555402797391158405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4809735407203729854877873 3607301555402797391158405)
                  ·
                    refine ⟨676369041638024510842201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607301555402797391158405 676369041638024510842201)
                    ·
                      rfl

theorem cell22_1975836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1975836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975836 prefixEnd_1975836 := by exact prefixLift 1975836
  have htrace : WordTrace (prefixWord ++ tailWord_1975836) baseStart_1975836 baseEnd_1975836 := by
    simpa [prefixWord, tailWord_1975836, baseEnd_1975836] using wordTrace_append hprefix tailTrace_1975836
  have hstable : (prefixWord ++ tailWord_1975836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975836).length < 2 ^ (prefixWord ++ tailWord_1975836).sum := by decide
  have hdescent : baseEnd_1975836 < baseStart_1975836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975840 : List Nat := [2, 1, 1, 6, 1, 1, 4, 2, 4]
def baseStart_1975840 : Nat := 118140960795 + 1975840 * 2 ^ 59
def prefixEnd_1975840 : Nat := 4983230072969 + 3 ^ 40 * 1975840 * 2
def baseEnd_1975840 : Nat := 225456803639923277914063

theorem tailTrace_1975840 : CollatzResearch.WordTrace tailWord_1975840 prefixEnd_1975840 225456803639923277914063 := by
  unfold tailWord_1975840
  simp only [CollatzResearch.WordTrace]
  refine ⟨36032402580938300725806487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48043203441251067634408649 36032402580938300725806487)
  ·
    refine ⟨54048603871407451088709731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36032402580938300725806487 54048603871407451088709731)
    ·
      refine ⟨81072905807111176633064597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54048603871407451088709731 81072905807111176633064597)
      ·
        refine ⟨3800292459708336404674903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81072905807111176633064597 3800292459708336404674903)
        ·
          refine ⟨5700438689562504607012355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800292459708336404674903 5700438689562504607012355)
          ·
            refine ⟨8550658034343756910518533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700438689562504607012355 8550658034343756910518533)
            ·
              refine ⟨1603248381439454420722225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8550658034343756910518533 1603248381439454420722225)
              ·
                refine ⟨1202436286079590815541669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603248381439454420722225 1202436286079590815541669)
                ·
                  refine ⟨225456803639923277914063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202436286079590815541669 225456803639923277914063)
                  ·
                    rfl

theorem cell22_1975840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 4].length) (baseStart_1975840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975840 prefixEnd_1975840 := by exact prefixLift 1975840
  have htrace : WordTrace (prefixWord ++ tailWord_1975840) baseStart_1975840 baseEnd_1975840 := by
    simpa [prefixWord, tailWord_1975840, baseEnd_1975840] using wordTrace_append hprefix tailTrace_1975840
  have hstable : (prefixWord ++ tailWord_1975840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975840).length < 2 ^ (prefixWord ++ tailWord_1975840).sum := by decide
  have hdescent : baseEnd_1975840 < baseStart_1975840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975868 : List Nat := [2, 2, 2, 2, 4, 1, 3, 6]
def baseStart_1975868 : Nat := 118140960795 + 1975868 * 2 ^ 59
def prefixEnd_1975868 : Nat := 4983230072969 + 3 ^ 40 * 1975868 * 2
def baseEnd_1975868 : Nat := 75153332876887454893567

theorem tailTrace_1975868 : CollatzResearch.WordTrace tailWord_1975868 prefixEnd_1975868 75153332876887454893567 := by
  unfold tailWord_1975868
  simp only [CollatzResearch.WordTrace]
  refine ⟨36032913202887581116816129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48043884270516774822421505 36032913202887581116816129)
  ·
    refine ⟨27024684902165685837612097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36032913202887581116816129 27024684902165685837612097)
    ·
      refine ⟨20268513676624264378209073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27024684902165685837612097 20268513676624264378209073)
      ·
        refine ⟨15201385257468198283656805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20268513676624264378209073 15201385257468198283656805)
        ·
          refine ⟨2850259735775287178185651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15201385257468198283656805 2850259735775287178185651)
          ·
            refine ⟨4275389603662930767278477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850259735775287178185651 4275389603662930767278477)
            ·
              refine ⟨1603271101373599037729429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4275389603662930767278477 1603271101373599037729429)
              ·
                refine ⟨75153332876887454893567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1603271101373599037729429 75153332876887454893567)
                ·
                  rfl

theorem cell22_1975868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 6].length) (baseStart_1975868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975868 prefixEnd_1975868 := by exact prefixLift 1975868
  have htrace : WordTrace (prefixWord ++ tailWord_1975868) baseStart_1975868 baseEnd_1975868 := by
    simpa [prefixWord, tailWord_1975868, baseEnd_1975868] using wordTrace_append hprefix tailTrace_1975868
  have hstable : (prefixWord ++ tailWord_1975868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975868).length < 2 ^ (prefixWord ++ tailWord_1975868).sum := by decide
  have hdescent : baseEnd_1975868 < baseStart_1975868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975900 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1975900 : Nat := 118140960795 + 1975900 * 2 ^ 59
def prefixEnd_1975900 : Nat := 4983230072969 + 3 ^ 40 * 1975900 * 2
def baseEnd_1975900 : Nat := 676390950145949677242005

theorem tailTrace_1975900 : CollatzResearch.WordTrace tailWord_1975900 prefixEnd_1975900 676390950145949677242005 := by
  unfold tailWord_1975900
  simp only [CollatzResearch.WordTrace]
  refine ⟨36033496770829615849398577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48044662361106154465864769 36033496770829615849398577)
  ·
    refine ⟨27025122578122211887048933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36033496770829615849398577 27025122578122211887048933)
    ·
      refine ⟨5067210483397914728821675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27025122578122211887048933 5067210483397914728821675)
      ·
        refine ⟨7600815725096872093232513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067210483397914728821675 7600815725096872093232513)
        ·
          refine ⟨5700611793822654069924385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7600815725096872093232513 5700611793822654069924385)
          ·
            refine ⟨4275458845366990552443289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5700611793822654069924385 4275458845366990552443289)
            ·
              refine ⟨3206594134025242914332467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4275458845366990552443289 3206594134025242914332467)
              ·
                refine ⟨4809891201037864371498701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206594134025242914332467 4809891201037864371498701)
                ·
                  refine ⟨1803709200389199139312013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4809891201037864371498701 1803709200389199139312013)
                  ·
                    refine ⟨676390950145949677242005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1803709200389199139312013 676390950145949677242005)
                    ·
                      rfl

theorem cell22_1975900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1975900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975900 prefixEnd_1975900 := by exact prefixLift 1975900
  have htrace : WordTrace (prefixWord ++ tailWord_1975900) baseStart_1975900 baseEnd_1975900 := by
    simpa [prefixWord, tailWord_1975900, baseEnd_1975900] using wordTrace_append hprefix tailTrace_1975900
  have hstable : (prefixWord ++ tailWord_1975900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975900).length < 2 ^ (prefixWord ++ tailWord_1975900).sum := by decide
  have hdescent : baseEnd_1975900 < baseStart_1975900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975911 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1975911 : Nat := 118140960795 + 1975911 * 2 ^ 59
def prefixEnd_1975911 : Nat := 4983230072969 + 3 ^ 40 * 1975911 * 2
def baseEnd_1975911 : Nat := 676394715670749315216971

theorem tailTrace_1975911 : CollatzResearch.WordTrace tailWord_1975911 prefixEnd_1975911 676394715670749315216971 := by
  unfold tailWord_1975911
  simp only [CollatzResearch.WordTrace]
  refine ⟨72067394744619380577447587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48044929829746253718298391 72067394744619380577447587)
  ·
    refine ⟨108101092116929070866171381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72067394744619380577447587 108101092116929070866171381)
    ·
      refine ⟨10134477385962100393703567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108101092116929070866171381 10134477385962100393703567)
      ·
        refine ⟨15201716078943150590555351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10134477385962100393703567 15201716078943150590555351)
        ·
          refine ⟨22802574118414725885833027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15201716078943150590555351 22802574118414725885833027)
          ·
            refine ⟨34203861177622088828749541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22802574118414725885833027 34203861177622088828749541)
            ·
              refine ⟨6413223970804141655390539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34203861177622088828749541 6413223970804141655390539)
              ·
                refine ⟨9619835956206212483085809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413223970804141655390539 9619835956206212483085809)
                ·
                  refine ⟨7214876967154659362314357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9619835956206212483085809 7214876967154659362314357)
                  ·
                    refine ⟨676394715670749315216971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7214876967154659362314357 676394715670749315216971)
                    ·
                      rfl

theorem cell22_1975911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1975911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975911 prefixEnd_1975911 := by exact prefixLift 1975911
  have htrace : WordTrace (prefixWord ++ tailWord_1975911) baseStart_1975911 baseEnd_1975911 := by
    simpa [prefixWord, tailWord_1975911, baseEnd_1975911] using wordTrace_append hprefix tailTrace_1975911
  have hstable : (prefixWord ++ tailWord_1975911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975911).length < 2 ^ (prefixWord ++ tailWord_1975911).sum := by decide
  have hdescent : baseEnd_1975911 < baseStart_1975911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975943 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1975943 : Nat := 118140960795 + 1975943 * 2 ^ 59
def prefixEnd_1975943 : Nat := 4983230072969 + 3 ^ 40 * 1975943 * 2
def baseEnd_1975943 : Nat := 676405669924711898416873

theorem tailTrace_1975943 : CollatzResearch.WordTrace tailWord_1975943 prefixEnd_1975943 676405669924711898416873 := by
  unfold tailWord_1975943
  simp only [CollatzResearch.WordTrace]
  refine ⟨72068561880503450042612483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48045707920335633361741655 72068561880503450042612483)
  ·
    refine ⟨108102842820755175063918725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72068561880503450042612483 108102842820755175063918725)
    ·
      refine ⟨20269283028891595324484761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108102842820755175063918725 20269283028891595324484761)
      ·
        refine ⟨15201962271668696493363571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20269283028891595324484761 15201962271668696493363571)
        ·
          refine ⟨22802943407503044740045357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15201962271668696493363571 22802943407503044740045357)
          ·
            refine ⟨8551103777813641777517009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22802943407503044740045357 8551103777813641777517009)
            ·
              refine ⟨6413327833360231333137757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8551103777813641777517009 6413327833360231333137757)
              ·
                refine ⟨2404997937510086749926659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6413327833360231333137757 2404997937510086749926659)
                ·
                  refine ⟨3607496906265130124889989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404997937510086749926659 3607496906265130124889989)
                  ·
                    refine ⟨676405669924711898416873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607496906265130124889989 676405669924711898416873)
                    ·
                      rfl

theorem cell22_1975943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1975943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975943 prefixEnd_1975943 := by exact prefixLift 1975943
  have htrace : WordTrace (prefixWord ++ tailWord_1975943) baseStart_1975943 baseEnd_1975943 := by
    simpa [prefixWord, tailWord_1975943, baseEnd_1975943] using wordTrace_append hprefix tailTrace_1975943
  have hstable : (prefixWord ++ tailWord_1975943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975943).length < 2 ^ (prefixWord ++ tailWord_1975943).sum := by decide
  have hdescent : baseEnd_1975943 < baseStart_1975943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975971 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 4, 4]
def baseStart_1975971 : Nat := 118140960795 + 1975971 * 2 ^ 59
def prefixEnd_1975971 : Nat := 4983230072969 + 3 ^ 40 * 1975971 * 2
def baseEnd_1975971 : Nat := 676415254896929158716787

theorem tailTrace_1975971 : CollatzResearch.WordTrace tailWord_1975971 prefixEnd_1975971 676415254896929158716787 := by
  unfold tailWord_1975971
  simp only [CollatzResearch.WordTrace]
  refine ⟨72069583124402010824631767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48046388749601340549754511 72069583124402010824631767)
  ·
    refine ⟨108104374686603016236947651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72069583124402010824631767 108104374686603016236947651)
    ·
      refine ⟨162156562029904524355421477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108104374686603016236947651 162156562029904524355421477)
      ·
        refine ⟨30404355380607098316641527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162156562029904524355421477 30404355380607098316641527)
        ·
          refine ⟨45606533070910647474962291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30404355380607098316641527 45606533070910647474962291)
          ·
            refine ⟨68409799606365971212443437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45606533070910647474962291 68409799606365971212443437)
            ·
              refine ⟨25653674852387239204666289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68409799606365971212443437 25653674852387239204666289)
              ·
                refine ⟨19240256139290429403499717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25653674852387239204666289 19240256139290429403499717)
                ·
                  refine ⟨3607548026116955513156197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19240256139290429403499717 3607548026116955513156197)
                  ·
                    refine ⟨676415254896929158716787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607548026116955513156197 676415254896929158716787)
                    ·
                      rfl

theorem cell22_1975971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 4].length) (baseStart_1975971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975971 prefixEnd_1975971 := by exact prefixLift 1975971
  have htrace : WordTrace (prefixWord ++ tailWord_1975971) baseStart_1975971 baseEnd_1975971 := by
    simpa [prefixWord, tailWord_1975971, baseEnd_1975971] using wordTrace_append hprefix tailTrace_1975971
  have hstable : (prefixWord ++ tailWord_1975971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975971).length < 2 ^ (prefixWord ++ tailWord_1975971).sum := by decide
  have hdescent : baseEnd_1975971 < baseStart_1975971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975986 : List Nat := [3, 2, 1, 1, 1, 2, 4, 8]
def baseStart_1975986 : Nat := 118140960795 + 1975986 * 2 ^ 59
def prefixEnd_1975986 : Nat := 4983230072969 + 3 ^ 40 * 1975986 * 2
def baseEnd_1975986 : Nat := 75157821078163791065749

theorem tailTrace_1975986 : CollatzResearch.WordTrace tailWord_1975986 prefixEnd_1975986 75157821078163791065749 := by
  unfold tailWord_1975986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017532554836917096606953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48046753479565112257618541 18017532554836917096606953)
  ·
    refine ⟨13513149416127687822455215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18017532554836917096606953 13513149416127687822455215)
    ·
      refine ⟨20269724124191531733682823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13513149416127687822455215 20269724124191531733682823)
      ·
        refine ⟨30404586186287297600524235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20269724124191531733682823 30404586186287297600524235)
        ·
          refine ⟨45606879279430946400786353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30404586186287297600524235 45606879279430946400786353)
          ·
            refine ⟨34205159459573209800589765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45606879279430946400786353 34205159459573209800589765)
            ·
              refine ⟨6413467398669976837610581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34205159459573209800589765 6413467398669976837610581)
              ·
                refine ⟨75157821078163791065749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6413467398669976837610581 75157821078163791065749)
                ·
                  rfl

theorem cell22_1975986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_1975986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975986 prefixEnd_1975986 := by exact prefixLift 1975986
  have htrace : WordTrace (prefixWord ++ tailWord_1975986) baseStart_1975986 baseEnd_1975986 := by
    simpa [prefixWord, tailWord_1975986, baseEnd_1975986] using wordTrace_append hprefix tailTrace_1975986
  have hstable : (prefixWord ++ tailWord_1975986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975986).length < 2 ^ (prefixWord ++ tailWord_1975986).sum := by decide
  have hdescent : baseEnd_1975986 < baseStart_1975986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975990 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1975990 : Nat := 118140960795 + 1975990 * 2 ^ 59
def prefixEnd_1975990 : Nat := 4983230072969 + 3 ^ 40 * 1975990 * 2
def baseEnd_1975990 : Nat := 676421758985219442491729

theorem tailTrace_1975990 : CollatzResearch.WordTrace tailWord_1975990 prefixEnd_1975990 676421758985219442491729 := by
  unfold tailWord_1975990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4504392256958323566848339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48046850740888784713048949 4504392256958323566848339)
  ·
    refine ⟨6756588385437485350272509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4504392256958323566848339 6756588385437485350272509)
    ·
      refine ⟨2533720644539057006352191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6756588385437485350272509 2533720644539057006352191)
      ·
        refine ⟨3800580966808585509528287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533720644539057006352191 3800580966808585509528287)
        ·
          refine ⟨5700871450212878264292431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800580966808585509528287 5700871450212878264292431)
          ·
            refine ⟨8551307175319317396438647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700871450212878264292431 8551307175319317396438647)
            ·
              refine ⟨12826960762978976094657971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8551307175319317396438647 12826960762978976094657971)
              ·
                refine ⟨19240441144468464141986957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12826960762978976094657971 19240441144468464141986957)
                ·
                  refine ⟨7215165429175674053245109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19240441144468464141986957 7215165429175674053245109)
                  ·
                    refine ⟨676421758985219442491729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7215165429175674053245109 676421758985219442491729)
                    ·
                      rfl

theorem cell22_1975990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1975990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1975990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1975990 prefixEnd_1975990 := by exact prefixLift 1975990
  have htrace : WordTrace (prefixWord ++ tailWord_1975990) baseStart_1975990 baseEnd_1975990 := by
    simpa [prefixWord, tailWord_1975990, baseEnd_1975990] using wordTrace_append hprefix tailTrace_1975990
  have hstable : (prefixWord ++ tailWord_1975990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975990).length < 2 ^ (prefixWord ++ tailWord_1975990).sum := by decide
  have hdescent : baseEnd_1975990 < baseStart_1975990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976020 : List Nat := [2, 4, 1, 3, 1, 3, 1, 7]
def baseStart_1976020 : Nat := 118140960795 + 1976020 * 2 ^ 59
def prefixEnd_1976020 : Nat := 4983230072969 + 3 ^ 40 * 1976020 * 2
def baseEnd_1976020 : Nat := 75159114288701040471293

theorem tailTrace_1976020 : CollatzResearch.WordTrace tailWord_1976020 prefixEnd_1976020 75159114288701040471293 := by
  unfold tailWord_1976020
  simp only [CollatzResearch.WordTrace]
  refine ⟨36035685150612246096582757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48047580200816328128777009 36035685150612246096582757)
  ·
    refine ⟨6756690965739796143109267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36035685150612246096582757 6756690965739796143109267)
    ·
      refine ⟨10135036448609694214663901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6756690965739796143109267 10135036448609694214663901)
      ·
        refine ⟨3800638668228635330498963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10135036448609694214663901 3800638668228635330498963)
        ·
          refine ⟨5700958002342952995748445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800638668228635330498963 5700958002342952995748445)
          ·
            refine ⟨2137859250878607373405667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5700958002342952995748445 2137859250878607373405667)
            ·
              refine ⟨3206788876317911060108501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137859250878607373405667 3206788876317911060108501)
              ·
                refine ⟨75159114288701040471293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3206788876317911060108501 75159114288701040471293)
                ·
                  rfl

theorem cell22_1976020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 7].length) (baseStart_1976020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976020 prefixEnd_1976020 := by exact prefixLift 1976020
  have htrace : WordTrace (prefixWord ++ tailWord_1976020) baseStart_1976020 baseEnd_1976020 := by
    simpa [prefixWord, tailWord_1976020, baseEnd_1976020] using wordTrace_append hprefix tailTrace_1976020
  have hstable : (prefixWord ++ tailWord_1976020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976020).length < 2 ^ (prefixWord ++ tailWord_1976020).sum := by decide
  have hdescent : baseEnd_1976020 < baseStart_1976020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976039 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1976039 : Nat := 118140960795 + 1976039 * 2 ^ 59
def prefixEnd_1976039 : Nat := 4983230072969 + 3 ^ 40 * 1976039 * 2
def baseEnd_1976039 : Nat := 676438532686599648016579

theorem tailTrace_1976039 : CollatzResearch.WordTrace tailWord_1976039 prefixEnd_1976039 676438532686599648016579 := by
  unfold tailWord_1976039
  simp only [CollatzResearch.WordTrace]
  refine ⟨72072063288155658438107171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48048042192103772292071447 72072063288155658438107171)
  ·
    refine ⟨108108094932233487657160757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72072063288155658438107171 108108094932233487657160757)
    ·
      refine ⟨10135133899896889467858821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108108094932233487657160757 10135133899896889467858821)
      ·
        refine ⟨1900337606230666775223529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10135133899896889467858821 1900337606230666775223529)
        ·
          refine ⟨1425253204673000081417647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1900337606230666775223529 1425253204673000081417647)
          ·
            refine ⟨2137879807009500122126471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425253204673000081417647 2137879807009500122126471)
            ·
              refine ⟨3206819710514250183189707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137879807009500122126471 3206819710514250183189707)
              ·
                refine ⟨4810229565771375274784561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206819710514250183189707 4810229565771375274784561)
                ·
                  refine ⟨3607672174328531456088421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4810229565771375274784561 3607672174328531456088421)
                  ·
                    refine ⟨676438532686599648016579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607672174328531456088421 676438532686599648016579)
                    ·
                      rfl

theorem cell22_1976039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1976039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976039 prefixEnd_1976039 := by exact prefixLift 1976039
  have htrace : WordTrace (prefixWord ++ tailWord_1976039) baseStart_1976039 baseEnd_1976039 := by
    simpa [prefixWord, tailWord_1976039, baseEnd_1976039] using wordTrace_append hprefix tailTrace_1976039
  have hstable : (prefixWord ++ tailWord_1976039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976039).length < 2 ^ (prefixWord ++ tailWord_1976039).sum := by decide
  have hdescent : baseEnd_1976039 < baseStart_1976039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976078 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1976078 : Nat := 118140960795 + 1976078 * 2 ^ 59
def prefixEnd_1976078 : Nat := 4983230072969 + 3 ^ 40 * 1976078 * 2
def baseEnd_1976078 : Nat := 676451883183616546291459

theorem tailTrace_1976078 : CollatzResearch.WordTrace tailWord_1976078 prefixEnd_1976078 676451883183616546291459 := by
  unfold tailWord_1976078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9009185716876796012347111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48048990490009578732517925 9009185716876796012347111)
  ·
    refine ⟨13513778575315194018520667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9009185716876796012347111 13513778575315194018520667)
    ·
      refine ⟨20270667862972791027781001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13513778575315194018520667 20270667862972791027781001)
      ·
        refine ⟨15203000897229593270835751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20270667862972791027781001 15203000897229593270835751)
        ·
          refine ⟨22804501345844389906253627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15203000897229593270835751 22804501345844389906253627)
          ·
            refine ⟨34206752018766584859380441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22804501345844389906253627 34206752018766584859380441)
            ·
              refine ⟨25655064014074938644535331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34206752018766584859380441 25655064014074938644535331)
              ·
                refine ⟨38482596021112407966802997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25655064014074938644535331 38482596021112407966802997)
                ·
                  refine ⟨3607743376979288246887781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38482596021112407966802997 3607743376979288246887781)
                  ·
                    refine ⟨676451883183616546291459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607743376979288246887781 676451883183616546291459)
                    ·
                      rfl

theorem cell22_1976078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1976078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976078 prefixEnd_1976078 := by exact prefixLift 1976078
  have htrace : WordTrace (prefixWord ++ tailWord_1976078) baseStart_1976078 baseEnd_1976078 := by
    simpa [prefixWord, tailWord_1976078, baseEnd_1976078] using wordTrace_append hprefix tailTrace_1976078
  have hstable : (prefixWord ++ tailWord_1976078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976078).length < 2 ^ (prefixWord ++ tailWord_1976078).sum := by decide
  have hdescent : baseEnd_1976078 < baseStart_1976078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976095 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 1, 4]
def baseStart_1976095 : Nat := 118140960795 + 1976095 * 2 ^ 59
def prefixEnd_1976095 : Nat := 4983230072969 + 3 ^ 40 * 1976095 * 2
def baseEnd_1976095 : Nat := 676457702631034168616407

theorem tailTrace_1976095 : CollatzResearch.WordTrace tailWord_1976095 prefixEnd_1976095 676457702631034168616407 := by
  unfold tailWord_1976095
  simp only [CollatzResearch.WordTrace]
  refine ⟨72074105775952780002145739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48049403850635186668097159 72074105775952780002145739)
  ·
    refine ⟨108111158663929170003218609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72074105775952780002145739 108111158663929170003218609)
    ·
      refine ⟨81083368997946877502413957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108111158663929170003218609 81083368997946877502413957)
      ·
        refine ⟨15203131687115039531702617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81083368997946877502413957 15203131687115039531702617)
        ·
          refine ⟨11402348765336279648776963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15203131687115039531702617 11402348765336279648776963)
          ·
            refine ⟨17103523148004419473165445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11402348765336279648776963 17103523148004419473165445)
            ·
              refine ⟨3206910590250828651218521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17103523148004419473165445 3206910590250828651218521)
              ·
                refine ⟨2405182942688121488413891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206910590250828651218521 2405182942688121488413891)
                ·
                  refine ⟨3607774414032182232620837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405182942688121488413891 3607774414032182232620837)
                  ·
                    refine ⟨676457702631034168616407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3607774414032182232620837 676457702631034168616407)
                    ·
                      rfl

theorem cell22_1976095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_1976095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976095 prefixEnd_1976095 := by exact prefixLift 1976095
  have htrace : WordTrace (prefixWord ++ tailWord_1976095) baseStart_1976095 baseEnd_1976095 := by
    simpa [prefixWord, tailWord_1976095, baseEnd_1976095] using wordTrace_append hprefix tailTrace_1976095
  have hstable : (prefixWord ++ tailWord_1976095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976095).length < 2 ^ (prefixWord ++ tailWord_1976095).sum := by decide
  have hdescent : baseEnd_1976095 < baseStart_1976095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976127 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 6]
def baseStart_1976127 : Nat := 118140960795 + 1976127 * 2 ^ 59
def prefixEnd_1976127 : Nat := 4983230072969 + 3 ^ 40 * 1976127 * 2
def baseEnd_1976127 : Nat := 225489552294998917272103

theorem tailTrace_1976127 : CollatzResearch.WordTrace tailWord_1976127 prefixEnd_1976127 225489552294998917272103 := by
  unfold tailWord_1976127
  simp only [CollatzResearch.WordTrace]
  refine ⟨72075272911836849467310635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48050181941224566311540423 72075272911836849467310635)
  ·
    refine ⟨108112909367755274200965953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72075272911836849467310635 108112909367755274200965953)
    ·
      refine ⟨81084682025816455650724465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108112909367755274200965953 81084682025816455650724465)
      ·
        refine ⟨60813511519362341738043349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81084682025816455650724465 60813511519362341738043349)
        ·
          refine ⟨1425316676235054884485391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 60813511519362341738043349 1425316676235054884485391)
          ·
            refine ⟨2137975014352582326728087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425316676235054884485391 2137975014352582326728087)
            ·
              refine ⟨3206962521528873490092131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137975014352582326728087 3206962521528873490092131)
              ·
                refine ⟨4810443782293310235138197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206962521528873490092131 4810443782293310235138197)
                ·
                  refine ⟨225489552294998917272103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4810443782293310235138197 225489552294998917272103)
                  ·
                    rfl

theorem cell22_1976127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 6].length) (baseStart_1976127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976127 prefixEnd_1976127 := by exact prefixLift 1976127
  have htrace : WordTrace (prefixWord ++ tailWord_1976127) baseStart_1976127 baseEnd_1976127 := by
    simpa [prefixWord, tailWord_1976127, baseEnd_1976127] using wordTrace_append hprefix tailTrace_1976127
  have hstable : (prefixWord ++ tailWord_1976127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976127).length < 2 ^ (prefixWord ++ tailWord_1976127).sum := by decide
  have hdescent : baseEnd_1976127 < baseStart_1976127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976138 : List Nat := [3, 1, 2, 1, 1, 1, 6, 7]
def baseStart_1976138 : Nat := 118140960795 + 1976138 * 2 ^ 59
def prefixEnd_1976138 : Nat := 4983230072969 + 3 ^ 40 * 1976138 * 2
def baseEnd_1976138 : Nat := 75163602489977376643475

theorem tailTrace_1976138 : CollatzResearch.WordTrace tailWord_1976138 prefixEnd_1976138 75163602489977376643475 := by
  unfold tailWord_1976138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18018918528699249586490267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48050449409864665563974045 18018918528699249586490267)
  ·
    refine ⟨27028377793048874379735401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18018918528699249586490267 27028377793048874379735401)
    ·
      refine ⟨20271283344786655784801551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27028377793048874379735401 20271283344786655784801551)
      ·
        refine ⟨30406925017179983677202327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20271283344786655784801551 30406925017179983677202327)
        ·
          refine ⟨45610387525769975515803491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30406925017179983677202327 45610387525769975515803491)
          ·
            refine ⟨68415581288654963273705237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45610387525769975515803491 68415581288654963273705237)
            ·
              refine ⟨3206980372905701403454933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68415581288654963273705237 3206980372905701403454933)
              ·
                refine ⟨75163602489977376643475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3206980372905701403454933 75163602489977376643475)
                ·
                  rfl

theorem cell22_1976138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 7].length) (baseStart_1976138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976138 prefixEnd_1976138 := by exact prefixLift 1976138
  have htrace : WordTrace (prefixWord ++ tailWord_1976138) baseStart_1976138 baseEnd_1976138 := by
    simpa [prefixWord, tailWord_1976138, baseEnd_1976138] using wordTrace_append hprefix tailTrace_1976138
  have hstable : (prefixWord ++ tailWord_1976138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976138).length < 2 ^ (prefixWord ++ tailWord_1976138).sum := by decide
  have hdescent : baseEnd_1976138 < baseStart_1976138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976238 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1976238 : Nat := 118140960795 + 1976238 * 2 ^ 59
def prefixEnd_1976238 : Nat := 4983230072969 + 3 ^ 40 * 1976238 * 2
def baseEnd_1976238 : Nat := 676506654453429462290969

theorem tailTrace_1976238 : CollatzResearch.WordTrace tailWord_1976238 prefixEnd_1976238 676506654453429462290969 := by
  unfold tailWord_1976238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9009915176804339428075171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48052880942956476949734245 9009915176804339428075171)
  ·
    refine ⟨13514872765206509142112757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9009915176804339428075171 13514872765206509142112757)
    ·
      refine ⟨1267019321738110232073071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13514872765206509142112757 1267019321738110232073071)
      ·
        refine ⟨1900528982607165348109607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267019321738110232073071 1900528982607165348109607)
        ·
          refine ⟨2850793473910748022164411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900528982607165348109607 2850793473910748022164411)
          ·
            refine ⟨4276190210866122033246617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850793473910748022164411 4276190210866122033246617)
            ·
              refine ⟨3207142658149591524934963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4276190210866122033246617 3207142658149591524934963)
              ·
                refine ⟨4810713987224387287402445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207142658149591524934963 4810713987224387287402445)
                ·
                  refine ⟨1804017745209145232775917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4810713987224387287402445 1804017745209145232775917)
                  ·
                    refine ⟨676506654453429462290969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1804017745209145232775917 676506654453429462290969)
                    ·
                      rfl

theorem cell22_1976238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1976238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976238 prefixEnd_1976238 := by exact prefixLift 1976238
  have htrace : WordTrace (prefixWord ++ tailWord_1976238) baseStart_1976238 baseEnd_1976238 := by
    simpa [prefixWord, tailWord_1976238, baseEnd_1976238] using wordTrace_append hprefix tailTrace_1976238
  have hstable : (prefixWord ++ tailWord_1976238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976238).length < 2 ^ (prefixWord ++ tailWord_1976238).sum := by decide
  have hdescent : baseEnd_1976238 < baseStart_1976238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976245 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 6]
def baseStart_1976245 : Nat := 118140960795 + 1976245 * 2 ^ 59
def prefixEnd_1976245 : Nat := 4983230072969 + 3 ^ 40 * 1976245 * 2
def baseEnd_1976245 : Nat := 225503016898827925788649

theorem tailTrace_1976245 : CollatzResearch.WordTrace tailWord_1976245 prefixEnd_1976245 225503016898827925788649 := by
  unfold tailWord_1976245
  simp only [CollatzResearch.WordTrace]
  refine ⟨72079576725409355620106189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48053051150272903746737459 72079576725409355620106189)
  ·
    refine ⟨27029841272028508357539821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72079576725409355620106189 27029841272028508357539821)
    ·
      refine ⟨10136190477010690634077433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27029841272028508357539821 10136190477010690634077433)
      ·
        refine ⟨7602142857758017975558075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10136190477010690634077433 7602142857758017975558075)
        ·
          refine ⟨11403214286637026963337113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7602142857758017975558075 11403214286637026963337113)
          ·
            refine ⟨8552410714977770222502835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11403214286637026963337113 8552410714977770222502835)
            ·
              refine ⟨12828616072466655333754253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552410714977770222502835 12828616072466655333754253)
              ·
                refine ⟨4810731027174995750157845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12828616072466655333754253 4810731027174995750157845)
                ·
                  refine ⟨225503016898827925788649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4810731027174995750157845 225503016898827925788649)
                  ·
                    rfl

theorem cell22_1976245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_1976245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976245 prefixEnd_1976245 := by exact prefixLift 1976245
  have htrace : WordTrace (prefixWord ++ tailWord_1976245) baseStart_1976245 baseEnd_1976245 := by
    simpa [prefixWord, tailWord_1976245, baseEnd_1976245] using wordTrace_append hprefix tailTrace_1976245
  have hstable : (prefixWord ++ tailWord_1976245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976245).length < 2 ^ (prefixWord ++ tailWord_1976245).sum := by decide
  have hdescent : baseEnd_1976245 < baseStart_1976245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976277 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_1976277 : Nat := 118140960795 + 1976277 * 2 ^ 59
def prefixEnd_1976277 : Nat := 4983230072969 + 3 ^ 40 * 1976277 * 2
def baseEnd_1976277 : Nat := 676520004950446360565849

theorem tailTrace_1976277 : CollatzResearch.WordTrace tailWord_1976277 prefixEnd_1976277 676520004950446360565849 := by
  unfold tailWord_1976277
  simp only [CollatzResearch.WordTrace]
  refine ⟨72080743861293425085271085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48053829240862283390180723 72080743861293425085271085)
  ·
    refine ⟨27030278947985034406976657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72080743861293425085271085 27030278947985034406976657)
    ·
      refine ⟨20272709210988775805232493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27030278947985034406976657 20272709210988775805232493)
      ·
        refine ⟨7602265954120790926962185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20272709210988775805232493 7602265954120790926962185)
        ·
          refine ⟨5701699465590593195221639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7602265954120790926962185 5701699465590593195221639)
          ·
            refine ⟨8552549198385889792832459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5701699465590593195221639 8552549198385889792832459)
            ·
              refine ⟨12828823797578834689248689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552549198385889792832459 12828823797578834689248689)
              ·
                refine ⟨9621617848184126016936517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12828823797578834689248689 9621617848184126016936517)
                ·
                  refine ⟨1804053346534523628175597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9621617848184126016936517 1804053346534523628175597)
                  ·
                    refine ⟨676520004950446360565849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1804053346534523628175597 676520004950446360565849)
                    ·
                      rfl

theorem cell22_1976277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_1976277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976277 prefixEnd_1976277 := by exact prefixLift 1976277
  have htrace : WordTrace (prefixWord ++ tailWord_1976277) baseStart_1976277 baseEnd_1976277 := by
    simpa [prefixWord, tailWord_1976277, baseEnd_1976277] using wordTrace_append hprefix tailTrace_1976277
  have hstable : (prefixWord ++ tailWord_1976277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976277).length < 2 ^ (prefixWord ++ tailWord_1976277).sum := by decide
  have hdescent : baseEnd_1976277 < baseStart_1976277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976397 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1976397 : Nat := 118140960795 + 1976397 * 2 ^ 59
def prefixEnd_1976397 : Nat := 4983230072969 + 3 ^ 40 * 1976397 * 2
def baseEnd_1976397 : Nat := 225520361134268682521827

theorem tailTrace_1976397 : CollatzResearch.WordTrace tailWord_1976397 prefixEnd_1976397 225520361134268682521827 := by
  unfold tailWord_1976397
  simp only [CollatzResearch.WordTrace]
  refine ⟨72085120620858685579639445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48056747080572457053092963 72085120620858685579639445)
  ·
    refine ⟨3378990029102750886545599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72085120620858685579639445 3378990029102750886545599)
    ·
      refine ⟨5068485043654126329818399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3378990029102750886545599 5068485043654126329818399)
      ·
        refine ⟨7602727565481189494727599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5068485043654126329818399 7602727565481189494727599)
        ·
          refine ⟨11404091348221784242091399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7602727565481189494727599 11404091348221784242091399)
          ·
            refine ⟨17106137022332676363137099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11404091348221784242091399 17106137022332676363137099)
            ·
              refine ⟨25659205533499014544705649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17106137022332676363137099 25659205533499014544705649)
              ·
                refine ⟨19244404150124260908529237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25659205533499014544705649 19244404150124260908529237)
                ·
                  refine ⟨225520361134268682521827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19244404150124260908529237 225520361134268682521827)
                  ·
                    rfl

theorem cell22_1976397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1976397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976397 prefixEnd_1976397 := by exact prefixLift 1976397
  have htrace : WordTrace (prefixWord ++ tailWord_1976397) baseStart_1976397 baseEnd_1976397 := by
    simpa [prefixWord, tailWord_1976397, baseEnd_1976397] using wordTrace_append hprefix tailTrace_1976397
  have hstable : (prefixWord ++ tailWord_1976397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976397).length < 2 ^ (prefixWord ++ tailWord_1976397).sum := by decide
  have hdescent : baseEnd_1976397 < baseStart_1976397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976425 : List Nat := [1, 2, 1, 1, 1, 5, 2, 9]
def baseStart_1976425 : Nat := 118140960795 + 1976425 * 2 ^ 59
def prefixEnd_1976425 : Nat := 4983230072969 + 3 ^ 40 * 1976425 * 2
def baseEnd_1976425 : Nat := 75174518708335923096155

theorem tailTrace_1976425 : CollatzResearch.WordTrace tailWord_1976425 prefixEnd_1976425 75174518708335923096155 := by
  unfold tailWord_1976425
  simp only [CollatzResearch.WordTrace]
  refine ⟨72086141864757246361658729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48057427909838164241105819 72086141864757246361658729)
  ·
    refine ⟨54064606398567934771244047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72086141864757246361658729 54064606398567934771244047)
    ·
      refine ⟨81096909597851902156866071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54064606398567934771244047 81096909597851902156866071)
      ·
        refine ⟨121645364396777853235299107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81096909597851902156866071 121645364396777853235299107)
        ·
          refine ⟨182468046595166779852948661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121645364396777853235299107 182468046595166779852948661)
          ·
            refine ⟨17106379368296885611213937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182468046595166779852948661 17106379368296885611213937)
            ·
              refine ⟨12829784526222664208410453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17106379368296885611213937 12829784526222664208410453)
              ·
                refine ⟨75174518708335923096155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12829784526222664208410453 75174518708335923096155)
                ·
                  rfl

theorem cell22_1976425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 9].length) (baseStart_1976425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976425 prefixEnd_1976425 := by exact prefixLift 1976425
  have htrace : WordTrace (prefixWord ++ tailWord_1976425) baseStart_1976425 baseEnd_1976425 := by
    simpa [prefixWord, tailWord_1976425, baseEnd_1976425] using wordTrace_append hprefix tailTrace_1976425
  have hstable : (prefixWord ++ tailWord_1976425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976425).length < 2 ^ (prefixWord ++ tailWord_1976425).sum := by decide
  have hdescent : baseEnd_1976425 < baseStart_1976425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976440 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_1976440 : Nat := 118140960795 + 1976440 * 2 ^ 59
def prefixEnd_1976440 : Nat := 4983230072969 + 3 ^ 40 * 1976440 * 2
def baseEnd_1976440 : Nat := 676575803181568268740349

theorem tailTrace_1976440 : CollatzResearch.WordTrace tailWord_1976440 prefixEnd_1976440 676575803181568268740349 := by
  unfold tailWord_1976440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36043344479851451961727387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48057792639801935948969849 36043344479851451961727387)
  ·
    refine ⟨54065016719777177942591081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36043344479851451961727387 54065016719777177942591081)
    ·
      refine ⟨40548762539832883456943311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54065016719777177942591081 40548762539832883456943311)
      ·
        refine ⟨60823143809749325185414967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40548762539832883456943311 60823143809749325185414967)
        ·
          refine ⟨91234715714623987778122451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60823143809749325185414967 91234715714623987778122451)
          ·
            refine ⟨136852073571935981667183677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91234715714623987778122451 136852073571935981667183677)
            ·
              refine ⟨51319527589475993125193879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136852073571935981667183677 51319527589475993125193879)
              ·
                refine ⟨76979291384213989687790819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51319527589475993125193879 76979291384213989687790819)
                ·
                  refine ⟨115468937076320984531686229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76979291384213989687790819 115468937076320984531686229)
                  ·
                    refine ⟨676575803181568268740349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115468937076320984531686229 676575803181568268740349)
                    ·
                      rfl

theorem cell22_1976440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_1976440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976440 prefixEnd_1976440 := by exact prefixLift 1976440
  have htrace : WordTrace (prefixWord ++ tailWord_1976440) baseStart_1976440 baseEnd_1976440 := by
    simpa [prefixWord, tailWord_1976440, baseEnd_1976440] using wordTrace_append hprefix tailTrace_1976440
  have hstable : (prefixWord ++ tailWord_1976440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976440).length < 2 ^ (prefixWord ++ tailWord_1976440).sum := by decide
  have hdescent : baseEnd_1976440 < baseStart_1976440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976549 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 6]
def baseStart_1976549 : Nat := 118140960795 + 1976549 * 2 ^ 59
def prefixEnd_1976549 : Nat := 4983230072969 + 3 ^ 40 * 1976549 * 2
def baseEnd_1976549 : Nat := 225537705369709439255005

theorem tailTrace_1976549 : CollatzResearch.WordTrace tailWord_1976549 prefixEnd_1976549 225537705369709439255005 := by
  unfold tailWord_1976549
  simp only [CollatzResearch.WordTrace]
  refine ⟨72090664516308015539172701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48060443010872010359448467 72090664516308015539172701)
  ·
    refine ⟨27033999193615505827189763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72090664516308015539172701 27033999193615505827189763)
    ·
      refine ⟨40550998790423258740784645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27033999193615505827189763 40550998790423258740784645)
      ·
        refine ⟨7603312273204361013897121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40550998790423258740784645 7603312273204361013897121)
        ·
          refine ⟨5702484204903270760422841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7603312273204361013897121 5702484204903270760422841)
          ·
            refine ⟨4276863153677453070317131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702484204903270760422841 4276863153677453070317131)
            ·
              refine ⟨6415294730516179605475697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276863153677453070317131 6415294730516179605475697)
              ·
                refine ⟨4811471047887134704106773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6415294730516179605475697 4811471047887134704106773)
                ·
                  refine ⟨225537705369709439255005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4811471047887134704106773 225537705369709439255005)
                  ·
                    rfl

theorem cell22_1976549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_1976549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976549 prefixEnd_1976549 := by exact prefixLift 1976549
  have htrace : WordTrace (prefixWord ++ tailWord_1976549) baseStart_1976549 baseEnd_1976549 := by
    simpa [prefixWord, tailWord_1976549, baseEnd_1976549] using wordTrace_append hprefix tailTrace_1976549
  have hstable : (prefixWord ++ tailWord_1976549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976549).length < 2 ^ (prefixWord ++ tailWord_1976549).sum := by decide
  have hdescent : baseEnd_1976549 < baseStart_1976549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976566 : List Nat := [5, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1976566 : Nat := 118140960795 + 1976566 * 2 ^ 59
def prefixEnd_1976566 : Nat := 4983230072969 + 3 ^ 40 * 1976566 * 2
def baseEnd_1976566 : Nat := 225539645185515313363321

theorem tailTrace_1976566 : CollatzResearch.WordTrace tailWord_1976566 prefixEnd_1976566 225539645185515313363321 := by
  unfold tailWord_1976566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4505705284827901715158847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48060856371497618295027701 4505705284827901715158847)
  ·
    refine ⟨6758557927241852572738271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4505705284827901715158847 6758557927241852572738271)
    ·
      refine ⟨10137836890862778859107407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6758557927241852572738271 10137836890862778859107407)
      ·
        refine ⟨15206755336294168288661111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10137836890862778859107407 15206755336294168288661111)
        ·
          refine ⟨22810133004441252432991667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15206755336294168288661111 22810133004441252432991667)
          ·
            refine ⟨34215199506661878649487501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810133004441252432991667 34215199506661878649487501)
            ·
              refine ⟨12830699814998204493557813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34215199506661878649487501 12830699814998204493557813)
              ·
                refine ⟨1202878107656081671271045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12830699814998204493557813 1202878107656081671271045)
                ·
                  refine ⟨225539645185515313363321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202878107656081671271045 225539645185515313363321)
                  ·
                    rfl

theorem cell22_1976566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1976566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976566 prefixEnd_1976566 := by exact prefixLift 1976566
  have htrace : WordTrace (prefixWord ++ tailWord_1976566) baseStart_1976566 baseEnd_1976566 := by
    simpa [prefixWord, tailWord_1976566, baseEnd_1976566] using wordTrace_append hprefix tailTrace_1976566
  have hstable : (prefixWord ++ tailWord_1976566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976566).length < 2 ^ (prefixWord ++ tailWord_1976566).sum := by decide
  have hdescent : baseEnd_1976566 < baseStart_1976566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976577 : List Nat := [1, 2, 4, 1, 1, 2, 11]
def baseStart_1976577 : Nat := 118140960795 + 1976577 * 2 ^ 59
def prefixEnd_1976577 : Nat := 4983230072969 + 3 ^ 40 * 1976577 * 2
def baseEnd_1976577 : Nat := 25060100040049836224627

theorem tailTrace_1976577 : CollatzResearch.WordTrace tailWord_1976577 prefixEnd_1976577 25060100040049836224627 := by
  unfold tailWord_1976577
  simp only [CollatzResearch.WordTrace]
  refine ⟨72091685760206576321191985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48061123840137717547461323 72091685760206576321191985)
  ·
    refine ⟨54068764320154932240893989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72091685760206576321191985 54068764320154932240893989)
    ·
      refine ⟨10137893310029049795167623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54068764320154932240893989 10137893310029049795167623)
      ·
        refine ⟨15206839965043574692751435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10137893310029049795167623 15206839965043574692751435)
        ·
          refine ⟨22810259947565362039127153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15206839965043574692751435 22810259947565362039127153)
          ·
            refine ⟨17107694960674021529345365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22810259947565362039127153 17107694960674021529345365)
            ·
              refine ⟨25060100040049836224627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17107694960674021529345365 25060100040049836224627)
              ·
                rfl

theorem cell22_1976577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 11].length) (baseStart_1976577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976577 prefixEnd_1976577 := by exact prefixLift 1976577
  have htrace : WordTrace (prefixWord ++ tailWord_1976577) baseStart_1976577 baseEnd_1976577 := by
    simpa [prefixWord, tailWord_1976577, baseEnd_1976577] using wordTrace_append hprefix tailTrace_1976577
  have hstable : (prefixWord ++ tailWord_1976577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976577).length < 2 ^ (prefixWord ++ tailWord_1976577).sum := by decide
  have hdescent : baseEnd_1976577 < baseStart_1976577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976639 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 5]
def baseStart_1976639 : Nat := 118140960795 + 1976639 * 2 ^ 59
def prefixEnd_1976639 : Nat := 4983230072969 + 3 ^ 40 * 1976639 * 2
def baseEnd_1976639 : Nat := 225547974982799361004913

theorem tailTrace_1976639 : CollatzResearch.WordTrace tailWord_1976639 prefixEnd_1976639 225547974982799361004913 := by
  unfold tailWord_1976639
  simp only [CollatzResearch.WordTrace]
  refine ⟨72093947085981960909948971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48062631390654640606632647 72093947085981960909948971)
  ·
    refine ⟨108140920628972941364923457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72093947085981960909948971 108140920628972941364923457)
    ·
      refine ⟨81105690471729706023692593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108140920628972941364923457 81105690471729706023692593)
      ·
        refine ⟨60829267853797279517769445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81105690471729706023692593 60829267853797279517769445)
        ·
          refine ⟨11405487722586989909581771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60829267853797279517769445 11405487722586989909581771)
          ·
            refine ⟨17108231583880484864372657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11405487722586989909581771 17108231583880484864372657)
            ·
              refine ⟨12831173687910363648279493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17108231583880484864372657 12831173687910363648279493)
              ·
                refine ⟨2405845066483193184052405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12831173687910363648279493 2405845066483193184052405)
                ·
                  refine ⟨225547974982799361004913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2405845066483193184052405 225547974982799361004913)
                  ·
                    rfl

theorem cell22_1976639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 5].length) (baseStart_1976639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976639 prefixEnd_1976639 := by exact prefixLift 1976639
  have htrace : WordTrace (prefixWord ++ tailWord_1976639) baseStart_1976639 baseEnd_1976639 := by
    simpa [prefixWord, tailWord_1976639, baseEnd_1976639] using wordTrace_append hprefix tailTrace_1976639
  have hstable : (prefixWord ++ tailWord_1976639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976639).length < 2 ^ (prefixWord ++ tailWord_1976639).sum := by decide
  have hdescent : baseEnd_1976639 < baseStart_1976639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976656 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 5]
def baseStart_1976656 : Nat := 118140960795 + 1976656 * 2 ^ 59
def prefixEnd_1976656 : Nat := 4983230072969 + 3 ^ 40 * 1976656 * 2
def baseEnd_1976656 : Nat := 225549914798605235113229

theorem tailTrace_1976656 : CollatzResearch.WordTrace tailWord_1976656 prefixEnd_1976656 225549914798605235113229 := by
  unfold tailWord_1976656
  simp only [CollatzResearch.WordTrace]
  refine ⟨36047283563460186406658911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48063044751280248542211881 36047283563460186406658911)
  ·
    refine ⟨54070925345190279609988367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36047283563460186406658911 54070925345190279609988367)
    ·
      refine ⟨81106388017785419414982551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54070925345190279609988367 81106388017785419414982551)
      ·
        refine ⟨121659582026678129122473827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81106388017785419414982551 121659582026678129122473827)
        ·
          refine ⟨182489373040017193683710741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121659582026678129122473827 182489373040017193683710741)
          ·
            refine ⟨8554189361250805953923941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182489373040017193683710741 8554189361250805953923941)
            ·
              refine ⟨1603910505234526116360739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8554189361250805953923941 1603910505234526116360739)
              ·
                refine ⟨2405865757851789174541109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603910505234526116360739 2405865757851789174541109)
                ·
                  refine ⟨225549914798605235113229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2405865757851789174541109 225549914798605235113229)
                  ·
                    rfl

theorem cell22_1976656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_1976656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976656 prefixEnd_1976656 := by exact prefixLift 1976656
  have htrace : WordTrace (prefixWord ++ tailWord_1976656) baseStart_1976656 baseEnd_1976656 := by
    simpa [prefixWord, tailWord_1976656, baseEnd_1976656] using wordTrace_append hprefix tailTrace_1976656
  have hstable : (prefixWord ++ tailWord_1976656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976656).length < 2 ^ (prefixWord ++ tailWord_1976656).sum := by decide
  have hdescent : baseEnd_1976656 < baseStart_1976656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976716 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_1976716 : Nat := 118140960795 + 1976716 * 2 ^ 59
def prefixEnd_1976716 : Nat := 4983230072969 + 3 ^ 40 * 1976716 * 2
def baseEnd_1976716 : Nat := 676670283621995548839503

theorem tailTrace_1976716 : CollatzResearch.WordTrace tailWord_1976716 prefixEnd_1976716 676670283621995548839503 := by
  unfold tailWord_1976716
  simp only [CollatzResearch.WordTrace]
  refine ⟨36048377753351501530251001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48064503671135335373668001 36048377753351501530251001)
  ·
    refine ⟨27036283315013626147688251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36048377753351501530251001 27036283315013626147688251)
    ·
      refine ⟨40554424972520439221532377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27036283315013626147688251 40554424972520439221532377)
      ·
        refine ⟨30415818729390329416149283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40554424972520439221532377 30415818729390329416149283)
        ·
          refine ⟨45623728094085494124223925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30415818729390329416149283 45623728094085494124223925)
          ·
            refine ⟨4277224508820515074145993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45623728094085494124223925 4277224508820515074145993)
            ·
              refine ⟨3207918381615386305609495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277224508820515074145993 3207918381615386305609495)
              ·
                refine ⟨4811877572423079458414243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207918381615386305609495 4811877572423079458414243)
                ·
                  refine ⟨7217816358634619187621365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811877572423079458414243 7217816358634619187621365)
                  ·
                    refine ⟨676670283621995548839503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7217816358634619187621365 676670283621995548839503)
                    ·
                      rfl

theorem cell22_1976716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_1976716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976716 prefixEnd_1976716 := by exact prefixLift 1976716
  have htrace : WordTrace (prefixWord ++ tailWord_1976716) baseStart_1976716 baseEnd_1976716 := by
    simpa [prefixWord, tailWord_1976716, baseEnd_1976716] using wordTrace_append hprefix tailTrace_1976716
  have hstable : (prefixWord ++ tailWord_1976716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976716).length < 2 ^ (prefixWord ++ tailWord_1976716).sum := by decide
  have hdescent : baseEnd_1976716 < baseStart_1976716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976737 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 1, 4]
def baseStart_1976737 : Nat := 118140960795 + 1976737 * 2 ^ 59
def prefixEnd_1976737 : Nat := 4983230072969 + 3 ^ 40 * 1976737 * 2
def baseEnd_1976737 : Nat := 676677472351158494064439

theorem tailTrace_1976737 : CollatzResearch.WordTrace tailWord_1976737 prefixEnd_1976737 676677472351158494064439 := by
  unfold tailWord_1976737
  simp only [CollatzResearch.WordTrace]
  refine ⟨72097521439626923647016465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48065014293084615764677643 72097521439626923647016465)
  ·
    refine ⟨54073141079720192735262349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72097521439626923647016465 54073141079720192735262349)
    ·
      refine ⟨20277427904895072275723381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54073141079720192735262349 20277427904895072275723381)
      ·
        refine ⟨1901008866083913025849067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20277427904895072275723381 1901008866083913025849067)
        ·
          refine ⟨2851513299125869538773601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901008866083913025849067 2851513299125869538773601)
          ·
            refine ⟨2138634974344402154080201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2851513299125869538773601 2138634974344402154080201)
            ·
              refine ⟨1603976230758301615560151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138634974344402154080201 1603976230758301615560151)
              ·
                refine ⟨2405964346137452423340227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603976230758301615560151 2405964346137452423340227)
                ·
                  refine ⟨3608946519206178635010341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405964346137452423340227 3608946519206178635010341)
                  ·
                    refine ⟨676677472351158494064439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3608946519206178635010341 676677472351158494064439)
                    ·
                      rfl

theorem cell22_1976737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_1976737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976737 prefixEnd_1976737 := by exact prefixLift 1976737
  have htrace : WordTrace (prefixWord ++ tailWord_1976737) baseStart_1976737 baseEnd_1976737 := by
    simpa [prefixWord, tailWord_1976737, baseEnd_1976737] using wordTrace_append hprefix tailTrace_1976737
  have hstable : (prefixWord ++ tailWord_1976737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976737).length < 2 ^ (prefixWord ++ tailWord_1976737).sum := by decide
  have hdescent : baseEnd_1976737 < baseStart_1976737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976780 : List Nat := [2, 2, 1, 4, 4, 1, 2, 6]
def baseStart_1976780 : Nat := 118140960795 + 1976780 * 2 ^ 59
def prefixEnd_1976780 : Nat := 4983230072969 + 3 ^ 40 * 1976780 * 2
def baseEnd_1976780 : Nat := 75188021347768968359923

theorem tailTrace_1976780 : CollatzResearch.WordTrace tailWord_1976780 prefixEnd_1976780 75188021347768968359923 := by
  unfold tailWord_1976780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36049544889235570995415897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48066059852314094660554529 36049544889235570995415897)
  ·
    refine ⟨27037158666926678246561923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36049544889235570995415897 27037158666926678246561923)
    ·
      refine ⟨40555738000390017369842885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27037158666926678246561923 40555738000390017369842885)
      ·
        refine ⟨7604200875073128256845541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40555738000390017369842885 7604200875073128256845541)
        ·
          refine ⟨1425787664076211548158539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7604200875073128256845541 1425787664076211548158539)
          ·
            refine ⟨2138681496114317322237809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425787664076211548158539 2138681496114317322237809)
            ·
              refine ⟨1604011122085737991678357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138681496114317322237809 1604011122085737991678357)
              ·
                refine ⟨75188021347768968359923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1604011122085737991678357 75188021347768968359923)
                ·
                  rfl

theorem cell22_1976780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 6].length) (baseStart_1976780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976780 prefixEnd_1976780 := by exact prefixLift 1976780
  have htrace : WordTrace (prefixWord ++ tailWord_1976780) baseStart_1976780 baseEnd_1976780 := by
    simpa [prefixWord, tailWord_1976780, baseEnd_1976780] using wordTrace_append hprefix tailTrace_1976780
  have hstable : (prefixWord ++ tailWord_1976780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976780).length < 2 ^ (prefixWord ++ tailWord_1976780).sum := by decide
  have hdescent : baseEnd_1976780 < baseStart_1976780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976851 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 1, 5]
def baseStart_1976851 : Nat := 118140960795 + 1976851 * 2 ^ 59
def prefixEnd_1976851 : Nat := 4983230072969 + 3 ^ 40 * 1976851 * 2
def baseEnd_1976851 : Nat := 676716496880900196714089

theorem tailTrace_1976851 : CollatzResearch.WordTrace tailWord_1976851 prefixEnd_1976851 676716496880900196714089 := by
  unfold tailWord_1976851
  simp only [CollatzResearch.WordTrace]
  refine ⟨72101679361213921116666407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48067786240809280744444271 72101679361213921116666407)
  ·
    refine ⟨108152519041820881674999611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72101679361213921116666407 108152519041820881674999611)
    ·
      refine ⟨162228778562731322512499417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108152519041820881674999611 162228778562731322512499417)
      ·
        refine ⟨121671583922048491884374563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162228778562731322512499417 121671583922048491884374563)
        ·
          refine ⟨182507375883072737826561845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121671583922048491884374563 182507375883072737826561845)
          ·
            refine ⟨17110066489038069171240173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182507375883072737826561845 17110066489038069171240173)
            ·
              refine ⟨6416274933389275939215065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17110066489038069171240173 6416274933389275939215065)
              ·
                refine ⟨4812206200041956954411299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416274933389275939215065 4812206200041956954411299)
                ·
                  refine ⟨7218309300062935431616949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812206200041956954411299 7218309300062935431616949)
                  ·
                    refine ⟨676716496880900196714089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7218309300062935431616949 676716496880900196714089)
                    ·
                      rfl

theorem cell22_1976851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_1976851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976851 prefixEnd_1976851 := by exact prefixLift 1976851
  have htrace : WordTrace (prefixWord ++ tailWord_1976851) baseStart_1976851 baseEnd_1976851 := by
    simpa [prefixWord, tailWord_1976851, baseEnd_1976851] using wordTrace_append hprefix tailTrace_1976851
  have hstable : (prefixWord ++ tailWord_1976851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976851).length < 2 ^ (prefixWord ++ tailWord_1976851).sum := by decide
  have hdescent : baseEnd_1976851 < baseStart_1976851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976853 : List Nat := [1, 3, 2, 1, 3, 1, 2, 5, 4]
def baseStart_1976853 : Nat := 118140960795 + 1976853 * 2 ^ 59
def prefixEnd_1976853 : Nat := 4983230072969 + 3 ^ 40 * 1976853 * 2
def baseEnd_1976853 : Nat := 225572393840590952721361

theorem tailTrace_1976853 : CollatzResearch.WordTrace tailWord_1976853 prefixEnd_1976853 225572393840590952721361 := by
  unfold tailWord_1976853
  simp only [CollatzResearch.WordTrace]
  refine ⟨72101752307206675458239213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48067834871471116972159475 72101752307206675458239213)
  ·
    refine ⟨27038157115202503296839705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72101752307206675458239213 27038157115202503296839705)
    ·
      refine ⟨20278617836401877472629779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27038157115202503296839705 20278617836401877472629779)
      ·
        refine ⟨30417926754602816208944669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20278617836401877472629779 30417926754602816208944669)
        ·
          refine ⟨11406722532976056078354251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30417926754602816208944669 11406722532976056078354251)
          ·
            refine ⟨17110083799464084117531377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11406722532976056078354251 17110083799464084117531377)
            ·
              refine ⟨12832562849598063088148533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17110083799464084117531377 12832562849598063088148533)
              ·
                refine ⟨1203052767149818414513925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12832562849598063088148533 1203052767149818414513925)
                ·
                  refine ⟨225572393840590952721361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203052767149818414513925 225572393840590952721361)
                  ·
                    rfl

theorem cell22_1976853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_1976853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976853 prefixEnd_1976853 := by exact prefixLift 1976853
  have htrace : WordTrace (prefixWord ++ tailWord_1976853) baseStart_1976853 baseEnd_1976853 := by
    simpa [prefixWord, tailWord_1976853, baseEnd_1976853] using wordTrace_append hprefix tailTrace_1976853
  have hstable : (prefixWord ++ tailWord_1976853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976853).length < 2 ^ (prefixWord ++ tailWord_1976853).sum := by decide
  have hdescent : baseEnd_1976853 < baseStart_1976853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976866 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1976866 : Nat := 118140960795 + 1976866 * 2 ^ 59
def prefixEnd_1976866 : Nat := 4983230072969 + 3 ^ 40 * 1976866 * 2
def baseEnd_1976866 : Nat := 676721631687445157589043

theorem tailTrace_1976866 : CollatzResearch.WordTrace tailWord_1976866 prefixEnd_1976866 676721631687445157589043 := by
  unfold tailWord_1976866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18025556614039894669615613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48068150970773052452308301 18025556614039894669615613)
  ·
    refine ⟨6759583730264960501105855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18025556614039894669615613 6759583730264960501105855)
    ·
      refine ⟨10139375595397440751658783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6759583730264960501105855 10139375595397440751658783)
      ·
        refine ⟨15209063393096161127488175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10139375595397440751658783 15209063393096161127488175)
        ·
          refine ⟨22813595089644241691232263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15209063393096161127488175 22813595089644241691232263)
          ·
            refine ⟨34220392634466362536848395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22813595089644241691232263 34220392634466362536848395)
            ·
              refine ⟨51330588951699543805272593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34220392634466362536848395 51330588951699543805272593)
              ·
                refine ⟨38497941713774657853954445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51330588951699543805272593 38497941713774657853954445)
                ·
                  refine ⟨14436728142665496695232917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38497941713774657853954445 14436728142665496695232917)
                  ·
                    refine ⟨676721631687445157589043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14436728142665496695232917 676721631687445157589043)
                    ·
                      rfl

theorem cell22_1976866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1976866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976866 prefixEnd_1976866 := by exact prefixLift 1976866
  have htrace : WordTrace (prefixWord ++ tailWord_1976866) baseStart_1976866 baseEnd_1976866 := by
    simpa [prefixWord, tailWord_1976866, baseEnd_1976866] using wordTrace_append hprefix tailTrace_1976866
  have hstable : (prefixWord ++ tailWord_1976866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976866).length < 2 ^ (prefixWord ++ tailWord_1976866).sum := by decide
  have hdescent : baseEnd_1976866 < baseStart_1976866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976881 : List Nat := [1, 2, 2, 3, 1, 1, 5, 7]
def baseStart_1976881 : Nat := 118140960795 + 1976881 * 2 ^ 59
def prefixEnd_1976881 : Nat := 4983230072969 + 3 ^ 40 * 1976881 * 2
def baseEnd_1976881 : Nat := 75191862943776679829333

theorem tailTrace_1976881 : CollatzResearch.WordTrace tailWord_1976881 prefixEnd_1976881 75191862943776679829333 := by
  unfold tailWord_1976881
  simp only [CollatzResearch.WordTrace]
  refine ⟨72102773551105236240258497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48068515700736824160172331 72102773551105236240258497)
  ·
    refine ⟨54077080163328927180193873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72102773551105236240258497 54077080163328927180193873)
    ·
      refine ⟨40557810122496695385145405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54077080163328927180193873 40557810122496695385145405)
      ·
        refine ⟨15209178795936260769429527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40557810122496695385145405 15209178795936260769429527)
        ·
          refine ⟨22813768193904391154144291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15209178795936260769429527 22813768193904391154144291)
          ·
            refine ⟨34220652290856586731216437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22813768193904391154144291 34220652290856586731216437)
            ·
              refine ⟨3208186152267805006051541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34220652290856586731216437 3208186152267805006051541)
              ·
                refine ⟨75191862943776679829333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3208186152267805006051541 75191862943776679829333)
                ·
                  rfl

theorem cell22_1976881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 7].length) (baseStart_1976881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976881 prefixEnd_1976881 := by exact prefixLift 1976881
  have htrace : WordTrace (prefixWord ++ tailWord_1976881) baseStart_1976881 baseEnd_1976881 := by
    simpa [prefixWord, tailWord_1976881, baseEnd_1976881] using wordTrace_append hprefix tailTrace_1976881
  have hstable : (prefixWord ++ tailWord_1976881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976881).length < 2 ^ (prefixWord ++ tailWord_1976881).sum := by decide
  have hdescent : baseEnd_1976881 < baseStart_1976881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976964 : List Nat := [2, 3, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_1976964 : Nat := 118140960795 + 1976964 * 2 ^ 59
def prefixEnd_1976964 : Nat := 4983230072969 + 3 ^ 40 * 1976964 * 2
def baseEnd_1976964 : Nat := 676755179090205568638743

theorem tailTrace_1976964 : CollatzResearch.WordTrace tailWord_1976964 prefixEnd_1976964 676755179090205568638743 := by
  unfold tailWord_1976964
  simp only [CollatzResearch.WordTrace]
  refine ⟨36052900404902270707764973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48070533873203027610353297 36052900404902270707764973)
  ·
    refine ⟨13519837651838351515411865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36052900404902270707764973 13519837651838351515411865)
    ·
      refine ⟨10139878238878763636558899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13519837651838351515411865 10139878238878763636558899)
      ·
        refine ⟨15209817358318145454838349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10139878238878763636558899 15209817358318145454838349)
        ·
          refine ⟨5703681509369304545564381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15209817358318145454838349 5703681509369304545564381)
          ·
            refine ⟨2138880566013489204586643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5703681509369304545564381 2138880566013489204586643)
            ·
              refine ⟨3208320849020233806879965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138880566013489204586643 3208320849020233806879965)
              ·
                refine ⟨1203120318382587677579987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3208320849020233806879965 1203120318382587677579987)
                ·
                  refine ⟨1804680477573881516369981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203120318382587677579987 1804680477573881516369981)
                  ·
                    refine ⟨676755179090205568638743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1804680477573881516369981 676755179090205568638743)
                    ·
                      rfl

theorem cell22_1976964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_1976964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976964 prefixEnd_1976964 := by exact prefixLift 1976964
  have htrace : WordTrace (prefixWord ++ tailWord_1976964) baseStart_1976964 baseEnd_1976964 := by
    simpa [prefixWord, tailWord_1976964, baseEnd_1976964] using wordTrace_append hprefix tailTrace_1976964
  have hstable : (prefixWord ++ tailWord_1976964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976964).length < 2 ^ (prefixWord ++ tailWord_1976964).sum := by decide
  have hdescent : baseEnd_1976964 < baseStart_1976964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976990 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1976990 : Nat := 118140960795 + 1976990 * 2 ^ 59
def prefixEnd_1976990 : Nat := 4983230072969 + 3 ^ 40 * 1976990 * 2
def baseEnd_1976990 : Nat := 676764079421550167488663

theorem tailTrace_1976990 : CollatzResearch.WordTrace tailWord_1976990 prefixEnd_1976990 676764079421550167488663 := by
  unfold tailWord_1976990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013343638463793481997053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48071166071806898570650949 9013343638463793481997053)
  ·
    refine ⟨3380003864423922555748895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9013343638463793481997053 3380003864423922555748895)
    ·
      refine ⟨5070005796635883833623343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3380003864423922555748895 5070005796635883833623343)
      ·
        refine ⟨7605008694953825750435015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070005796635883833623343 7605008694953825750435015)
        ·
          refine ⟨11407513042430738625652523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7605008694953825750435015 11407513042430738625652523)
          ·
            refine ⟨17111269563646107938478785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407513042430738625652523 17111269563646107938478785)
            ·
              refine ⟨12833452172734580953859089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17111269563646107938478785 12833452172734580953859089)
              ·
                refine ⟨9625089129550935715394317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12833452172734580953859089 9625089129550935715394317)
                ·
                  refine ⟨3609408423581600893272869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9625089129550935715394317 3609408423581600893272869)
                  ·
                    refine ⟨676764079421550167488663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609408423581600893272869 676764079421550167488663)
                    ·
                      rfl

theorem cell22_1976990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1976990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1976990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1976990 prefixEnd_1976990 := by exact prefixLift 1976990
  have htrace : WordTrace (prefixWord ++ tailWord_1976990) baseStart_1976990 baseEnd_1976990 := by
    simpa [prefixWord, tailWord_1976990, baseEnd_1976990] using wordTrace_append hprefix tailTrace_1976990
  have hstable : (prefixWord ++ tailWord_1976990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976990).length < 2 ^ (prefixWord ++ tailWord_1976990).sum := by decide
  have hdescent : baseEnd_1976990 < baseStart_1976990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977082 : List Nat := [3, 1, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_1977082 : Nat := 118140960795 + 1977082 * 2 ^ 59
def prefixEnd_1977082 : Nat := 4983230072969 + 3 ^ 40 * 1977082 * 2
def baseEnd_1977082 : Nat := 676795572901692594188381

theorem tailTrace_1977082 : CollatzResearch.WordTrace tailWord_1977082 prefixEnd_1977082 676795572901692594188381 := by
  unfold tailWord_1977082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18027526155844261892081375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48073403082251365045550333 18027526155844261892081375)
  ·
    refine ⟨27041289233766392838122063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18027526155844261892081375 27041289233766392838122063)
    ·
      refine ⟨40561933850649589257183095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27041289233766392838122063 40561933850649589257183095)
      ·
        refine ⟨60842900775974383885774643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40561933850649589257183095 60842900775974383885774643)
        ·
          refine ⟨91264351163961575828661965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60842900775974383885774643 91264351163961575828661965)
          ·
            refine ⟨34224131686485590935748237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91264351163961575828661965 34224131686485590935748237)
            ·
              refine ⟨12834049382432096600905589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34224131686485590935748237 12834049382432096600905589)
              ·
                refine ⟨1203192129603009056334899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12834049382432096600905589 1203192129603009056334899)
                ·
                  refine ⟨1804788194404513584502349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203192129603009056334899 1804788194404513584502349)
                  ·
                    refine ⟨676795572901692594188381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1804788194404513584502349 676795572901692594188381)
                    ·
                      rfl

theorem cell22_1977082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_1977082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977082 prefixEnd_1977082 := by exact prefixLift 1977082
  have htrace : WordTrace (prefixWord ++ tailWord_1977082) baseStart_1977082 baseEnd_1977082 := by
    simpa [prefixWord, tailWord_1977082, baseEnd_1977082] using wordTrace_append hprefix tailTrace_1977082
  have hstable : (prefixWord ++ tailWord_1977082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977082).length < 2 ^ (prefixWord ++ tailWord_1977082).sum := by decide
  have hdescent : baseEnd_1977082 < baseStart_1977082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977095 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 7]
def baseStart_1977095 : Nat := 118140960795 + 1977095 * 2 ^ 59
def prefixEnd_1977095 : Nat := 4983230072969 + 3 ^ 40 * 1977095 * 2
def baseEnd_1977095 : Nat := 225600007689121631204447

theorem tailTrace_1977095 : CollatzResearch.WordTrace tailWord_1977095 prefixEnd_1977095 225600007689121631204447 := by
  unfold tailWord_1977095
  simp only [CollatzResearch.WordTrace]
  refine ⟨72110578772329950788548739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48073719181553300525699159 72110578772329950788548739)
  ·
    refine ⟨108165868158494926182823109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72110578772329950788548739 108165868158494926182823109)
    ·
      refine ⟨20281100279717798659279333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108165868158494926182823109 20281100279717798659279333)
      ·
        refine ⟨3802706302447087248614875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20281100279717798659279333 3802706302447087248614875)
        ·
          refine ⟨5704059453670630872922313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802706302447087248614875 5704059453670630872922313)
          ·
            refine ⟨4278044590252973154691735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704059453670630872922313 4278044590252973154691735)
            ·
              refine ⟨6417066885379459732037603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278044590252973154691735 6417066885379459732037603)
              ·
                refine ⟨9625600328069189598056405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417066885379459732037603 9625600328069189598056405)
                ·
                  refine ⟨225600007689121631204447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9625600328069189598056405 225600007689121631204447)
                  ·
                    rfl

theorem cell22_1977095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 7].length) (baseStart_1977095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977095 prefixEnd_1977095 := by exact prefixLift 1977095
  have htrace : WordTrace (prefixWord ++ tailWord_1977095) baseStart_1977095 baseEnd_1977095 := by
    simpa [prefixWord, tailWord_1977095, baseEnd_1977095] using wordTrace_append hprefix tailTrace_1977095
  have hstable : (prefixWord ++ tailWord_1977095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977095).length < 2 ^ (prefixWord ++ tailWord_1977095).sum := by decide
  have hdescent : baseEnd_1977095 < baseStart_1977095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977155 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 4, 3]
def baseStart_1977155 : Nat := 118140960795 + 1977155 * 2 ^ 59
def prefixEnd_1977155 : Nat := 4983230072969 + 3 ^ 40 * 1977155 * 2
def baseEnd_1977155 : Nat := 676820562293544737113157

theorem tailTrace_1977155 : CollatzResearch.WordTrace tailWord_1977155 prefixEnd_1977155 676820562293544737113157 := by
  unfold tailWord_1977155
  simp only [CollatzResearch.WordTrace]
  refine ⟨72112767152112581035732919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48075178101408387357155279 72112767152112581035732919)
  ·
    refine ⟨108169150728168871553599379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72112767152112581035732919 108169150728168871553599379)
    ·
      refine ⟨162253726092253307330399069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108169150728168871553599379 162253726092253307330399069)
      ·
        refine ⟨60845147284594990248899651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162253726092253307330399069 60845147284594990248899651)
        ·
          refine ⟨91267720926892485373349477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60845147284594990248899651 91267720926892485373349477)
          ·
            refine ⟨17112697673792341007503027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91267720926892485373349477 17112697673792341007503027)
            ·
              refine ⟨25669046510688511511254541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17112697673792341007503027 25669046510688511511254541)
              ·
                refine ⟨9625892441508191816720453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25669046510688511511254541 9625892441508191816720453)
                ·
                  refine ⟨1804854832782785965635085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9625892441508191816720453 1804854832782785965635085)
                  ·
                    refine ⟨676820562293544737113157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1804854832782785965635085 676820562293544737113157)
                    ·
                      rfl

theorem cell22_1977155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 3].length) (baseStart_1977155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977155 prefixEnd_1977155 := by exact prefixLift 1977155
  have htrace : WordTrace (prefixWord ++ tailWord_1977155) baseStart_1977155 baseEnd_1977155 := by
    simpa [prefixWord, tailWord_1977155, baseEnd_1977155] using wordTrace_append hprefix tailTrace_1977155
  have hstable : (prefixWord ++ tailWord_1977155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977155).length < 2 ^ (prefixWord ++ tailWord_1977155).sum := by decide
  have hdescent : baseEnd_1977155 < baseStart_1977155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977168 : List Nat := [2, 1, 1, 1, 1, 4, 3, 9]
def baseStart_1977168 : Nat := 118140960795 + 1977168 * 2 ^ 59
def prefixEnd_1977168 : Nat := 4983230072969 + 3 ^ 40 * 1977168 * 2
def baseEnd_1977168 : Nat := 75202779162135226282013

theorem tailTrace_1977168 : CollatzResearch.WordTrace tailWord_1977168 prefixEnd_1977168 75202779162135226282013 := by
  unfold tailWord_1977168
  simp only [CollatzResearch.WordTrace]
  refine ⟨36056620650532742127978079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48075494200710322837304105 36056620650532742127978079)
  ·
    refine ⟨54084930975799113191967119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36056620650532742127978079 54084930975799113191967119)
    ·
      refine ⟨81127396463698669787950679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54084930975799113191967119 81127396463698669787950679)
      ·
        refine ⟨121691094695548004681926019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81127396463698669787950679 121691094695548004681926019)
        ·
          refine ⟨182536642043322007022889029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121691094695548004681926019 182536642043322007022889029)
          ·
            refine ⟨34225620383122876316791693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182536642043322007022889029 34225620383122876316791693)
            ·
              refine ⟨12834607643671078618796885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34225620383122876316791693 12834607643671078618796885)
              ·
                refine ⟨75202779162135226282013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12834607643671078618796885 75202779162135226282013)
                ·
                  rfl

theorem cell22_1977168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 9].length) (baseStart_1977168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977168 prefixEnd_1977168 := by exact prefixLift 1977168
  have htrace : WordTrace (prefixWord ++ tailWord_1977168) baseStart_1977168 baseEnd_1977168 := by
    simpa [prefixWord, tailWord_1977168, baseEnd_1977168] using wordTrace_append hprefix tailTrace_1977168
  have hstable : (prefixWord ++ tailWord_1977168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977168).length < 2 ^ (prefixWord ++ tailWord_1977168).sum := by decide
  have hdescent : baseEnd_1977168 < baseStart_1977168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977170 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1977170 : Nat := 118140960795 + 1977170 * 2 ^ 59
def prefixEnd_1977170 : Nat := 4983230072969 + 3 ^ 40 * 1977170 * 2
def baseEnd_1977170 : Nat := 676825697100089697988111

theorem tailTrace_1977170 : CollatzResearch.WordTrace tailWord_1977170 prefixEnd_1977170 676825697100089697988111 := by
  unfold tailWord_1977170
  simp only [CollatzResearch.WordTrace]
  refine ⟨18028328561764559649382241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48075542831372159065019309 18028328561764559649382241)
  ·
    refine ⟨13521246421323419737036681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18028328561764559649382241 13521246421323419737036681)
    ·
      refine ⟨10140934815992564802777511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13521246421323419737036681 10140934815992564802777511)
      ·
        refine ⟨15211402223988847204166267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10140934815992564802777511 15211402223988847204166267)
        ·
          refine ⟨22817103335983270806249401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15211402223988847204166267 22817103335983270806249401)
          ·
            refine ⟨17112827501987453104687051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22817103335983270806249401 17112827501987453104687051)
            ·
              refine ⟨25669241252981179657030577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17112827501987453104687051 25669241252981179657030577)
              ·
                refine ⟨19251930939735884742772933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25669241252981179657030577 19251930939735884742772933)
                ·
                  refine ⟨3609737051200478389269925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19251930939735884742772933 3609737051200478389269925)
                  ·
                    refine ⟨676825697100089697988111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609737051200478389269925 676825697100089697988111)
                    ·
                      rfl

theorem cell22_1977170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1977170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977170 prefixEnd_1977170 := by exact prefixLift 1977170
  have htrace : WordTrace (prefixWord ++ tailWord_1977170) baseStart_1977170 baseEnd_1977170 := by
    simpa [prefixWord, tailWord_1977170, baseEnd_1977170] using wordTrace_append hprefix tailTrace_1977170
  have hstable : (prefixWord ++ tailWord_1977170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977170).length < 2 ^ (prefixWord ++ tailWord_1977170).sum := by decide
  have hdescent : baseEnd_1977170 < baseStart_1977170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977187 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 2, 4]
def baseStart_1977187 : Nat := 118140960795 + 1977187 * 2 ^ 59
def prefixEnd_1977187 : Nat := 4983230072969 + 3 ^ 40 * 1977187 * 2
def baseEnd_1977187 : Nat := 676831516547507320313059

theorem tailTrace_1977187 : CollatzResearch.WordTrace tailWord_1977187 prefixEnd_1977187 676831516547507320313059 := by
  unfold tailWord_1977187
  simp only [CollatzResearch.WordTrace]
  refine ⟨72113934287996650500897815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48075956191997767000598543 72113934287996650500897815)
  ·
    refine ⟨108170901431994975751346723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72113934287996650500897815 108170901431994975751346723)
    ·
      refine ⟨162256352147992463627020085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108170901431994975751346723 162256352147992463627020085)
      ·
        refine ⟨15211533013874293465033133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162256352147992463627020085 15211533013874293465033133)
        ·
          refine ⟨5704324880202860049387425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15211533013874293465033133 5704324880202860049387425)
          ·
            refine ⟨4278243660152145037040569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704324880202860049387425 4278243660152145037040569)
            ·
              refine ⟨3208682745114108777780427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278243660152145037040569 3208682745114108777780427)
              ·
                refine ⟨4813024117671163166670641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208682745114108777780427 4813024117671163166670641)
                ·
                  refine ⟨3609768088253372375002981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4813024117671163166670641 3609768088253372375002981)
                  ·
                    refine ⟨676831516547507320313059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609768088253372375002981 676831516547507320313059)
                    ·
                      rfl

theorem cell22_1977187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 4].length) (baseStart_1977187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977187 prefixEnd_1977187 := by exact prefixLift 1977187
  have htrace : WordTrace (prefixWord ++ tailWord_1977187) baseStart_1977187 baseEnd_1977187 := by
    simpa [prefixWord, tailWord_1977187, baseEnd_1977187] using wordTrace_append hprefix tailTrace_1977187
  have hstable : (prefixWord ++ tailWord_1977187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977187).length < 2 ^ (prefixWord ++ tailWord_1977187).sum := by decide
  have hdescent : baseEnd_1977187 < baseStart_1977187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977206 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_1977206 : Nat := 118140960795 + 1977206 * 2 ^ 59
def prefixEnd_1977206 : Nat := 4983230072969 + 3 ^ 40 * 1977206 * 2
def baseEnd_1977206 : Nat := 676838020635797604088001

theorem tailTrace_1977206 : CollatzResearch.WordTrace tailWord_1977206 prefixEnd_1977206 676838020635797604088001 := by
  unfold tailWord_1977206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507164204682988546614967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48076418183285211163892981 4507164204682988546614967)
  ·
    refine ⟨6760746307024482819922451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4507164204682988546614967 6760746307024482819922451)
    ·
      refine ⟨10141119460536724229883677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6760746307024482819922451 10141119460536724229883677)
      ·
        refine ⟨3802919797701271586206379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10141119460536724229883677 3802919797701271586206379)
        ·
          refine ⟨5704379696551907379309569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802919797701271586206379 5704379696551907379309569)
          ·
            refine ⟨4278284772413930534482177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704379696551907379309569 4278284772413930534482177)
            ·
              refine ⟨3208713579310447900861633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278284772413930534482177 3208713579310447900861633)
              ·
                refine ⟨2406535184482835925646225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208713579310447900861633 2406535184482835925646225)
                ·
                  refine ⟨1804901388362126944234669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2406535184482835925646225 1804901388362126944234669)
                  ·
                    refine ⟨676838020635797604088001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1804901388362126944234669 676838020635797604088001)
                    ·
                      rfl

theorem cell22_1977206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_1977206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977206 prefixEnd_1977206 := by exact prefixLift 1977206
  have htrace : WordTrace (prefixWord ++ tailWord_1977206) baseStart_1977206 baseEnd_1977206 := by
    simpa [prefixWord, tailWord_1977206, baseEnd_1977206] using wordTrace_append hprefix tailTrace_1977206
  have hstable : (prefixWord ++ tailWord_1977206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977206).length < 2 ^ (prefixWord ++ tailWord_1977206).sum := by decide
  have hdescent : baseEnd_1977206 < baseStart_1977206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977238 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1977238 : Nat := 118140960795 + 1977238 * 2 ^ 59
def prefixEnd_1977238 : Nat := 4983230072969 + 3 ^ 40 * 1977238 * 2
def baseEnd_1977238 : Nat := 676848974889760187287903

theorem tailTrace_1977238 : CollatzResearch.WordTrace tailWord_1977238 prefixEnd_1977238 676848974889760187287903 := by
  unfold tailWord_1977238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507237150675742888187773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48077196273874590807336245 4507237150675742888187773)
  ·
    refine ⟨1690213931503403583070415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4507237150675742888187773 1690213931503403583070415)
    ·
      refine ⟨2535320897255105374605623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1690213931503403583070415 2535320897255105374605623)
      ·
        refine ⟨3802981345882658061908435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535320897255105374605623 3802981345882658061908435)
        ·
          refine ⟨5704472018823987092862653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802981345882658061908435 5704472018823987092862653)
          ·
            refine ⟨2139177007058995159823495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5704472018823987092862653 2139177007058995159823495)
            ·
              refine ⟨3208765510588492739735243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139177007058995159823495 3208765510588492739735243)
              ·
                refine ⟨4813148265882739109602865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208765510588492739735243 4813148265882739109602865)
                ·
                  refine ⟨3609861199412054332202149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4813148265882739109602865 3609861199412054332202149)
                  ·
                    refine ⟨676848974889760187287903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609861199412054332202149 676848974889760187287903)
                    ·
                      rfl

theorem cell22_1977238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1977238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977238 prefixEnd_1977238 := by exact prefixLift 1977238
  have htrace : WordTrace (prefixWord ++ tailWord_1977238) baseStart_1977238 baseEnd_1977238 := by
    simpa [prefixWord, tailWord_1977238, baseEnd_1977238] using wordTrace_append hprefix tailTrace_1977238
  have hstable : (prefixWord ++ tailWord_1977238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977238).length < 2 ^ (prefixWord ++ tailWord_1977238).sum := by decide
  have hdescent : baseEnd_1977238 < baseStart_1977238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977245 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1977245 : Nat := 118140960795 + 1977245 * 2 ^ 59
def prefixEnd_1977245 : Nat := 4983230072969 + 3 ^ 40 * 1977245 * 2
def baseEnd_1977245 : Nat := 676851371132814502362881

theorem tailTrace_1977245 : CollatzResearch.WordTrace tailWord_1977245 prefixEnd_1977245 676851371132814502362881 := by
  unfold tailWord_1977245
  simp only [CollatzResearch.WordTrace]
  refine ⟨72116049721786526406509189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48077366481191017604339459 72116049721786526406509189)
  ·
    refine ⟨13521759322834973701220473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72116049721786526406509189 13521759322834973701220473)
    ·
      refine ⟨10141319492126230275915355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13521759322834973701220473 10141319492126230275915355)
      ·
        refine ⟨15211979238189345413873033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141319492126230275915355 15211979238189345413873033)
        ·
          refine ⟨11408984428642009060404775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15211979238189345413873033 11408984428642009060404775)
          ·
            refine ⟨17113476642963013590607163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11408984428642009060404775 17113476642963013590607163)
            ·
              refine ⟨25670214964444520385910745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17113476642963013590607163 25670214964444520385910745)
              ·
                refine ⟨19252661223333390289433059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25670214964444520385910745 19252661223333390289433059)
                ·
                  refine ⟨28878991835000085434149589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19252661223333390289433059 28878991835000085434149589)
                  ·
                    refine ⟨676851371132814502362881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28878991835000085434149589 676851371132814502362881)
                    ·
                      rfl

theorem cell22_1977245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1977245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977245 prefixEnd_1977245 := by exact prefixLift 1977245
  have htrace : WordTrace (prefixWord ++ tailWord_1977245) baseStart_1977245 baseEnd_1977245 := by
    simpa [prefixWord, tailWord_1977245, baseEnd_1977245] using wordTrace_append hprefix tailTrace_1977245
  have hstable : (prefixWord ++ tailWord_1977245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977245).length < 2 ^ (prefixWord ++ tailWord_1977245).sum := by decide
  have hdescent : baseEnd_1977245 < baseStart_1977245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977268 : List Nat := [2, 5, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1977268 : Nat := 118140960795 + 1977268 * 2 ^ 59
def prefixEnd_1977268 : Nat := 4983230072969 + 3 ^ 40 * 1977268 * 2
def baseEnd_1977268 : Nat := 676859244502850109037811

theorem tailTrace_1977268 : CollatzResearch.WordTrace tailWord_1977268 prefixEnd_1977268 676859244502850109037811 := by
  unfold tailWord_1977268
  simp only [CollatzResearch.WordTrace]
  refine ⟨36058444300351600667298229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48077925733802134223064305 36058444300351600667298229)
  ·
    refine ⟨3380479153157962562559209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36058444300351600667298229 3380479153157962562559209)
    ·
      refine ⟨2535359364868471921919407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3380479153157962562559209 2535359364868471921919407)
      ·
        refine ⟨3803039047302707882879111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535359364868471921919407 3803039047302707882879111)
        ·
          refine ⟨5704558570954061824318667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803039047302707882879111 5704558570954061824318667)
          ·
            refine ⟨8556837856431092736478001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704558570954061824318667 8556837856431092736478001)
            ·
              refine ⟨6417628392323319552358501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8556837856431092736478001 6417628392323319552358501)
              ·
                refine ⟨1203305323560622416067219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6417628392323319552358501 1203305323560622416067219)
                ·
                  refine ⟨1804957985340933624100829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203305323560622416067219 1804957985340933624100829)
                  ·
                    refine ⟨676859244502850109037811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1804957985340933624100829 676859244502850109037811)
                    ·
                      rfl

theorem cell22_1977268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1977268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977268 prefixEnd_1977268 := by exact prefixLift 1977268
  have htrace : WordTrace (prefixWord ++ tailWord_1977268) baseStart_1977268 baseEnd_1977268 := by
    simpa [prefixWord, tailWord_1977268, baseEnd_1977268] using wordTrace_append hprefix tailTrace_1977268
  have hstable : (prefixWord ++ tailWord_1977268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977268).length < 2 ^ (prefixWord ++ tailWord_1977268).sum := by decide
  have hdescent : baseEnd_1977268 < baseStart_1977268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977294 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1977294 : Nat := 118140960795 + 1977294 * 2 ^ 59
def prefixEnd_1977294 : Nat := 4983230072969 + 3 ^ 40 * 1977294 * 2
def baseEnd_1977294 : Nat := 676868144834194707887731

theorem tailTrace_1977294 : CollatzResearch.WordTrace tailWord_1977294 prefixEnd_1977294 676868144834194707887731 := by
  unfold tailWord_1977294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9014729612326125971880367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48078557932406005183361957 9014729612326125971880367)
  ·
    refine ⟨13522094418489188957820551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9014729612326125971880367 13522094418489188957820551)
    ·
      refine ⟨20283141627733783436730827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13522094418489188957820551 20283141627733783436730827)
      ·
        refine ⟨30424712441600675155096241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20283141627733783436730827 30424712441600675155096241)
        ·
          refine ⟨22818534331200506366322181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30424712441600675155096241 22818534331200506366322181)
          ·
            refine ⟨4278475187100094943685409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22818534331200506366322181 4278475187100094943685409)
            ·
              refine ⟨3208856390325071207764057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278475187100094943685409 3208856390325071207764057)
              ·
                refine ⟨2406642292743803405823043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208856390325071207764057 2406642292743803405823043)
                ·
                  refine ⟨3609963439115705108734565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406642292743803405823043 3609963439115705108734565)
                  ·
                    refine ⟨676868144834194707887731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3609963439115705108734565 676868144834194707887731)
                    ·
                      rfl

theorem cell22_1977294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1977294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977294 prefixEnd_1977294 := by exact prefixLift 1977294
  have htrace : WordTrace (prefixWord ++ tailWord_1977294) baseStart_1977294 baseEnd_1977294 := by
    simpa [prefixWord, tailWord_1977294, baseEnd_1977294] using wordTrace_append hprefix tailTrace_1977294
  have hstable : (prefixWord ++ tailWord_1977294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977294).length < 2 ^ (prefixWord ++ tailWord_1977294).sum := by decide
  have hdescent : baseEnd_1977294 < baseStart_1977294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977320 : List Nat := [2, 1, 4, 1, 1, 1, 12]
def baseStart_1977320 : Nat := 118140960795 + 1977320 * 2 ^ 59
def prefixEnd_1977320 : Nat := 4983230072969 + 3 ^ 40 * 1977320 * 2
def baseEnd_1977320 : Nat := 25069520191316270619913

theorem tailTrace_1977320 : CollatzResearch.WordTrace tailWord_1977320 prefixEnd_1977320 25069520191316270619913 := by
  unfold tailWord_1977320
  simp only [CollatzResearch.WordTrace]
  refine ⟨36059392598257407107744707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48079190131009876143659609 36059392598257407107744707)
  ·
    refine ⟨54089088897386110661617061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36059392598257407107744707 54089088897386110661617061)
    ·
      refine ⟨10141704168259895749053199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54089088897386110661617061 10141704168259895749053199)
      ·
        refine ⟨15212556252389843623579799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141704168259895749053199 15212556252389843623579799)
        ·
          refine ⟨22818834378584765435369699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15212556252389843623579799 22818834378584765435369699)
          ·
            refine ⟨34228251567877148153054549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22818834378584765435369699 34228251567877148153054549)
            ·
              refine ⟨25069520191316270619913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34228251567877148153054549 25069520191316270619913)
              ·
                rfl

theorem cell22_1977320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 12].length) (baseStart_1977320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977320 prefixEnd_1977320 := by exact prefixLift 1977320
  have htrace : WordTrace (prefixWord ++ tailWord_1977320) baseStart_1977320 baseEnd_1977320 := by
    simpa [prefixWord, tailWord_1977320, baseEnd_1977320] using wordTrace_append hprefix tailTrace_1977320
  have hstable : (prefixWord ++ tailWord_1977320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977320).length < 2 ^ (prefixWord ++ tailWord_1977320).sum := by decide
  have hdescent : baseEnd_1977320 < baseStart_1977320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977322 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1977322 : Nat := 118140960795 + 1977322 * 2 ^ 59
def prefixEnd_1977322 : Nat := 4983230072969 + 3 ^ 40 * 1977322 * 2
def baseEnd_1977322 : Nat := 676877729806411968187645

theorem tailTrace_1977322 : CollatzResearch.WordTrace tailWord_1977322 prefixEnd_1977322 676877729806411968187645 := by
  unfold tailWord_1977322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029714535626892139265555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48079238761671712371374813 18029714535626892139265555)
  ·
    refine ⟨27044571803440338208898333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18029714535626892139265555 27044571803440338208898333)
    ·
      refine ⟨10141714426290126828336875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27044571803440338208898333 10141714426290126828336875)
      ·
        refine ⟨15212571639435190242505313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141714426290126828336875 15212571639435190242505313)
        ·
          refine ⟨11409428729576392681878985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15212571639435190242505313 11409428729576392681878985)
          ·
            refine ⟨8557071547182294511409239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11409428729576392681878985 8557071547182294511409239)
            ·
              refine ⟨12835607320773441767113859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8557071547182294511409239 12835607320773441767113859)
              ·
                refine ⟨19253410981160162650670789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12835607320773441767113859 19253410981160162650670789)
                ·
                  refine ⟨3610014558967530497000773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19253410981160162650670789 3610014558967530497000773)
                  ·
                    refine ⟨676877729806411968187645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610014558967530497000773 676877729806411968187645)
                    ·
                      rfl

theorem cell22_1977322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1977322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977322 prefixEnd_1977322 := by exact prefixLift 1977322
  have htrace : WordTrace (prefixWord ++ tailWord_1977322) baseStart_1977322 baseEnd_1977322 := by
    simpa [prefixWord, tailWord_1977322, baseEnd_1977322] using wordTrace_append hprefix tailTrace_1977322
  have hstable : (prefixWord ++ tailWord_1977322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977322).length < 2 ^ (prefixWord ++ tailWord_1977322).sum := by decide
  have hdescent : baseEnd_1977322 < baseStart_1977322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977326 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_1977326 : Nat := 118140960795 + 1977326 * 2 ^ 59
def prefixEnd_1977326 : Nat := 4983230072969 + 3 ^ 40 * 1977326 * 2
def baseEnd_1977326 : Nat := 225626366362719097029211

theorem tailTrace_1977326 : CollatzResearch.WordTrace tailWord_1977326 prefixEnd_1977326 225626366362719097029211 := by
  unfold tailWord_1977326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9014875504311634655025979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48079336022995384826805221 9014875504311634655025979)
  ·
    refine ⟨13522313256467451982538969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9014875504311634655025979 13522313256467451982538969)
    ·
      refine ⟨10141734942350588986904227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13522313256467451982538969 10141734942350588986904227)
      ·
        refine ⟨15212602413525883480356341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141734942350588986904227 15212602413525883480356341)
        ·
          refine ⟨1426181476268051576283407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15212602413525883480356341 1426181476268051576283407)
          ·
            refine ⟨2139272214402077364425111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426181476268051576283407 2139272214402077364425111)
            ·
              refine ⟨3208908321603116046637667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139272214402077364425111 3208908321603116046637667)
              ·
                refine ⟨4813362482404674069956501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208908321603116046637667 4813362482404674069956501)
                ·
                  refine ⟨225626366362719097029211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4813362482404674069956501 225626366362719097029211)
                  ·
                    rfl

theorem cell22_1977326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_1977326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977326 prefixEnd_1977326 := by exact prefixLift 1977326
  have htrace : WordTrace (prefixWord ++ tailWord_1977326) baseStart_1977326 baseEnd_1977326 := by
    simpa [prefixWord, tailWord_1977326, baseEnd_1977326] using wordTrace_append hprefix tailTrace_1977326
  have hstable : (prefixWord ++ tailWord_1977326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977326).length < 2 ^ (prefixWord ++ tailWord_1977326).sum := by decide
  have hdescent : baseEnd_1977326 < baseStart_1977326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977332 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1977332 : Nat := 118140960795 + 1977332 * 2 ^ 59
def prefixEnd_1977332 : Nat := 4983230072969 + 3 ^ 40 * 1977332 * 2
def baseEnd_1977332 : Nat := 225627051003591758479205

theorem tailTrace_1977332 : CollatzResearch.WordTrace tailWord_1977332 prefixEnd_1977332 225627051003591758479205 := by
  unfold tailWord_1977332
  simp only [CollatzResearch.WordTrace]
  refine ⟨36059611436235670132463125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48079481914980893509950833 36059611436235670132463125)
  ·
    refine ⟨1690294286073547037459209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36059611436235670132463125 1690294286073547037459209)
    ·
      refine ⟨1267720714555160278094407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1690294286073547037459209 1267720714555160278094407)
      ·
        refine ⟨1901581071832740417141611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267720714555160278094407 1901581071832740417141611)
        ·
          refine ⟨2852371607749110625712417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901581071832740417141611 2852371607749110625712417)
          ·
            refine ⟨2139278705811832969284313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2852371607749110625712417 2139278705811832969284313)
            ·
              refine ⟨1604459029358874726963235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139278705811832969284313 1604459029358874726963235)
              ·
                refine ⟨2406688544038312090444853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604459029358874726963235 2406688544038312090444853)
                ·
                  refine ⟨225627051003591758479205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2406688544038312090444853 225627051003591758479205)
                  ·
                    rfl

theorem cell22_1977332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1977332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977332 prefixEnd_1977332 := by exact prefixLift 1977332
  have htrace : WordTrace (prefixWord ++ tailWord_1977332) baseStart_1977332 baseEnd_1977332 := by
    simpa [prefixWord, tailWord_1977332, baseEnd_1977332] using wordTrace_append hprefix tailTrace_1977332
  have hstable : (prefixWord ++ tailWord_1977332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977332).length < 2 ^ (prefixWord ++ tailWord_1977332).sum := by decide
  have hdescent : baseEnd_1977332 < baseStart_1977332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977429 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1977429 : Nat := 118140960795 + 1977429 * 2 ^ 59
def prefixEnd_1977429 : Nat := 4983230072969 + 3 ^ 40 * 1977429 * 2
def baseEnd_1977429 : Nat := 676914358093099355762317

theorem tailTrace_1977429 : CollatzResearch.WordTrace tailWord_1977429 prefixEnd_1977429 676914358093099355762317 := by
  unfold tailWord_1977429
  simp only [CollatzResearch.WordTrace]
  refine ⟨72122760753119925831207341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48081840502079950554138227 72122760753119925831207341)
  ·
    refine ⟨27046035282419972186702753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72122760753119925831207341 27046035282419972186702753)
    ·
      refine ⟨20284526461814979140027065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27046035282419972186702753 20284526461814979140027065)
      ·
        refine ⟨15213394846361234355020299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20284526461814979140027065 15213394846361234355020299)
        ·
          refine ⟨22820092269541851532530449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15213394846361234355020299 22820092269541851532530449)
          ·
            refine ⟨17115069202156388649397837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22820092269541851532530449 17115069202156388649397837)
            ·
              refine ⟨6418150950808645743524189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17115069202156388649397837 6418150950808645743524189)
              ·
                refine ⟨2406806606553242153821571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6418150950808645743524189 2406806606553242153821571)
                ·
                  refine ⟨3610209909829863230732357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406806606553242153821571 3610209909829863230732357)
                  ·
                    refine ⟨676914358093099355762317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610209909829863230732357 676914358093099355762317)
                    ·
                      rfl

theorem cell22_1977429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1977429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977429 prefixEnd_1977429 := by exact prefixLift 1977429
  have htrace : WordTrace (prefixWord ++ tailWord_1977429) baseStart_1977429 baseEnd_1977429 := by
    simpa [prefixWord, tailWord_1977429, baseEnd_1977429] using wordTrace_append hprefix tailTrace_1977429
  have hstable : (prefixWord ++ tailWord_1977429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977429).length < 2 ^ (prefixWord ++ tailWord_1977429).sum := by decide
  have hdescent : baseEnd_1977429 < baseStart_1977429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977457 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1977457 : Nat := 118140960795 + 1977457 * 2 ^ 59
def prefixEnd_1977457 : Nat := 4983230072969 + 3 ^ 40 * 1977457 * 2
def baseEnd_1977457 : Nat := 676923943065316616062231

theorem tailTrace_1977457 : CollatzResearch.WordTrace tailWord_1977457 prefixEnd_1977457 676923943065316616062231 := by
  unfold tailWord_1977457
  simp only [CollatzResearch.WordTrace]
  refine ⟨72123781997018486613226625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48082521331345657742151083 72123781997018486613226625)
  ·
    refine ⟨54092836497763864959919969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72123781997018486613226625 54092836497763864959919969)
    ·
      refine ⟨40569627373322898719939977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54092836497763864959919969 40569627373322898719939977)
      ·
        refine ⟨30427220529992174039954983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40569627373322898719939977 30427220529992174039954983)
        ·
          refine ⟨45640830794988261059932475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30427220529992174039954983 45640830794988261059932475)
          ·
            refine ⟨68461246192482391589898713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45640830794988261059932475 68461246192482391589898713)
            ·
              refine ⟨51345934644361793692424035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68461246192482391589898713 51345934644361793692424035)
              ·
                refine ⟨77018901966542690538636053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51345934644361793692424035 77018901966542690538636053)
                ·
                  refine ⟨3610261029681688618998565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77018901966542690538636053 3610261029681688618998565)
                  ·
                    refine ⟨676923943065316616062231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610261029681688618998565 676923943065316616062231)
                    ·
                      rfl

theorem cell22_1977457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1977457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977457 prefixEnd_1977457 := by exact prefixLift 1977457
  have htrace : WordTrace (prefixWord ++ tailWord_1977457) baseStart_1977457 baseEnd_1977457 := by
    simpa [prefixWord, tailWord_1977457, baseEnd_1977457] using wordTrace_append hprefix tailTrace_1977457
  have hstable : (prefixWord ++ tailWord_1977457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977457).length < 2 ^ (prefixWord ++ tailWord_1977457).sum := by decide
  have hdescent : baseEnd_1977457 < baseStart_1977457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977506 : List Nat := [3, 3, 1, 3, 2, 1, 2, 7]
def baseStart_1977506 : Nat := 118140960795 + 1977506 * 2 ^ 59
def prefixEnd_1977506 : Nat := 4983230072969 + 3 ^ 40 * 1977506 * 2
def baseEnd_1977506 : Nat := 75215635196299646843009

theorem tailTrace_1977506 : CollatzResearch.WordTrace tailWord_1977506 prefixEnd_1977506 75215635196299646843009 := by
  unfold tailWord_1977506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18031392293460241995440093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48083712782560645321173581 18031392293460241995440093)
  ·
    refine ⟨6761772110047590748290035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18031392293460241995440093 6761772110047590748290035)
    ·
      refine ⟨10142658165071386122435053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6761772110047590748290035 10142658165071386122435053)
      ·
        refine ⟨3803496811901769795913145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10142658165071386122435053 3803496811901769795913145)
        ·
          refine ⟨2852622608926327346934859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3803496811901769795913145 2852622608926327346934859)
          ·
            refine ⟨4278933913389491020402289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852622608926327346934859 4278933913389491020402289)
            ·
              refine ⟨3209200435042118265301717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278933913389491020402289 3209200435042118265301717)
              ·
                refine ⟨75215635196299646843009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3209200435042118265301717 75215635196299646843009)
                ·
                  rfl

theorem cell22_1977506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_1977506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977506 prefixEnd_1977506 := by exact prefixLift 1977506
  have htrace : WordTrace (prefixWord ++ tailWord_1977506) baseStart_1977506 baseEnd_1977506 := by
    simpa [prefixWord, tailWord_1977506, baseEnd_1977506] using wordTrace_append hprefix tailTrace_1977506
  have hstable : (prefixWord ++ tailWord_1977506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977506).length < 2 ^ (prefixWord ++ tailWord_1977506).sum := by decide
  have hdescent : baseEnd_1977506 < baseStart_1977506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977579 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 6]
def baseStart_1977579 : Nat := 118140960795 + 1977579 * 2 ^ 59
def prefixEnd_1977579 : Nat := 4983230072969 + 3 ^ 40 * 1977579 * 2
def baseEnd_1977579 : Nat := 225655235386182988170619

theorem tailTrace_1977579 : CollatzResearch.WordTrace tailWord_1977579 prefixEnd_1977579 225655235386182988170619 := by
  unfold tailWord_1977579
  simp only [CollatzResearch.WordTrace]
  refine ⟨72128231702576501449167791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48085487801717667632778527 72128231702576501449167791)
  ·
    refine ⟨108192347553864752173751687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72128231702576501449167791 108192347553864752173751687)
    ·
      refine ⟨162288521330797128260627531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108192347553864752173751687 162288521330797128260627531)
      ·
        refine ⟨243432781996195692390941297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162288521330797128260627531 243432781996195692390941297)
        ·
          refine ⟨182574586497146769293205973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243432781996195692390941297 182574586497146769293205973)
          ·
            refine ⟨4279091871026877405309515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 182574586497146769293205973 4279091871026877405309515)
            ·
              refine ⟨6418637806540316107964273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279091871026877405309515 6418637806540316107964273)
              ·
                refine ⟨4813978354905237080973205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6418637806540316107964273 4813978354905237080973205)
                ·
                  refine ⟨225655235386182988170619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4813978354905237080973205 225655235386182988170619)
                  ·
                    rfl

theorem cell22_1977579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 6].length) (baseStart_1977579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977579 prefixEnd_1977579 := by exact prefixLift 1977579
  have htrace : WordTrace (prefixWord ++ tailWord_1977579) baseStart_1977579 baseEnd_1977579 := by
    simpa [prefixWord, tailWord_1977579, baseEnd_1977579] using wordTrace_append hprefix tailTrace_1977579
  have hstable : (prefixWord ++ tailWord_1977579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977579).length < 2 ^ (prefixWord ++ tailWord_1977579).sum := by decide
  have hdescent : baseEnd_1977579 < baseStart_1977579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977581 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1977581 : Nat := 118140960795 + 1977581 * 2 ^ 59
def prefixEnd_1977581 : Nat := 4983230072969 + 3 ^ 40 * 1977581 * 2
def baseEnd_1977581 : Nat := 676966390799421625961851

theorem tailTrace_1977581 : CollatzResearch.WordTrace tailWord_1977581 prefixEnd_1977581 676966390799421625961851 := by
  unfold tailWord_1977581
  simp only [CollatzResearch.WordTrace]
  refine ⟨72128304648569255790740597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48085536432379503860493731 72128304648569255790740597)
  ·
    refine ⟨6762028560803367730381931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72128304648569255790740597 6762028560803367730381931)
    ·
      refine ⟨10143042841205051595572897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6762028560803367730381931 10143042841205051595572897)
      ·
        refine ⟨7607282130903788696679673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10143042841205051595572897 7607282130903788696679673)
        ·
          refine ⟨5705461598177841522509755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7607282130903788696679673 5705461598177841522509755)
          ·
            refine ⟨8558192397266762283764633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705461598177841522509755 8558192397266762283764633)
            ·
              refine ⟨6418644297950071712823475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558192397266762283764633 6418644297950071712823475)
              ·
                refine ⟨9627966446925107569235213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418644297950071712823475 9627966446925107569235213)
                ·
                  refine ⟨3610487417596915338463205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9627966446925107569235213 3610487417596915338463205)
                  ·
                    refine ⟨676966390799421625961851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610487417596915338463205 676966390799421625961851)
                    ·
                      rfl

theorem cell22_1977581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1977581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977581 prefixEnd_1977581 := by exact prefixLift 1977581
  have htrace : WordTrace (prefixWord ++ tailWord_1977581) baseStart_1977581 baseEnd_1977581 := by
    simpa [prefixWord, tailWord_1977581, baseEnd_1977581] using wordTrace_append hprefix tailTrace_1977581
  have hstable : (prefixWord ++ tailWord_1977581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977581).length < 2 ^ (prefixWord ++ tailWord_1977581).sum := by decide
  have hdescent : baseEnd_1977581 < baseStart_1977581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977594 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_1977594 : Nat := 118140960795 + 1977594 * 2 ^ 59
def prefixEnd_1977594 : Nat := 4983230072969 + 3 ^ 40 * 1977594 * 2
def baseEnd_1977594 : Nat := 676970840965093925386811

theorem tailTrace_1977594 : CollatzResearch.WordTrace tailWord_1977594 prefixEnd_1977594 676970840965093925386811 := by
  unfold tailWord_1977594
  simp only [CollatzResearch.WordTrace]
  refine ⟨18032194699380539752740959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48085852531681439340642557 18032194699380539752740959)
  ·
    refine ⟨27048292049070809629111439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18032194699380539752740959 27048292049070809629111439)
    ·
      refine ⟨40572438073606214443667159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27048292049070809629111439 40572438073606214443667159)
      ·
        refine ⟨60858657110409321665500739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40572438073606214443667159 60858657110409321665500739)
        ·
          refine ⟨91287985665613982498251109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60858657110409321665500739 91287985665613982498251109)
          ·
            refine ⟨17116497312302621718422083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91287985665613982498251109 17116497312302621718422083)
            ·
              refine ⟨25674745968453932577633125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17116497312302621718422083 25674745968453932577633125)
              ·
                refine ⟨4814014869085112358306211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25674745968453932577633125 4814014869085112358306211)
                ·
                  refine ⟨7221022303627668537459317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814014869085112358306211 7221022303627668537459317)
                  ·
                    refine ⟨676970840965093925386811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7221022303627668537459317 676970840965093925386811)
                    ·
                      rfl

theorem cell22_1977594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_1977594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977594 prefixEnd_1977594 := by exact prefixLift 1977594
  have htrace : WordTrace (prefixWord ++ tailWord_1977594) baseStart_1977594 baseEnd_1977594 := by
    simpa [prefixWord, tailWord_1977594, baseEnd_1977594] using wordTrace_append hprefix tailTrace_1977594
  have hstable : (prefixWord ++ tailWord_1977594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977594).length < 2 ^ (prefixWord ++ tailWord_1977594).sum := by decide
  have hdescent : baseEnd_1977594 < baseStart_1977594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977598 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1977598 : Nat := 118140960795 + 1977598 * 2 ^ 59
def prefixEnd_1977598 : Nat := 4983230072969 + 3 ^ 40 * 1977598 * 2
def baseEnd_1977598 : Nat := 676972210246839248286799

theorem tailTrace_1977598 : CollatzResearch.WordTrace tailWord_1977598 prefixEnd_1977598 676972210246839248286799 := by
  unfold tailWord_1977598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016115586188458461763681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48085949793005111796072965 9016115586188458461763681)
  ·
    refine ⟨6762086689641343846322761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9016115586188458461763681 6762086689641343846322761)
    ·
      refine ⟨5071565017231007884742071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6762086689641343846322761 5071565017231007884742071)
      ·
        refine ⟨7607347525846511827113107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5071565017231007884742071 7607347525846511827113107)
        ·
          refine ⟨11411021288769767740669661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7607347525846511827113107 11411021288769767740669661)
          ·
            refine ⟨4279132983288662902751123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11411021288769767740669661 4279132983288662902751123)
            ·
              refine ⟨6418699474932994354126685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279132983288662902751123 6418699474932994354126685)
              ·
                refine ⟨2407012303099872882797507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6418699474932994354126685 2407012303099872882797507)
                ·
                  refine ⟨3610518454649809324196261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407012303099872882797507 3610518454649809324196261)
                  ·
                    refine ⟨676972210246839248286799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610518454649809324196261 676972210246839248286799)
                    ·
                      rfl

theorem cell22_1977598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1977598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977598 prefixEnd_1977598 := by exact prefixLift 1977598
  have htrace : WordTrace (prefixWord ++ tailWord_1977598) baseStart_1977598 baseEnd_1977598 := by
    simpa [prefixWord, tailWord_1977598, baseEnd_1977598] using wordTrace_append hprefix tailTrace_1977598
  have hstable : (prefixWord ++ tailWord_1977598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977598).length < 2 ^ (prefixWord ++ tailWord_1977598).sum := by decide
  have hdescent : baseEnd_1977598 < baseStart_1977598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977609 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_1977609 : Nat := 118140960795 + 1977609 * 2 ^ 59
def prefixEnd_1977609 : Nat := 4983230072969 + 3 ^ 40 * 1977609 * 2
def baseEnd_1977609 : Nat := 676975975771638886261765

theorem tailTrace_1977609 : CollatzResearch.WordTrace tailWord_1977609 prefixEnd_1977609 676975975771638886261765 := by
  unfold tailWord_1977609
  simp only [CollatzResearch.WordTrace]
  refine ⟨72129325892467816572759881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48086217261645211048506587 72129325892467816572759881)
  ·
    refine ⟨54096994419350862429569911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72129325892467816572759881 54096994419350862429569911)
    ·
      refine ⟨81145491629026293644354867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54096994419350862429569911 81145491629026293644354867)
      ·
        refine ⟨121718237443539440466532301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81145491629026293644354867 121718237443539440466532301)
        ·
          refine ⟨45644339041327290174949613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121718237443539440466532301 45644339041327290174949613)
          ·
            refine ⟨17116627140497733815606105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45644339041327290174949613 17116627140497733815606105)
            ·
              refine ⟨12837470355373300361704579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17116627140497733815606105 12837470355373300361704579)
              ·
                refine ⟨19256205533059950542556869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12837470355373300361704579 19256205533059950542556869)
                ·
                  refine ⟨3610538537448740726729413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19256205533059950542556869 3610538537448740726729413)
                  ·
                    refine ⟨676975975771638886261765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610538537448740726729413 676975975771638886261765)
                    ·
                      rfl

theorem cell22_1977609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_1977609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977609 prefixEnd_1977609 := by exact prefixLift 1977609
  have htrace : WordTrace (prefixWord ++ tailWord_1977609) baseStart_1977609 baseEnd_1977609 := by
    simpa [prefixWord, tailWord_1977609, baseEnd_1977609] using wordTrace_append hprefix tailTrace_1977609
  have hstable : (prefixWord ++ tailWord_1977609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977609).length < 2 ^ (prefixWord ++ tailWord_1977609).sum := by decide
  have hdescent : baseEnd_1977609 < baseStart_1977609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977611 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 4, 3]
def baseStart_1977611 : Nat := 118140960795 + 1977611 * 2 ^ 59
def prefixEnd_1977611 : Nat := 4983230072969 + 3 ^ 40 * 1977611 * 2
def baseEnd_1977611 : Nat := 676976660412511547711759

theorem tailTrace_1977611 : CollatzResearch.WordTrace tailWord_1977611 prefixEnd_1977611 676976660412511547711759 := by
  unfold tailWord_1977611
  simp only [CollatzResearch.WordTrace]
  refine ⟨72129398838460570914332687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48086265892307047276221791 72129398838460570914332687)
  ·
    refine ⟨108194098257690856371499031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72129398838460570914332687 108194098257690856371499031)
    ·
      refine ⟨162291147386536284557248547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108194098257690856371499031 162291147386536284557248547)
      ·
        refine ⟨243436721079804426835872821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162291147386536284557248547 243436721079804426835872821)
        ·
          refine ⟨22822192601231665015863077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243436721079804426835872821 22822192601231665015863077)
          ·
            refine ⟨4279161112730937190474327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22822192601231665015863077 4279161112730937190474327)
            ·
              refine ⟨6418741669096405785711491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279161112730937190474327 6418741669096405785711491)
              ·
                refine ⟨9628112503644608678567237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418741669096405785711491 9628112503644608678567237)
                ·
                  refine ⟨1805271094433364127231357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9628112503644608678567237 1805271094433364127231357)
                  ·
                    refine ⟨676976660412511547711759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1805271094433364127231357 676976660412511547711759)
                    ·
                      rfl

theorem cell22_1977611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 3].length) (baseStart_1977611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977611 prefixEnd_1977611 := by exact prefixLift 1977611
  have htrace : WordTrace (prefixWord ++ tailWord_1977611) baseStart_1977611 baseEnd_1977611 := by
    simpa [prefixWord, tailWord_1977611, baseEnd_1977611] using wordTrace_append hprefix tailTrace_1977611
  have hstable : (prefixWord ++ tailWord_1977611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977611).length < 2 ^ (prefixWord ++ tailWord_1977611).sum := by decide
  have hdescent : baseEnd_1977611 < baseStart_1977611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977673 : List Nat := [1, 2, 1, 1, 2, 3, 2, 6, 1, 3]
def baseStart_1977673 : Nat := 118140960795 + 1977673 * 2 ^ 59
def prefixEnd_1977673 : Nat := 4983230072969 + 3 ^ 40 * 1977673 * 2
def baseEnd_1977673 : Nat := 676997884279564052661569

theorem tailTrace_1977673 : CollatzResearch.WordTrace tailWord_1977673 prefixEnd_1977673 676997884279564052661569 := by
  unfold tailWord_1977673
  simp only [CollatzResearch.WordTrace]
  refine ⟨72131660164235955503089673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48087773442823970335393115 72131660164235955503089673)
  ·
    refine ⟨54098745123176966627317255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72131660164235955503089673 54098745123176966627317255)
    ·
      refine ⟨81148117684765449940975883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54098745123176966627317255 81148117684765449940975883)
      ·
        refine ⟨121722176527148174911463825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81148117684765449940975883 121722176527148174911463825)
        ·
          refine ⟨91291632395361131183597869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121722176527148174911463825 91291632395361131183597869)
          ·
            refine ⟨34234362148260424193849201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91291632395361131183597869 34234362148260424193849201)
            ·
              refine ⟨25675771611195318145386901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34234362148260424193849201 25675771611195318145386901)
              ·
                refine ⟨1203551794274780538065011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25675771611195318145386901 1203551794274780538065011)
                ·
                  refine ⟨1805327691412170807097517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203551794274780538065011 1805327691412170807097517)
                  ·
                    refine ⟨676997884279564052661569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1805327691412170807097517 676997884279564052661569)
                    ·
                      rfl

theorem cell22_1977673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 3].length) (baseStart_1977673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977673 prefixEnd_1977673 := by exact prefixLift 1977673
  have htrace : WordTrace (prefixWord ++ tailWord_1977673) baseStart_1977673 baseEnd_1977673 := by
    simpa [prefixWord, tailWord_1977673, baseEnd_1977673] using wordTrace_append hprefix tailTrace_1977673
  have hstable : (prefixWord ++ tailWord_1977673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977673).length < 2 ^ (prefixWord ++ tailWord_1977673).sum := by decide
  have hdescent : baseEnd_1977673 < baseStart_1977673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977748 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1977748 : Nat := 118140960795 + 1977748 * 2 ^ 59
def prefixEnd_1977748 : Nat := 4983230072969 + 3 ^ 40 * 1977748 * 2
def baseEnd_1977748 : Nat := 225674519437429619012113

theorem tailTrace_1977748 : CollatzResearch.WordTrace tailWord_1977748 prefixEnd_1977748 225674519437429619012113 := by
  unfold tailWord_1977748
  simp only [CollatzResearch.WordTrace]
  refine ⟨36067197819482121656034949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48089597092642828874713265 36067197819482121656034949)
  ·
    refine ⟨6762599591152897810506553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36067197819482121656034949 6762599591152897810506553)
    ·
      refine ⟨5071949693364673357879915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6762599591152897810506553 5071949693364673357879915)
      ·
        refine ⟨7607924540047010036819873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5071949693364673357879915 7607924540047010036819873)
        ·
          refine ⟨5705943405035257527614905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7607924540047010036819873 5705943405035257527614905)
          ·
            refine ⟨4279457553776443145711179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5705943405035257527614905 4279457553776443145711179)
            ·
              refine ⟨6419186330664664718566769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279457553776443145711179 6419186330664664718566769)
              ·
                refine ⟨4814389747998498538925077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6419186330664664718566769 4814389747998498538925077)
                ·
                  refine ⟨225674519437429619012113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4814389747998498538925077 225674519437429619012113)
                  ·
                    rfl

theorem cell22_1977748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1977748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977748 prefixEnd_1977748 := by exact prefixLift 1977748
  have htrace : WordTrace (prefixWord ++ tailWord_1977748) baseStart_1977748 baseEnd_1977748 := by
    simpa [prefixWord, tailWord_1977748, baseEnd_1977748] using wordTrace_append hprefix tailTrace_1977748
  have hstable : (prefixWord ++ tailWord_1977748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977748).length < 2 ^ (prefixWord ++ tailWord_1977748).sum := by decide
  have hdescent : baseEnd_1977748 < baseStart_1977748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977806 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1977806 : Nat := 118140960795 + 1977806 * 2 ^ 59
def prefixEnd_1977806 : Nat := 4983230072969 + 3 ^ 40 * 1977806 * 2
def baseEnd_1977806 : Nat := 677043412897596039086161

theorem tailTrace_1977806 : CollatzResearch.WordTrace tailWord_1977806 prefixEnd_1977806 677043412897596039086161 := by
  unfold tailWord_1977806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9017063884094264902210159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48091007381836079478454181 9017063884094264902210159)
  ·
    refine ⟨13525595826141397353315239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9017063884094264902210159 13525595826141397353315239)
    ·
      refine ⟨20288393739212096029972859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13525595826141397353315239 20288393739212096029972859)
      ·
        refine ⟨30432590608818144044959289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20288393739212096029972859 30432590608818144044959289)
        ·
          refine ⟨22824442956613608033719467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30432590608818144044959289 22824442956613608033719467)
          ·
            refine ⟨34236664434920412050579201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22824442956613608033719467 34236664434920412050579201)
            ·
              refine ⟨25677498326190309037934401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34236664434920412050579201 25677498326190309037934401)
              ·
                refine ⟨19258123744642731778450801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25677498326190309037934401 19258123744642731778450801)
                ·
                  refine ⟨14443592808482048833838101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19258123744642731778450801 14443592808482048833838101)
                  ·
                    refine ⟨677043412897596039086161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14443592808482048833838101 677043412897596039086161)
                    ·
                      rfl

theorem cell22_1977806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1977806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977806 prefixEnd_1977806 := by exact prefixLift 1977806
  have htrace : WordTrace (prefixWord ++ tailWord_1977806) baseStart_1977806 baseEnd_1977806 := by
    simpa [prefixWord, tailWord_1977806, baseEnd_1977806] using wordTrace_append hprefix tailTrace_1977806
  have hstable : (prefixWord ++ tailWord_1977806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977806).length < 2 ^ (prefixWord ++ tailWord_1977806).sum := by decide
  have hdescent : baseEnd_1977806 < baseStart_1977806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977836 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_1977836 : Nat := 118140960795 + 1977836 * 2 ^ 59
def prefixEnd_1977836 : Nat := 4983230072969 + 3 ^ 40 * 1977836 * 2
def baseEnd_1977836 : Nat := 677053682510685960836069

theorem tailTrace_1977836 : CollatzResearch.WordTrace tailWord_1977836 prefixEnd_1977836 677053682510685960836069 := by
  unfold tailWord_1977836
  simp only [CollatzResearch.WordTrace]
  refine ⟨36068802631322717170636681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48091736841763622894182241 36068802631322717170636681)
  ·
    refine ⟨27051601973492037877977511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36068802631322717170636681 27051601973492037877977511)
    ·
      refine ⟨40577402960238056816966267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27051601973492037877977511 40577402960238056816966267)
      ·
        refine ⟨60866104440357085225449401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40577402960238056816966267 60866104440357085225449401)
        ·
          refine ⟨45649578330267813919087051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60866104440357085225449401 45649578330267813919087051)
          ·
            refine ⟨68474367495401720878630577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45649578330267813919087051 68474367495401720878630577)
            ·
              refine ⟨51355775621551290658972933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68474367495401720878630577 51355775621551290658972933)
              ·
                refine ⟨9629207929040866998557425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51355775621551290658972933 9629207929040866998557425)
                ·
                  refine ⟨7221905946780650248918069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9629207929040866998557425 7221905946780650248918069)
                  ·
                    refine ⟨677053682510685960836069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7221905946780650248918069 677053682510685960836069)
                    ·
                      rfl

theorem cell22_1977836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_1977836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977836 prefixEnd_1977836 := by exact prefixLift 1977836
  have htrace : WordTrace (prefixWord ++ tailWord_1977836) baseStart_1977836 baseEnd_1977836 := by
    simpa [prefixWord, tailWord_1977836, baseEnd_1977836] using wordTrace_append hprefix tailTrace_1977836
  have hstable : (prefixWord ++ tailWord_1977836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977836).length < 2 ^ (prefixWord ++ tailWord_1977836).sum := by decide
  have hdescent : baseEnd_1977836 < baseStart_1977836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977838 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1977838 : Nat := 118140960795 + 1977838 * 2 ^ 59
def prefixEnd_1977838 : Nat := 4983230072969 + 3 ^ 40 * 1977838 * 2
def baseEnd_1977838 : Nat := 225684789050519540762021

theorem tailTrace_1977838 : CollatzResearch.WordTrace tailWord_1977838 prefixEnd_1977838 225684789050519540762021 := by
  unfold tailWord_1977838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9017209776079773585355771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48091785472425459121897445 9017209776079773585355771)
  ·
    refine ⟨13525814664119660378033657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9017209776079773585355771 13525814664119660378033657)
    ·
      refine ⟨10144360998089745283525243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13525814664119660378033657 10144360998089745283525243)
      ·
        refine ⟨15216541497134617925287865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10144360998089745283525243 15216541497134617925287865)
        ·
          refine ⟨11412406122850963443965899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15216541497134617925287865 11412406122850963443965899)
          ·
            refine ⟨17118609184276445165948849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11412406122850963443965899 17118609184276445165948849)
            ·
              refine ⟨12838956888207333874461637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17118609184276445165948849 12838956888207333874461637)
              ·
                refine ⟨2407304416538875101461557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12838956888207333874461637 2407304416538875101461557)
                ·
                  refine ⟨225684789050519540762021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2407304416538875101461557 225684789050519540762021)
                  ·
                    rfl

theorem cell22_1977838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1977838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977838 prefixEnd_1977838 := by exact prefixLift 1977838
  have htrace : WordTrace (prefixWord ++ tailWord_1977838) baseStart_1977838 baseEnd_1977838 := by
    simpa [prefixWord, tailWord_1977838, baseEnd_1977838] using wordTrace_append hprefix tailTrace_1977838
  have hstable : (prefixWord ++ tailWord_1977838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977838).length < 2 ^ (prefixWord ++ tailWord_1977838).sum := by decide
  have hdescent : baseEnd_1977838 < baseStart_1977838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977842 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_1977842 : Nat := 118140960795 + 1977842 * 2 ^ 59
def prefixEnd_1977842 : Nat := 4983230072969 + 3 ^ 40 * 1977842 * 2
def baseEnd_1977842 : Nat := 677055736433303945186051

theorem tailTrace_1977842 : CollatzResearch.WordTrace tailWord_1977842 prefixEnd_1977842 677055736433303945186051 := by
  unfold tailWord_1977842
  simp only [CollatzResearch.WordTrace]
  refine ⟨18034456025155924341497945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48091882733749131577327853 18034456025155924341497945)
  ·
    refine ⟨13525842018866943256123459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18034456025155924341497945 13525842018866943256123459)
    ·
      refine ⟨20288763028300414884185189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13525842018866943256123459 20288763028300414884185189)
      ·
        refine ⟨3804143067806327790784723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20288763028300414884185189 3804143067806327790784723)
        ·
          refine ⟨5706214601709491686177085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3804143067806327790784723 5706214601709491686177085)
          ·
            refine ⟨2139830475641059382316407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5706214601709491686177085 2139830475641059382316407)
            ·
              refine ⟨3209745713461589073474611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139830475641059382316407 3209745713461589073474611)
              ·
                refine ⟨4814618570192383610211917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209745713461589073474611 4814618570192383610211917)
                ·
                  refine ⟨1805481963822143853829469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4814618570192383610211917 1805481963822143853829469)
                  ·
                    refine ⟨677055736433303945186051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1805481963822143853829469 677055736433303945186051)
                    ·
                      rfl

theorem cell22_1977842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_1977842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977842 prefixEnd_1977842 := by exact prefixLift 1977842
  have htrace : WordTrace (prefixWord ++ tailWord_1977842) baseStart_1977842 baseEnd_1977842 := by
    simpa [prefixWord, tailWord_1977842, baseEnd_1977842] using wordTrace_append hprefix tailTrace_1977842
  have hstable : (prefixWord ++ tailWord_1977842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977842).length < 2 ^ (prefixWord ++ tailWord_1977842).sum := by decide
  have hdescent : baseEnd_1977842 < baseStart_1977842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977851 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 5, 4]
def baseStart_1977851 : Nat := 118140960795 + 1977851 * 2 ^ 59
def prefixEnd_1977851 : Nat := 4983230072969 + 3 ^ 40 * 1977851 * 2
def baseEnd_1977851 : Nat := 677058817317230921711023

theorem tailTrace_1977851 : CollatzResearch.WordTrace tailWord_1977851 prefixEnd_1977851 677058817317230921711023 := by
  unfold tailWord_1977851
  simp only [CollatzResearch.WordTrace]
  refine ⟨72138152357591091903069407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48092101571727394602046271 72138152357591091903069407)
  ·
    refine ⟨108207228536386637854604111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72138152357591091903069407 108207228536386637854604111)
    ·
      refine ⟨162310842804579956781906167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108207228536386637854604111 162310842804579956781906167)
      ·
        refine ⟨243466264206869935172859251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162310842804579956781906167 243466264206869935172859251)
        ·
          refine ⟨365199396310304902759288877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243466264206869935172859251 365199396310304902759288877)
          ·
            refine ⟨136949773616364338534733329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365199396310304902759288877 136949773616364338534733329)
            ·
              refine ⟨102712330212273253901049997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136949773616364338534733329 102712330212273253901049997)
              ·
                refine ⟨38517123829602470212893749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102712330212273253901049997 38517123829602470212893749)
                ·
                  refine ⟨3610980359025231582458789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38517123829602470212893749 3610980359025231582458789)
                  ·
                    refine ⟨677058817317230921711023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3610980359025231582458789 677058817317230921711023)
                    ·
                      rfl

theorem cell22_1977851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 4].length) (baseStart_1977851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977851 prefixEnd_1977851 := by exact prefixLift 1977851
  have htrace : WordTrace (prefixWord ++ tailWord_1977851) baseStart_1977851 baseEnd_1977851 := by
    simpa [prefixWord, tailWord_1977851, baseEnd_1977851] using wordTrace_append hprefix tailTrace_1977851
  have hstable : (prefixWord ++ tailWord_1977851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977851).length < 2 ^ (prefixWord ++ tailWord_1977851).sum := by decide
  have hdescent : baseEnd_1977851 < baseStart_1977851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977898 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1977898 : Nat := 118140960795 + 1977898 * 2 ^ 59
def prefixEnd_1977898 : Nat := 4983230072969 + 3 ^ 40 * 1977898 * 2
def baseEnd_1977898 : Nat := 677074906377738465785879

theorem tailTrace_1977898 : CollatzResearch.WordTrace tailWord_1977898 prefixEnd_1977898 677074906377738465785879 := by
  unfold tailWord_1977898
  simp only [CollatzResearch.WordTrace]
  refine ⟨18034966647105204732507587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48093244392280545953353565 18034966647105204732507587)
  ·
    refine ⟨27052449970657807098761381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18034966647105204732507587 27052449970657807098761381)
    ·
      refine ⟨5072334369498338831017759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27052449970657807098761381 5072334369498338831017759)
      ·
        refine ⟨7608501554247508246526639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072334369498338831017759 7608501554247508246526639)
        ·
          refine ⟨11412752331371262369789959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608501554247508246526639 11412752331371262369789959)
          ·
            refine ⟨17119128497056893554684939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11412752331371262369789959 17119128497056893554684939)
            ·
              refine ⟨25678692745585340332027409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17119128497056893554684939 25678692745585340332027409)
              ·
                refine ⟨19259019559189005249020557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25678692745585340332027409 19259019559189005249020557)
                ·
                  refine ⟨7222132334695876968382709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19259019559189005249020557 7222132334695876968382709)
                  ·
                    refine ⟨677074906377738465785879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7222132334695876968382709 677074906377738465785879)
                    ·
                      rfl

theorem cell22_1977898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1977898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977898 prefixEnd_1977898 := by exact prefixLift 1977898
  have htrace : WordTrace (prefixWord ++ tailWord_1977898) baseStart_1977898 baseEnd_1977898 := by
    simpa [prefixWord, tailWord_1977898, baseEnd_1977898] using wordTrace_append hprefix tailTrace_1977898
  have hstable : (prefixWord ++ tailWord_1977898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977898).length < 2 ^ (prefixWord ++ tailWord_1977898).sum := by decide
  have hdescent : baseEnd_1977898 < baseStart_1977898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977949 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1977949 : Nat := 118140960795 + 1977949 * 2 ^ 59
def prefixEnd_1977949 : Nat := 4983230072969 + 3 ^ 40 * 1977949 * 2
def baseEnd_1977949 : Nat := 677092364719991332760723

theorem tailTrace_1977949 : CollatzResearch.WordTrace tailWord_1977949 prefixEnd_1977949 677092364719991332760723 := by
  unfold tailWord_1977949
  simp only [CollatzResearch.WordTrace]
  refine ⟨72141726711236054640136901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48094484474157369760091267 72141726711236054640136901)
  ·
    refine ⟨13526573758356760245025669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72141726711236054640136901 13526573758356760245025669)
    ·
      refine ⟨2536232579691892545942313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13526573758356760245025669 2536232579691892545942313)
      ·
        refine ⟨1902174434768919409456735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2536232579691892545942313 1902174434768919409456735)
        ·
          refine ⟨2853261652153379114185103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902174434768919409456735 2853261652153379114185103)
          ·
            refine ⟨4279892478230068671277655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853261652153379114185103 4279892478230068671277655)
            ·
              refine ⟨6419838717345103006916483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279892478230068671277655 6419838717345103006916483)
              ·
                refine ⟨9629758076017654510374725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419838717345103006916483 9629758076017654510374725)
                ·
                  refine ⟨1805579639253310220695261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9629758076017654510374725 1805579639253310220695261)
                  ·
                    refine ⟨677092364719991332760723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1805579639253310220695261 677092364719991332760723)
                    ·
                      rfl

theorem cell22_1977949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1977949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977949 prefixEnd_1977949 := by exact prefixLift 1977949
  have htrace : WordTrace (prefixWord ++ tailWord_1977949) baseStart_1977949 baseEnd_1977949 := by
    simpa [prefixWord, tailWord_1977949, baseEnd_1977949] using wordTrace_append hprefix tailTrace_1977949
  have hstable : (prefixWord ++ tailWord_1977949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977949).length < 2 ^ (prefixWord ++ tailWord_1977949).sum := by decide
  have hdescent : baseEnd_1977949 < baseStart_1977949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977994 : List Nat := [3, 1, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_1977994 : Nat := 118140960795 + 1977994 * 2 ^ 59
def prefixEnd_1977994 : Nat := 4983230072969 + 3 ^ 40 * 1977994 * 2
def baseEnd_1977994 : Nat := 677107769139626215385585

theorem tailTrace_1977994 : CollatzResearch.WordTrace tailWord_1977994 prefixEnd_1977994 677107769139626215385585 := by
  unfold tailWord_1977994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18035841999018256831381259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48095578664048684883683357 18035841999018256831381259)
  ·
    refine ⟨27053762998527385247071889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18035841999018256831381259 27053762998527385247071889)
    ·
      refine ⟨20290322248895538935303917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27053762998527385247071889 20290322248895538935303917)
      ·
        refine ⟨7608870843335827100738969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20290322248895538935303917 7608870843335827100738969)
        ·
          refine ⟨5706653132501870325554227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7608870843335827100738969 5706653132501870325554227)
          ·
            refine ⟨8559979698752805488331341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5706653132501870325554227 8559979698752805488331341)
            ·
              refine ⟨3209992387032302058124253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8559979698752805488331341 3209992387032302058124253)
              ·
                refine ⟨1203747145137113271796595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3209992387032302058124253 1203747145137113271796595)
                ·
                  refine ⟨1805620717705669907694893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203747145137113271796595 1805620717705669907694893)
                  ·
                    refine ⟨677107769139626215385585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1805620717705669907694893 677107769139626215385585)
                    ·
                      rfl

theorem cell22_1977994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_1977994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1977994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1977994 prefixEnd_1977994 := by exact prefixLift 1977994
  have htrace : WordTrace (prefixWord ++ tailWord_1977994) baseStart_1977994 baseEnd_1977994 := by
    simpa [prefixWord, tailWord_1977994, baseEnd_1977994] using wordTrace_append hprefix tailTrace_1977994
  have hstable : (prefixWord ++ tailWord_1977994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977994).length < 2 ^ (prefixWord ++ tailWord_1977994).sum := by decide
  have hdescent : baseEnd_1977994 < baseStart_1977994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978037 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1978037 : Nat := 118140960795 + 1978037 * 2 ^ 59
def prefixEnd_1978037 : Nat := 4983230072969 + 3 ^ 40 * 1978037 * 2
def baseEnd_1978037 : Nat := 677122488918388436560453

theorem tailTrace_1978037 : CollatzResearch.WordTrace tailWord_1978037 prefixEnd_1978037 677122488918388436560453 := by
  unfold tailWord_1978037
  simp only [CollatzResearch.WordTrace]
  refine ⟨72144936334917245669340365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48096624223278163779560243 72144936334917245669340365)
  ·
    refine ⟨27054351125593967126002637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72144936334917245669340365 27054351125593967126002637)
    ·
      refine ⟨10145381672097737672250989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27054351125593967126002637 10145381672097737672250989)
      ·
        refine ⟨3804518127036651627094121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10145381672097737672250989 3804518127036651627094121)
        ·
          refine ⟨2853388595277488720320591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3804518127036651627094121 2853388595277488720320591)
          ·
            refine ⟨4280082892916233080480887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853388595277488720320591 4280082892916233080480887)
            ·
              refine ⟨6420124339374349620721331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280082892916233080480887 6420124339374349620721331)
              ·
                refine ⟨9630186509061524431081997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420124339374349620721331 9630186509061524431081997)
                ·
                  refine ⟨3611319940898071661655749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9630186509061524431081997 3611319940898071661655749)
                  ·
                    refine ⟨677122488918388436560453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3611319940898071661655749 677122488918388436560453)
                    ·
                      rfl

theorem cell22_1978037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1978037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978037 prefixEnd_1978037 := by exact prefixLift 1978037
  have htrace : WordTrace (prefixWord ++ tailWord_1978037) baseStart_1978037 baseEnd_1978037 := by
    simpa [prefixWord, tailWord_1978037, baseEnd_1978037] using wordTrace_append hprefix tailTrace_1978037
  have hstable : (prefixWord ++ tailWord_1978037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978037).length < 2 ^ (prefixWord ++ tailWord_1978037).sum := by decide
  have hdescent : baseEnd_1978037 < baseStart_1978037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978052 : List Nat := [2, 3, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1978052 : Nat := 118140960795 + 1978052 * 2 ^ 59
def prefixEnd_1978052 : Nat := 4983230072969 + 3 ^ 40 * 1978052 * 2
def baseEnd_1978052 : Nat := 225709207908311132478469

theorem tailTrace_1978052 : CollatzResearch.WordTrace tailWord_1978052 prefixEnd_1978052 225709207908311132478469 := by
  unfold tailWord_1978052
  simp only [CollatzResearch.WordTrace]
  refine ⟨36072741714931451615568205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48096988953241935487424273 36072741714931451615568205)
  ·
    refine ⟨13527278143099294355838077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36072741714931451615568205 13527278143099294355838077)
    ·
      refine ⟨5072729303662235383439279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13527278143099294355838077 5072729303662235383439279)
      ·
        refine ⟨7609093955493353075158919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072729303662235383439279 7609093955493353075158919)
        ·
          refine ⟨11413640933240029612738379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7609093955493353075158919 11413640933240029612738379)
          ·
            refine ⟨17120461399860044419107569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11413640933240029612738379 17120461399860044419107569)
            ·
              refine ⟨12840346049895033314330677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17120461399860044419107569 12840346049895033314330677)
              ·
                refine ⟨1203782442177659373218501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12840346049895033314330677 1203782442177659373218501)
                ·
                  refine ⟨225709207908311132478469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203782442177659373218501 225709207908311132478469)
                  ·
                    rfl

theorem cell22_1978052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1978052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978052 prefixEnd_1978052 := by exact prefixLift 1978052
  have htrace : WordTrace (prefixWord ++ tailWord_1978052) baseStart_1978052 baseEnd_1978052 := by
    simpa [prefixWord, tailWord_1978052, baseEnd_1978052] using wordTrace_append hprefix tailTrace_1978052
  have hstable : (prefixWord ++ tailWord_1978052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978052).length < 2 ^ (prefixWord ++ tailWord_1978052).sum := by decide
  have hdescent : baseEnd_1978052 < baseStart_1978052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978065 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_1978065 : Nat := 118140960795 + 1978065 * 2 ^ 59
def prefixEnd_1978065 : Nat := 4983230072969 + 3 ^ 40 * 1978065 * 2
def baseEnd_1978065 : Nat := 677132073890605696860367

theorem tailTrace_1978065 : CollatzResearch.WordTrace tailWord_1978065 prefixEnd_1978065 677132073890605696860367 := by
  unfold tailWord_1978065
  simp only [CollatzResearch.WordTrace]
  refine ⟨72145957578815806451359649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48097305052543870967573099 72145957578815806451359649)
  ·
    refine ⟨54109468184111854838519737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72145957578815806451359649 54109468184111854838519737)
    ·
      refine ⟨40582101138083891128889803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54109468184111854838519737 40582101138083891128889803)
      ·
        refine ⟨60873151707125836693334705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40582101138083891128889803 60873151707125836693334705)
        ·
          refine ⟨45654863780344377520001029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60873151707125836693334705 45654863780344377520001029)
          ·
            refine ⟨8560286958814570785000193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45654863780344377520001029 8560286958814570785000193)
            ·
              refine ⟨6420215219110928088750145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8560286958814570785000193 6420215219110928088750145)
              ·
                refine ⟨4815161414333196066562609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6420215219110928088750145 4815161414333196066562609)
                ·
                  refine ⟨3611371060749897049921957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4815161414333196066562609 3611371060749897049921957)
                  ·
                    refine ⟨677132073890605696860367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3611371060749897049921957 677132073890605696860367)
                    ·
                      rfl

theorem cell22_1978065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_1978065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978065 prefixEnd_1978065 := by exact prefixLift 1978065
  have htrace : WordTrace (prefixWord ++ tailWord_1978065) baseStart_1978065 baseEnd_1978065 := by
    simpa [prefixWord, tailWord_1978065, baseEnd_1978065] using wordTrace_append hprefix tailTrace_1978065
  have hstable : (prefixWord ++ tailWord_1978065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978065).length < 2 ^ (prefixWord ++ tailWord_1978065).sum := by decide
  have hdescent : baseEnd_1978065 < baseStart_1978065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978140 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1978140 : Nat := 118140960795 + 1978140 * 2 ^ 59
def prefixEnd_1978140 : Nat := 4983230072969 + 3 ^ 40 * 1978140 * 2
def baseEnd_1978140 : Nat := 677157747923330501235137

theorem tailTrace_1978140 : CollatzResearch.WordTrace tailWord_1978140 prefixEnd_1978140 677157747923330501235137 := by
  unfold tailWord_1978140
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074346526772047130169937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48099128702362729506893249 36074346526772047130169937)
  ·
    refine ⟨27055759895079035347627453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36074346526772047130169937 27055759895079035347627453)
    ·
      refine ⟨10145909960654638255360295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27055759895079035347627453 10145909960654638255360295)
      ·
        refine ⟨15218864940981957383040443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10145909960654638255360295 15218864940981957383040443)
        ·
          refine ⟨22828297411472936074560665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15218864940981957383040443 22828297411472936074560665)
          ·
            refine ⟨17121223058604702055920499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22828297411472936074560665 17121223058604702055920499)
            ·
              refine ⟨25681834587907053083880749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17121223058604702055920499 25681834587907053083880749)
              ·
                refine ⟨9630687970465144906455281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25681834587907053083880749 9630687970465144906455281)
                ·
                  refine ⟨7223015977848858679841461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9630687970465144906455281 7223015977848858679841461)
                  ·
                    refine ⟨677157747923330501235137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7223015977848858679841461 677157747923330501235137)
                    ·
                      rfl

theorem cell22_1978140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1978140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978140 prefixEnd_1978140 := by exact prefixLift 1978140
  have htrace : WordTrace (prefixWord ++ tailWord_1978140) baseStart_1978140 baseEnd_1978140 := by
    simpa [prefixWord, tailWord_1978140, baseEnd_1978140] using wordTrace_append hprefix tailTrace_1978140
  have hstable : (prefixWord ++ tailWord_1978140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978140).length < 2 ^ (prefixWord ++ tailWord_1978140).sum := by decide
  have hdescent : baseEnd_1978140 < baseStart_1978140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978163 : List Nat := [1, 1, 1, 2, 8, 1, 1, 3, 1, 3]
def baseStart_1978163 : Nat := 118140960795 + 1978163 * 2 ^ 59
def prefixEnd_1978163 : Nat := 4983230072969 + 3 ^ 40 * 1978163 * 2
def baseEnd_1978163 : Nat := 677165621293366107910067

theorem tailTrace_1978163 : CollatzResearch.WordTrace tailWord_1978163 prefixEnd_1978163 677165621293366107910067 := by
  unfold tailWord_1978163
  simp only [CollatzResearch.WordTrace]
  refine ⟨72149531932460769188427143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48099687954973846125618095 72149531932460769188427143)
  ·
    refine ⟨108224297898691153782640715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72149531932460769188427143 108224297898691153782640715)
    ·
      refine ⟨162336446848036730673961073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108224297898691153782640715 162336446848036730673961073)
      ·
        refine ⟨121752335136027548005470805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162336446848036730673961073 121752335136027548005470805)
        ·
          refine ⟨1426785177375322828189111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 121752335136027548005470805 1426785177375322828189111)
          ·
            refine ⟨2140177766062984242283667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426785177375322828189111 2140177766062984242283667)
            ·
              refine ⟨3210266649094476363425501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140177766062984242283667 3210266649094476363425501)
              ·
                refine ⟨1203849993410428636284563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3210266649094476363425501 1203849993410428636284563)
                ·
                  refine ⟨1805774990115642954426845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203849993410428636284563 1805774990115642954426845)
                  ·
                    refine ⟨677165621293366107910067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1805774990115642954426845 677165621293366107910067)
                    ·
                      rfl

theorem cell22_1978163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 1, 3].length) (baseStart_1978163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978163 prefixEnd_1978163 := by exact prefixLift 1978163
  have htrace : WordTrace (prefixWord ++ tailWord_1978163) baseStart_1978163 baseEnd_1978163 := by
    simpa [prefixWord, tailWord_1978163, baseEnd_1978163] using wordTrace_append hprefix tailTrace_1978163
  have hstable : (prefixWord ++ tailWord_1978163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978163).length < 2 ^ (prefixWord ++ tailWord_1978163).sum := by decide
  have hdescent : baseEnd_1978163 < baseStart_1978163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978172 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_1978172 : Nat := 118140960795 + 1978172 * 2 ^ 59
def prefixEnd_1978172 : Nat := 4983230072969 + 3 ^ 40 * 1978172 * 2
def baseEnd_1978172 : Nat := 677168702177293084435039

theorem tailTrace_1978172 : CollatzResearch.WordTrace tailWord_1978172 prefixEnd_1978172 677168702177293084435039 := by
  unfold tailWord_1978172
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074930094714081862752385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48099906792952109150336513 36074930094714081862752385)
  ·
    refine ⟨27056197571035561397064289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36074930094714081862752385 27056197571035561397064289)
    ·
      refine ⟨20292148178276671047798217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27056197571035561397064289 20292148178276671047798217)
      ·
        refine ⟨15219111133707503285848663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20292148178276671047798217 15219111133707503285848663)
        ·
          refine ⟨22828666700561254928772995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15219111133707503285848663 22828666700561254928772995)
          ·
            refine ⟨34243000050841882393159493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22828666700561254928772995 34243000050841882393159493)
            ·
              refine ⟨6420562509532852948717405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34243000050841882393159493 6420562509532852948717405)
              ·
                refine ⟨2407710941074819855769027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6420562509532852948717405 2407710941074819855769027)
                ·
                  refine ⟨3611566411612229783653541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407710941074819855769027 3611566411612229783653541)
                  ·
                    refine ⟨677168702177293084435039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3611566411612229783653541 677168702177293084435039)
                    ·
                      rfl

theorem cell22_1978172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_1978172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978172 prefixEnd_1978172 := by exact prefixLift 1978172
  have htrace : WordTrace (prefixWord ++ tailWord_1978172) baseStart_1978172 baseEnd_1978172 := by
    simpa [prefixWord, tailWord_1978172, baseEnd_1978172] using wordTrace_append hprefix tailTrace_1978172
  have hstable : (prefixWord ++ tailWord_1978172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978172).length < 2 ^ (prefixWord ++ tailWord_1978172).sum := by decide
  have hdescent : baseEnd_1978172 < baseStart_1978172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978215 : List Nat := [1, 1, 5, 1, 2, 1, 1, 10]
def baseStart_1978215 : Nat := 118140960795 + 1978215 * 2 ^ 59
def prefixEnd_1978215 : Nat := 4983230072969 + 3 ^ 40 * 1978215 * 2
def baseEnd_1978215 : Nat := 75242602439561700623323

theorem tailTrace_1978215 : CollatzResearch.WordTrace tailWord_1978215 prefixEnd_1978215 75242602439561700623323 := by
  unfold tailWord_1978215
  simp only [CollatzResearch.WordTrace]
  refine ⟨72151428528272382069320099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48100952352181588046213399 72151428528272382069320099)
  ·
    refine ⟨108227142792408573103980149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72151428528272382069320099 108227142792408573103980149)
    ·
      refine ⟨10146294636788303728498139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108227142792408573103980149 10146294636788303728498139)
      ·
        refine ⟨15219441955182455592747209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10146294636788303728498139 15219441955182455592747209)
        ·
          refine ⟨11414581466386841694560407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15219441955182455592747209 11414581466386841694560407)
          ·
            refine ⟨17121872199580262541840611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11414581466386841694560407 17121872199580262541840611)
            ·
              refine ⟨25682808299370393812760917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17121872199580262541840611 25682808299370393812760917)
              ·
                refine ⟨75242602439561700623323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25682808299370393812760917 75242602439561700623323)
                ·
                  rfl

theorem cell22_1978215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 10].length) (baseStart_1978215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978215 prefixEnd_1978215 := by exact prefixLift 1978215
  have htrace : WordTrace (prefixWord ++ tailWord_1978215) baseStart_1978215 baseEnd_1978215 := by
    simpa [prefixWord, tailWord_1978215, baseEnd_1978215] using wordTrace_append hprefix tailTrace_1978215
  have hstable : (prefixWord ++ tailWord_1978215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978215).length < 2 ^ (prefixWord ++ tailWord_1978215).sum := by decide
  have hdescent : baseEnd_1978215 < baseStart_1978215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978238 : List Nat := [4, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1978238 : Nat := 118140960795 + 1978238 * 2 ^ 59
def prefixEnd_1978238 : Nat := 4983230072969 + 3 ^ 40 * 1978238 * 2
def baseEnd_1978238 : Nat := 225730431775363637428279

theorem tailTrace_1978238 : CollatzResearch.WordTrace tailWord_1978238 prefixEnd_1978238 225730431775363637428279 := by
  unfold tailWord_1978238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019033425898632124675921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48101511604792704664938245 9019033425898632124675921)
  ·
    refine ⟨6764275069423974093506941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9019033425898632124675921 6764275069423974093506941)
    ·
      refine ⟨2536603151033990285065103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6764275069423974093506941 2536603151033990285065103)
      ·
        refine ⟨3804904726550985427597655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536603151033990285065103 3804904726550985427597655)
        ·
          refine ⟨5707357089826478141396483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3804904726550985427597655 5707357089826478141396483)
          ·
            refine ⟨8561035634739717212094725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707357089826478141396483 8561035634739717212094725)
            ·
              refine ⟨1605194181513696977267761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8561035634739717212094725 1605194181513696977267761)
              ·
                refine ⟨1203895636135272732950821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605194181513696977267761 1203895636135272732950821)
                ·
                  refine ⟨225730431775363637428279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203895636135272732950821 225730431775363637428279)
                  ·
                    rfl

theorem cell22_1978238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1978238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978238 prefixEnd_1978238 := by exact prefixLift 1978238
  have htrace : WordTrace (prefixWord ++ tailWord_1978238) baseStart_1978238 baseEnd_1978238 := by
    simpa [prefixWord, tailWord_1978238, baseEnd_1978238] using wordTrace_append hprefix tailTrace_1978238
  have hstable : (prefixWord ++ tailWord_1978238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978238).length < 2 ^ (prefixWord ++ tailWord_1978238).sum := by decide
  have hdescent : baseEnd_1978238 < baseStart_1978238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978245 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1978245 : Nat := 118140960795 + 1978245 * 2 ^ 59
def prefixEnd_1978245 : Nat := 4983230072969 + 3 ^ 40 * 1978245 * 2
def baseEnd_1978245 : Nat := 677193691569145227359815

theorem tailTrace_1978245 : CollatzResearch.WordTrace tailWord_1978245 prefixEnd_1978245 677193691569145227359815 := by
  unfold tailWord_1978245
  simp only [CollatzResearch.WordTrace]
  refine ⟨72152522718163697192912189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48101681812109131461941459 72152522718163697192912189)
  ·
    refine ⟨27057196019311386447342071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72152522718163697192912189 27057196019311386447342071)
    ·
      refine ⟨40585794028967079671013107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27057196019311386447342071 40585794028967079671013107)
      ·
        refine ⟨60878691043450619506519661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40585794028967079671013107 60878691043450619506519661)
        ·
          refine ⟨22829509141293982314944873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60878691043450619506519661 22829509141293982314944873)
          ·
            refine ⟨17122131855970486736208655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22829509141293982314944873 17122131855970486736208655)
            ·
              refine ⟨25683197783955730104312983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17122131855970486736208655 25683197783955730104312983)
              ·
                refine ⟨38524796675933595156469475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25683197783955730104312983 38524796675933595156469475)
                ·
                  refine ⟨57787195013900392734704213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38524796675933595156469475 57787195013900392734704213)
                  ·
                    refine ⟨677193691569145227359815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57787195013900392734704213 677193691569145227359815)
                    ·
                      rfl

theorem cell22_1978245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1978245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978245 prefixEnd_1978245 := by exact prefixLift 1978245
  have htrace : WordTrace (prefixWord ++ tailWord_1978245) baseStart_1978245 baseEnd_1978245 := by
    simpa [prefixWord, tailWord_1978245, baseEnd_1978245] using wordTrace_append hprefix tailTrace_1978245
  have hstable : (prefixWord ++ tailWord_1978245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978245).length < 2 ^ (prefixWord ++ tailWord_1978245).sum := by decide
  have hdescent : baseEnd_1978245 < baseStart_1978245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978275 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 3, 7]
def baseStart_1978275 : Nat := 118140960795 + 1978275 * 2 ^ 59
def prefixEnd_1978275 : Nat := 4983230072969 + 3 ^ 40 * 1978275 * 2
def baseEnd_1978275 : Nat := 677203961182235149109723

theorem tailTrace_1978275 : CollatzResearch.WordTrace tailWord_1978275 prefixEnd_1978275 677203961182235149109723 := by
  unfold tailWord_1978275
  simp only [CollatzResearch.WordTrace]
  refine ⟨72153616908055012316504279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48102411272036674877669519 72153616908055012316504279)
  ·
    refine ⟨108230425362082518474756419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72153616908055012316504279 108230425362082518474756419)
    ·
      refine ⟨162345638043123777712134629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108230425362082518474756419 162345638043123777712134629)
      ·
        refine ⟨30439807133085708321025243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162345638043123777712134629 30439807133085708321025243)
        ·
          refine ⟨45659710699628562481537865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30439807133085708321025243 45659710699628562481537865)
          ·
            refine ⟨34244783024721421861153399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45659710699628562481537865 34244783024721421861153399)
            ·
              refine ⟨51367174537082132791730099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34244783024721421861153399 51367174537082132791730099)
              ·
                refine ⟨77050761805623199187595149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51367174537082132791730099 77050761805623199187595149)
                ·
                  refine ⟨28894035677108699695348181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77050761805623199187595149 28894035677108699695348181)
                  ·
                    refine ⟨677203961182235149109723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28894035677108699695348181 677203961182235149109723)
                    ·
                      rfl

theorem cell22_1978275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_1978275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978275 prefixEnd_1978275 := by exact prefixLift 1978275
  have htrace : WordTrace (prefixWord ++ tailWord_1978275) baseStart_1978275 baseEnd_1978275 := by
    simpa [prefixWord, tailWord_1978275, baseEnd_1978275] using wordTrace_append hprefix tailTrace_1978275
  have hstable : (prefixWord ++ tailWord_1978275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978275).length < 2 ^ (prefixWord ++ tailWord_1978275).sum := by decide
  have hdescent : baseEnd_1978275 < baseStart_1978275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978337 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1978337 : Nat := 118140960795 + 1978337 * 2 ^ 59
def prefixEnd_1978337 : Nat := 4983230072969 + 3 ^ 40 * 1978337 * 2
def baseEnd_1978337 : Nat := 677225185049287654059533

theorem tailTrace_1978337 : CollatzResearch.WordTrace tailWord_1978337 prefixEnd_1978337 677225185049287654059533 := by
  unfold tailWord_1978337
  simp only [CollatzResearch.WordTrace]
  refine ⟨72155878233830396905261265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48103918822553597936840843 72155878233830396905261265)
  ·
    refine ⟨54116908675372797678945949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72155878233830396905261265 54116908675372797678945949)
    ·
      refine ⟨20293840753264799129604731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54116908675372797678945949 20293840753264799129604731)
      ·
        refine ⟨30440761129897198694407097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20293840753264799129604731 30440761129897198694407097)
        ·
          refine ⟨22830570847422899020805323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30440761129897198694407097 22830570847422899020805323)
          ·
            refine ⟨34245856271134348531207985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22830570847422899020805323 34245856271134348531207985)
            ·
              refine ⟨25684392203350761398405989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34245856271134348531207985 25684392203350761398405989)
              ·
                refine ⟨4815823538128267762201123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25684392203350761398405989 4815823538128267762201123)
                ·
                  refine ⟨7223735307192401643301685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815823538128267762201123 7223735307192401643301685)
                  ·
                    refine ⟨677225185049287654059533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7223735307192401643301685 677225185049287654059533)
                    ·
                      rfl

theorem cell22_1978337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1978337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978337 prefixEnd_1978337 := by exact prefixLift 1978337
  have htrace : WordTrace (prefixWord ++ tailWord_1978337) baseStart_1978337 baseEnd_1978337 := by
    simpa [prefixWord, tailWord_1978337, baseEnd_1978337] using wordTrace_append hprefix tailTrace_1978337
  have hstable : (prefixWord ++ tailWord_1978337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978337).length < 2 ^ (prefixWord ++ tailWord_1978337).sum := by decide
  have hdescent : baseEnd_1978337 < baseStart_1978337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978352 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_1978352 : Nat := 118140960795 + 1978352 * 2 ^ 59
def prefixEnd_1978352 : Nat := 4983230072969 + 3 ^ 40 * 1978352 * 2
def baseEnd_1978352 : Nat := 677230319855832614934487

theorem tailTrace_1978352 : CollatzResearch.WordTrace tailWord_1978352 prefixEnd_1978352 677230319855832614934487 := by
  unfold tailWord_1978352
  simp only [CollatzResearch.WordTrace]
  refine ⟨36078212664388027233528655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48104283552517369644704873 36078212664388027233528655)
  ·
    refine ⟨54117318996582040850292983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36078212664388027233528655 54117318996582040850292983)
    ·
      refine ⟨81175978494873061275439475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54117318996582040850292983 81175978494873061275439475)
      ·
        refine ⟨121763967742309591913159213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81175978494873061275439475 121763967742309591913159213)
        ·
          refine ⟨45661487903366096967434705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121763967742309591913159213 45661487903366096967434705)
          ·
            refine ⟨34246115927524572725576029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45661487903366096967434705 34246115927524572725576029)
            ·
              refine ⟨12842293472821714772091011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34246115927524572725576029 12842293472821714772091011)
              ·
                refine ⟨19263440209232572158136517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842293472821714772091011 19263440209232572158136517)
                ·
                  refine ⟨3611895039231107279650597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19263440209232572158136517 3611895039231107279650597)
                  ·
                    refine ⟨677230319855832614934487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3611895039231107279650597 677230319855832614934487)
                    ·
                      rfl

theorem cell22_1978352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_1978352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978352 prefixEnd_1978352 := by exact prefixLift 1978352
  have htrace : WordTrace (prefixWord ++ tailWord_1978352) baseStart_1978352 baseEnd_1978352 := by
    simpa [prefixWord, tailWord_1978352, baseEnd_1978352] using wordTrace_append hprefix tailTrace_1978352
  have hstable : (prefixWord ++ tailWord_1978352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978352).length < 2 ^ (prefixWord ++ tailWord_1978352).sum := by decide
  have hdescent : baseEnd_1978352 < baseStart_1978352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978388 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1978388 : Nat := 118140960795 + 1978388 * 2 ^ 59
def prefixEnd_1978388 : Nat := 4983230072969 + 3 ^ 40 * 1978388 * 2
def baseEnd_1978388 : Nat := 677242643391540521034377

theorem tailTrace_1978388 : CollatzResearch.WordTrace tailWord_1978388 prefixEnd_1978388 677242643391540521034377 := by
  unfold tailWord_1978388
  simp only [CollatzResearch.WordTrace]
  refine ⟨36078869178322816307683909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48105158904430421743578545 36078869178322816307683909)
  ·
    refine ⟨6764787970935528057690733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36078869178322816307683909 6764787970935528057690733)
    ·
      refine ⟨2536795489100823021634025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6764787970935528057690733 2536795489100823021634025)
      ·
        refine ⟨1902596616825617266225519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2536795489100823021634025 1902596616825617266225519)
        ·
          refine ⟨2853894925238425899338279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902596616825617266225519 2853894925238425899338279)
          ·
            refine ⟨4280842387857638849007419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853894925238425899338279 4280842387857638849007419)
            ·
              refine ⟨6421263581786458273511129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280842387857638849007419 6421263581786458273511129)
              ·
                refine ⟨4815947686339843705133347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6421263581786458273511129 4815947686339843705133347)
                ·
                  refine ⟨7223921529509765557700021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815947686339843705133347 7223921529509765557700021)
                  ·
                    refine ⟨677242643391540521034377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7223921529509765557700021 677242643391540521034377)
                    ·
                      rfl

theorem cell22_1978388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1978388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978388 prefixEnd_1978388 := by exact prefixLift 1978388
  have htrace : WordTrace (prefixWord ++ tailWord_1978388) baseStart_1978388 baseEnd_1978388 := by
    simpa [prefixWord, tailWord_1978388, baseEnd_1978388] using wordTrace_append hprefix tailTrace_1978388
  have hstable : (prefixWord ++ tailWord_1978388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978388).length < 2 ^ (prefixWord ++ tailWord_1978388).sum := by decide
  have hdescent : baseEnd_1978388 < baseStart_1978388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978407 : List Nat := [1, 1, 7, 1, 3, 1, 2, 2, 4]
def baseStart_1978407 : Nat := 118140960795 + 1978407 * 2 ^ 59
def prefixEnd_1978407 : Nat := 4983230072969 + 3 ^ 40 * 1978407 * 2
def baseEnd_1978407 : Nat := 225749715826610268269773

theorem tailTrace_1978407 : CollatzResearch.WordTrace tailWord_1978407 prefixEnd_1978407 225749715826610268269773 := by
  unfold tailWord_1978407
  simp only [CollatzResearch.WordTrace]
  refine ⟨72158431343576798860309475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48105620895717865906872983 72158431343576798860309475)
  ·
    refine ⟨108237647015365198290464213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72158431343576798860309475 108237647015365198290464213)
    ·
      refine ⟨2536819851922621834932755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 108237647015365198290464213 2536819851922621834932755)
      ·
        refine ⟨3805229777883932752399133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536819851922621834932755 3805229777883932752399133)
        ·
          refine ⟨1426961166706474782149675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3805229777883932752399133 1426961166706474782149675)
          ·
            refine ⟨2140441750059712173224513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426961166706474782149675 2140441750059712173224513)
            ·
              refine ⟨1605331312544784129918385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140441750059712173224513 1605331312544784129918385)
              ·
                refine ⟨1203998484408588097438789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605331312544784129918385 1203998484408588097438789)
                ·
                  refine ⟨225749715826610268269773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203998484408588097438789 225749715826610268269773)
                  ·
                    rfl

theorem cell22_1978407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 4].length) (baseStart_1978407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978407 prefixEnd_1978407 := by exact prefixLift 1978407
  have htrace : WordTrace (prefixWord ++ tailWord_1978407) baseStart_1978407 baseEnd_1978407 := by
    simpa [prefixWord, tailWord_1978407, baseEnd_1978407] using wordTrace_append hprefix tailTrace_1978407
  have hstable : (prefixWord ++ tailWord_1978407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978407).length < 2 ^ (prefixWord ++ tailWord_1978407).sum := by decide
  have hdescent : baseEnd_1978407 < baseStart_1978407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978414 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1978414 : Nat := 118140960795 + 1978414 * 2 ^ 59
def prefixEnd_1978414 : Nat := 4983230072969 + 3 ^ 40 * 1978414 * 2
def baseEnd_1978414 : Nat := 677251543722885119884297

theorem tailTrace_1978414 : CollatzResearch.WordTrace tailWord_1978414 prefixEnd_1978414 677251543722885119884297 := by
  unfold tailWord_1978414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019835831818929881976787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48105791103034292703876197 9019835831818929881976787)
  ·
    refine ⟨13529753747728394822965181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9019835831818929881976787 13529753747728394822965181)
    ·
      refine ⟨5073657655398148058611943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13529753747728394822965181 5073657655398148058611943)
      ·
        refine ⟨7610486483097222087917915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073657655398148058611943 7610486483097222087917915)
        ·
          refine ⟨11415729724645833131876873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610486483097222087917915 11415729724645833131876873)
          ·
            refine ⟨8561797293484374848907655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11415729724645833131876873 8561797293484374848907655)
            ·
              refine ⟨12842695940226562273361483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561797293484374848907655 12842695940226562273361483)
              ·
                refine ⟨19264043910339843410042225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842695940226562273361483 19264043910339843410042225)
                ·
                  refine ⟨14448032932754882557531669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19264043910339843410042225 14448032932754882557531669)
                  ·
                    refine ⟨677251543722885119884297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14448032932754882557531669 677251543722885119884297)
                    ·
                      rfl

theorem cell22_1978414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1978414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978414 prefixEnd_1978414 := by exact prefixLift 1978414
  have htrace : WordTrace (prefixWord ++ tailWord_1978414) baseStart_1978414 baseEnd_1978414 := by
    simpa [prefixWord, tailWord_1978414, baseEnd_1978414] using wordTrace_append hprefix tailTrace_1978414
  have hstable : (prefixWord ++ tailWord_1978414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978414).length < 2 ^ (prefixWord ++ tailWord_1978414).sum := by decide
  have hdescent : baseEnd_1978414 < baseStart_1978414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978427 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 2, 5]
def baseStart_1978427 : Nat := 118140960795 + 1978427 * 2 ^ 59
def prefixEnd_1978427 : Nat := 4983230072969 + 3 ^ 40 * 1978427 * 2
def baseEnd_1978427 : Nat := 677255993888557419309257

theorem tailTrace_1978427 : CollatzResearch.WordTrace tailWord_1978427 prefixEnd_1978427 677255993888557419309257 := by
  unfold tailWord_1978427
  simp only [CollatzResearch.WordTrace]
  refine ⟨72159160803504342276037535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48106107202336228184025023 72159160803504342276037535)
  ·
    refine ⟨108238741205256513414056303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72159160803504342276037535 108238741205256513414056303)
    ·
      refine ⟨162358111807884770121084455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108238741205256513414056303 162358111807884770121084455)
      ·
        refine ⟨243537167711827155181626683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162358111807884770121084455 243537167711827155181626683)
        ·
          refine ⟨365305751567740732772440025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243537167711827155181626683 365305751567740732772440025)
          ·
            refine ⟨273979313675805549579330019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365305751567740732772440025 273979313675805549579330019)
            ·
              refine ⟨410968970513708324368995029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273979313675805549579330019 410968970513708324368995029)
              ·
                refine ⟨9632085246415038852398321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 410968970513708324368995029 9632085246415038852398321)
                ·
                  refine ⟨7224063934811279139298741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9632085246415038852398321 7224063934811279139298741)
                  ·
                    refine ⟨677255993888557419309257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7224063934811279139298741 677255993888557419309257)
                    ·
                      rfl

theorem cell22_1978427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_1978427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978427 prefixEnd_1978427 := by exact prefixLift 1978427
  have htrace : WordTrace (prefixWord ++ tailWord_1978427) baseStart_1978427 baseEnd_1978427 := by
    simpa [prefixWord, tailWord_1978427, baseEnd_1978427] using wordTrace_append hprefix tailTrace_1978427
  have hstable : (prefixWord ++ tailWord_1978427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978427).length < 2 ^ (prefixWord ++ tailWord_1978427).sum := by decide
  have hdescent : baseEnd_1978427 < baseStart_1978427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978429 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 5]
def baseStart_1978429 : Nat := 118140960795 + 1978429 * 2 ^ 59
def prefixEnd_1978429 : Nat := 4983230072969 + 3 ^ 40 * 1978429 * 2
def baseEnd_1978429 : Nat := 225752226176476693586417

theorem tailTrace_1978429 : CollatzResearch.WordTrace tailWord_1978429 prefixEnd_1978429 225752226176476693586417 := by
  unfold tailWord_1978429
  simp only [CollatzResearch.WordTrace]
  refine ⟨72159233749497096617610341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48106155832998064411740227 72159233749497096617610341)
  ·
    refine ⟨13529856328030705615801939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72159233749497096617610341 13529856328030705615801939)
    ·
      refine ⟨20294784492046058423702909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13529856328030705615801939 20294784492046058423702909)
      ·
        refine ⟨7610544184517271908888591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20294784492046058423702909 7610544184517271908888591)
        ·
          refine ⟨11415816276775907863332887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610544184517271908888591 11415816276775907863332887)
          ·
            refine ⟨17123724415163861794999331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11415816276775907863332887 17123724415163861794999331)
            ·
              refine ⟨25685586622745792692498997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17123724415163861794999331 25685586622745792692498997)
              ·
                refine ⟨2408023745882418064921781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25685586622745792692498997 2408023745882418064921781)
                ·
                  refine ⟨225752226176476693586417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2408023745882418064921781 225752226176476693586417)
                  ·
                    rfl

theorem cell22_1978429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_1978429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978429 prefixEnd_1978429 := by exact prefixLift 1978429
  have htrace : WordTrace (prefixWord ++ tailWord_1978429) baseStart_1978429 baseEnd_1978429 := by
    simpa [prefixWord, tailWord_1978429, baseEnd_1978429] using wordTrace_append hprefix tailTrace_1978429
  have hstable : (prefixWord ++ tailWord_1978429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978429).length < 2 ^ (prefixWord ++ tailWord_1978429).sum := by decide
  have hdescent : baseEnd_1978429 < baseStart_1978429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978450 : List Nat := [3, 2, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1978450 : Nat := 118140960795 + 1978450 * 2 ^ 59
def prefixEnd_1978450 : Nat := 4983230072969 + 3 ^ 40 * 1978450 * 2
def baseEnd_1978450 : Nat := 677263867258593025984187

theorem tailTrace_1978450 : CollatzResearch.WordTrace tailWord_1978450 prefixEnd_1978450 677263867258593025984187 := by
  unfold tailWord_1978450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18039999920605254301031201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48106666454947344802749869 18039999920605254301031201)
  ·
    refine ⟨13529999940453940725773401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18039999920605254301031201 13529999940453940725773401)
    ·
      refine ⟨10147499955340455544330051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13529999940453940725773401 10147499955340455544330051)
      ·
        refine ⟨15221249933010683316495077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10147499955340455544330051 15221249933010683316495077)
        ·
          refine ⟨2853984362439503121842827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15221249933010683316495077 2853984362439503121842827)
          ·
            refine ⟨4280976543659254682764241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853984362439503121842827 4280976543659254682764241)
            ·
              refine ⟨3210732407744441012073181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4280976543659254682764241 3210732407744441012073181)
              ·
                refine ⟨1204024652904165379527443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3210732407744441012073181 1204024652904165379527443)
                ·
                  refine ⟨1806036979356248069291165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204024652904165379527443 1806036979356248069291165)
                  ·
                    refine ⟨677263867258593025984187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1806036979356248069291165 677263867258593025984187)
                    ·
                      rfl

theorem cell22_1978450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1978450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978450 prefixEnd_1978450 := by exact prefixLift 1978450
  have htrace : WordTrace (prefixWord ++ tailWord_1978450) baseStart_1978450 baseEnd_1978450 := by
    simpa [prefixWord, tailWord_1978450, baseEnd_1978450] using wordTrace_append hprefix tailTrace_1978450
  have hstable : (prefixWord ++ tailWord_1978450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978450).length < 2 ^ (prefixWord ++ tailWord_1978450).sum := by decide
  have hdescent : baseEnd_1978450 < baseStart_1978450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978457 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 8]
def baseStart_1978457 : Nat := 118140960795 + 1978457 * 2 ^ 59
def prefixEnd_1978457 : Nat := 4983230072969 + 3 ^ 40 * 1978457 * 2
def baseEnd_1978457 : Nat := 225755421167215780353055

theorem tailTrace_1978457 : CollatzResearch.WordTrace tailWord_1978457 prefixEnd_1978457 225755421167215780353055 := by
  unfold tailWord_1978457
  simp only [CollatzResearch.WordTrace]
  refine ⟨72160254993395657399629625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48106836662263771599753083 72160254993395657399629625)
  ·
    refine ⟨54120191245046743049722219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72160254993395657399629625 54120191245046743049722219)
    ·
      refine ⟨81180286867570114574583329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54120191245046743049722219 81180286867570114574583329)
      ·
        refine ⟨60885215150677585930937497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81180286867570114574583329 60885215150677585930937497)
        ·
          refine ⟨45663911363008189448203123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60885215150677585930937497 45663911363008189448203123)
          ·
            refine ⟨68495867044512284172304685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45663911363008189448203123 68495867044512284172304685)
            ·
              refine ⟨25685950141692106564614257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68495867044512284172304685 25685950141692106564614257)
              ·
                refine ⟨19264462606269079923460693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25685950141692106564614257 19264462606269079923460693)
                ·
                  refine ⟨225755421167215780353055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19264462606269079923460693 225755421167215780353055)
                  ·
                    rfl

theorem cell22_1978457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_1978457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978457 prefixEnd_1978457 := by exact prefixLift 1978457
  have htrace : WordTrace (prefixWord ++ tailWord_1978457) baseStart_1978457 baseEnd_1978457 := by
    simpa [prefixWord, tailWord_1978457, baseEnd_1978457] using wordTrace_append hprefix tailTrace_1978457
  have hstable : (prefixWord ++ tailWord_1978457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978457).length < 2 ^ (prefixWord ++ tailWord_1978457).sum := by decide
  have hdescent : baseEnd_1978457 < baseStart_1978457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978461 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1978461 : Nat := 118140960795 + 1978461 * 2 ^ 59
def prefixEnd_1978461 : Nat := 4983230072969 + 3 ^ 40 * 1978461 * 2
def baseEnd_1978461 : Nat := 677267632783392663959153

theorem tailTrace_1978461 : CollatzResearch.WordTrace tailWord_1978461 prefixEnd_1978461 677267632783392663959153 := by
  unfold tailWord_1978461
  simp only [CollatzResearch.WordTrace]
  refine ⟨72160400885381166082775237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48106933923587444055183491 72160400885381166082775237)
  ·
    refine ⟨13530075166008968640520357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72160400885381166082775237 13530075166008968640520357)
    ·
      refine ⟨2536889093626681620097567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13530075166008968640520357 2536889093626681620097567)
      ·
        refine ⟨3805333640440022430146351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536889093626681620097567 3805333640440022430146351)
        ·
          refine ⟨5708000460660033645219527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805333640440022430146351 5708000460660033645219527)
          ·
            refine ⟨8562000690990050467829291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708000460660033645219527 8562000690990050467829291)
            ·
              refine ⟨12843001036485075701743937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8562000690990050467829291 12843001036485075701743937)
              ·
                refine ⟨9632250777363806776307953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12843001036485075701743937 9632250777363806776307953)
                ·
                  refine ⟨7224188083022855082230965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9632250777363806776307953 7224188083022855082230965)
                  ·
                    refine ⟨677267632783392663959153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7224188083022855082230965 677267632783392663959153)
                    ·
                      rfl

theorem cell22_1978461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1978461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978461 prefixEnd_1978461 := by exact prefixLift 1978461
  have htrace : WordTrace (prefixWord ++ tailWord_1978461) baseStart_1978461 baseEnd_1978461 := by
    simpa [prefixWord, tailWord_1978461, baseEnd_1978461] using wordTrace_append hprefix tailTrace_1978461
  have hstable : (prefixWord ++ tailWord_1978461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978461).length < 2 ^ (prefixWord ++ tailWord_1978461).sum := by decide
  have hdescent : baseEnd_1978461 < baseStart_1978461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978506 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1978506 : Nat := 118140960795 + 1978506 * 2 ^ 59
def prefixEnd_1978506 : Nat := 4983230072969 + 3 ^ 40 * 1978506 * 2
def baseEnd_1978506 : Nat := 677283037203027546584015

theorem tailTrace_1978506 : CollatzResearch.WordTrace tailWord_1978506 prefixEnd_1978506 677283037203027546584015 := by
  unfold tailWord_1978506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18040510542554534692040843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48108028113478759178775581 18040510542554534692040843)
  ·
    refine ⟨27060765813831802038061265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18040510542554534692040843 27060765813831802038061265)
    ·
      refine ⟨20295574360373851528545949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27060765813831802038061265 20295574360373851528545949)
      ·
        refine ⟨7610840385140194323204731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20295574360373851528545949 7610840385140194323204731)
        ·
          refine ⟨11416260577710291484807097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610840385140194323204731 11416260577710291484807097)
          ·
            refine ⟨8562195433282718613605323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11416260577710291484807097 8562195433282718613605323)
            ·
              refine ⟨12843293149924077920407985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8562195433282718613605323 12843293149924077920407985)
              ·
                refine ⟨9632469862443058440305989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12843293149924077920407985 9632469862443058440305989)
                ·
                  refine ⟨1806088099208073457557373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9632469862443058440305989 1806088099208073457557373)
                  ·
                    refine ⟨677283037203027546584015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1806088099208073457557373 677283037203027546584015)
                    ·
                      rfl

theorem cell22_1978506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1978506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978506 prefixEnd_1978506 := by exact prefixLift 1978506
  have htrace : WordTrace (prefixWord ++ tailWord_1978506) baseStart_1978506 baseEnd_1978506 := by
    simpa [prefixWord, tailWord_1978506, baseEnd_1978506] using wordTrace_append hprefix tailTrace_1978506
  have hstable : (prefixWord ++ tailWord_1978506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978506).length < 2 ^ (prefixWord ++ tailWord_1978506).sum := by decide
  have hdescent : baseEnd_1978506 < baseStart_1978506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978518 : List Nat := [5, 3, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1978518 : Nat := 118140960795 + 1978518 * 2 ^ 59
def prefixEnd_1978518 : Nat := 4983230072969 + 3 ^ 40 * 1978518 * 2
def baseEnd_1978518 : Nat := 677287145048263515283979

theorem tailTrace_1978518 : CollatzResearch.WordTrace tailWord_1978518 prefixEnd_1978518 677287145048263515283979 := by
  unfold tailWord_1978518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510154990385916551100013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48108319897449776545066805 4510154990385916551100013)
  ·
    refine ⟨1691308121394718706662505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4510154990385916551100013 1691308121394718706662505)
    ·
      refine ⟨1268481091046039029996879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1691308121394718706662505 1268481091046039029996879)
      ·
        refine ⟨1902721636569058544995319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268481091046039029996879 1902721636569058544995319)
        ·
          refine ⟨2854082454853587817492979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902721636569058544995319 2854082454853587817492979)
          ·
            refine ⟨4281123682280381726239469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854082454853587817492979 4281123682280381726239469)
            ·
              refine ⟨1605421380855143147339801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4281123682280381726239469 1605421380855143147339801)
              ·
                refine ⟨1204066035641357360504851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605421380855143147339801 1204066035641357360504851)
                ·
                  refine ⟨1806099053462036040757277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204066035641357360504851 1806099053462036040757277)
                  ·
                    refine ⟨677287145048263515283979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1806099053462036040757277 677287145048263515283979)
                    ·
                      rfl

theorem cell22_1978518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1978518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978518 prefixEnd_1978518 := by exact prefixLift 1978518
  have htrace : WordTrace (prefixWord ++ tailWord_1978518) baseStart_1978518 baseEnd_1978518 := by
    simpa [prefixWord, tailWord_1978518, baseEnd_1978518] using wordTrace_append hprefix tailTrace_1978518
  have hstable : (prefixWord ++ tailWord_1978518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978518).length < 2 ^ (prefixWord ++ tailWord_1978518).sum := by decide
  have hdescent : baseEnd_1978518 < baseStart_1978518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978568 : List Nat := [2, 1, 3, 1, 2, 1, 1, 7, 1, 3]
def baseStart_1978568 : Nat := 118140960795 + 1978568 * 2 ^ 59
def prefixEnd_1978568 : Nat := 4983230072969 + 3 ^ 40 * 1978568 * 2
def baseEnd_1978568 : Nat := 677304261070080051533825

theorem tailTrace_1978568 : CollatzResearch.WordTrace tailWord_1978568 prefixEnd_1978568 677304261070080051533825 := by
  unfold tailWord_1978568
  simp only [CollatzResearch.WordTrace]
  refine ⟨36082151747996761678460179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48109535663995682237946905 36082151747996761678460179)
  ·
    refine ⟨54123227621995142517690269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36082151747996761678460179 54123227621995142517690269)
    ·
      refine ⟨20296210358248178444133851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54123227621995142517690269 20296210358248178444133851)
      ·
        refine ⟨30444315537372267666200777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20296210358248178444133851 30444315537372267666200777)
        ·
          refine ⟨22833236653029200749650583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30444315537372267666200777 22833236653029200749650583)
          ·
            refine ⟨34249854979543801124475875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22833236653029200749650583 34249854979543801124475875)
            ·
              refine ⟨51374782469315701686713813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34249854979543801124475875 51374782469315701686713813)
              ·
                refine ⟨1204096464124586758282355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51374782469315701686713813 1204096464124586758282355)
                ·
                  refine ⟨1806144696186880137423533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204096464124586758282355 1806144696186880137423533)
                  ·
                    refine ⟨677304261070080051533825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1806144696186880137423533 677304261070080051533825)
                    ·
                      rfl

theorem cell22_1978568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_1978568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978568 prefixEnd_1978568 := by exact prefixLift 1978568
  have htrace : WordTrace (prefixWord ++ tailWord_1978568) baseStart_1978568 baseEnd_1978568 := by
    simpa [prefixWord, tailWord_1978568, baseEnd_1978568] using wordTrace_append hprefix tailTrace_1978568
  have hstable : (prefixWord ++ tailWord_1978568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978568).length < 2 ^ (prefixWord ++ tailWord_1978568).sum := by decide
  have hdescent : baseEnd_1978568 < baseStart_1978568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978585 : List Nat := [1, 2, 1, 2, 3, 1, 6, 2, 1, 3]
def baseStart_1978585 : Nat := 118140960795 + 1978585 * 2 ^ 59
def prefixEnd_1978585 : Nat := 4983230072969 + 3 ^ 40 * 1978585 * 2
def baseEnd_1978585 : Nat := 677310080517497673858773

theorem tailTrace_1978585 : CollatzResearch.WordTrace tailWord_1978585 prefixEnd_1978585 677310080517497673858773 := by
  unfold tailWord_1978585
  simp only [CollatzResearch.WordTrace]
  refine ⟨72164923536931935260289209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48109949024621290173526139 72164923536931935260289209)
  ·
    refine ⟨54123692652698951445216907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72164923536931935260289209 54123692652698951445216907)
    ·
      refine ⟨81185538979048427167825361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54123692652698951445216907 81185538979048427167825361)
      ·
        refine ⟨60889154234286320375869021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81185538979048427167825361 60889154234286320375869021)
        ·
          refine ⟨22833432837857370140950883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60889154234286320375869021 22833432837857370140950883)
          ·
            refine ⟨34250149256786055211426325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22833432837857370140950883 34250149256786055211426325)
            ·
              refine ⟨1605475746411846338035609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34250149256786055211426325 1605475746411846338035609)
              ·
                refine ⟨1204106809808884753526707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605475746411846338035609 1204106809808884753526707)
                ·
                  refine ⟨1806160214713327130290061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204106809808884753526707 1806160214713327130290061)
                  ·
                    refine ⟨677310080517497673858773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1806160214713327130290061 677310080517497673858773)
                    ·
                      rfl

theorem cell22_1978585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 3].length) (baseStart_1978585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978585 prefixEnd_1978585 := by exact prefixLift 1978585
  have htrace : WordTrace (prefixWord ++ tailWord_1978585) baseStart_1978585 baseEnd_1978585 := by
    simpa [prefixWord, tailWord_1978585, baseEnd_1978585] using wordTrace_append hprefix tailTrace_1978585
  have hstable : (prefixWord ++ tailWord_1978585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978585).length < 2 ^ (prefixWord ++ tailWord_1978585).sum := by decide
  have hdescent : baseEnd_1978585 < baseStart_1978585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978609 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 8]
def baseStart_1978609 : Nat := 118140960795 + 1978609 * 2 ^ 59
def prefixEnd_1978609 : Nat := 4983230072969 + 3 ^ 40 * 1978609 * 2
def baseEnd_1978609 : Nat := 225772765402656537086233

theorem tailTrace_1978609 : CollatzResearch.WordTrace tailWord_1978609 prefixEnd_1978609 225772765402656537086233 := by
  unfold tailWord_1978609
  simp only [CollatzResearch.WordTrace]
  refine ⟨72165798888844987359162881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48110532592563324906108587 72165798888844987359162881)
  ·
    refine ⟨54124349166633740519372161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72165798888844987359162881 54124349166633740519372161)
    ·
      refine ⟨40593261874975305389529121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54124349166633740519372161 40593261874975305389529121)
      ·
        refine ⟨30444946406231479042146841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40593261874975305389529121 30444946406231479042146841)
        ·
          refine ⟨22833709804673609281610131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30444946406231479042146841 22833709804673609281610131)
          ·
            refine ⟨34250564707010413922415197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22833709804673609281610131 34250564707010413922415197)
            ·
              refine ⟨12843961765128905220905699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34250564707010413922415197 12843961765128905220905699)
              ·
                refine ⟨19265942647693357831358549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12843961765128905220905699 19265942647693357831358549)
                ·
                  refine ⟨225772765402656537086233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19265942647693357831358549 225772765402656537086233)
                  ·
                    rfl

theorem cell22_1978609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_1978609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978609 prefixEnd_1978609 := by exact prefixLift 1978609
  have htrace : WordTrace (prefixWord ++ tailWord_1978609) baseStart_1978609 baseEnd_1978609 := by
    simpa [prefixWord, tailWord_1978609, baseEnd_1978609] using wordTrace_append hprefix tailTrace_1978609
  have hstable : (prefixWord ++ tailWord_1978609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978609).length < 2 ^ (prefixWord ++ tailWord_1978609).sum := by decide
  have hdescent : baseEnd_1978609 < baseStart_1978609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978611 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 1, 4]
def baseStart_1978611 : Nat := 118140960795 + 1978611 * 2 ^ 59
def prefixEnd_1978611 : Nat := 4983230072969 + 3 ^ 40 * 1978611 * 2
def baseEnd_1978611 : Nat := 677318980848842272708693

theorem tailTrace_1978611 : CollatzResearch.WordTrace tailWord_1978611 prefixEnd_1978611 677318980848842272708693 := by
  unfold tailWord_1978611
  simp only [CollatzResearch.WordTrace]
  refine ⟨72165871834837741700735687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48110581223225161133823791 72165871834837741700735687)
  ·
    refine ⟨108248807752256612551103531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72165871834837741700735687 108248807752256612551103531)
    ·
      refine ⟨162373211628384918826655297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108248807752256612551103531 162373211628384918826655297)
      ·
        refine ⟨121779908721288689119991473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162373211628384918826655297 121779908721288689119991473)
        ·
          refine ⟨91334931540966516839993605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121779908721288689119991473 91334931540966516839993605)
          ·
            refine ⟨17125299663931221907498801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91334931540966516839993605 17125299663931221907498801)
            ·
              refine ⟨12843974747948416430624101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17125299663931221907498801 12843974747948416430624101)
              ·
                refine ⟨2408245265240328080742019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12843974747948416430624101 2408245265240328080742019)
                ·
                  refine ⟨3612367897860492121113029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408245265240328080742019 3612367897860492121113029)
                  ·
                    refine ⟨677318980848842272708693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3612367897860492121113029 677318980848842272708693)
                    ·
                      rfl

theorem cell22_1978611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 4].length) (baseStart_1978611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978611 prefixEnd_1978611 := by exact prefixLift 1978611
  have htrace : WordTrace (prefixWord ++ tailWord_1978611) baseStart_1978611 baseEnd_1978611 := by
    simpa [prefixWord, tailWord_1978611, baseEnd_1978611] using wordTrace_append hprefix tailTrace_1978611
  have hstable : (prefixWord ++ tailWord_1978611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978611).length < 2 ^ (prefixWord ++ tailWord_1978611).sum := by decide
  have hdescent : baseEnd_1978611 < baseStart_1978611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978656 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_1978656 : Nat := 118140960795 + 1978656 * 2 ^ 59
def prefixEnd_1978656 : Nat := 4983230072969 + 3 ^ 40 * 1978656 * 2
def baseEnd_1978656 : Nat := 677334385268477155333555

theorem tailTrace_1978656 : CollatzResearch.WordTrace tailWord_1978656 prefixEnd_1978656 677334385268477155333555 := by
  unfold tailWord_1978656
  simp only [CollatzResearch.WordTrace]
  refine ⟨36083756559837357193061911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48111675413116476257415881 36083756559837357193061911)
  ·
    refine ⟨54125634839756035789592867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36083756559837357193061911 54125634839756035789592867)
    ·
      refine ⟨81188452259634053684389301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54125634839756035789592867 81188452259634053684389301)
      ·
        refine ⟨7611417399340692532911497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81188452259634053684389301 7611417399340692532911497)
        ·
          refine ⟨5708563049505519399683623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7611417399340692532911497 5708563049505519399683623)
          ·
            refine ⟨8562844574258279099525435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708563049505519399683623 8562844574258279099525435)
            ·
              refine ⟨12844266861387418649288153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8562844574258279099525435 12844266861387418649288153)
              ·
                refine ⟨9633200146040563986966115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12844266861387418649288153 9633200146040563986966115)
                ·
                  refine ⟨14449800219060845980449173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9633200146040563986966115 14449800219060845980449173)
                  ·
                    refine ⟨677334385268477155333555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14449800219060845980449173 677334385268477155333555)
                    ·
                      rfl

theorem cell22_1978656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_1978656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978656 prefixEnd_1978656 := by exact prefixLift 1978656
  have htrace : WordTrace (prefixWord ++ tailWord_1978656) baseStart_1978656 baseEnd_1978656 := by
    simpa [prefixWord, tailWord_1978656, baseEnd_1978656] using wordTrace_append hprefix tailTrace_1978656
  have hstable : (prefixWord ++ tailWord_1978656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978656).length < 2 ^ (prefixWord ++ tailWord_1978656).sum := by decide
  have hdescent : baseEnd_1978656 < baseStart_1978656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978658 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1978658 : Nat := 118140960795 + 1978658 * 2 ^ 59
def prefixEnd_1978658 : Nat := 4983230072969 + 3 ^ 40 * 1978658 * 2
def baseEnd_1978658 : Nat := 677335069909349816783549

theorem tailTrace_1978658 : CollatzResearch.WordTrace tailWord_1978658 prefixEnd_1978658 677335069909349816783549 := by
  unfold tailWord_1978658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18041896516416867181924157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48111724043778312485131085 18041896516416867181924157)
  ·
    refine ⟨6765711193656325193221559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18041896516416867181924157 6765711193656325193221559)
    ·
      refine ⟨10148566790484487789832339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6765711193656325193221559 10148566790484487789832339)
      ·
        refine ⟨15222850185726731684748509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10148566790484487789832339 15222850185726731684748509)
        ·
          refine ⟨5708568819647524381780691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15222850185726731684748509 5708568819647524381780691)
          ·
            refine ⟨8562853229471286572671037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708568819647524381780691 8562853229471286572671037)
            ·
              refine ⟨3211069961051732464751639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8562853229471286572671037 3211069961051732464751639)
              ·
                refine ⟨4816604941577598697127459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3211069961051732464751639 4816604941577598697127459)
                ·
                  refine ⟨7224907412366398045691189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816604941577598697127459 7224907412366398045691189)
                  ·
                    refine ⟨677335069909349816783549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7224907412366398045691189 677335069909349816783549)
                    ·
                      rfl

theorem cell22_1978658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1978658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978658 prefixEnd_1978658 := by exact prefixLift 1978658
  have htrace : WordTrace (prefixWord ++ tailWord_1978658) baseStart_1978658 baseEnd_1978658 := by
    simpa [prefixWord, tailWord_1978658, baseEnd_1978658] using wordTrace_append hprefix tailTrace_1978658
  have hstable : (prefixWord ++ tailWord_1978658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978658).length < 2 ^ (prefixWord ++ tailWord_1978658).sum := by decide
  have hdescent : baseEnd_1978658 < baseStart_1978658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978671 : List Nat := [1, 1, 2, 1, 2, 1, 8, 6]
def baseStart_1978671 : Nat := 118140960795 + 1978671 * 2 ^ 59
def prefixEnd_1978671 : Nat := 4983230072969 + 3 ^ 40 * 1978671 * 2
def baseEnd_1978671 : Nat := 75259946675002457356501

theorem tailTrace_1978671 : CollatzResearch.WordTrace tailWord_1978671 prefixEnd_1978671 75259946675002457356501 := by
  unfold tailWord_1978671
  simp only [CollatzResearch.WordTrace]
  refine ⟨72168060214620371947919867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48112040143080247965279911 72168060214620371947919867)
  ·
    refine ⟨108252090321930557921879801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72168060214620371947919867 108252090321930557921879801)
    ·
      refine ⟨81189067741447918441409851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108252090321930557921879801 81189067741447918441409851)
      ·
        refine ⟨121783601612171877662114777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81189067741447918441409851 121783601612171877662114777)
        ·
          refine ⟨91337701209128908246586083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121783601612171877662114777 91337701209128908246586083)
          ·
            refine ⟨137006551813693362369879125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91337701209128908246586083 137006551813693362369879125)
            ·
              refine ⟨1605545529066719090272021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 137006551813693362369879125 1605545529066719090272021)
              ·
                refine ⟨75259946675002457356501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1605545529066719090272021 75259946675002457356501)
                ·
                  rfl

theorem cell22_1978671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 6].length) (baseStart_1978671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978671 prefixEnd_1978671 := by exact prefixLift 1978671
  have htrace : WordTrace (prefixWord ++ tailWord_1978671) baseStart_1978671 baseEnd_1978671 := by
    simpa [prefixWord, tailWord_1978671, baseEnd_1978671] using wordTrace_append hprefix tailTrace_1978671
  have hstable : (prefixWord ++ tailWord_1978671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978671).length < 2 ^ (prefixWord ++ tailWord_1978671).sum := by decide
  have hdescent : baseEnd_1978671 < baseStart_1978671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978709 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_1978709 : Nat := 118140960795 + 1978709 * 2 ^ 59
def prefixEnd_1978709 : Nat := 4983230072969 + 3 ^ 40 * 1978709 * 2
def baseEnd_1978709 : Nat := 677352528251602683758393

theorem tailTrace_1978709 : CollatzResearch.WordTrace tailWord_1978709 prefixEnd_1978709 677352528251602683758393 := by
  unfold tailWord_1978709
  simp only [CollatzResearch.WordTrace]
  refine ⟨72169446188482704437803181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48112964125655136291868787 72169446188482704437803181)
  ·
    refine ⟨27063542320681014164176193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72169446188482704437803181 27063542320681014164176193)
    ·
      refine ⟨20297656740510760623132145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27063542320681014164176193 20297656740510760623132145)
      ·
        refine ⟨15223242555383070467349109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20297656740510760623132145 15223242555383070467349109)
        ·
          refine ⟨1427178989567162856313979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15223242555383070467349109 1427178989567162856313979)
          ·
            refine ⟨2140768484350744284470969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427178989567162856313979 2140768484350744284470969)
            ·
              refine ⟨1605576363263058213353227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140768484350744284470969 1605576363263058213353227)
              ·
                refine ⟨2408364544894587320029841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605576363263058213353227 2408364544894587320029841)
                ·
                  refine ⟨1806273408670940490022381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2408364544894587320029841 1806273408670940490022381)
                  ·
                    refine ⟨677352528251602683758393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1806273408670940490022381 677352528251602683758393)
                    ·
                      rfl

theorem cell22_1978709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_1978709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978709 prefixEnd_1978709 := by exact prefixLift 1978709
  have htrace : WordTrace (prefixWord ++ tailWord_1978709) baseStart_1978709 baseEnd_1978709 := by
    simpa [prefixWord, tailWord_1978709, baseEnd_1978709] using wordTrace_append hprefix tailTrace_1978709
  have hstable : (prefixWord ++ tailWord_1978709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978709).length < 2 ^ (prefixWord ++ tailWord_1978709).sum := by decide
  have hdescent : baseEnd_1978709 < baseStart_1978709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978746 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_1978746 : Nat := 118140960795 + 1978746 * 2 ^ 59
def prefixEnd_1978746 : Nat := 4983230072969 + 3 ^ 40 * 1978746 * 2
def baseEnd_1978746 : Nat := 677365194107746920583279

theorem tailTrace_1978746 : CollatzResearch.WordTrace tailWord_1978746 prefixEnd_1978746 677365194107746920583279 := by
  unfold tailWord_1978746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18042698922337164939225023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48113863792899106504600061 18042698922337164939225023)
  ·
    refine ⟨27064048383505747408837535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18042698922337164939225023 27064048383505747408837535)
    ·
      refine ⟨40596072575258621113256303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27064048383505747408837535 40596072575258621113256303)
      ·
        refine ⟨60894108862887931669884455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40596072575258621113256303 60894108862887931669884455)
        ·
          refine ⟨91341163294331897504826683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60894108862887931669884455 91341163294331897504826683)
          ·
            refine ⟨137011744941497846257240025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91341163294331897504826683 137011744941497846257240025)
            ·
              refine ⟨102758808706123384692930019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137011744941497846257240025 102758808706123384692930019)
              ·
                refine ⟨154138213059185077039395029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102758808706123384692930019 154138213059185077039395029)
                ·
                  refine ⟨3612614368574650243110821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 154138213059185077039395029 3612614368574650243110821)
                  ·
                    refine ⟨677365194107746920583279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3612614368574650243110821 677365194107746920583279)
                    ·
                      rfl

theorem cell22_1978746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_1978746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978746 prefixEnd_1978746 := by exact prefixLift 1978746
  have htrace : WordTrace (prefixWord ++ tailWord_1978746) baseStart_1978746 baseEnd_1978746 := by
    simpa [prefixWord, tailWord_1978746, baseEnd_1978746] using wordTrace_append hprefix tailTrace_1978746
  have hstable : (prefixWord ++ tailWord_1978746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978746).length < 2 ^ (prefixWord ++ tailWord_1978746).sum := by decide
  have hdescent : baseEnd_1978746 < baseStart_1978746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978778 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_1978778 : Nat := 118140960795 + 1978778 * 2 ^ 59
def prefixEnd_1978778 : Nat := 4983230072969 + 3 ^ 40 * 1978778 * 2
def baseEnd_1978778 : Nat := 225792049453903167927727

theorem tailTrace_1978778 : CollatzResearch.WordTrace tailWord_1978778 prefixEnd_1978778 225792049453903167927727 := by
  unfold tailWord_1978778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18042990706308182305516247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48114641883488486148043325 18042990706308182305516247)
  ·
    refine ⟨27064486059462273458274371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18042990706308182305516247 27064486059462273458274371)
    ·
      refine ⟨40596729089193410187411557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27064486059462273458274371 40596729089193410187411557)
      ·
        refine ⟨7611886704223764410139667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40596729089193410187411557 7611886704223764410139667)
        ·
          refine ⟨11417830056335646615209501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7611886704223764410139667 11417830056335646615209501)
          ·
            refine ⟨4281686271125867480703563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11417830056335646615209501 4281686271125867480703563)
            ·
              refine ⟨6422529406688801221055345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281686271125867480703563 6422529406688801221055345)
              ·
                refine ⟨4816897055016600915791509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6422529406688801221055345 4816897055016600915791509)
                ·
                  refine ⟨225792049453903167927727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4816897055016600915791509 225792049453903167927727)
                  ·
                    rfl

theorem cell22_1978778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_1978778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978778 prefixEnd_1978778 := by exact prefixLift 1978778
  have htrace : WordTrace (prefixWord ++ tailWord_1978778) baseStart_1978778 baseEnd_1978778 := by
    simpa [prefixWord, tailWord_1978778, baseEnd_1978778] using wordTrace_append hprefix tailTrace_1978778
  have hstable : (prefixWord ++ tailWord_1978778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978778).length < 2 ^ (prefixWord ++ tailWord_1978778).sum := by decide
  have hdescent : baseEnd_1978778 < baseStart_1978778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978797 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1978797 : Nat := 118140960795 + 1978797 * 2 ^ 59
def prefixEnd_1978797 : Nat := 4983230072969 + 3 ^ 40 * 1978797 * 2
def baseEnd_1978797 : Nat := 677382652449999787558123

theorem tailTrace_1978797 : CollatzResearch.WordTrace tailWord_1978797 prefixEnd_1978797 677382652449999787558123 := by
  unfold tailWord_1978797
  simp only [CollatzResearch.WordTrace]
  refine ⟨72172655812163895467006645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48115103874775930311337763 72172655812163895467006645)
  ·
    refine ⟨6766186482390365200031873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72172655812163895467006645 6766186482390365200031873)
    ·
      refine ⟨5074639861792773900023905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6766186482390365200031873 5074639861792773900023905)
      ·
        refine ⟨3805979896344580425017929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5074639861792773900023905 3805979896344580425017929)
        ·
          refine ⟨2854484922258435318763447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3805979896344580425017929 2854484922258435318763447)
          ·
            refine ⟨4281727383387652978145171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854484922258435318763447 4281727383387652978145171)
            ·
              refine ⟨6422591075081479467217757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281727383387652978145171 6422591075081479467217757)
              ·
                refine ⟨2408471653155554800206659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6422591075081479467217757 2408471653155554800206659)
                ·
                  refine ⟨3612707479733332200309989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408471653155554800206659 3612707479733332200309989)
                  ·
                    refine ⟨677382652449999787558123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3612707479733332200309989 677382652449999787558123)
                    ·
                      rfl

theorem cell22_1978797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1978797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978797 prefixEnd_1978797 := by exact prefixLift 1978797
  have htrace : WordTrace (prefixWord ++ tailWord_1978797) baseStart_1978797 baseEnd_1978797 := by
    simpa [prefixWord, tailWord_1978797, baseEnd_1978797] using wordTrace_append hprefix tailTrace_1978797
  have hstable : (prefixWord ++ tailWord_1978797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978797).length < 2 ^ (prefixWord ++ tailWord_1978797).sum := by decide
  have hdescent : baseEnd_1978797 < baseStart_1978797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978885 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 5]
def baseStart_1978885 : Nat := 118140960795 + 1978885 * 2 ^ 59
def prefixEnd_1978885 : Nat := 4983230072969 + 3 ^ 40 * 1978885 * 2
def baseEnd_1978885 : Nat := 225804258882798963785951

theorem tailTrace_1978885 : CollatzResearch.WordTrace tailWord_1978885 prefixEnd_1978885 225804258882798963785951 := by
  unfold tailWord_1978885
  simp only [CollatzResearch.WordTrace]
  refine ⟨72175865435845086496210109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48117243623896724330806739 72175865435845086496210109)
  ·
    refine ⟨27065949538441907436078791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72175865435845086496210109 27065949538441907436078791)
    ·
      refine ⟨40598924307662861154118187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27065949538441907436078791 40598924307662861154118187)
      ·
        refine ⟨60898386461494291731177281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40598924307662861154118187 60898386461494291731177281)
        ·
          refine ⟨45673789846120718798382961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60898386461494291731177281 45673789846120718798382961)
          ·
            refine ⟨34255342384590539098787221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45673789846120718798382961 34255342384590539098787221)
            ·
              refine ⟨1605719174277681520255651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34255342384590539098787221 1605719174277681520255651)
              ·
                refine ⟨2408578761416522280383477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605719174277681520255651 2408578761416522280383477)
                ·
                  refine ⟨225804258882798963785951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2408578761416522280383477 225804258882798963785951)
                  ·
                    rfl

theorem cell22_1978885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_1978885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978885 prefixEnd_1978885 := by exact prefixLift 1978885
  have htrace : WordTrace (prefixWord ++ tailWord_1978885) baseStart_1978885 baseEnd_1978885 := by
    simpa [prefixWord, tailWord_1978885, baseEnd_1978885] using wordTrace_append hprefix tailTrace_1978885
  have hstable : (prefixWord ++ tailWord_1978885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978885).length < 2 ^ (prefixWord ++ tailWord_1978885).sum := by decide
  have hdescent : baseEnd_1978885 < baseStart_1978885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978919 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 5]
def baseStart_1978919 : Nat := 118140960795 + 1978919 * 2 ^ 59
def prefixEnd_1978919 : Nat := 4983230072969 + 3 ^ 40 * 1978919 * 2
def baseEnd_1978919 : Nat := 225808138514410712002583

theorem tailTrace_1978919 : CollatzResearch.WordTrace tailWord_1978919 prefixEnd_1978919 225808138514410712002583 := by
  unfold tailWord_1978919
  simp only [CollatzResearch.WordTrace]
  refine ⟨72177105517721910302947811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48118070345147940201965207 72177105517721910302947811)
  ·
    refine ⟨108265658276582865454421717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72177105517721910302947811 108265658276582865454421717)
    ·
      refine ⟨2537476365857410909088009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 108265658276582865454421717 2537476365857410909088009)
      ·
        refine ⟨1903107274393058181816007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2537476365857410909088009 1903107274393058181816007)
        ·
          refine ⟨2854660911589587272724011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903107274393058181816007 2854660911589587272724011)
          ·
            refine ⟨4281991367384380909086017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854660911589587272724011 4281991367384380909086017)
            ·
              refine ⟨3211493525538285681814513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4281991367384380909086017 3211493525538285681814513)
              ·
                refine ⟨2408620144153714261360885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211493525538285681814513 2408620144153714261360885)
                ·
                  refine ⟨225808138514410712002583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2408620144153714261360885 225808138514410712002583)
                  ·
                    rfl

theorem cell22_1978919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 5].length) (baseStart_1978919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978919 prefixEnd_1978919 := by exact prefixLift 1978919
  have htrace : WordTrace (prefixWord ++ tailWord_1978919) baseStart_1978919 baseEnd_1978919 := by
    simpa [prefixWord, tailWord_1978919, baseEnd_1978919] using wordTrace_append hprefix tailTrace_1978919
  have hstable : (prefixWord ++ tailWord_1978919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978919).length < 2 ^ (prefixWord ++ tailWord_1978919).sum := by decide
  have hdescent : baseEnd_1978919 < baseStart_1978919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978943 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 1, 6]
def baseStart_1978943 : Nat := 118140960795 + 1978943 * 2 ^ 59
def prefixEnd_1978943 : Nat := 4983230072969 + 3 ^ 40 * 1978943 * 2
def baseEnd_1978943 : Nat := 677432631233704073407675

theorem tailTrace_1978943 : CollatzResearch.WordTrace tailWord_1978943 prefixEnd_1978943 677432631233704073407675 := by
  unfold tailWord_1978943
  simp only [CollatzResearch.WordTrace]
  refine ⟨72177980869634962401821483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48118653913089974934547655 72177980869634962401821483)
  ·
    refine ⟨108266971304452443602732225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72177980869634962401821483 108266971304452443602732225)
    ·
      refine ⟨81200228478339332702049169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108266971304452443602732225 81200228478339332702049169)
      ·
        refine ⟨60900171358754499526536877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81200228478339332702049169 60900171358754499526536877)
        ·
          refine ⟨22837564259532937322451329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60900171358754499526536877 22837564259532937322451329)
          ·
            refine ⟨17128173194649702991838497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22837564259532937322451329 17128173194649702991838497)
            ·
              refine ⟨12846129895987277243878873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17128173194649702991838497 12846129895987277243878873)
              ·
                refine ⟨9634597421990457932909155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12846129895987277243878873 9634597421990457932909155)
                ·
                  refine ⟨14451896132985686899363733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9634597421990457932909155 14451896132985686899363733)
                  ·
                    refine ⟨677432631233704073407675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14451896132985686899363733 677432631233704073407675)
                    ·
                      rfl

theorem cell22_1978943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_1978943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978943 prefixEnd_1978943 := by exact prefixLift 1978943
  have htrace : WordTrace (prefixWord ++ tailWord_1978943) baseStart_1978943 baseEnd_1978943 := by
    simpa [prefixWord, tailWord_1978943, baseEnd_1978943] using wordTrace_append hprefix tailTrace_1978943
  have hstable : (prefixWord ++ tailWord_1978943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978943).length < 2 ^ (prefixWord ++ tailWord_1978943).sum := by decide
  have hdescent : baseEnd_1978943 < baseStart_1978943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978945 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1978945 : Nat := 118140960795 + 1978945 * 2 ^ 59
def prefixEnd_1978945 : Nat := 4983230072969 + 3 ^ 40 * 1978945 * 2
def baseEnd_1978945 : Nat := 677433315874576734857669

theorem tailTrace_1978945 : CollatzResearch.WordTrace tailWord_1978945 prefixEnd_1978945 677433315874576734857669 := by
  unfold tailWord_1978945
  simp only [CollatzResearch.WordTrace]
  refine ⟨72178053815627716743394289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48118702543751811162262859 72178053815627716743394289)
  ·
    refine ⟨54133540361720787557545717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72178053815627716743394289 54133540361720787557545717)
    ·
      refine ⟨5075019408911323833519911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54133540361720787557545717 5075019408911323833519911)
      ·
        refine ⟨7612529113366985750279867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075019408911323833519911 7612529113366985750279867)
        ·
          refine ⟨11418793670050478625419801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7612529113366985750279867 11418793670050478625419801)
          ·
            refine ⟨8564095252537858969064851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11418793670050478625419801 8564095252537858969064851)
            ·
              refine ⟨12846142878806788453597277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8564095252537858969064851 12846142878806788453597277)
              ·
                refine ⟨4817303579552545670098979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12846142878806788453597277 4817303579552545670098979)
                ·
                  refine ⟨7225955369328818505148469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4817303579552545670098979 7225955369328818505148469)
                  ·
                    refine ⟨677433315874576734857669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7225955369328818505148469 677433315874576734857669)
                    ·
                      rfl

theorem cell22_1978945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1978945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978945 prefixEnd_1978945 := by exact prefixLift 1978945
  have htrace : WordTrace (prefixWord ++ tailWord_1978945) baseStart_1978945 baseEnd_1978945 := by
    simpa [prefixWord, tailWord_1978945, baseEnd_1978945] using wordTrace_append hprefix tailTrace_1978945
  have hstable : (prefixWord ++ tailWord_1978945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978945).length < 2 ^ (prefixWord ++ tailWord_1978945).sum := by decide
  have hdescent : baseEnd_1978945 < baseStart_1978945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978958 : List Nat := [4, 1, 1, 1, 1, 2, 2, 10]
def baseStart_1978958 : Nat := 118140960795 + 1978958 * 2 ^ 59
def prefixEnd_1978958 : Nat := 4983230072969 + 3 ^ 40 * 1978958 * 2
def baseEnd_1978958 : Nat := 75270862893361003809181

theorem tailTrace_1978958 : CollatzResearch.WordTrace tailWord_1978958 prefixEnd_1978958 75270862893361003809181 := by
  unfold tailWord_1978958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022315995572577495452191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48119018643053746642411685 9022315995572577495452191)
  ·
    refine ⟨13533473993358866243178287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9022315995572577495452191 13533473993358866243178287)
    ·
      refine ⟨20300210990038299364767431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13533473993358866243178287 20300210990038299364767431)
      ·
        refine ⟨30450316485057449047151147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20300210990038299364767431 30450316485057449047151147)
        ·
          refine ⟨45675474727586173570726721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30450316485057449047151147 45675474727586173570726721)
          ·
            refine ⟨34256606045689630178045041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45675474727586173570726721 34256606045689630178045041)
            ·
              refine ⟨25692454534267222633533781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34256606045689630178045041 25692454534267222633533781)
              ·
                refine ⟨75270862893361003809181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25692454534267222633533781 75270862893361003809181)
                ·
                  rfl

theorem cell22_1978958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_1978958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978958 prefixEnd_1978958 := by exact prefixLift 1978958
  have htrace : WordTrace (prefixWord ++ tailWord_1978958) baseStart_1978958 baseEnd_1978958 := by
    simpa [prefixWord, tailWord_1978958, baseEnd_1978958] using wordTrace_append hprefix tailTrace_1978958
  have hstable : (prefixWord ++ tailWord_1978958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978958).length < 2 ^ (prefixWord ++ tailWord_1978958).sum := by decide
  have hdescent : baseEnd_1978958 < baseStart_1978958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978988 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_1978988 : Nat := 118140960795 + 1978988 * 2 ^ 59
def prefixEnd_1978988 : Nat := 4983230072969 + 3 ^ 40 * 1978988 * 2
def baseEnd_1978988 : Nat := 677448035653338956032537

theorem tailTrace_1978988 : CollatzResearch.WordTrace tailWord_1978988 prefixEnd_1978988 677448035653338956032537 := by
  unfold tailWord_1978988
  simp only [CollatzResearch.WordTrace]
  refine ⟨36089811077235967543604809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48119748102981290058139745 36089811077235967543604809)
  ·
    refine ⟨27067358307926975657703607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36089811077235967543604809 27067358307926975657703607)
    ·
      refine ⟨40601037461890463486555411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27067358307926975657703607 40601037461890463486555411)
      ·
        refine ⟨60901556192835695229833117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40601037461890463486555411 60901556192835695229833117)
        ·
          refine ⟨22838083572313385711187419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60901556192835695229833117 22838083572313385711187419)
          ·
            refine ⟨34257125358470078566781129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22838083572313385711187419 34257125358470078566781129)
            ·
              refine ⟨25692844018852558925085847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34257125358470078566781129 25692844018852558925085847)
              ·
                refine ⟨38539266028278838387628771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25692844018852558925085847 38539266028278838387628771)
                ·
                  refine ⟨57808899042418257581443157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38539266028278838387628771 57808899042418257581443157)
                  ·
                    refine ⟨677448035653338956032537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57808899042418257581443157 677448035653338956032537)
                    ·
                      rfl

theorem cell22_1978988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_1978988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1978988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1978988 prefixEnd_1978988 := by exact prefixLift 1978988
  have htrace : WordTrace (prefixWord ++ tailWord_1978988) baseStart_1978988 baseEnd_1978988 := by
    simpa [prefixWord, tailWord_1978988, baseEnd_1978988] using wordTrace_append hprefix tailTrace_1978988
  have hstable : (prefixWord ++ tailWord_1978988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978988).length < 2 ^ (prefixWord ++ tailWord_1978988).sum := by decide
  have hdescent : baseEnd_1978988 < baseStart_1978988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979041 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 3, 3]
def baseStart_1979041 : Nat := 118140960795 + 1979041 * 2 ^ 59
def prefixEnd_1979041 : Nat := 4983230072969 + 3 ^ 40 * 1979041 * 2
def baseEnd_1979041 : Nat := 677466178636464484457375

theorem tailTrace_1979041 : CollatzResearch.WordTrace tailWord_1979041 prefixEnd_1979041 677466178636464484457375 := by
  unfold tailWord_1979041
  simp only [CollatzResearch.WordTrace]
  refine ⟨72181555223279925138888977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48121036815519950092592651 72181555223279925138888977)
  ·
    refine ⟨54136166417459943854166733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72181555223279925138888977 54136166417459943854166733)
    ·
      refine ⟨20301062406547478945312525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54136166417459943854166733 20301062406547478945312525)
      ·
        refine ⟨7612898402455304604492197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20301062406547478945312525 7612898402455304604492197)
        ·
          refine ⟨1427418450460369613342287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7612898402455304604492197 1427418450460369613342287)
          ·
            refine ⟨2141127675690554420013431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427418450460369613342287 2141127675690554420013431)
            ·
              refine ⟨3211691513535831630020147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141127675690554420013431 3211691513535831630020147)
              ·
                refine ⟨4817537270303747445030221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3211691513535831630020147 4817537270303747445030221)
                ·
                  refine ⟨1806576476363905291886333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4817537270303747445030221 1806576476363905291886333)
                  ·
                    refine ⟨677466178636464484457375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1806576476363905291886333 677466178636464484457375)
                    ·
                      rfl

theorem cell22_1979041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_1979041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979041 prefixEnd_1979041 := by exact prefixLift 1979041
  have htrace : WordTrace (prefixWord ++ tailWord_1979041) baseStart_1979041 baseEnd_1979041 := by
    simpa [prefixWord, tailWord_1979041, baseEnd_1979041] using wordTrace_append hprefix tailTrace_1979041
  have hstable : (prefixWord ++ tailWord_1979041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979041).length < 2 ^ (prefixWord ++ tailWord_1979041).sum := by decide
  have hdescent : baseEnd_1979041 < baseStart_1979041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
