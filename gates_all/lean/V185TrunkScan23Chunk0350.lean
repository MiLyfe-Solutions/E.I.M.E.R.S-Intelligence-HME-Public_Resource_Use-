import V185TrunkScan23Chunk0349

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2070571 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 4]
def baseStart_2070571 : Nat := 118140960795 + 2070571 * 2 ^ 59
def prefixEnd_2070571 : Nat := 4983230072969 + 3 ^ 40 * 2070571 * 2
def baseEnd_2070571 : Nat := 1063198152260723615140123

theorem tailTrace_2070571 : CollatzResearch.WordTrace tailWord_2070571 prefixEnd_2070571 1063198152260723615140123 := by
  unfold tailWord_2070571
  simp only [CollatzResearch.WordTrace]
  refine ⟨75519928581682367218355567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50346619054454911478903711 75519928581682367218355567)
  ·
    refine ⟨113279892872523550827533351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75519928581682367218355567 113279892872523550827533351)
    ·
      refine ⟨169919839308785326241300027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113279892872523550827533351 169919839308785326241300027)
      ·
        refine ⟨254879758963177989361950041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169919839308785326241300027 254879758963177989361950041)
        ·
          refine ⟨191159819222383492021462531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254879758963177989361950041 191159819222383492021462531)
          ·
            refine ⟨286739728833575238032193797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191159819222383492021462531 286739728833575238032193797)
            ·
              refine ⟨53763699156295357131036337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286739728833575238032193797 53763699156295357131036337)
              ·
                refine ⟨40322774367221517848277253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53763699156295357131036337 40322774367221517848277253)
                ·
                  refine ⟨7560520193854034596551985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40322774367221517848277253 7560520193854034596551985)
                  ·
                    refine ⟨5670390145390525947413989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7560520193854034596551985 5670390145390525947413989)
                    ·
                      refine ⟨1063198152260723615140123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5670390145390525947413989 1063198152260723615140123)
                      ·
                        rfl

theorem cell23_2070571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 4].length) (baseStart_2070571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070571 prefixEnd_2070571 := by exact prefixLift 2070571
  have htrace : WordTrace (prefixWord ++ tailWord_2070571) baseStart_2070571 baseEnd_2070571 := by
    simpa [prefixWord, tailWord_2070571, baseEnd_2070571] using wordTrace_append hprefix tailTrace_2070571
  have hstable : (prefixWord ++ tailWord_2070571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070571).length < 2 ^ (prefixWord ++ tailWord_2070571).sum := by decide
  have hdescent : baseEnd_2070571 < baseStart_2070571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070578 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2070578 : Nat := 118140960795 + 2070578 * 2 ^ 59
def prefixEnd_2070578 : Nat := 4983230072969 + 3 ^ 40 * 2070578 * 2
def baseEnd_2070578 : Nat := 1063201746625305087752591

theorem tailTrace_2070578 : CollatzResearch.WordTrace tailWord_2070578 prefixEnd_2070578 1063201746625305087752591 := by
  unfold tailWord_2070578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18880045973164251853465097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50346789261771338275906925 18880045973164251853465097)
  ·
    refine ⟨14160034479873188890098823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18880045973164251853465097 14160034479873188890098823)
    ·
      refine ⟨21240051719809783335148235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14160034479873188890098823 21240051719809783335148235)
      ·
        refine ⟨31860077579714675002722353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21240051719809783335148235 31860077579714675002722353)
        ·
          refine ⟨23895058184786006252041765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31860077579714675002722353 23895058184786006252041765)
          ·
            refine ⟨4480323409647376172257831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23895058184786006252041765 4480323409647376172257831)
            ·
              refine ⟨6720485114471064258386747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480323409647376172257831 6720485114471064258386747)
              ·
                refine ⟨10080727671706596387580121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6720485114471064258386747 10080727671706596387580121)
                ·
                  refine ⟨7560545753779947290685091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10080727671706596387580121 7560545753779947290685091)
                  ·
                    refine ⟨11340818630669920936027637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560545753779947290685091 11340818630669920936027637)
                    ·
                      refine ⟨1063201746625305087752591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11340818630669920936027637 1063201746625305087752591)
                      ·
                        rfl

theorem cell23_2070578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2070578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070578 prefixEnd_2070578 := by exact prefixLift 2070578
  have htrace : WordTrace (prefixWord ++ tailWord_2070578) baseStart_2070578 baseEnd_2070578 := by
    simpa [prefixWord, tailWord_2070578, baseEnd_2070578] using wordTrace_append hprefix tailTrace_2070578
  have hstable : (prefixWord ++ tailWord_2070578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070578).length < 2 ^ (prefixWord ++ tailWord_2070578).sum := by decide
  have hdescent : baseEnd_2070578 < baseStart_2070578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070581 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 9]
def baseStart_2070581 : Nat := 118140960795 + 2070581 * 2 ^ 59
def prefixEnd_2070581 : Nat := 4983230072969 + 3 ^ 40 * 2070581 * 2
def baseEnd_2070581 : Nat := 118133698563029841779453

theorem tailTrace_2070581 : CollatzResearch.WordTrace tailWord_2070581 prefixEnd_2070581 118133698563029841779453 := by
  unfold tailWord_2070581
  simp only [CollatzResearch.WordTrace]
  refine ⟨75520293311646138926219597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50346862207764092617479731 75520293311646138926219597)
  ·
    refine ⟨28320109991867302097332349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75520293311646138926219597 28320109991867302097332349)
    ·
      refine ⟨10620041246950238286499631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28320109991867302097332349 10620041246950238286499631)
      ·
        refine ⟨15930061870425357429749447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10620041246950238286499631 15930061870425357429749447)
        ·
          refine ⟨23895092805638036144624171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15930061870425357429749447 23895092805638036144624171)
          ·
            refine ⟨35842639208457054216936257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23895092805638036144624171 35842639208457054216936257)
            ·
              refine ⟨26881979406342790662702193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35842639208457054216936257 26881979406342790662702193)
              ·
                refine ⟨20161484554757092997026645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26881979406342790662702193 20161484554757092997026645)
                ·
                  refine ⟨118133698563029841779453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20161484554757092997026645 118133698563029841779453)
                  ·
                    rfl

theorem cell23_2070581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_2070581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070581 prefixEnd_2070581 := by exact prefixLift 2070581
  have htrace : WordTrace (prefixWord ++ tailWord_2070581) baseStart_2070581 baseEnd_2070581 := by
    simpa [prefixWord, tailWord_2070581, baseEnd_2070581] using wordTrace_append hprefix tailTrace_2070581
  have hstable : (prefixWord ++ tailWord_2070581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070581).length < 2 ^ (prefixWord ++ tailWord_2070581).sum := by decide
  have hdescent : baseEnd_2070581 < baseStart_2070581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070628 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_2070628 : Nat := 118140960795 + 2070628 * 2 ^ 59
def prefixEnd_2070628 : Nat := 4983230072969 + 3 ^ 40 * 2070628 * 2
def baseEnd_2070628 : Nat := 354409140219343297375787

theorem tailTrace_2070628 : CollatzResearch.WordTrace tailWord_2070628 prefixEnd_2070628 354409140219343297375787 := by
  unfold tailWord_2070628
  simp only [CollatzResearch.WordTrace]
  refine ⟨37761003771237932976590269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50348005028317243968787025 37761003771237932976590269)
  ·
    refine ⟨14160376414214224866221351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37761003771237932976590269 14160376414214224866221351)
    ·
      refine ⟨21240564621321337299332027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14160376414214224866221351 21240564621321337299332027)
      ·
        refine ⟨31860846931982005948998041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21240564621321337299332027 31860846931982005948998041)
        ·
          refine ⟨23895635198986504461748531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31860846931982005948998041 23895635198986504461748531)
          ·
            refine ⟨35843452798479756692622797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23895635198986504461748531 35843452798479756692622797)
            ·
              refine ⟨13441294799429908759733549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35843452798479756692622797 13441294799429908759733549)
              ·
                refine ⟨5040485549786215784900081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13441294799429908759733549 5040485549786215784900081)
                ·
                  refine ⟨3780364162339661838675061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5040485549786215784900081 3780364162339661838675061)
                  ·
                    refine ⟨354409140219343297375787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3780364162339661838675061 354409140219343297375787)
                    ·
                      rfl

theorem cell23_2070628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_2070628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070628 prefixEnd_2070628 := by exact prefixLift 2070628
  have htrace : WordTrace (prefixWord ++ tailWord_2070628) baseStart_2070628 baseEnd_2070628 := by
    simpa [prefixWord, tailWord_2070628, baseEnd_2070628] using wordTrace_append hprefix tailTrace_2070628
  have hstable : (prefixWord ++ tailWord_2070628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070628).length < 2 ^ (prefixWord ++ tailWord_2070628).sum := by decide
  have hdescent : baseEnd_2070628 < baseStart_2070628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070638 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2070638 : Nat := 118140960795 + 2070638 * 2 ^ 59
def prefixEnd_2070638 : Nat := 4983230072969 + 3 ^ 40 * 2070638 * 2
def baseEnd_2070638 : Nat := 1063232555464574853002315

theorem tailTrace_2070638 : CollatzResearch.WordTrace tailWord_2070638 prefixEnd_2070638 1063232555464574853002315 := by
  unfold tailWord_2070638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9440296534054954707630571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50348248181626425107363045 9440296534054954707630571)
  ·
    refine ⟨14160444801082432061445857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9440296534054954707630571 14160444801082432061445857)
    ·
      refine ⟨10620333600811824046084393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14160444801082432061445857 10620333600811824046084393)
      ·
        refine ⟨7965250200608868034563295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10620333600811824046084393 7965250200608868034563295)
        ·
          refine ⟨11947875300913302051844943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965250200608868034563295 11947875300913302051844943)
          ·
            refine ⟨17921812951369953077767415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947875300913302051844943 17921812951369953077767415)
            ·
              refine ⟨26882719427054929616651123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17921812951369953077767415 26882719427054929616651123)
              ·
                refine ⟨40324079140582394424976685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26882719427054929616651123 40324079140582394424976685)
                ·
                  refine ⟨15121529677718397909366257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40324079140582394424976685 15121529677718397909366257)
                  ·
                    refine ⟨11341147258288798432024693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15121529677718397909366257 11341147258288798432024693)
                    ·
                      refine ⟨1063232555464574853002315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11341147258288798432024693 1063232555464574853002315)
                      ·
                        rfl

theorem cell23_2070638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2070638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070638 prefixEnd_2070638 := by exact prefixLift 2070638
  have htrace : WordTrace (prefixWord ++ tailWord_2070638) baseStart_2070638 baseEnd_2070638 := by
    simpa [prefixWord, tailWord_2070638, baseEnd_2070638] using wordTrace_append hprefix tailTrace_2070638
  have hstable : (prefixWord ++ tailWord_2070638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070638).length < 2 ^ (prefixWord ++ tailWord_2070638).sum := by decide
  have hdescent : baseEnd_2070638 < baseStart_2070638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070665 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 2, 4, 2]
def baseStart_2070665 : Nat := 118140960795 + 2070665 * 2 ^ 59
def prefixEnd_2070665 : Nat := 4983230072969 + 3 ^ 40 * 2070665 * 2
def baseEnd_2070665 : Nat := 1063246419442246247364691

theorem tailTrace_2070665 : CollatzResearch.WordTrace tailWord_2070665 prefixEnd_2070665 1063246419442246247364691 := by
  unfold tailWord_2070665
  simp only [CollatzResearch.WordTrace]
  refine ⟨75523357043341821272277449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50348904695561214181518299 75523357043341821272277449)
  ·
    refine ⟨56642517782506365954208087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75523357043341821272277449 56642517782506365954208087)
    ·
      refine ⟨84963776673759548931312131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56642517782506365954208087 84963776673759548931312131)
      ·
        refine ⟨127445665010639323396968197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84963776673759548931312131 127445665010639323396968197)
        ·
          refine ⟨23896062189494873136931537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127445665010639323396968197 23896062189494873136931537)
          ·
            refine ⟨17922046642121154852698653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23896062189494873136931537 17922046642121154852698653)
            ·
              refine ⟨6720767490795433069761995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17922046642121154852698653 6720767490795433069761995)
              ·
                refine ⟨10081151236193149604642993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6720767490795433069761995 10081151236193149604642993)
                ·
                  refine ⟨7560863427144862203482245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10081151236193149604642993 7560863427144862203482245)
                  ·
                    refine ⟨1417661892589661663152921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7560863427144862203482245 1417661892589661663152921)
                    ·
                      refine ⟨1063246419442246247364691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417661892589661663152921 1063246419442246247364691)
                      ·
                        rfl

theorem cell23_2070665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 4, 2].length) (baseStart_2070665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070665 prefixEnd_2070665 := by exact prefixLift 2070665
  have htrace : WordTrace (prefixWord ++ tailWord_2070665) baseStart_2070665 baseEnd_2070665 := by
    simpa [prefixWord, tailWord_2070665, baseEnd_2070665] using wordTrace_append hprefix tailTrace_2070665
  have hstable : (prefixWord ++ tailWord_2070665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070665).length < 2 ^ (prefixWord ++ tailWord_2070665).sum := by decide
  have hdescent : baseEnd_2070665 < baseStart_2070665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070685 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_2070685 : Nat := 118140960795 + 2070685 * 2 ^ 59
def prefixEnd_2070685 : Nat := 4983230072969 + 3 ^ 40 * 2070685 * 2
def baseEnd_2070685 : Nat := 1063256689055336169114599

theorem tailTrace_2070685 : CollatzResearch.WordTrace tailWord_2070685 prefixEnd_2070685 1063256689055336169114599 := by
  unfold tailWord_2070685
  simp only [CollatzResearch.WordTrace]
  refine ⟨75524086503269364688005509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50349391002179576458670339 75524086503269364688005509)
  ·
    refine ⟨14160766219363005879001033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75524086503269364688005509 14160766219363005879001033)
    ·
      refine ⟨10620574664522254409250775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14160766219363005879001033 10620574664522254409250775)
      ·
        refine ⟨15930861996783381613876163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10620574664522254409250775 15930861996783381613876163)
        ·
          refine ⟨23896292995175072420814245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15930861996783381613876163 23896292995175072420814245)
          ·
            refine ⟨4480554936595326078902671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23896292995175072420814245 4480554936595326078902671)
            ·
              refine ⟨6720832404892989118354007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480554936595326078902671 6720832404892989118354007)
              ·
                refine ⟨10081248607339483677531011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6720832404892989118354007 10081248607339483677531011)
                ·
                  refine ⟨15121872911009225516296517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10081248607339483677531011 15121872911009225516296517)
                  ·
                    refine ⟨2835351170814229784305597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15121872911009225516296517 2835351170814229784305597)
                    ·
                      refine ⟨1063256689055336169114599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2835351170814229784305597 1063256689055336169114599)
                      ·
                        rfl

theorem cell23_2070685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_2070685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070685 prefixEnd_2070685 := by exact prefixLift 2070685
  have htrace : WordTrace (prefixWord ++ tailWord_2070685) baseStart_2070685 baseEnd_2070685 := by
    simpa [prefixWord, tailWord_2070685, baseEnd_2070685] using wordTrace_append hprefix tailTrace_2070685
  have hstable : (prefixWord ++ tailWord_2070685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070685).length < 2 ^ (prefixWord ++ tailWord_2070685).sum := by decide
  have hdescent : baseEnd_2070685 < baseStart_2070685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070705 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 8]
def baseStart_2070705 : Nat := 118140960795 + 2070705 * 2 ^ 59
def prefixEnd_2070705 : Nat := 4983230072969 + 3 ^ 40 * 2070705 * 2
def baseEnd_2070705 : Nat := 118140773185380676762723

theorem tailTrace_2070705 : CollatzResearch.WordTrace tailWord_2070705 prefixEnd_2070705 118140773185380676762723 := by
  unfold tailWord_2070705
  simp only [CollatzResearch.WordTrace]
  refine ⟨75524815963196908103733569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50349877308797938735822379 75524815963196908103733569)
  ·
    refine ⟨56643611972397681077800177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75524815963196908103733569 56643611972397681077800177)
    ·
      refine ⟨42482708979298260808350133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56643611972397681077800177 42482708979298260808350133)
      ·
        refine ⟨3982753966809211950782825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42482708979298260808350133 3982753966809211950782825)
        ·
          refine ⟨2987065475106908963087119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3982753966809211950782825 2987065475106908963087119)
          ·
            refine ⟨4480598212660363444630679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987065475106908963087119 4480598212660363444630679)
            ·
              refine ⟨6720897318990545166946019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480598212660363444630679 6720897318990545166946019)
              ·
                refine ⟨10081345978485817750419029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6720897318990545166946019 10081345978485817750419029)
                ·
                  refine ⟨118140773185380676762723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10081345978485817750419029 118140773185380676762723)
                  ·
                    rfl

theorem cell23_2070705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 8].length) (baseStart_2070705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070705 prefixEnd_2070705 := by exact prefixLift 2070705
  have htrace : WordTrace (prefixWord ++ tailWord_2070705) baseStart_2070705 baseEnd_2070705 := by
    simpa [prefixWord, tailWord_2070705, baseEnd_2070705] using wordTrace_append hprefix tailTrace_2070705
  have hstable : (prefixWord ++ tailWord_2070705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070705).length < 2 ^ (prefixWord ++ tailWord_2070705).sum := by decide
  have hdescent : baseEnd_2070705 < baseStart_2070705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070709 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_2070709 : Nat := 118140960795 + 2070709 * 2 ^ 59
def prefixEnd_2070709 : Nat := 4983230072969 + 3 ^ 40 * 2070709 * 2
def baseEnd_2070709 : Nat := 354423004197014691738163

theorem tailTrace_2070709 : CollatzResearch.WordTrace tailWord_2070709 prefixEnd_2070709 354423004197014691738163 := by
  unfold tailWord_2070709
  simp only [CollatzResearch.WordTrace]
  refine ⟨75524961855182416786879181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50349974570121611191252787 75524961855182416786879181)
  ·
    refine ⟨28321860695693406295079693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75524961855182416786879181 28321860695693406295079693)
    ·
      refine ⟨10620697760885027360654885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28321860695693406295079693 10620697760885027360654885)
      ·
        refine ⟨1991380830165942630122791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10620697760885027360654885 1991380830165942630122791)
        ·
          refine ⟨2987071245248913945184187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991380830165942630122791 2987071245248913945184187)
          ·
            refine ⟨4480606867873370917776281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987071245248913945184187 4480606867873370917776281)
            ·
              refine ⟨3360455150905028188332211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4480606867873370917776281 3360455150905028188332211)
              ·
                refine ⟨5040682726357542282498317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360455150905028188332211 5040682726357542282498317)
                ·
                  refine ⟨1890256022384078355936869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5040682726357542282498317 1890256022384078355936869)
                  ·
                    refine ⟨354423004197014691738163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890256022384078355936869 354423004197014691738163)
                    ·
                      rfl

theorem cell23_2070709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_2070709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070709 prefixEnd_2070709 := by exact prefixLift 2070709
  have htrace : WordTrace (prefixWord ++ tailWord_2070709) baseStart_2070709 baseEnd_2070709 := by
    simpa [prefixWord, tailWord_2070709, baseEnd_2070709] using wordTrace_append hprefix tailTrace_2070709
  have hstable : (prefixWord ++ tailWord_2070709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070709).length < 2 ^ (prefixWord ++ tailWord_2070709).sum := by decide
  have hdescent : baseEnd_2070709 < baseStart_2070709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070725 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 1, 5, 2]
def baseStart_2070725 : Nat := 118140960795 + 2070725 * 2 ^ 59
def prefixEnd_2070725 : Nat := 4983230072969 + 3 ^ 40 * 2070725 * 2
def baseEnd_2070725 : Nat := 1063277228281516012614415

theorem tailTrace_2070725 : CollatzResearch.WordTrace tailWord_2070725 prefixEnd_2070725 1063277228281516012614415 := by
  unfold tailWord_2070725
  simp only [CollatzResearch.WordTrace]
  refine ⟨75525545423124451519461629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50350363615416301012974419 75525545423124451519461629)
  ·
    refine ⟨28322079533671669319798111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75525545423124451519461629 28322079533671669319798111)
    ·
      refine ⟨42483119300507503979697167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28322079533671669319798111 42483119300507503979697167)
      ·
        refine ⟨63724678950761255969545751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42483119300507503979697167 63724678950761255969545751)
        ·
          refine ⟨95587018426141883954318627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63724678950761255969545751 95587018426141883954318627)
          ·
            refine ⟨143380527639212825931477941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95587018426141883954318627 143380527639212825931477941)
            ·
              refine ⟨13441924466176202431076057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143380527639212825931477941 13441924466176202431076057)
              ·
                refine ⟨10081443349632151823307043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13441924466176202431076057 10081443349632151823307043)
                ·
                  refine ⟨15122165024448227734960565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10081443349632151823307043 15122165024448227734960565)
                  ·
                    refine ⟨1417702971042021350152553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15122165024448227734960565 1417702971042021350152553)
                    ·
                      refine ⟨1063277228281516012614415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417702971042021350152553 1063277228281516012614415)
                      ·
                        rfl

theorem cell23_2070725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_2070725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070725 prefixEnd_2070725 := by exact prefixLift 2070725
  have htrace : WordTrace (prefixWord ++ tailWord_2070725) baseStart_2070725 baseEnd_2070725 := by
    simpa [prefixWord, tailWord_2070725, baseEnd_2070725] using wordTrace_append hprefix tailTrace_2070725
  have hstable : (prefixWord ++ tailWord_2070725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070725).length < 2 ^ (prefixWord ++ tailWord_2070725).sum := by decide
  have hdescent : baseEnd_2070725 < baseStart_2070725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070735 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 1, 5]
def baseStart_2070735 : Nat := 118140960795 + 2070735 * 2 ^ 59
def prefixEnd_2070735 : Nat := 4983230072969 + 3 ^ 40 * 2070735 * 2
def baseEnd_2070735 : Nat := 354427454362686991163123

theorem tailTrace_2070735 : CollatzResearch.WordTrace tailWord_2070735 prefixEnd_2070735 354427454362686991163123 := by
  unfold tailWord_2070735
  simp only [CollatzResearch.WordTrace]
  refine ⟨75525910153088223227325659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50350606768725482151550439 75525910153088223227325659)
  ·
    refine ⟨113288865229632334840988489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75525910153088223227325659 113288865229632334840988489)
    ·
      refine ⟨84966648922224251130741367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113288865229632334840988489 84966648922224251130741367)
      ·
        refine ⟨127449973383336376696112051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84966648922224251130741367 127449973383336376696112051)
        ·
          refine ⟨191174960075004565044168077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127449973383336376696112051 191174960075004565044168077)
          ·
            refine ⟨71690610028126711891563029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191174960075004565044168077 71690610028126711891563029)
            ·
              refine ⟨3360497345068439619917017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71690610028126711891563029 3360497345068439619917017)
              ·
                refine ⟨2520373008801329714937763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360497345068439619917017 2520373008801329714937763)
                ·
                  refine ⟨3780559513201994572406645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520373008801329714937763 3780559513201994572406645)
                  ·
                    refine ⟨354427454362686991163123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3780559513201994572406645 354427454362686991163123)
                    ·
                      rfl

theorem cell23_2070735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_2070735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070735 prefixEnd_2070735 := by exact prefixLift 2070735
  have htrace : WordTrace (prefixWord ++ tailWord_2070735) baseStart_2070735 baseEnd_2070735 := by
    simpa [prefixWord, tailWord_2070735, baseEnd_2070735] using wordTrace_append hprefix tailTrace_2070735
  have hstable : (prefixWord ++ tailWord_2070735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070735).length < 2 ^ (prefixWord ++ tailWord_2070735).sum := by decide
  have hdescent : baseEnd_2070735 < baseStart_2070735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070759 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2070759 : Nat := 118140960795 + 2070759 * 2 ^ 59
def prefixEnd_2070759 : Nat := 4983230072969 + 3 ^ 40 * 2070759 * 2
def baseEnd_2070759 : Nat := 1063294686623768879589259

theorem tailTrace_2070759 : CollatzResearch.WordTrace tailWord_2070759 prefixEnd_2070759 1063294686623768879589259 := by
  unfold tailWord_2070759
  simp only [CollatzResearch.WordTrace]
  refine ⟨75526785505001275326199331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50351190336667516884132887 75526785505001275326199331)
  ·
    refine ⟨113290178257501912989298997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75526785505001275326199331 113290178257501912989298997)
    ·
      refine ⟨10620954211640804342746781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113290178257501912989298997 10620954211640804342746781)
      ·
        refine ⟨3982857829365301628530043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10620954211640804342746781 3982857829365301628530043)
        ·
          refine ⟨5974286744047952442795065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3982857829365301628530043 5974286744047952442795065)
          ·
            refine ⟨4480715058035964332096299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5974286744047952442795065 4480715058035964332096299)
            ·
              refine ⟨6721072587053946498144449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480715058035964332096299 6721072587053946498144449)
              ·
                refine ⟨5040804440290459873608337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6721072587053946498144449 5040804440290459873608337)
                ·
                  refine ⟨3780603330217844905206253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5040804440290459873608337 3780603330217844905206253)
                  ·
                    refine ⟨1417726248831691839452345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780603330217844905206253 1417726248831691839452345)
                    ·
                      refine ⟨1063294686623768879589259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417726248831691839452345 1063294686623768879589259)
                      ·
                        rfl

theorem cell23_2070759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2070759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070759 prefixEnd_2070759 := by exact prefixLift 2070759
  have htrace : WordTrace (prefixWord ++ tailWord_2070759) baseStart_2070759 baseEnd_2070759 := by
    simpa [prefixWord, tailWord_2070759, baseEnd_2070759] using wordTrace_append hprefix tailTrace_2070759
  have hstable : (prefixWord ++ tailWord_2070759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070759).length < 2 ^ (prefixWord ++ tailWord_2070759).sum := by decide
  have hdescent : baseEnd_2070759 < baseStart_2070759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070778 : List Nat := [3, 1, 1, 1, 1, 5, 1, 10]
def baseStart_2070778 : Nat := 118140960795 + 2070778 * 2 ^ 59
def prefixEnd_2070778 : Nat := 4983230072969 + 3 ^ 40 * 2070778 * 2
def baseEnd_2070778 : Nat := 39381646028007566861173

theorem tailTrace_2070778 : CollatzResearch.WordTrace tailWord_2070778 prefixEnd_2070778 39381646028007566861173 := by
  unfold tailWord_2070778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18881869622983110392785247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50351652327954961047427325 18881869622983110392785247)
  ·
    refine ⟨28322804434474665589177871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18881869622983110392785247 28322804434474665589177871)
    ·
      refine ⟨42484206651711998383766807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28322804434474665589177871 42484206651711998383766807)
      ·
        refine ⟨63726309977567997575650211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42484206651711998383766807 63726309977567997575650211)
        ·
          refine ⟨95589464966351996363475317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63726309977567997575650211 95589464966351996363475317)
          ·
            refine ⟨8961512340595499659075811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95589464966351996363475317 8961512340595499659075811)
            ·
              refine ⟨13442268510893249488613717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961512340595499659075811 13442268510893249488613717)
              ·
                refine ⟨39381646028007566861173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13442268510893249488613717 39381646028007566861173)
                ·
                  rfl

theorem cell23_2070778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 10].length) (baseStart_2070778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070778 prefixEnd_2070778 := by exact prefixLift 2070778
  have htrace : WordTrace (prefixWord ++ tailWord_2070778) baseStart_2070778 baseEnd_2070778 := by
    simpa [prefixWord, tailWord_2070778, baseEnd_2070778] using wordTrace_append hprefix tailTrace_2070778
  have hstable : (prefixWord ++ tailWord_2070778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070778).length < 2 ^ (prefixWord ++ tailWord_2070778).sum := by decide
  have hdescent : baseEnd_2070778 < baseStart_2070778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070785 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2070785 : Nat := 118140960795 + 2070785 * 2 ^ 59
def prefixEnd_2070785 : Nat := 4983230072969 + 3 ^ 40 * 2070785 * 2
def baseEnd_2070785 : Nat := 1063308037120785777864139

theorem tailTrace_2070785 : CollatzResearch.WordTrace tailWord_2070785 prefixEnd_2070785 1063308037120785777864139 := by
  unfold tailWord_2070785
  simp only [CollatzResearch.WordTrace]
  refine ⟨75527733802907081766645809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50351822535271387844430539 75527733802907081766645809)
  ·
    refine ⟨56645800352180311324984357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75527733802907081766645809 56645800352180311324984357)
    ·
      refine ⟨10621087566033808373434567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56645800352180311324984357 10621087566033808373434567)
      ·
        refine ⟨15931631349050712560151851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621087566033808373434567 15931631349050712560151851)
        ·
          refine ⟨23897447023576068840227777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15931631349050712560151851 23897447023576068840227777)
          ·
            refine ⟨17923085267682051630170833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23897447023576068840227777 17923085267682051630170833)
            ·
              refine ⟨13442313950761538722628125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17923085267682051630170833 13442313950761538722628125)
              ·
                refine ⟨5040867731535577020985547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13442313950761538722628125 5040867731535577020985547)
                ·
                  refine ⟨7561301597303365531478321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040867731535577020985547 7561301597303365531478321)
                  ·
                    refine ⟨5670976197977524148608741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7561301597303365531478321 5670976197977524148608741)
                    ·
                      refine ⟨1063308037120785777864139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5670976197977524148608741 1063308037120785777864139)
                      ·
                        rfl

theorem cell23_2070785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2070785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070785 prefixEnd_2070785 := by exact prefixLift 2070785
  have htrace : WordTrace (prefixWord ++ tailWord_2070785) baseStart_2070785 baseEnd_2070785 := by
    simpa [prefixWord, tailWord_2070785, baseEnd_2070785] using wordTrace_append hprefix tailTrace_2070785
  have hstable : (prefixWord ++ tailWord_2070785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070785).length < 2 ^ (prefixWord ++ tailWord_2070785).sum := by decide
  have hdescent : baseEnd_2070785 < baseStart_2070785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070792 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_2070792 : Nat := 118140960795 + 2070792 * 2 ^ 59
def prefixEnd_2070792 : Nat := 4983230072969 + 3 ^ 40 * 2070792 * 2
def baseEnd_2070792 : Nat := 1063311631485367250476607

theorem tailTrace_2070792 : CollatzResearch.WordTrace tailWord_2070792 prefixEnd_2070792 1063311631485367250476607 := by
  unfold tailWord_2070792
  simp only [CollatzResearch.WordTrace]
  refine ⟨37763994556940860981075315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50351992742587814641433753 37763994556940860981075315)
  ·
    refine ⟨56645991835411291471612973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37763994556940860981075315 56645991835411291471612973)
    ·
      refine ⟨21242246938279234301854865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56645991835411291471612973 21242246938279234301854865)
      ·
        refine ⟨15931685203709425726391149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21242246938279234301854865 15931685203709425726391149)
        ·
          refine ⟨5974381951391034647396681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15931685203709425726391149 5974381951391034647396681)
          ·
            refine ⟨4480786463543275985547511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5974381951391034647396681 4480786463543275985547511)
            ·
              refine ⟨6721179695314913978321267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480786463543275985547511 6721179695314913978321267)
              ·
                refine ⟨10081769542972370967481901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721179695314913978321267 10081769542972370967481901)
                ·
                  refine ⟨3780663578614639112805713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10081769542972370967481901 3780663578614639112805713)
                  ·
                    refine ⟨2835497683960979334604285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3780663578614639112805713 2835497683960979334604285)
                    ·
                      refine ⟨1063311631485367250476607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2835497683960979334604285 1063311631485367250476607)
                      ·
                        rfl

theorem cell23_2070792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_2070792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070792 prefixEnd_2070792 := by exact prefixLift 2070792
  have htrace : WordTrace (prefixWord ++ tailWord_2070792) baseStart_2070792 baseEnd_2070792 := by
    simpa [prefixWord, tailWord_2070792, baseEnd_2070792] using wordTrace_append hprefix tailTrace_2070792
  have hstable : (prefixWord ++ tailWord_2070792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070792).length < 2 ^ (prefixWord ++ tailWord_2070792).sum := by decide
  have hdescent : baseEnd_2070792 < baseStart_2070792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070805 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_2070805 : Nat := 118140960795 + 2070805 * 2 ^ 59
def prefixEnd_2070805 : Nat := 4983230072969 + 3 ^ 40 * 2070805 * 2
def baseEnd_2070805 : Nat := 1063318306733875699614047

theorem tailTrace_2070805 : CollatzResearch.WordTrace tailWord_2070805 prefixEnd_2070805 1063318306733875699614047 := by
  unfold tailWord_2070805
  simp only [CollatzResearch.WordTrace]
  refine ⟨75528463262834625182373869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50352308841889750121582579 75528463262834625182373869)
  ·
    refine ⟨28323173723562984443390201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75528463262834625182373869 28323173723562984443390201)
    ·
      refine ⟨21242380292672238332542651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28323173723562984443390201 21242380292672238332542651)
      ·
        refine ⟨31863570439008357498813977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21242380292672238332542651 31863570439008357498813977)
        ·
          refine ⟨23897677829256268124110483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31863570439008357498813977 23897677829256268124110483)
          ·
            refine ⟨35846516743884402186165725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23897677829256268124110483 35846516743884402186165725)
            ·
              refine ⟨13442443778956650819812147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35846516743884402186165725 13442443778956650819812147)
              ·
                refine ⟨20163665668434976229718221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442443778956650819812147 20163665668434976229718221)
                ·
                  refine ⟨7561374625663116086144333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20163665668434976229718221 7561374625663116086144333)
                  ·
                    refine ⟨2835515484623668532304125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7561374625663116086144333 2835515484623668532304125)
                    ·
                      refine ⟨1063318306733875699614047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2835515484623668532304125 1063318306733875699614047)
                      ·
                        rfl

theorem cell23_2070805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_2070805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070805 prefixEnd_2070805 := by exact prefixLift 2070805
  have htrace : WordTrace (prefixWord ++ tailWord_2070805) baseStart_2070805 baseEnd_2070805 := by
    simpa [prefixWord, tailWord_2070805, baseEnd_2070805] using wordTrace_append hprefix tailTrace_2070805
  have hstable : (prefixWord ++ tailWord_2070805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070805).length < 2 ^ (prefixWord ++ tailWord_2070805).sum := by decide
  have hdescent : baseEnd_2070805 < baseStart_2070805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070829 : List Nat := [1, 5, 3, 1, 2, 2, 1, 8]
def baseStart_2070829 : Nat := 118140960795 + 2070829 * 2 ^ 59
def prefixEnd_2070829 : Nat := 4983230072969 + 3 ^ 40 * 2070829 * 2
def baseEnd_2070829 : Nat := 39382615935910503915331

theorem tailTrace_2070829 : CollatzResearch.WordTrace tailWord_2070829 prefixEnd_2070829 39382615935910503915331 := by
  unfold tailWord_2070829
  simp only [CollatzResearch.WordTrace]
  refine ⟨75529338614747677281247541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50352892409831784854165027 75529338614747677281247541)
  ·
    refine ⟨7080875495132594745116957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75529338614747677281247541 7080875495132594745116957)
    ·
      refine ⟨2655328310674723029418859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7080875495132594745116957 2655328310674723029418859)
      ·
        refine ⟨3982992466012084544128289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655328310674723029418859 3982992466012084544128289)
        ·
          refine ⟨2987244349509063408096217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3982992466012084544128289 2987244349509063408096217)
          ·
            refine ⟨2240433262131797556072163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2987244349509063408096217 2240433262131797556072163)
            ·
              refine ⟨3360649893197696334108245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240433262131797556072163 3360649893197696334108245)
              ·
                refine ⟨39382615935910503915331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3360649893197696334108245 39382615935910503915331)
                ·
                  rfl

theorem cell23_2070829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 8].length) (baseStart_2070829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070829 prefixEnd_2070829 := by exact prefixLift 2070829
  have htrace : WordTrace (prefixWord ++ tailWord_2070829) baseStart_2070829 baseEnd_2070829 := by
    simpa [prefixWord, tailWord_2070829, baseEnd_2070829] using wordTrace_append hprefix tailTrace_2070829
  have hstable : (prefixWord ++ tailWord_2070829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070829).length < 2 ^ (prefixWord ++ tailWord_2070829).sum := by decide
  have hdescent : baseEnd_2070829 < baseStart_2070829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070862 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_2070862 : Nat := 118140960795 + 2070862 * 2 ^ 59
def prefixEnd_2070862 : Nat := 4983230072969 + 3 ^ 40 * 2070862 * 2
def baseEnd_2070862 : Nat := 1063347575131181976601285

theorem tailTrace_2070862 : CollatzResearch.WordTrace tailWord_2070862 prefixEnd_2070862 1063347575131181976601285 := by
  unfold tailWord_2070862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441317777953515489649855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50353694815752082611465893 9441317777953515489649855)
  ·
    refine ⟨14161976666930273234474783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9441317777953515489649855 14161976666930273234474783)
    ·
      refine ⟨21242965000395409851712175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14161976666930273234474783 21242965000395409851712175)
      ·
        refine ⟨31864447500593114777568263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21242965000395409851712175 31864447500593114777568263)
        ·
          refine ⟨47796671250889672166352395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31864447500593114777568263 47796671250889672166352395)
          ·
            refine ⟨71695006876334508249528593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47796671250889672166352395 71695006876334508249528593)
            ·
              refine ⟨53771255157250881187146445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71695006876334508249528593 53771255157250881187146445)
              ·
                refine ⟨20164220683969080445179917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53771255157250881187146445 20164220683969080445179917)
                ·
                  refine ⟨7561582756488405166942469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20164220683969080445179917 7561582756488405166942469)
                  ·
                    refine ⟨1417796766841575968801713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561582756488405166942469 1417796766841575968801713)
                    ·
                      refine ⟨1063347575131181976601285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417796766841575968801713 1063347575131181976601285)
                      ·
                        rfl

theorem cell23_2070862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_2070862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070862 prefixEnd_2070862 := by exact prefixLift 2070862
  have htrace : WordTrace (prefixWord ++ tailWord_2070862) baseStart_2070862 baseEnd_2070862 := by
    simpa [prefixWord, tailWord_2070862, baseEnd_2070862] using wordTrace_append hprefix tailTrace_2070862
  have hstable : (prefixWord ++ tailWord_2070862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070862).length < 2 ^ (prefixWord ++ tailWord_2070862).sum := by decide
  have hdescent : baseEnd_2070862 < baseStart_2070862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070866 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_2070866 : Nat := 118140960795 + 2070866 * 2 ^ 59
def prefixEnd_2070866 : Nat := 4983230072969 + 3 ^ 40 * 2070866 * 2
def baseEnd_2070866 : Nat := 1063349629053799960951267

theorem tailTrace_2070866 : CollatzResearch.WordTrace tailWord_2070866 prefixEnd_2070866 1063349629053799960951267 := by
  unfold tailWord_2070866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18882672028903408150086113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50353792077075755066896301 18882672028903408150086113)
  ·
    refine ⟨14162004021677556112564585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18882672028903408150086113 14162004021677556112564585)
    ·
      refine ⟨10621503016258167084423439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14162004021677556112564585 10621503016258167084423439)
      ·
        refine ⟨15932254524387250626635159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621503016258167084423439 15932254524387250626635159)
        ·
          refine ⟨23898381786580875939952739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15932254524387250626635159 23898381786580875939952739)
          ·
            refine ⟨35847572679871313909929109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23898381786580875939952739 35847572679871313909929109)
            ·
              refine ⟨1680354969368967839527927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35847572679871313909929109 1680354969368967839527927)
              ·
                refine ⟨2520532454053451759291891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680354969368967839527927 2520532454053451759291891)
                ·
                  refine ⟨3780798681080177638937837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520532454053451759291891 3780798681080177638937837)
                  ·
                    refine ⟨1417799505405066614601689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780798681080177638937837 1417799505405066614601689)
                    ·
                      refine ⟨1063349629053799960951267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417799505405066614601689 1063349629053799960951267)
                      ·
                        rfl

theorem cell23_2070866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_2070866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070866 prefixEnd_2070866 := by exact prefixLift 2070866
  have htrace : WordTrace (prefixWord ++ tailWord_2070866) baseStart_2070866 baseEnd_2070866 := by
    simpa [prefixWord, tailWord_2070866, baseEnd_2070866] using wordTrace_append hprefix tailTrace_2070866
  have hstable : (prefixWord ++ tailWord_2070866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070866).length < 2 ^ (prefixWord ++ tailWord_2070866).sum := by decide
  have hdescent : baseEnd_2070866 < baseStart_2070866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070885 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 7]
def baseStart_2070885 : Nat := 118140960795 + 2070885 * 2 ^ 59
def prefixEnd_2070885 : Nat := 4983230072969 + 3 ^ 40 * 2070885 * 2
def baseEnd_2070885 : Nat := 118151042798470598512631

theorem tailTrace_2070885 : CollatzResearch.WordTrace tailWord_2070885 prefixEnd_2070885 118151042798470598512631 := by
  unfold tailWord_2070885
  simp only [CollatzResearch.WordTrace]
  refine ⟨75531381102544798845286109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50354254068363199230190739 75531381102544798845286109)
  ·
    refine ⟨28324267913454299566982291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75531381102544798845286109 28324267913454299566982291)
    ·
      refine ⟨42486401870181449350473437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28324267913454299566982291 42486401870181449350473437)
      ·
        refine ⟨15932400701318043506427539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42486401870181449350473437 15932400701318043506427539)
        ·
          refine ⟨23898601051977065259641309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15932400701318043506427539 23898601051977065259641309)
          ·
            refine ⟨8961975394491399472365491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23898601051977065259641309 8961975394491399472365491)
            ·
              refine ⟨13442963091737099208548237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961975394491399472365491 13442963091737099208548237)
              ·
                refine ⟨5041111159401412203205589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13442963091737099208548237 5041111159401412203205589)
                ·
                  refine ⟨118151042798470598512631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5041111159401412203205589 118151042798470598512631)
                  ·
                    rfl

theorem cell23_2070885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_2070885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070885 prefixEnd_2070885 := by exact prefixLift 2070885
  have htrace : WordTrace (prefixWord ++ tailWord_2070885) baseStart_2070885 baseEnd_2070885 := by
    simpa [prefixWord, tailWord_2070885, baseEnd_2070885] using wordTrace_append hprefix tailTrace_2070885
  have hstable : (prefixWord ++ tailWord_2070885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070885).length < 2 ^ (prefixWord ++ tailWord_2070885).sum := by decide
  have hdescent : baseEnd_2070885 < baseStart_2070885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070895 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 3]
def baseStart_2070895 : Nat := 118140960795 + 2070895 * 2 ^ 59
def prefixEnd_2070895 : Nat := 4983230072969 + 3 ^ 40 * 2070895 * 2
def baseEnd_2070895 : Nat := 1063364519992780347488633

theorem tailTrace_2070895 : CollatzResearch.WordTrace tailWord_2070895 prefixEnd_2070895 1063364519992780347488633 := by
  unfold tailWord_2070895
  simp only [CollatzResearch.WordTrace]
  refine ⟨75531745832508570553150139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50354497221672380368766759 75531745832508570553150139)
  ·
    refine ⟨113297618748762855829725209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75531745832508570553150139 113297618748762855829725209)
    ·
      refine ⟨84973214061572141872293907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113297618748762855829725209 84973214061572141872293907)
      ·
        refine ⟨127459821092358212808440861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84973214061572141872293907 127459821092358212808440861)
        ·
          refine ⟨47797432909634329803165323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127459821092358212808440861 47797432909634329803165323)
          ·
            refine ⟨71696149364451494704747985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47797432909634329803165323 71696149364451494704747985)
            ·
              refine ⟨53772112023338621028560989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71696149364451494704747985 53772112023338621028560989)
              ·
                refine ⟨20164542008751982885710371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53772112023338621028560989 20164542008751982885710371)
                ·
                  refine ⟨30246813013127974328565557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20164542008751982885710371 30246813013127974328565557)
                  ·
                    refine ⟨2835638719980747593303021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30246813013127974328565557 2835638719980747593303021)
                    ·
                      refine ⟨1063364519992780347488633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2835638719980747593303021 1063364519992780347488633)
                      ·
                        rfl

theorem cell23_2070895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 3].length) (baseStart_2070895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070895 prefixEnd_2070895 := by exact prefixLift 2070895
  have htrace : WordTrace (prefixWord ++ tailWord_2070895) baseStart_2070895 baseEnd_2070895 := by
    simpa [prefixWord, tailWord_2070895, baseEnd_2070895] using wordTrace_append hprefix tailTrace_2070895
  have hstable : (prefixWord ++ tailWord_2070895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070895).length < 2 ^ (prefixWord ++ tailWord_2070895).sum := by decide
  have hdescent : baseEnd_2070895 < baseStart_2070895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070936 : List Nat := [2, 1, 2, 5, 1, 2, 3, 2, 5]
def baseStart_2070936 : Nat := 118140960795 + 2070936 * 2 ^ 59
def prefixEnd_2070936 : Nat := 4983230072969 + 3 ^ 40 * 2070936 * 2
def baseEnd_2070936 : Nat := 118153952522179409675105

theorem tailTrace_2070936 : CollatzResearch.WordTrace tailWord_2070936 prefixEnd_2070936 118153952522179409675105 := by
  unfold tailWord_2070936
  simp only [CollatzResearch.WordTrace]
  refine ⟨37766620612680017277696331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50355494150240023036928441 37766620612680017277696331)
  ·
    refine ⟨56649930919020025916544497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37766620612680017277696331 56649930919020025916544497)
    ·
      refine ⟨42487448189265019437408373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56649930919020025916544497 42487448189265019437408373)
      ·
        refine ⟨3983198267743595572257035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42487448189265019437408373 3983198267743595572257035)
        ·
          refine ⟨5974797401615393358385553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983198267743595572257035 5974797401615393358385553)
          ·
            refine ⟨4481098051211545018789165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5974797401615393358385553 4481098051211545018789165)
            ·
              refine ⟨1680411769204329382045937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4481098051211545018789165 1680411769204329382045937)
              ·
                refine ⟨1260308826903247036534453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680411769204329382045937 1260308826903247036534453)
                ·
                  refine ⟨118153952522179409675105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1260308826903247036534453 118153952522179409675105)
                  ·
                    rfl

theorem cell23_2070936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 5].length) (baseStart_2070936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070936 prefixEnd_2070936 := by exact prefixLift 2070936
  have htrace : WordTrace (prefixWord ++ tailWord_2070936) baseStart_2070936 baseEnd_2070936 := by
    simpa [prefixWord, tailWord_2070936, baseEnd_2070936] using wordTrace_append hprefix tailTrace_2070936
  have hstable : (prefixWord ++ tailWord_2070936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070936).length < 2 ^ (prefixWord ++ tailWord_2070936).sum := by decide
  have hdescent : baseEnd_2070936 < baseStart_2070936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070962 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_2070962 : Nat := 118140960795 + 2070962 * 2 ^ 59
def prefixEnd_2070962 : Nat := 4983230072969 + 3 ^ 40 * 2070962 * 2
def baseEnd_2070962 : Nat := 354466307732210528450275

theorem tailTrace_2070962 : CollatzResearch.WordTrace tailWord_2070962 prefixEnd_2070962 354466307732210528450275 := by
  unfold tailWord_2070962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18883547380816460248959785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50356126348843893997226093 18883547380816460248959785)
  ·
    refine ⟨14162660535612345186719839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18883547380816460248959785 14162660535612345186719839)
    ·
      refine ⟨21243990803418517780079759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162660535612345186719839 21243990803418517780079759)
      ·
        refine ⟨31865986205127776670119639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21243990803418517780079759 31865986205127776670119639)
        ·
          refine ⟨47798979307691665005179459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31865986205127776670119639 47798979307691665005179459)
          ·
            refine ⟨71698468961537497507769189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47798979307691665005179459 71698468961537497507769189)
            ·
              refine ⟨13443462930288280782706723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71698468961537497507769189 13443462930288280782706723)
              ·
                refine ⟨20165194395432421174060085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13443462930288280782706723 20165194395432421174060085)
                ·
                  refine ⟨1890486974571789485068133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20165194395432421174060085 1890486974571789485068133)
                  ·
                    refine ⟨354466307732210528450275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890486974571789485068133 354466307732210528450275)
                    ·
                      rfl

theorem cell23_2070962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_2070962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070962 prefixEnd_2070962 := by exact prefixLift 2070962
  have htrace : WordTrace (prefixWord ++ tailWord_2070962) baseStart_2070962 baseEnd_2070962 := by
    simpa [prefixWord, tailWord_2070962, baseEnd_2070962] using wordTrace_append hprefix tailTrace_2070962
  have hstable : (prefixWord ++ tailWord_2070962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070962).length < 2 ^ (prefixWord ++ tailWord_2070962).sum := by decide
  have hdescent : baseEnd_2070962 < baseStart_2070962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070969 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2070969 : Nat := 118140960795 + 2070969 * 2 ^ 59
def prefixEnd_2070969 : Nat := 4983230072969 + 3 ^ 40 * 2070969 * 2
def baseEnd_2070969 : Nat := 1063402517561213057963293

theorem tailTrace_2070969 : CollatzResearch.WordTrace tailWord_2070969 prefixEnd_2070969 1063402517561213057963293 := by
  unfold tailWord_2070969
  simp only [CollatzResearch.WordTrace]
  refine ⟨75534444834240481191343961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50356296556160320794229307 75534444834240481191343961)
  ·
    refine ⟨56650833625680360893507971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75534444834240481191343961 56650833625680360893507971)
    ·
      refine ⟨84976250438520541340261957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56650833625680360893507971 84976250438520541340261957)
      ·
        refine ⟨15933046957222601501299117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84976250438520541340261957 15933046957222601501299117)
        ·
          refine ⟨5974892608958475562987169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15933046957222601501299117 5974892608958475562987169)
          ·
            refine ⟨4481169456718856672240377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5974892608958475562987169 4481169456718856672240377)
            ·
              refine ⟨3360877092539142504180283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4481169456718856672240377 3360877092539142504180283)
              ·
                refine ⟨5041315638808713756270425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3360877092539142504180283 5041315638808713756270425)
                ·
                  refine ⟨3780986729106535317202819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5041315638808713756270425 3780986729106535317202819)
                  ·
                    refine ⟨5671480093659802975804229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3780986729106535317202819 5671480093659802975804229)
                    ·
                      refine ⟨1063402517561213057963293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5671480093659802975804229 1063402517561213057963293)
                      ·
                        rfl

theorem cell23_2070969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2070969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070969 prefixEnd_2070969 := by exact prefixLift 2070969
  have htrace : WordTrace (prefixWord ++ tailWord_2070969) baseStart_2070969 baseEnd_2070969 := by
    simpa [prefixWord, tailWord_2070969, baseEnd_2070969] using wordTrace_append hprefix tailTrace_2070969
  have hstable : (prefixWord ++ tailWord_2070969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070969).length < 2 ^ (prefixWord ++ tailWord_2070969).sum := by decide
  have hdescent : baseEnd_2070969 < baseStart_2070969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070979 : List Nat := [1, 1, 1, 3, 1, 1, 3, 7, 1, 4]
def baseStart_2070979 : Nat := 118140960795 + 2070979 * 2 ^ 59
def prefixEnd_2070979 : Nat := 4983230072969 + 3 ^ 40 * 2070979 * 2
def baseEnd_2070979 : Nat := 354469217455919339612749

theorem tailTrace_2070979 : CollatzResearch.WordTrace tailWord_2070979 prefixEnd_2070979 354469217455919339612749 := by
  unfold tailWord_2070979
  simp only [CollatzResearch.WordTrace]
  refine ⟨75534809564204252899207991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50356539709469501932805327 75534809564204252899207991)
  ·
    refine ⟨113302214346306379348811987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75534809564204252899207991 113302214346306379348811987)
    ·
      refine ⟨169953321519459569023217981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113302214346306379348811987 169953321519459569023217981)
      ·
        refine ⟨63732495569797338383706743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169953321519459569023217981 63732495569797338383706743)
        ·
          refine ⟨95598743354696007575560115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63732495569797338383706743 95598743354696007575560115)
          ·
            refine ⟨143398115032044011363340173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95598743354696007575560115 143398115032044011363340173)
            ·
              refine ⟨53774293137016504261252565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143398115032044011363340173 53774293137016504261252565)
              ·
                refine ⟨1260334995398824318623107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53774293137016504261252565 1260334995398824318623107)
                ·
                  refine ⟨1890502493098236477934661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260334995398824318623107 1890502493098236477934661)
                  ·
                    refine ⟨354469217455919339612749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890502493098236477934661 354469217455919339612749)
                    ·
                      rfl

theorem cell23_2070979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 4].length) (baseStart_2070979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070979 prefixEnd_2070979 := by exact prefixLift 2070979
  have htrace : WordTrace (prefixWord ++ tailWord_2070979) baseStart_2070979 baseEnd_2070979 := by
    simpa [prefixWord, tailWord_2070979, baseEnd_2070979] using wordTrace_append hprefix tailTrace_2070979
  have hstable : (prefixWord ++ tailWord_2070979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070979).length < 2 ^ (prefixWord ++ tailWord_2070979).sum := by decide
  have hdescent : baseEnd_2070979 < baseStart_2070979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071019 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 3]
def baseStart_2071019 : Nat := 118140960795 + 2071019 * 2 ^ 59
def prefixEnd_2071019 : Nat := 4983230072969 + 3 ^ 40 * 2071019 * 2
def baseEnd_2071019 : Nat := 1063428191593937862338063

theorem tailTrace_2071019 : CollatzResearch.WordTrace tailWord_2071019 prefixEnd_2071019 1063428191593937862338063 := by
  unfold tailWord_2071019
  simp only [CollatzResearch.WordTrace]
  refine ⟨75536268484059339730664111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50357512322706226487109407 75536268484059339730664111)
  ·
    refine ⟨113304402726089009595996167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75536268484059339730664111 113304402726089009595996167)
    ·
      refine ⟨169956604089133514393994251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113304402726089009595996167 169956604089133514393994251)
      ·
        refine ⟨254934906133700271590991377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169956604089133514393994251 254934906133700271590991377)
        ·
          refine ⟨191201179600275203693243533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254934906133700271590991377 191201179600275203693243533)
          ·
            refine ⟨71700442350103201384966325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191201179600275203693243533 71700442350103201384966325)
            ·
              refine ⟨6721916470322175129840593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71700442350103201384966325 6721916470322175129840593)
              ·
                refine ⟨5041437352741631347380445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6721916470322175129840593 5041437352741631347380445)
                ·
                  refine ⟨1890539007278111755267667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5041437352741631347380445 1890539007278111755267667)
                  ·
                    refine ⟨2835808510917167632901501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1890539007278111755267667 2835808510917167632901501)
                    ·
                      refine ⟨1063428191593937862338063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2835808510917167632901501 1063428191593937862338063)
                      ·
                        rfl

theorem cell23_2071019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 1, 3].length) (baseStart_2071019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071019 prefixEnd_2071019 := by exact prefixLift 2071019
  have htrace : WordTrace (prefixWord ++ tailWord_2071019) baseStart_2071019 baseEnd_2071019 := by
    simpa [prefixWord, tailWord_2071019, baseEnd_2071019] using wordTrace_append hprefix tailTrace_2071019
  have hstable : (prefixWord ++ tailWord_2071019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071019).length < 2 ^ (prefixWord ++ tailWord_2071019).sum := by decide
  have hdescent : baseEnd_2071019 < baseStart_2071019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071069 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2071069 : Nat := 118140960795 + 2071069 * 2 ^ 59
def prefixEnd_2071069 : Nat := 4983230072969 + 3 ^ 40 * 2071069 * 2
def baseEnd_2071069 : Nat := 354484621875554222237611

theorem tailTrace_2071069 : CollatzResearch.WordTrace tailWord_2071069 prefixEnd_2071069 354484621875554222237611 := by
  unfold tailWord_2071069
  simp only [CollatzResearch.WordTrace]
  refine ⟨75538092133878198269984261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50358728089252132179989507 75538092133878198269984261)
  ·
    refine ⟨14163392275102162175622049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75538092133878198269984261 14163392275102162175622049)
    ·
      refine ⟨10622544206326621631716537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14163392275102162175622049 10622544206326621631716537)
      ·
        refine ⟨7966908154744966223787403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10622544206326621631716537 7966908154744966223787403)
        ·
          refine ⟨11950362232117449335681105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966908154744966223787403 11950362232117449335681105)
          ·
            refine ⟨8962771674088087001760829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11950362232117449335681105 8962771674088087001760829)
            ·
              refine ⟨3361039377783032625660311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8962771674088087001760829 3361039377783032625660311)
              ·
                refine ⟨5041559066674548938490467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361039377783032625660311 5041559066674548938490467)
                ·
                  refine ⟨7562338600011823407735701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041559066674548938490467 7562338600011823407735701)
                  ·
                    refine ⟨354484621875554222237611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7562338600011823407735701 354484621875554222237611)
                    ·
                      rfl

theorem cell23_2071069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2071069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071069 prefixEnd_2071069 := by exact prefixLift 2071069
  have htrace : WordTrace (prefixWord ++ tailWord_2071069) baseStart_2071069 baseEnd_2071069 := by
    simpa [prefixWord, tailWord_2071069, baseEnd_2071069] using wordTrace_append hprefix tailTrace_2071069
  have hstable : (prefixWord ++ tailWord_2071069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071069).length < 2 ^ (prefixWord ++ tailWord_2071069).sum := by decide
  have hdescent : baseEnd_2071069 < baseStart_2071069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071169 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2071169 : Nat := 118140960795 + 2071169 * 2 ^ 59
def prefixEnd_2071169 : Nat := 4983230072969 + 3 ^ 40 * 2071169 * 2
def baseEnd_2071169 : Nat := 1063505213692112275462373

theorem tailTrace_2071169 : CollatzResearch.WordTrace tailWord_2071169 prefixEnd_2071169 1063505213692112275462373 := by
  unfold tailWord_2071169
  simp only [CollatzResearch.WordTrace]
  refine ⟨75541739433515915348624561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50361159622343943565749707 75541739433515915348624561)
  ·
    refine ⟨56656304575136936511468421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75541739433515915348624561 56656304575136936511468421)
    ·
      refine ⟨10623057107838175595900329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56656304575136936511468421 10623057107838175595900329)
      ·
        refine ⟨7967292830878631696925247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10623057107838175595900329 7967292830878631696925247)
        ·
          refine ⟨11950939246317947545387871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967292830878631696925247 11950939246317947545387871)
          ·
            refine ⟨17926408869476921318081807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11950939246317947545387871 17926408869476921318081807)
            ·
              refine ⟨26889613304215381977122711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17926408869476921318081807 26889613304215381977122711)
              ·
                refine ⟨40334419956323072965684067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26889613304215381977122711 40334419956323072965684067)
                ·
                  refine ⟨60501629934484609448526101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40334419956323072965684067 60501629934484609448526101)
                  ·
                    refine ⟨2836013903178966067899661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60501629934484609448526101 2836013903178966067899661)
                    ·
                      refine ⟨1063505213692112275462373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2836013903178966067899661 1063505213692112275462373)
                      ·
                        rfl

theorem cell23_2071169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2071169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071169 prefixEnd_2071169 := by exact prefixLift 2071169
  have htrace : WordTrace (prefixWord ++ tailWord_2071169) baseStart_2071169 baseEnd_2071169 := by
    simpa [prefixWord, tailWord_2071169, baseEnd_2071169] using wordTrace_append hprefix tailTrace_2071169
  have hstable : (prefixWord ++ tailWord_2071169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071169).length < 2 ^ (prefixWord ++ tailWord_2071169).sum := by decide
  have hdescent : baseEnd_2071169 < baseStart_2071169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071239 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_2071239 : Nat := 118140960795 + 2071239 * 2 ^ 59
def prefixEnd_2071239 : Nat := 4983230072969 + 3 ^ 40 * 2071239 * 2
def baseEnd_2071239 : Nat := 1063541157337927001587051

theorem tailTrace_2071239 : CollatzResearch.WordTrace tailWord_2071239 prefixEnd_2071239 1063541157337927001587051 := by
  unfold tailWord_2071239
  simp only [CollatzResearch.WordTrace]
  refine ⟨75544292543262317303672771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50362861695508211535781847 75544292543262317303672771)
  ·
    refine ⟨113316438814893475955509157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75544292543262317303672771 113316438814893475955509157)
    ·
      refine ⟨21246832277792526741657967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113316438814893475955509157 21246832277792526741657967)
      ·
        refine ⟨31870248416688790112486951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21246832277792526741657967 31870248416688790112486951)
        ·
          refine ⟨47805372625033185168730427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31870248416688790112486951 47805372625033185168730427)
          ·
            refine ⟨71708058937549777753095641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47805372625033185168730427 71708058937549777753095641)
            ·
              refine ⟨53781044203162333314821731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71708058937549777753095641 53781044203162333314821731)
              ·
                refine ⟨80671566304743499972232597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53781044203162333314821731 80671566304743499972232597)
                ·
                  refine ⟨3781479670534851561198403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80671566304743499972232597 3781479670534851561198403)
                  ·
                    refine ⟨5672219505802277341797605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3781479670534851561198403 5672219505802277341797605)
                    ·
                      refine ⟨1063541157337927001587051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5672219505802277341797605 1063541157337927001587051)
                      ·
                        rfl

theorem cell23_2071239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_2071239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071239 prefixEnd_2071239 := by exact prefixLift 2071239
  have htrace : WordTrace (prefixWord ++ tailWord_2071239) baseStart_2071239 baseEnd_2071239 := by
    simpa [prefixWord, tailWord_2071239, baseEnd_2071239] using wordTrace_append hprefix tailTrace_2071239
  have hstable : (prefixWord ++ tailWord_2071239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071239).length < 2 ^ (prefixWord ++ tailWord_2071239).sum := by decide
  have hdescent : baseEnd_2071239 < baseStart_2071239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071279 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 8]
def baseStart_2071279 : Nat := 118140960795 + 2071279 * 2 ^ 59
def prefixEnd_2071279 : Nat := 4983230072969 + 3 ^ 40 * 2071279 * 2
def baseEnd_2071279 : Nat := 118173521840456316120763

theorem tailTrace_2071279 : CollatzResearch.WordTrace tailWord_2071279 prefixEnd_2071279 118173521840456316120763 := by
  unfold tailWord_2071279
  simp only [CollatzResearch.WordTrace]
  refine ⟨75545751463117404135128891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50363834308744936090085927 75545751463117404135128891)
  ·
    refine ⟨113318627194676106202693337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75545751463117404135128891 113318627194676106202693337)
    ·
      refine ⟨84988970396007079652020003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113318627194676106202693337 84988970396007079652020003)
      ·
        refine ⟨127483455594010619478030005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84988970396007079652020003 127483455594010619478030005)
        ·
          refine ⟨11951573961938495576065313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127483455594010619478030005 11951573961938495576065313)
          ·
            refine ⟨8963680471453871682048985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11951573961938495576065313 8963680471453871682048985)
            ·
              refine ⟨6722760353590403761536739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8963680471453871682048985 6722760353590403761536739)
              ·
                refine ⟨10084140530385605642305109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6722760353590403761536739 10084140530385605642305109)
                ·
                  refine ⟨118173521840456316120763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10084140530385605642305109 118173521840456316120763)
                  ·
                    rfl

theorem cell23_2071279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 8].length) (baseStart_2071279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071279 prefixEnd_2071279 := by exact prefixLift 2071279
  have htrace : WordTrace (prefixWord ++ tailWord_2071279) baseStart_2071279 baseEnd_2071279 := by
    simpa [prefixWord, tailWord_2071279, baseEnd_2071279] using wordTrace_append hprefix tailTrace_2071279
  have hstable : (prefixWord ++ tailWord_2071279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071279).length < 2 ^ (prefixWord ++ tailWord_2071279).sum := by decide
  have hdescent : baseEnd_2071279 < baseStart_2071279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071333 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 2, 3, 2]
def baseStart_2071333 : Nat := 118140960795 + 2071333 * 2 ^ 59
def prefixEnd_2071333 : Nat := 4983230072969 + 3 ^ 40 * 2071333 * 2
def baseEnd_2071333 : Nat := 1063589424519449633811619

theorem tailTrace_2071333 : CollatzResearch.WordTrace tailWord_2071333 prefixEnd_2071333 1063589424519449633811619 := by
  unfold tailWord_2071333
  simp only [CollatzResearch.WordTrace]
  refine ⟨75547721004921771357594653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50365147336614514238396435 75547721004921771357594653)
  ·
    refine ⟨28330395376845664259097995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75547721004921771357594653 28330395376845664259097995)
    ·
      refine ⟨42495593065268496388646993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28330395376845664259097995 42495593065268496388646993)
      ·
        refine ⟨31871694798951372291485245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42495593065268496388646993 31871694798951372291485245)
        ·
          refine ⟨11951885549606764609306967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31871694798951372291485245 11951885549606764609306967)
          ·
            refine ⟨17927828324410146913960451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951885549606764609306967 17927828324410146913960451)
            ·
              refine ⟨26891742486615220370940677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17927828324410146913960451 26891742486615220370940677)
              ·
                refine ⟨5042201716240353819551377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26891742486615220370940677 5042201716240353819551377)
                ·
                  refine ⟨3781651287180265364663533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5042201716240353819551377 3781651287180265364663533)
                  ·
                    refine ⟨1418119232692599511748825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781651287180265364663533 1418119232692599511748825)
                    ·
                      refine ⟨1063589424519449633811619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418119232692599511748825 1063589424519449633811619)
                      ·
                        rfl

theorem cell23_2071333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_2071333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071333 prefixEnd_2071333 := by exact prefixLift 2071333
  have htrace : WordTrace (prefixWord ++ tailWord_2071333) baseStart_2071333 baseEnd_2071333 := by
    simpa [prefixWord, tailWord_2071333, baseEnd_2071333] using wordTrace_append hprefix tailTrace_2071333
  have hstable : (prefixWord ++ tailWord_2071333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071333).length < 2 ^ (prefixWord ++ tailWord_2071333).sum := by decide
  have hdescent : baseEnd_2071333 < baseStart_2071333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071340 : List Nat := [2, 2, 1, 1, 1, 4, 3, 4, 1, 1, 3]
def baseStart_2071340 : Nat := 118140960795 + 2071340 * 2 ^ 59
def prefixEnd_2071340 : Nat := 4983230072969 + 3 ^ 40 * 2071340 * 2
def baseEnd_2071340 : Nat := 1063593018884031106424087

theorem tailTrace_2071340 : CollatzResearch.WordTrace tailWord_2071340 prefixEnd_2071340 1063593018884031106424087 := by
  unfold tailWord_2071340
  simp only [CollatzResearch.WordTrace]
  refine ⟨37773988157948205776549737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50365317543930941035399649 37773988157948205776549737)
  ·
    refine ⟨28330491118461154332412303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37773988157948205776549737 28330491118461154332412303)
    ·
      refine ⟨42495736677691731498618455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28330491118461154332412303 42495736677691731498618455)
      ·
        refine ⟨63743605016537597247927683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42495736677691731498618455 63743605016537597247927683)
        ·
          refine ⟨95615407524806395871891525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63743605016537597247927683 95615407524806395871891525)
          ·
            refine ⟨17927888910901199225979661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95615407524806395871891525 17927888910901199225979661)
            ·
              refine ⟨6722958341587949709742373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17927888910901199225979661 6722958341587949709742373)
              ·
                refine ⟨1260554689047740570576695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6722958341587949709742373 1260554689047740570576695)
                ·
                  refine ⟨1890832033571610855865043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260554689047740570576695 1890832033571610855865043)
                  ·
                    refine ⟨2836248050357416283797565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1890832033571610855865043 2836248050357416283797565)
                    ·
                      refine ⟨1063593018884031106424087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2836248050357416283797565 1063593018884031106424087)
                      ·
                        rfl

theorem cell23_2071340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_2071340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071340 prefixEnd_2071340 := by exact prefixLift 2071340
  have htrace : WordTrace (prefixWord ++ tailWord_2071340) baseStart_2071340 baseEnd_2071340 := by
    simpa [prefixWord, tailWord_2071340, baseEnd_2071340] using wordTrace_append hprefix tailTrace_2071340
  have hstable : (prefixWord ++ tailWord_2071340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071340).length < 2 ^ (prefixWord ++ tailWord_2071340).sum := by decide
  have hdescent : baseEnd_2071340 < baseStart_2071340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071346 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2071346 : Nat := 118140960795 + 2071346 * 2 ^ 59
def prefixEnd_2071346 : Nat := 4983230072969 + 3 ^ 40 * 2071346 * 2
def baseEnd_2071346 : Nat := 1063596099767958082949059

theorem tailTrace_2071346 : CollatzResearch.WordTrace tailWord_2071346 prefixEnd_2071346 1063596099767958082949059 := by
  unfold tailWord_2071346
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887048788468668644454473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50365463435916449718545261 18887048788468668644454473)
  ·
    refine ⟨14165286591351501483340855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18887048788468668644454473 14165286591351501483340855)
    ·
      refine ⟨21247929887027252225011283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14165286591351501483340855 21247929887027252225011283)
      ·
        refine ⟨31871894830540878337516925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21247929887027252225011283 31871894830540878337516925)
        ·
          refine ⟨11951960561452829376568847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31871894830540878337516925 11951960561452829376568847)
          ·
            refine ⟨17927940842179244064853271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951960561452829376568847 17927940842179244064853271)
            ·
              refine ⟨26891911263268866097279907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17927940842179244064853271 26891911263268866097279907)
              ·
                refine ⟨40337866894903299145919861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26891911263268866097279907 40337866894903299145919861)
                ·
                  refine ⟨3781675021397184294929987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40337866894903299145919861 3781675021397184294929987)
                  ·
                    refine ⟨5672512532095776442394981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3781675021397184294929987 5672512532095776442394981)
                    ·
                      refine ⟨1063596099767958082949059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5672512532095776442394981 1063596099767958082949059)
                      ·
                        rfl

theorem cell23_2071346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2071346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071346 prefixEnd_2071346 := by exact prefixLift 2071346
  have htrace : WordTrace (prefixWord ++ tailWord_2071346) baseStart_2071346 baseEnd_2071346 := by
    simpa [prefixWord, tailWord_2071346, baseEnd_2071346] using wordTrace_append hprefix tailTrace_2071346
  have hstable : (prefixWord ++ tailWord_2071346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071346).length < 2 ^ (prefixWord ++ tailWord_2071346).sum := by decide
  have hdescent : baseEnd_2071346 < baseStart_2071346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071356 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_2071356 : Nat := 118140960795 + 2071356 * 2 ^ 59
def prefixEnd_2071356 : Nat := 4983230072969 + 3 ^ 40 * 2071356 * 2
def baseEnd_2071356 : Nat := 354533744858167681274671

theorem tailTrace_2071356 : CollatzResearch.WordTrace tailWord_2071356 prefixEnd_2071356 354533744858167681274671 := by
  unfold tailWord_2071356
  simp only [CollatzResearch.WordTrace]
  refine ⟨37774279941919223142840961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50365706589225630857121281 37774279941919223142840961)
  ·
    refine ⟨28330709956439417357130721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37774279941919223142840961 28330709956439417357130721)
    ·
      refine ⟨21248032467329563017848041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28330709956439417357130721 21248032467329563017848041)
      ·
        refine ⟨15936024350497172263386031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21248032467329563017848041 15936024350497172263386031)
        ·
          refine ⟨23904036525745758395079047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15936024350497172263386031 23904036525745758395079047)
          ·
            refine ⟨35856054788618637592618571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23904036525745758395079047 35856054788618637592618571)
            ·
              refine ⟨53784082182927956388927857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35856054788618637592618571 53784082182927956388927857)
              ·
                refine ⟨40338061637195967291695893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53784082182927956388927857 40338061637195967291695893)
                ·
                  refine ⟨1890846639243560966798245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40338061637195967291695893 1890846639243560966798245)
                  ·
                    refine ⟨354533744858167681274671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1890846639243560966798245 354533744858167681274671)
                    ·
                      rfl

theorem cell23_2071356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_2071356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071356 prefixEnd_2071356 := by exact prefixLift 2071356
  have htrace : WordTrace (prefixWord ++ tailWord_2071356) baseStart_2071356 baseEnd_2071356 := by
    simpa [prefixWord, tailWord_2071356, baseEnd_2071356] using wordTrace_append hprefix tailTrace_2071356
  have hstable : (prefixWord ++ tailWord_2071356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071356).length < 2 ^ (prefixWord ++ tailWord_2071356).sum := by decide
  have hdescent : baseEnd_2071356 < baseStart_2071356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071376 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_2071376 : Nat := 118140960795 + 2071376 * 2 ^ 59
def prefixEnd_2071376 : Nat := 4983230072969 + 3 ^ 40 * 2071376 * 2
def baseEnd_2071376 : Nat := 1063611504187592965573921

theorem tailTrace_2071376 : CollatzResearch.WordTrace tailWord_2071376 prefixEnd_2071376 1063611504187592965573921 := by
  unfold tailWord_2071376
  simp only [CollatzResearch.WordTrace]
  refine ⟨37774644671882994850704991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50366192895843993134273321 37774644671882994850704991)
  ·
    refine ⟨56661967007824492276057487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37774644671882994850704991 56661967007824492276057487)
    ·
      refine ⟨84992950511736738414086231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56661967007824492276057487 84992950511736738414086231)
      ·
        refine ⟨127489425767605107621129347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84992950511736738414086231 127489425767605107621129347)
        ·
          refine ⟨191234138651407661431694021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127489425767605107621129347 191234138651407661431694021)
          ·
            refine ⟨35856400997138936518442629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191234138651407661431694021 35856400997138936518442629)
            ·
              refine ⟨6723075186963550597207993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35856400997138936518442629 6723075186963550597207993)
              ·
                refine ⟨5042306390222662947905995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6723075186963550597207993 5042306390222662947905995)
                ·
                  refine ⟨7563459585333994421858993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042306390222662947905995 7563459585333994421858993)
                  ·
                    refine ⟨5672594689000495816394245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7563459585333994421858993 5672594689000495816394245)
                    ·
                      refine ⟨1063611504187592965573921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5672594689000495816394245 1063611504187592965573921)
                      ·
                        rfl

theorem cell23_2071376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_2071376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071376 prefixEnd_2071376 := by exact prefixLift 2071376
  have htrace : WordTrace (prefixWord ++ tailWord_2071376) baseStart_2071376 baseEnd_2071376 := by
    simpa [prefixWord, tailWord_2071376, baseEnd_2071376] using wordTrace_append hprefix tailTrace_2071376
  have hstable : (prefixWord ++ tailWord_2071376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071376).length < 2 ^ (prefixWord ++ tailWord_2071376).sum := by decide
  have hdescent : baseEnd_2071376 < baseStart_2071376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071377 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 1, 5]
def baseStart_2071377 : Nat := 118140960795 + 2071377 * 2 ^ 59
def prefixEnd_2071377 : Nat := 4983230072969 + 3 ^ 40 * 2071377 * 2
def baseEnd_2071377 : Nat := 354537339222749153887139

theorem tailTrace_2071377 : CollatzResearch.WordTrace tailWord_2071377 prefixEnd_2071377 354537339222749153887139 := by
  unfold tailWord_2071377
  simp only [CollatzResearch.WordTrace]
  refine ⟨75549325816762366872196385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50366217211174911248130923 75549325816762366872196385)
  ·
    refine ⟨56661994362571775154147289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75549325816762366872196385 56661994362571775154147289)
    ·
      refine ⟨42496495771928831365610467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56661994362571775154147289 42496495771928831365610467)
      ·
        refine ⟨63744743657893247048415701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42496495771928831365610467 63744743657893247048415701)
        ·
          refine ⟨1494017429481872977697243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 63744743657893247048415701 1494017429481872977697243)
          ·
            refine ⟨2241026144222809466545865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494017429481872977697243 2241026144222809466545865)
            ·
              refine ⟨1680769608167107099909399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241026144222809466545865 1680769608167107099909399)
              ·
                refine ⟨2521154412250660649864099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680769608167107099909399 2521154412250660649864099)
                ·
                  refine ⟨3781731618375990974796149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521154412250660649864099 3781731618375990974796149)
                  ·
                    refine ⟨354537339222749153887139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3781731618375990974796149 354537339222749153887139)
                    ·
                      rfl

theorem cell23_2071377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_2071377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071377 prefixEnd_2071377 := by exact prefixLift 2071377
  have htrace : WordTrace (prefixWord ++ tailWord_2071377) baseStart_2071377 baseEnd_2071377 := by
    simpa [prefixWord, tailWord_2071377, baseEnd_2071377] using wordTrace_append hprefix tailTrace_2071377
  have hstable : (prefixWord ++ tailWord_2071377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071377).length < 2 ^ (prefixWord ++ tailWord_2071377).sum := by decide
  have hdescent : baseEnd_2071377 < baseStart_2071377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071380 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2071380 : Nat := 118140960795 + 2071380 * 2 ^ 59
def prefixEnd_2071380 : Nat := 4983230072969 + 3 ^ 40 * 2071380 * 2
def baseEnd_2071380 : Nat := 1063613558110210949923903

theorem tailTrace_2071380 : CollatzResearch.WordTrace tailWord_2071380 prefixEnd_2071380 1063613558110210949923903 := by
  unfold tailWord_2071380
  simp only [CollatzResearch.WordTrace]
  refine ⟨37774717617875749192277797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50366290157167665589703729 37774717617875749192277797)
  ·
    refine ⟨7082759553351702973552087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37774717617875749192277797 7082759553351702973552087)
    ·
      refine ⟨10624139330027554460328131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7082759553351702973552087 10624139330027554460328131)
      ·
        refine ⟨15936208995041331690492197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10624139330027554460328131 15936208995041331690492197)
        ·
          refine ⟨2988039186570249691967287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15936208995041331690492197 2988039186570249691967287)
          ·
            refine ⟨4482058779855374537950931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988039186570249691967287 4482058779855374537950931)
            ·
              refine ⟨6723088169783061806926397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4482058779855374537950931 6723088169783061806926397)
              ·
                refine ⟨2521158063668648177597399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6723088169783061806926397 2521158063668648177597399)
                ·
                  refine ⟨3781737095502972266396099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2521158063668648177597399 3781737095502972266396099)
                  ·
                    refine ⟨5672605643254458399594149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3781737095502972266396099 5672605643254458399594149)
                    ·
                      refine ⟨1063613558110210949923903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5672605643254458399594149 1063613558110210949923903)
                      ·
                        rfl

theorem cell23_2071380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2071380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071380 prefixEnd_2071380 := by exact prefixLift 2071380
  have htrace : WordTrace (prefixWord ++ tailWord_2071380) baseStart_2071380 baseEnd_2071380 := by
    simpa [prefixWord, tailWord_2071380, baseEnd_2071380] using wordTrace_append hprefix tailTrace_2071380
  have hstable : (prefixWord ++ tailWord_2071380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071380).length < 2 ^ (prefixWord ++ tailWord_2071380).sum := by decide
  have hdescent : baseEnd_2071380 < baseStart_2071380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071397 : List Nat := [1, 3, 1, 3, 1, 1, 4, 4, 1, 2, 2]
def baseStart_2071397 : Nat := 118140960795 + 2071397 * 2 ^ 59
def prefixEnd_2071397 : Nat := 4983230072969 + 3 ^ 40 * 2071397 * 2
def baseEnd_2071397 : Nat := 1063622287281337383411325

theorem tailTrace_2071397 : CollatzResearch.WordTrace tailWord_2071397 prefixEnd_2071397 1063622287281337383411325 := by
  unfold tailWord_2071397
  simp only [CollatzResearch.WordTrace]
  refine ⟨75550055276689910287924445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50366703517793273525282963 75550055276689910287924445)
  ·
    refine ⟨28331270728758716357971667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75550055276689910287924445 28331270728758716357971667)
    ·
      refine ⟨42496906093138074536957501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28331270728758716357971667 42496906093138074536957501)
      ·
        refine ⟨15936339784926777951359063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42496906093138074536957501 15936339784926777951359063)
        ·
          refine ⟨23904509677390166927038595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15936339784926777951359063 23904509677390166927038595)
          ·
            refine ⟨35856764516085250390557893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23904509677390166927038595 35856764516085250390557893)
            ·
              refine ⟨6723143346765984448229605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35856764516085250390557893 6723143346765984448229605)
              ·
                refine ⟨1260589377518622084043051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6723143346765984448229605 1260589377518622084043051)
                ·
                  refine ⟨1890884066277933126064577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260589377518622084043051 1890884066277933126064577)
                  ·
                    refine ⟨1418163049708449844548433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1890884066277933126064577 1418163049708449844548433)
                    ·
                      refine ⟨1063622287281337383411325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418163049708449844548433 1063622287281337383411325)
                      ·
                        rfl

theorem cell23_2071397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_2071397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071397 prefixEnd_2071397 := by exact prefixLift 2071397
  have htrace : WordTrace (prefixWord ++ tailWord_2071397) baseStart_2071397 baseEnd_2071397 := by
    simpa [prefixWord, tailWord_2071397, baseEnd_2071397] using wordTrace_append hprefix tailTrace_2071397
  have hstable : (prefixWord ++ tailWord_2071397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071397).length < 2 ^ (prefixWord ++ tailWord_2071397).sum := by decide
  have hdescent : baseEnd_2071397 < baseStart_2071397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071423 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 3, 3, 2]
def baseStart_2071423 : Nat := 118140960795 + 2071423 * 2 ^ 59
def prefixEnd_2071423 : Nat := 4983230072969 + 3 ^ 40 * 2071423 * 2
def baseEnd_2071423 : Nat := 1063635637778354281686205

theorem tailTrace_2071423 : CollatzResearch.WordTrace tailWord_2071423 prefixEnd_2071423 1063635637778354281686205 := by
  unfold tailWord_2071423
  simp only [CollatzResearch.WordTrace]
  refine ⟨75551003574595716728370923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50367335716397144485580615 75551003574595716728370923)
  ·
    refine ⟨113326505361893575092556385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75551003574595716728370923 113326505361893575092556385)
    ·
      refine ⟨84994879021420181319417289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113326505361893575092556385 84994879021420181319417289)
      ·
        refine ⟨63746159266065135989562967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84994879021420181319417289 63746159266065135989562967)
        ·
          refine ⟨95619238899097703984344451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63746159266065135989562967 95619238899097703984344451)
          ·
            refine ⟨143428858348646555976516677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95619238899097703984344451 143428858348646555976516677)
            ·
              refine ⟨26892910940371229245596877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143428858348646555976516677 26892910940371229245596877)
              ·
                refine ⟨10084841602639210967098829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26892910940371229245596877 10084841602639210967098829)
                ·
                  refine ⟨3781815600989704112662061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10084841602639210967098829 3781815600989704112662061)
                  ·
                    refine ⟨1418180850371139042248273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3781815600989704112662061 1418180850371139042248273)
                    ·
                      refine ⟨1063635637778354281686205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418180850371139042248273 1063635637778354281686205)
                      ·
                        rfl

theorem cell23_2071423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_2071423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071423 prefixEnd_2071423 := by exact prefixLift 2071423
  have htrace : WordTrace (prefixWord ++ tailWord_2071423) baseStart_2071423 baseEnd_2071423 := by
    simpa [prefixWord, tailWord_2071423, baseEnd_2071423] using wordTrace_append hprefix tailTrace_2071423
  have hstable : (prefixWord ++ tailWord_2071423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071423).length < 2 ^ (prefixWord ++ tailWord_2071423).sum := by decide
  have hdescent : baseEnd_2071423 < baseStart_2071423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071560 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_2071560 : Nat := 118140960795 + 2071560 * 2 ^ 59
def prefixEnd_2071560 : Nat := 4983230072969 + 3 ^ 40 * 2071560 * 2
def baseEnd_2071560 : Nat := 1063705984628020245673075

theorem tailTrace_2071560 : CollatzResearch.WordTrace tailWord_2071560 prefixEnd_2071560 1063705984628020245673075 := by
  unfold tailWord_2071560
  simp only [CollatzResearch.WordTrace]
  refine ⟨37778000187549694563054067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50370666916732926084072089 37778000187549694563054067)
  ·
    refine ⟨56667000281324541844581101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37778000187549694563054067 56667000281324541844581101)
    ·
      refine ⟨21250125105496703191717913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56667000281324541844581101 21250125105496703191717913)
      ·
        refine ⟨15937593829122527393788435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21250125105496703191717913 15937593829122527393788435)
        ·
          refine ⟨23906390743683791090682653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15937593829122527393788435 23906390743683791090682653)
          ·
            refine ⟨8964896528881421659005995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23906390743683791090682653 8964896528881421659005995)
            ·
              refine ⟨13447344793322132488508993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8964896528881421659005995 13447344793322132488508993)
              ·
                refine ⟨10085508594991599366381745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13447344793322132488508993 10085508594991599366381745)
                ·
                  refine ⟨7564131446243699524786309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10085508594991599366381745 7564131446243699524786309)
                  ·
                    refine ⟨1418274646170693660897433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564131446243699524786309 1418274646170693660897433)
                    ·
                      refine ⟨1063705984628020245673075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418274646170693660897433 1063705984628020245673075)
                      ·
                        rfl

theorem cell23_2071560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_2071560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071560 prefixEnd_2071560 := by exact prefixLift 2071560
  have htrace : WordTrace (prefixWord ++ tailWord_2071560) baseStart_2071560 baseEnd_2071560 := by
    simpa [prefixWord, tailWord_2071560, baseEnd_2071560] using wordTrace_append hprefix tailTrace_2071560
  have hstable : (prefixWord ++ tailWord_2071560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071560).length < 2 ^ (prefixWord ++ tailWord_2071560).sum := by decide
  have hdescent : baseEnd_2071560 < baseStart_2071560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071610 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_2071610 : Nat := 118140960795 + 2071610 * 2 ^ 59
def prefixEnd_2071610 : Nat := 4983230072969 + 3 ^ 40 * 2071610 * 2
def baseEnd_2071610 : Nat := 1063731658660745050047845

theorem tailTrace_2071610 : CollatzResearch.WordTrace tailWord_2071610 prefixEnd_2071610 1063731658660745050047845 := by
  unfold tailWord_2071610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18889456006229561916357071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50371882683278831776952189 18889456006229561916357071)
  ·
    refine ⟨28334184009344342874535607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18889456006229561916357071 28334184009344342874535607)
    ·
      refine ⟨42501276014016514311803411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28334184009344342874535607 42501276014016514311803411)
      ·
        refine ⟨63751914021024771467705117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42501276014016514311803411 63751914021024771467705117)
        ·
          refine ⟨23906967757884289300389419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63751914021024771467705117 23906967757884289300389419)
          ·
            refine ⟨35860451636826433950584129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23906967757884289300389419 35860451636826433950584129)
            ·
              refine ⟨26895338727619825462938097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35860451636826433950584129 26895338727619825462938097)
              ·
                refine ⟨20171504045714869097203573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26895338727619825462938097 20171504045714869097203573)
                ·
                  refine ⟨1891078504285768977862835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20171504045714869097203573 1891078504285768977862835)
                  ·
                    refine ⟨2836617756428653466794253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1891078504285768977862835 2836617756428653466794253)
                    ·
                      refine ⟨1063731658660745050047845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2836617756428653466794253 1063731658660745050047845)
                      ·
                        rfl

theorem cell23_2071610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_2071610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071610 prefixEnd_2071610 := by exact prefixLift 2071610
  have htrace : WordTrace (prefixWord ++ tailWord_2071610) baseStart_2071610 baseEnd_2071610 := by
    simpa [prefixWord, tailWord_2071610, baseEnd_2071610] using wordTrace_append hprefix tailTrace_2071610
  have hstable : (prefixWord ++ tailWord_2071610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071610).length < 2 ^ (prefixWord ++ tailWord_2071610).sum := by decide
  have hdescent : baseEnd_2071610 < baseStart_2071610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071673 : List Nat := [1, 2, 1, 3, 5, 11]
def baseStart_2071673 : Nat := 118140960795 + 2071673 * 2 ^ 59
def prefixEnd_2071673 : Nat := 4983230072969 + 3 ^ 40 * 2071673 * 2
def baseEnd_2071673 : Nat := 4377629662312667915885

theorem tailTrace_2071673 : CollatzResearch.WordTrace tailWord_2071673 prefixEnd_2071673 4377629662312667915885 := by
  unfold tailWord_2071673
  simp only [CollatzResearch.WordTrace]
  refine ⟨75560121823690009424971673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50373414549126672949981115 75560121823690009424971673)
  ·
    refine ⟨56670091367767507068728755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75560121823690009424971673 56670091367767507068728755)
    ·
      refine ⟨85005137051651260603093133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56670091367767507068728755 85005137051651260603093133)
      ·
        refine ⟨31876926394369222726159925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85005137051651260603093133 31876926394369222726159925)
        ·
          refine ⟨2988461849472114630577493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31876926394369222726159925 2988461849472114630577493)
          ·
            refine ⟨4377629662312667915885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2988461849472114630577493 4377629662312667915885)
            ·
              rfl

theorem cell23_2071673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 11].length) (baseStart_2071673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071673 prefixEnd_2071673 := by exact prefixLift 2071673
  have htrace : WordTrace (prefixWord ++ tailWord_2071673) baseStart_2071673 baseEnd_2071673 := by
    simpa [prefixWord, tailWord_2071673, baseEnd_2071673] using wordTrace_append hprefix tailTrace_2071673
  have hstable : (prefixWord ++ tailWord_2071673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071673).length < 2 ^ (prefixWord ++ tailWord_2071673).sum := by decide
  have hdescent : baseEnd_2071673 < baseStart_2071673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071677 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_2071677 : Nat := 118140960795 + 2071677 * 2 ^ 59
def prefixEnd_2071677 : Nat := 4983230072969 + 3 ^ 40 * 2071677 * 2
def baseEnd_2071677 : Nat := 354588687288198762636679

theorem tailTrace_2071677 : CollatzResearch.WordTrace tailWord_2071677 prefixEnd_2071677 354588687288198762636679 := by
  unfold tailWord_2071677
  simp only [CollatzResearch.WordTrace]
  refine ⟨75560267715675518108117285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50373511810450345405411523 75560267715675518108117285)
  ·
    refine ⟨14167550196689159645271991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75560267715675518108117285 14167550196689159645271991)
    ·
      refine ⟨21251325295033739467907987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14167550196689159645271991 21251325295033739467907987)
      ·
        refine ⟨31876987942550609201861981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21251325295033739467907987 31876987942550609201861981)
        ·
          refine ⟨11953870478456478450698243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31876987942550609201861981 11953870478456478450698243)
          ·
            refine ⟨17930805717684717676047365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11953870478456478450698243 17930805717684717676047365)
            ·
              refine ⟨3362026072065884564258881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17930805717684717676047365 3362026072065884564258881)
              ·
                refine ⟨2521519554049413423194161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3362026072065884564258881 2521519554049413423194161)
                ·
                  refine ⟨1891139665537060067395621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2521519554049413423194161 1891139665537060067395621)
                  ·
                    refine ⟨354588687288198762636679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1891139665537060067395621 354588687288198762636679)
                    ·
                      rfl

theorem cell23_2071677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_2071677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071677 prefixEnd_2071677 := by exact prefixLift 2071677
  have htrace : WordTrace (prefixWord ++ tailWord_2071677) baseStart_2071677 baseEnd_2071677 := by
    simpa [prefixWord, tailWord_2071677, baseEnd_2071677] using wordTrace_append hprefix tailTrace_2071677
  have hstable : (prefixWord ++ tailWord_2071677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071677).length < 2 ^ (prefixWord ++ tailWord_2071677).sum := by decide
  have hdescent : baseEnd_2071677 < baseStart_2071677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071837 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2071837 : Nat := 118140960795 + 2071837 * 2 ^ 59
def prefixEnd_2071837 : Nat := 4983230072969 + 3 ^ 40 * 2071837 * 2
def baseEnd_2071837 : Nat := 1063848218769315661909301

theorem tailTrace_2071837 : CollatzResearch.WordTrace tailWord_2071837 prefixEnd_2071837 1063848218769315661909301 := by
  unfold tailWord_2071837
  simp only [CollatzResearch.WordTrace]
  refine ⟨75566103395095865433941765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50377402263397243622627843 75566103395095865433941765)
  ·
    refine ⟨14168644386580474768864081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75566103395095865433941765 14168644386580474768864081)
    ·
      refine ⟨10626483289935356076648061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14168644386580474768864081 10626483289935356076648061)
      ·
        refine ⟨3984931233725758528743023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10626483289935356076648061 3984931233725758528743023)
        ·
          refine ⟨5977396850588637793114535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984931233725758528743023 5977396850588637793114535)
          ·
            refine ⟨8966095275882956689671803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977396850588637793114535 8966095275882956689671803)
            ·
              refine ⟨13449142913824435034507705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966095275882956689671803 13449142913824435034507705)
              ·
                refine ⟨10086857185368326275880779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13449142913824435034507705 10086857185368326275880779)
                ·
                  refine ⟨15130285778052489413821169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10086857185368326275880779 15130285778052489413821169)
                  ·
                    refine ⟨11347714333539367060365877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15130285778052489413821169 11347714333539367060365877)
                    ·
                      refine ⟨1063848218769315661909301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11347714333539367060365877 1063848218769315661909301)
                      ·
                        rfl

theorem cell23_2071837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2071837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071837 prefixEnd_2071837 := by exact prefixLift 2071837
  have htrace : WordTrace (prefixWord ++ tailWord_2071837) baseStart_2071837 baseEnd_2071837 := by
    simpa [prefixWord, tailWord_2071837, baseEnd_2071837] using wordTrace_append hprefix tailTrace_2071837
  have hstable : (prefixWord ++ tailWord_2071837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071837).length < 2 ^ (prefixWord ++ tailWord_2071837).sum := by decide
  have hdescent : baseEnd_2071837 < baseStart_2071837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071884 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2071884 : Nat := 118140960795 + 2071884 * 2 ^ 59
def prefixEnd_2071884 : Nat := 4983230072969 + 3 ^ 40 * 2071884 * 2
def baseEnd_2071884 : Nat := 1063872352360076978021585

theorem tailTrace_2071884 : CollatzResearch.WordTrace tailWord_2071884 prefixEnd_2071884 1063872352360076978021585 := by
  unfold tailWord_2071884
  simp only [CollatzResearch.WordTrace]
  refine ⟨37783908812962796230451353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50378545083950394973935137 37783908812962796230451353)
  ·
    refine ⟨28337931609722097172838515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37783908812962796230451353 28337931609722097172838515)
    ·
      refine ⟨42506897414583145759257773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28337931609722097172838515 42506897414583145759257773)
      ·
        refine ⟨15940086530468679659721665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42506897414583145759257773 15940086530468679659721665)
        ·
          refine ⟨11955064897851509744791249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15940086530468679659721665 11955064897851509744791249)
          ·
            refine ⟨8966298673388632308593437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11955064897851509744791249 8966298673388632308593437)
            ·
              refine ⟨3362362002520737115722539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8966298673388632308593437 3362362002520737115722539)
              ·
                refine ⟨5043543003781105673583809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362362002520737115722539 5043543003781105673583809)
                ·
                  refine ⟨3782657252835829255187857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5043543003781105673583809 3782657252835829255187857)
                  ·
                    refine ⟨2836992939626871941390893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3782657252835829255187857 2836992939626871941390893)
                    ·
                      refine ⟨1063872352360076978021585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2836992939626871941390893 1063872352360076978021585)
                      ·
                        rfl

theorem cell23_2071884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2071884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071884 prefixEnd_2071884 := by exact prefixLift 2071884
  have htrace : WordTrace (prefixWord ++ tailWord_2071884) baseStart_2071884 baseEnd_2071884 := by
    simpa [prefixWord, tailWord_2071884, baseEnd_2071884] using wordTrace_append hprefix tailTrace_2071884
  have hstable : (prefixWord ++ tailWord_2071884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071884).length < 2 ^ (prefixWord ++ tailWord_2071884).sum := by decide
  have hdescent : baseEnd_2071884 < baseStart_2071884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071904 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 6]
def baseStart_2071904 : Nat := 118140960795 + 2071904 * 2 ^ 59
def prefixEnd_2071904 : Nat := 4983230072969 + 3 ^ 40 * 2071904 * 2
def baseEnd_2071904 : Nat := 118209180219240766641277

theorem tailTrace_2071904 : CollatzResearch.WordTrace tailWord_2071904 prefixEnd_2071904 118209180219240766641277 := by
  unfold tailWord_2071904
  simp only [CollatzResearch.WordTrace]
  refine ⟨37784273542926567938315383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50379031390568757251087177 37784273542926567938315383)
  ·
    refine ⟨56676410314389851907473075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37784273542926567938315383 56676410314389851907473075)
    ·
      refine ⟨85014615471584777861209613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56676410314389851907473075 85014615471584777861209613)
      ·
        refine ⟨31880480801844291697953605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85014615471584777861209613 31880480801844291697953605)
        ·
          refine ⟨5977590150345804693366301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31880480801844291697953605 5977590150345804693366301)
          ·
            refine ⟨2241596306379676760012363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5977590150345804693366301 2241596306379676760012363)
            ·
              refine ⟨3362394459569515140018545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241596306379676760012363 3362394459569515140018545)
              ·
                refine ⟨2521795844677136355013909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3362394459569515140018545 2521795844677136355013909)
                ·
                  refine ⟨118209180219240766641277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2521795844677136355013909 118209180219240766641277)
                  ·
                    rfl

theorem cell23_2071904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 6].length) (baseStart_2071904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071904 prefixEnd_2071904 := by exact prefixLift 2071904
  have htrace : WordTrace (prefixWord ++ tailWord_2071904) baseStart_2071904 baseEnd_2071904 := by
    simpa [prefixWord, tailWord_2071904, baseEnd_2071904] using wordTrace_append hprefix tailTrace_2071904
  have hstable : (prefixWord ++ tailWord_2071904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071904).length < 2 ^ (prefixWord ++ tailWord_2071904).sum := by decide
  have hdescent : baseEnd_2071904 < baseStart_2071904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071947 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 6, 4]
def baseStart_2071947 : Nat := 118140960795 + 2071947 * 2 ^ 59
def prefixEnd_2071947 : Nat := 4983230072969 + 3 ^ 40 * 2071947 * 2
def baseEnd_2071947 : Nat := 354634900547103410511265

theorem tailTrace_2071947 : CollatzResearch.WordTrace tailWord_2071947 prefixEnd_2071947 354634900547103410511265 := by
  unfold tailWord_2071947
  simp only [CollatzResearch.WordTrace]
  refine ⟨75570115424697354220446095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50380076949798236146964063 75570115424697354220446095)
  ·
    refine ⟨113355173137046031330669143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75570115424697354220446095 113355173137046031330669143)
    ·
      refine ⟨170032759705569046996003715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113355173137046031330669143 170032759705569046996003715)
      ·
        refine ⟨255049139558353570494005573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170032759705569046996003715 255049139558353570494005573)
        ·
          refine ⟨47821713667191294467626045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255049139558353570494005573 47821713667191294467626045)
          ·
            refine ⟨17933142625196735425359767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47821713667191294467626045 17933142625196735425359767)
            ·
              refine ⟨26899713937795103138039651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17933142625196735425359767 26899713937795103138039651)
              ·
                refine ⟨40349570906692654707059477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26899713937795103138039651 40349570906692654707059477)
                ·
                  refine ⟨1891386136251218189393413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40349570906692654707059477 1891386136251218189393413)
                  ·
                    refine ⟨354634900547103410511265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1891386136251218189393413 354634900547103410511265)
                    ·
                      rfl

theorem cell23_2071947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 4].length) (baseStart_2071947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071947 prefixEnd_2071947 := by exact prefixLift 2071947
  have htrace : WordTrace (prefixWord ++ tailWord_2071947) baseStart_2071947 baseEnd_2071947 := by
    simpa [prefixWord, tailWord_2071947, baseEnd_2071947] using wordTrace_append hprefix tailTrace_2071947
  have hstable : (prefixWord ++ tailWord_2071947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071947).length < 2 ^ (prefixWord ++ tailWord_2071947).sum := by decide
  have hdescent : baseEnd_2071947 < baseStart_2071947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071957 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_2071957 : Nat := 118140960795 + 2071957 * 2 ^ 59
def prefixEnd_2071957 : Nat := 4983230072969 + 3 ^ 40 * 2071957 * 2
def baseEnd_2071957 : Nat := 1063909836447855192408749

theorem tailTrace_2071957 : CollatzResearch.WordTrace tailWord_2071957 prefixEnd_2071957 1063909836447855192408749 := by
  unfold tailWord_2071957
  simp only [CollatzResearch.WordTrace]
  refine ⟨75570480154661125928310125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50380320103107417285540083 75570480154661125928310125)
  ·
    refine ⟨28338930057997922223116297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75570480154661125928310125 28338930057997922223116297)
    ·
      refine ⟨21254197543498441667337223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28338930057997922223116297 21254197543498441667337223)
      ·
        refine ⟨31881296315247662501005835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21254197543498441667337223 31881296315247662501005835)
        ·
          refine ⟨47821944472871493751508753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31881296315247662501005835 47821944472871493751508753)
          ·
            refine ⟨35866458354653620313631565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47821944472871493751508753 35866458354653620313631565)
            ·
              refine ⟨13449921882995107617611837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35866458354653620313631565 13449921882995107617611837)
              ·
                refine ⟨5043720706123165356604439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13449921882995107617611837 5043720706123165356604439)
                ·
                  refine ⟨7565581059184748034906659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043720706123165356604439 7565581059184748034906659)
                  ·
                    refine ⟨11348371588777122052359989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7565581059184748034906659 11348371588777122052359989)
                    ·
                      refine ⟨1063909836447855192408749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11348371588777122052359989 1063909836447855192408749)
                      ·
                        rfl

theorem cell23_2071957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_2071957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071957 prefixEnd_2071957 := by exact prefixLift 2071957
  have htrace : WordTrace (prefixWord ++ tailWord_2071957) baseStart_2071957 baseEnd_2071957 := by
    simpa [prefixWord, tailWord_2071957, baseEnd_2071957] using wordTrace_append hprefix tailTrace_2071957
  have hstable : (prefixWord ++ tailWord_2071957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071957).length < 2 ^ (prefixWord ++ tailWord_2071957).sum := by decide
  have hdescent : baseEnd_2071957 < baseStart_2071957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071965 : List Nat := [1, 4, 2, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_2071965 : Nat := 118140960795 + 2071965 * 2 ^ 59
def prefixEnd_2071965 : Nat := 4983230072969 + 3 ^ 40 * 2071965 * 2
def baseEnd_2071965 : Nat := 1063913944293091161108713

theorem tailTrace_2071965 : CollatzResearch.WordTrace tailWord_2071965 prefixEnd_2071965 1063913944293091161108713 := by
  unfold tailWord_2071965
  simp only [CollatzResearch.WordTrace]
  refine ⟨75570771938632143294601349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50380514625754762196400899 75570771938632143294601349)
  ·
    refine ⟨14169519738493526867737753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75570771938632143294601349 14169519738493526867737753)
    ·
      refine ⟨10627139803870145150803315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14169519738493526867737753 10627139803870145150803315)
      ·
        refine ⟨15940709705805217726204973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627139803870145150803315 15940709705805217726204973)
        ·
          refine ⟨5977766139676956647326865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15940709705805217726204973 5977766139676956647326865)
          ·
            refine ⟨4483324604757717485495149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5977766139676956647326865 4483324604757717485495149)
            ·
              refine ⟨1681246726784144057060681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4483324604757717485495149 1681246726784144057060681)
              ·
                refine ⟨1260935045088108042795511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681246726784144057060681 1260935045088108042795511)
                ·
                  refine ⟨1891402567632162064193267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260935045088108042795511 1891402567632162064193267)
                  ·
                    refine ⟨2837103851448243096289901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1891402567632162064193267 2837103851448243096289901)
                    ·
                      refine ⟨1063913944293091161108713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2837103851448243096289901 1063913944293091161108713)
                      ·
                        rfl

theorem cell23_2071965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_2071965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071965 prefixEnd_2071965 := by exact prefixLift 2071965
  have htrace : WordTrace (prefixWord ++ tailWord_2071965) baseStart_2071965 baseEnd_2071965 := by
    simpa [prefixWord, tailWord_2071965, baseEnd_2071965] using wordTrace_append hprefix tailTrace_2071965
  have hstable : (prefixWord ++ tailWord_2071965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071965).length < 2 ^ (prefixWord ++ tailWord_2071965).sum := by decide
  have hdescent : baseEnd_2071965 < baseStart_2071965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071967 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2071967 : Nat := 118140960795 + 2071967 * 2 ^ 59
def prefixEnd_2071967 : Nat := 4983230072969 + 3 ^ 40 * 2071967 * 2
def baseEnd_2071967 : Nat := 1063914971254400153283703

theorem tailTrace_2071967 : CollatzResearch.WordTrace tailWord_2071967 prefixEnd_2071967 1063914971254400153283703 := by
  unfold tailWord_2071967
  simp only [CollatzResearch.WordTrace]
  refine ⟨75570844884624897636174155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50380563256416598424116103 75570844884624897636174155)
  ·
    refine ⟨113356267326937346454261233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75570844884624897636174155 113356267326937346454261233)
    ·
      refine ⟨85017200495203009840695925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113356267326937346454261233 85017200495203009840695925)
      ·
        refine ⟨7970362546425282172565243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85017200495203009840695925 7970362546425282172565243)
        ·
          refine ⟨11955543819637923258847865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970362546425282172565243 11955543819637923258847865)
          ·
            refine ⟨8966657864728442444135899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11955543819637923258847865 8966657864728442444135899)
            ·
              refine ⟨13449986797092663666203849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966657864728442444135899 13449986797092663666203849)
              ·
                refine ⟨10087490097819497749652887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13449986797092663666203849 10087490097819497749652887)
                ·
                  refine ⟨15131235146729246624479331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10087490097819497749652887 15131235146729246624479331)
                  ·
                    refine ⟨22696852720093869936718997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15131235146729246624479331 22696852720093869936718997)
                    ·
                      refine ⟨1063914971254400153283703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22696852720093869936718997 1063914971254400153283703)
                      ·
                        rfl

theorem cell23_2071967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2071967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071967 prefixEnd_2071967 := by exact prefixLift 2071967
  have htrace : WordTrace (prefixWord ++ tailWord_2071967) baseStart_2071967 baseEnd_2071967 := by
    simpa [prefixWord, tailWord_2071967, baseEnd_2071967] using wordTrace_append hprefix tailTrace_2071967
  have hstable : (prefixWord ++ tailWord_2071967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071967).length < 2 ^ (prefixWord ++ tailWord_2071967).sum := by decide
  have hdescent : baseEnd_2071967 < baseStart_2071967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2071987 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 3]
def baseStart_2071987 : Nat := 118140960795 + 2071987 * 2 ^ 59
def prefixEnd_2071987 : Nat := 4983230072969 + 3 ^ 40 * 2071987 * 2
def baseEnd_2071987 : Nat := 1063925240867490075033611

theorem tailTrace_2071987 : CollatzResearch.WordTrace tailWord_2071987 prefixEnd_2071987 1063925240867490075033611 := by
  unfold tailWord_2071987
  simp only [CollatzResearch.WordTrace]
  refine ⟨75571574344552441051902215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50381049563034960701268143 75571574344552441051902215)
  ·
    refine ⟨113357361516828661577853323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75571574344552441051902215 113357361516828661577853323)
    ·
      refine ⟨170036042275242992366779985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113357361516828661577853323 170036042275242992366779985)
      ·
        refine ⟨127527031706432244275084989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170036042275242992366779985 127527031706432244275084989)
        ·
          refine ⟨47822636889912091603156871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127527031706432244275084989 47822636889912091603156871)
          ·
            refine ⟨71733955334868137404735307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47822636889912091603156871 71733955334868137404735307)
            ·
              refine ⟨107600933002302206107102961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71733955334868137404735307 107600933002302206107102961)
              ·
                refine ⟨80700699751726654580327221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107600933002302206107102961 80700699751726654580327221)
                ·
                  refine ⟨7565690601724373866905677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80700699751726654580327221 7565690601724373866905677)
                  ·
                    refine ⟨2837133975646640200089629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7565690601724373866905677 2837133975646640200089629)
                    ·
                      refine ⟨1063925240867490075033611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2837133975646640200089629 1063925240867490075033611)
                      ·
                        rfl

theorem cell23_2071987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_2071987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2071987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2071987 prefixEnd_2071987 := by exact prefixLift 2071987
  have htrace : WordTrace (prefixWord ++ tailWord_2071987) baseStart_2071987 baseEnd_2071987 := by
    simpa [prefixWord, tailWord_2071987, baseEnd_2071987] using wordTrace_append hprefix tailTrace_2071987
  have hstable : (prefixWord ++ tailWord_2071987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2071987).length < 2 ^ (prefixWord ++ tailWord_2071987).sum := by decide
  have hdescent : baseEnd_2071987 < baseStart_2071987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2071987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072022 : List Nat := [5, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_2072022 : Nat := 118140960795 + 2072022 * 2 ^ 59
def prefixEnd_2072022 : Nat := 4983230072969 + 3 ^ 40 * 2072022 * 2
def baseEnd_2072022 : Nat := 1063943212690397438095951

theorem tailTrace_2072022 : CollatzResearch.WordTrace tailWord_2072022 prefixEnd_2072022 1063943212690397438095951 := by
  unfold tailWord_2072022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723303181214102626839145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50381900599617094686284213 4723303181214102626839145)
  ·
    refine ⟨3542477385910576970129359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4723303181214102626839145 3542477385910576970129359)
    ·
      refine ⟨5313716078865865455194039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3542477385910576970129359 5313716078865865455194039)
      ·
        refine ⟨7970574118298798182791059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5313716078865865455194039 7970574118298798182791059)
        ·
          refine ⟨11955861177448197274186589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970574118298798182791059 11955861177448197274186589)
          ·
            refine ⟨4483447941543073977819971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11955861177448197274186589 4483447941543073977819971)
            ·
              refine ⟨6725171912314610966729957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483447941543073977819971 6725171912314610966729957)
              ·
                refine ⟨1260969733558989556261867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6725171912314610966729957 1260969733558989556261867)
                ·
                  refine ⟨1891454600338484334392801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260969733558989556261867 1891454600338484334392801)
                  ·
                    refine ⟨1418590950253863250794601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1891454600338484334392801 1418590950253863250794601)
                    ·
                      refine ⟨1063943212690397438095951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418590950253863250794601 1063943212690397438095951)
                      ·
                        rfl

theorem cell23_2072022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_2072022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072022 prefixEnd_2072022 := by exact prefixLift 2072022
  have htrace : WordTrace (prefixWord ++ tailWord_2072022) baseStart_2072022 baseEnd_2072022 := by
    simpa [prefixWord, tailWord_2072022, baseEnd_2072022] using wordTrace_append hprefix tailTrace_2072022
  have hstable : (prefixWord ++ tailWord_2072022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072022).length < 2 ^ (prefixWord ++ tailWord_2072022).sum := by decide
  have hdescent : baseEnd_2072022 < baseStart_2072022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072047 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_2072047 : Nat := 118140960795 + 2072047 * 2 ^ 59
def prefixEnd_2072047 : Nat := 4983230072969 + 3 ^ 40 * 2072047 * 2
def baseEnd_2072047 : Nat := 1063956049706759840283335

theorem tailTrace_2072047 : CollatzResearch.WordTrace tailWord_2072047 prefixEnd_2072047 1063956049706759840283335 := by
  unfold tailWord_2072047
  simp only [CollatzResearch.WordTrace]
  refine ⟨75573762724335071299086395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50382508482890047532724263 75573762724335071299086395)
  ·
    refine ⟨113360644086502606948629593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75573762724335071299086395 113360644086502606948629593)
    ·
      refine ⟨85020483064876955211472195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113360644086502606948629593 85020483064876955211472195)
      ·
        refine ⟨127530724597315432817208293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85020483064876955211472195 127530724597315432817208293)
        ·
          refine ⟨23912010861996643653226555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127530724597315432817208293 23912010861996643653226555)
          ·
            refine ⟨35868016292994965479839833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23912010861996643653226555 35868016292994965479839833)
            ·
              refine ⟨26901012219746224109879875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35868016292994965479839833 26901012219746224109879875)
              ·
                refine ⟨40351518329619336164819813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26901012219746224109879875 40351518329619336164819813)
                ·
                  refine ⟨7565909686803625530903715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40351518329619336164819813 7565909686803625530903715)
                  ·
                    refine ⟨11348864530205438296355573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7565909686803625530903715 11348864530205438296355573)
                    ·
                      refine ⟨1063956049706759840283335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11348864530205438296355573 1063956049706759840283335)
                      ·
                        rfl

theorem cell23_2072047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_2072047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072047 prefixEnd_2072047 := by exact prefixLift 2072047
  have htrace : WordTrace (prefixWord ++ tailWord_2072047) baseStart_2072047 baseEnd_2072047 := by
    simpa [prefixWord, tailWord_2072047, baseEnd_2072047] using wordTrace_append hprefix tailTrace_2072047
  have hstable : (prefixWord ++ tailWord_2072047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072047).length < 2 ^ (prefixWord ++ tailWord_2072047).sum := by decide
  have hdescent : baseEnd_2072047 < baseStart_2072047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072057 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_2072057 : Nat := 118140960795 + 2072057 * 2 ^ 59
def prefixEnd_2072057 : Nat := 4983230072969 + 3 ^ 40 * 2072057 * 2
def baseEnd_2072057 : Nat := 1063961184513304801158289

theorem tailTrace_2072057 : CollatzResearch.WordTrace tailWord_2072057 prefixEnd_2072057 1063961184513304801158289 := by
  unfold tailWord_2072057
  simp only [CollatzResearch.WordTrace]
  refine ⟨75574127454298843006950425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50382751636199228671300283 75574127454298843006950425)
  ·
    refine ⟨56680595590724132255212819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75574127454298843006950425 56680595590724132255212819)
    ·
      refine ⟨85020893386086198382819229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56680595590724132255212819 85020893386086198382819229)
      ·
        refine ⟨31882835019782324393557211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85020893386086198382819229 31882835019782324393557211)
        ·
          refine ⟨47824252529673486590335817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31882835019782324393557211 47824252529673486590335817)
          ·
            refine ⟨35868189397255114942751863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47824252529673486590335817 35868189397255114942751863)
            ·
              refine ⟨53802284095882672414127795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35868189397255114942751863 53802284095882672414127795)
              ·
                refine ⟨80703426143824008621191693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53802284095882672414127795 80703426143824008621191693)
                ·
                  refine ⟨30263784803934003232946885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80703426143824008621191693 30263784803934003232946885)
                  ·
                    refine ⟨5674459650737625606177541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30263784803934003232946885 5674459650737625606177541)
                    ·
                      refine ⟨1063961184513304801158289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5674459650737625606177541 1063961184513304801158289)
                      ·
                        rfl

theorem cell23_2072057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_2072057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072057 prefixEnd_2072057 := by exact prefixLift 2072057
  have htrace : WordTrace (prefixWord ++ tailWord_2072057) baseStart_2072057 baseEnd_2072057 := by
    simpa [prefixWord, tailWord_2072057, baseEnd_2072057] using wordTrace_append hprefix tailTrace_2072057
  have hstable : (prefixWord ++ tailWord_2072057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072057).length < 2 ^ (prefixWord ++ tailWord_2072057).sum := by decide
  have hdescent : baseEnd_2072057 < baseStart_2072057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072061 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_2072061 : Nat := 118140960795 + 2072061 * 2 ^ 59
def prefixEnd_2072061 : Nat := 4983230072969 + 3 ^ 40 * 2072061 * 2
def baseEnd_2072061 : Nat := 1063963238435922785508271

theorem tailTrace_2072061 : CollatzResearch.WordTrace tailWord_2072061 prefixEnd_2072061 1063963238435922785508271 := by
  unfold tailWord_2072061
  simp only [CollatzResearch.WordTrace]
  refine ⟨75574273346284351690096037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50382848897522901126730691 75574273346284351690096037)
  ·
    refine ⟨14170176252428315941893007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75574273346284351690096037 14170176252428315941893007)
    ·
      refine ⟨21255264378642473912839511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14170176252428315941893007 21255264378642473912839511)
      ·
        refine ⟨31882896567963710869259267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21255264378642473912839511 31882896567963710869259267)
        ·
          refine ⟨47824344851945566303888901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31882896567963710869259267 47824344851945566303888901)
          ·
            refine ⟨8967064659739793681979169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47824344851945566303888901 8967064659739793681979169)
            ·
              refine ⟨6725298494804845261484377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8967064659739793681979169 6725298494804845261484377)
              ·
                refine ⟨5043973871103633946113283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6725298494804845261484377 5043973871103633946113283)
                ·
                  refine ⟨7565960806655450919169925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043973871103633946113283 7565960806655450919169925)
                  ·
                    refine ⟨1418617651247897047344361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7565960806655450919169925 1418617651247897047344361)
                    ·
                      refine ⟨1063963238435922785508271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418617651247897047344361 1063963238435922785508271)
                      ·
                        rfl

theorem cell23_2072061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_2072061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072061 prefixEnd_2072061 := by exact prefixLift 2072061
  have htrace : WordTrace (prefixWord ++ tailWord_2072061) baseStart_2072061 baseEnd_2072061 := by
    simpa [prefixWord, tailWord_2072061, baseEnd_2072061] using wordTrace_append hprefix tailTrace_2072061
  have hstable : (prefixWord ++ tailWord_2072061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072061).length < 2 ^ (prefixWord ++ tailWord_2072061).sum := by decide
  have hdescent : baseEnd_2072061 < baseStart_2072061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072074 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2072074 : Nat := 118140960795 + 2072074 * 2 ^ 59
def prefixEnd_2072074 : Nat := 4983230072969 + 3 ^ 40 * 2072074 * 2
def baseEnd_2072074 : Nat := 1063969913684431234645711

theorem tailTrace_2072074 : CollatzResearch.WordTrace tailWord_2072074 prefixEnd_2072074 1063969913684431234645711 := by
  unfold tailWord_2072074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18893686873809313727579819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50383164996824836606879517 18893686873809313727579819)
  ·
    refine ⟨28340530310713970591369729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18893686873809313727579819 28340530310713970591369729)
    ·
      refine ⟨21255397733035477943527297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28340530310713970591369729 21255397733035477943527297)
      ·
        refine ⟨15941548299776608457645473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21255397733035477943527297 15941548299776608457645473)
        ·
          refine ⟨11956161224832456343234105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15941548299776608457645473 11956161224832456343234105)
          ·
            refine ⟨8967120918624342257425579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11956161224832456343234105 8967120918624342257425579)
            ·
              refine ⟨13450681377936513386138369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8967120918624342257425579 13450681377936513386138369)
              ·
                refine ⟨10088011033452385039603777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13450681377936513386138369 10088011033452385039603777)
                ·
                  refine ⟨7566008275089288779702833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10088011033452385039603777 7566008275089288779702833)
                  ·
                    refine ⟨5674506206316966584777125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7566008275089288779702833 5674506206316966584777125)
                    ·
                      refine ⟨1063969913684431234645711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5674506206316966584777125 1063969913684431234645711)
                      ·
                        rfl

theorem cell23_2072074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2072074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072074 prefixEnd_2072074 := by exact prefixLift 2072074
  have htrace : WordTrace (prefixWord ++ tailWord_2072074) baseStart_2072074 baseEnd_2072074 := by
    simpa [prefixWord, tailWord_2072074, baseEnd_2072074] using wordTrace_append hprefix tailTrace_2072074
  have hstable : (prefixWord ++ tailWord_2072074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072074).length < 2 ^ (prefixWord ++ tailWord_2072074).sum := by decide
  have hdescent : baseEnd_2072074 < baseStart_2072074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072107 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 5]
def baseStart_2072107 : Nat := 118140960795 + 2072107 * 2 ^ 59
def prefixEnd_2072107 : Nat := 4983230072969 + 3 ^ 40 * 2072107 * 2
def baseEnd_2072107 : Nat := 1063986858546029605533059

theorem tailTrace_2072107 : CollatzResearch.WordTrace tailWord_2072107 prefixEnd_2072107 1063986858546029605533059 := by
  unfold tailWord_2072107
  simp only [CollatzResearch.WordTrace]
  refine ⟨75575951104117701546270575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50383967402745134364180383 75575951104117701546270575)
  ·
    refine ⟨113363926656176552319405863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75575951104117701546270575 113363926656176552319405863)
    ·
      refine ⟨170045889984264828479108795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113363926656176552319405863 170045889984264828479108795)
      ·
        refine ⟨255068834976397242718663193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170045889984264828479108795 255068834976397242718663193)
        ·
          refine ⟨191301626232297932038997395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255068834976397242718663193 191301626232297932038997395)
          ·
            refine ⟨286952439348446898058496093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191301626232297932038997395 286952439348446898058496093)
            ·
              refine ⟨107607164755667586771936035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286952439348446898058496093 107607164755667586771936035)
              ·
                refine ⟨161410747133501380157904053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107607164755667586771936035 161410747133501380157904053)
                ·
                  refine ⟨15132257543765754389803505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161410747133501380157904053 15132257543765754389803505)
                  ·
                    refine ⟨11349193157824315792352629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15132257543765754389803505 11349193157824315792352629)
                    ·
                      refine ⟨1063986858546029605533059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11349193157824315792352629 1063986858546029605533059)
                      ·
                        rfl

theorem cell23_2072107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 5].length) (baseStart_2072107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072107 prefixEnd_2072107 := by exact prefixLift 2072107
  have htrace : WordTrace (prefixWord ++ tailWord_2072107) baseStart_2072107 baseEnd_2072107 := by
    simpa [prefixWord, tailWord_2072107, baseEnd_2072107] using wordTrace_append hprefix tailTrace_2072107
  have hstable : (prefixWord ++ tailWord_2072107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072107).length < 2 ^ (prefixWord ++ tailWord_2072107).sum := by decide
  have hdescent : baseEnd_2072107 < baseStart_2072107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072114 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_2072114 : Nat := 118140960795 + 2072114 * 2 ^ 59
def prefixEnd_2072114 : Nat := 4983230072969 + 3 ^ 40 * 2072114 * 2
def baseEnd_2072114 : Nat := 354663484303537026048509

theorem tailTrace_2072114 : CollatzResearch.WordTrace tailWord_2072114 prefixEnd_2072114 354663484303537026048509 := by
  unfold tailWord_2072114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894051603773085435443849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50384137610061561161183597 18894051603773085435443849)
  ·
    refine ⟨14170538702829814076582887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18894051603773085435443849 14170538702829814076582887)
    ·
      refine ⟨21255808054244721114874331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14170538702829814076582887 21255808054244721114874331)
      ·
        refine ⟨31883712081367081672311497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21255808054244721114874331 31883712081367081672311497)
        ·
          refine ⟨23912784061025311254233623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31883712081367081672311497 23912784061025311254233623)
          ·
            refine ⟨35869176091537966881350435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23912784061025311254233623 35869176091537966881350435)
            ·
              refine ⟨53803764137306950322025653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35869176091537966881350435 53803764137306950322025653)
              ·
                refine ⟨5044102887872526592689905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53803764137306950322025653 5044102887872526592689905)
                ·
                  refine ⟨3783077165904394944517429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5044102887872526592689905 3783077165904394944517429)
                  ·
                    refine ⟨354663484303537026048509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3783077165904394944517429 354663484303537026048509)
                    ·
                      rfl

theorem cell23_2072114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_2072114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072114 prefixEnd_2072114 := by exact prefixLift 2072114
  have htrace : WordTrace (prefixWord ++ tailWord_2072114) baseStart_2072114 baseEnd_2072114 := by
    simpa [prefixWord, tailWord_2072114, baseEnd_2072114] using wordTrace_append hprefix tailTrace_2072114
  have hstable : (prefixWord ++ tailWord_2072114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072114).length < 2 ^ (prefixWord ++ tailWord_2072114).sum := by decide
  have hdescent : baseEnd_2072114 < baseStart_2072114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072154 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_2072154 : Nat := 118140960795 + 2072154 * 2 ^ 59
def prefixEnd_2072154 : Nat := 4983230072969 + 3 ^ 40 * 2072154 * 2
def baseEnd_2072154 : Nat := 1064010992136790921645343

theorem tailTrace_2072154 : CollatzResearch.WordTrace tailWord_2072154 prefixEnd_2072154 1064010992136790921645343 := by
  unfold tailWord_2072154
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894416333736857143307879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50385110223298285715487677 18894416333736857143307879)
  ·
    refine ⟨28341624500605285714961819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18894416333736857143307879 28341624500605285714961819)
    ·
      refine ⟨42512436750907928572442729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28341624500605285714961819 42512436750907928572442729)
      ·
        refine ⟨31884327563180946429332047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42512436750907928572442729 31884327563180946429332047)
        ·
          refine ⟨47826491344771419643998071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31884327563180946429332047 47826491344771419643998071)
          ·
            refine ⟨71739737017157129465997107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47826491344771419643998071 71739737017157129465997107)
            ·
              refine ⟨107609605525735694198995661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71739737017157129465997107 107609605525735694198995661)
              ·
                refine ⟨40353602072150885324623373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107609605525735694198995661 40353602072150885324623373)
                ·
                  refine ⟨15132600777056581996733765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40353602072150885324623373 15132600777056581996733765)
                  ·
                    refine ⟨2837362645698109124387581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15132600777056581996733765 2837362645698109124387581)
                    ·
                      refine ⟨1064010992136790921645343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2837362645698109124387581 1064010992136790921645343)
                      ·
                        rfl

theorem cell23_2072154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_2072154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072154 prefixEnd_2072154 := by exact prefixLift 2072154
  have htrace : WordTrace (prefixWord ++ tailWord_2072154) baseStart_2072154 baseEnd_2072154 := by
    simpa [prefixWord, tailWord_2072154, baseEnd_2072154] using wordTrace_append hprefix tailTrace_2072154
  have hstable : (prefixWord ++ tailWord_2072154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072154).length < 2 ^ (prefixWord ++ tailWord_2072154).sum := by decide
  have hdescent : baseEnd_2072154 < baseStart_2072154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072168 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2072168 : Nat := 118140960795 + 2072168 * 2 ^ 59
def prefixEnd_2072168 : Nat := 4983230072969 + 3 ^ 40 * 2072168 * 2
def baseEnd_2072168 : Nat := 1064018180865953866870279

theorem tailTrace_2072168 : CollatzResearch.WordTrace tailWord_2072168 prefixEnd_2072168 1064018180865953866870279 := by
  unfold tailWord_2072168
  simp only [CollatzResearch.WordTrace]
  refine ⟨37789087978448354482120579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50385450637931139309494105 37789087978448354482120579)
  ·
    refine ⟨56683631967672531723180869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37789087978448354482120579 56683631967672531723180869)
    ·
      refine ⟨10628180993938599698096413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56683631967672531723180869 10628180993938599698096413)
      ·
        refine ⟨3985567872726974886786155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10628180993938599698096413 3985567872726974886786155)
        ·
          refine ⟨5978351809090462330179233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985567872726974886786155 5978351809090462330179233)
          ·
            refine ⟨4483763856817846747634425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978351809090462330179233 4483763856817846747634425)
            ·
              refine ⟨3362822892613385060725819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4483763856817846747634425 3362822892613385060725819)
              ·
                refine ⟨5044234338920077591088729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3362822892613385060725819 5044234338920077591088729)
                ·
                  refine ⟨3783175754190058193316547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5044234338920077591088729 3783175754190058193316547)
                  ·
                    refine ⟨5674763631285087289974821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3783175754190058193316547 5674763631285087289974821)
                    ·
                      refine ⟨1064018180865953866870279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5674763631285087289974821 1064018180865953866870279)
                      ·
                        rfl

theorem cell23_2072168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2072168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072168 prefixEnd_2072168 := by exact prefixLift 2072168
  have htrace : WordTrace (prefixWord ++ tailWord_2072168) baseStart_2072168 baseEnd_2072168 := by
    simpa [prefixWord, tailWord_2072168, baseEnd_2072168] using wordTrace_append hprefix tailTrace_2072168
  have hstable : (prefixWord ++ tailWord_2072168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072168).length < 2 ^ (prefixWord ++ tailWord_2072168).sum := by decide
  have hdescent : baseEnd_2072168 < baseStart_2072168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072204 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_2072204 : Nat := 118140960795 + 2072204 * 2 ^ 59
def prefixEnd_2072204 : Nat := 4983230072969 + 3 ^ 40 * 2072204 * 2
def baseEnd_2072204 : Nat := 354678888723171908673371

theorem tailTrace_2072204 : CollatzResearch.WordTrace tailWord_2072204 prefixEnd_2072204 354678888723171908673371 := by
  unfold tailWord_2072204
  simp only [CollatzResearch.WordTrace]
  refine ⟨37789744492383143556275833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50386325989844191408367777 37789744492383143556275833)
  ·
    refine ⟨28342308369287357667206875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37789744492383143556275833 28342308369287357667206875)
    ·
      refine ⟨42513462553931036500810313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28342308369287357667206875 42513462553931036500810313)
      ·
        refine ⟨31885096915448277375607735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42513462553931036500810313 31885096915448277375607735)
        ·
          refine ⟨47827645373172416063411603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31885096915448277375607735 47827645373172416063411603)
          ·
            refine ⟨71741468059758624095117405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47827645373172416063411603 71741468059758624095117405)
            ·
              refine ⟨26903050522409484035669027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71741468059758624095117405 26903050522409484035669027)
              ·
                refine ⟨40354575783614226053503541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26903050522409484035669027 40354575783614226053503541)
                ·
                  refine ⟨3783241479713833692515957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40354575783614226053503541 3783241479713833692515957)
                  ·
                    refine ⟨354678888723171908673371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3783241479713833692515957 354678888723171908673371)
                    ·
                      rfl

theorem cell23_2072204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_2072204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072204 prefixEnd_2072204 := by exact prefixLift 2072204
  have htrace : WordTrace (prefixWord ++ tailWord_2072204) baseStart_2072204 baseEnd_2072204 := by
    simpa [prefixWord, tailWord_2072204, baseEnd_2072204] using wordTrace_append hprefix tailTrace_2072204
  have hstable : (prefixWord ++ tailWord_2072204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072204).length < 2 ^ (prefixWord ++ tailWord_2072204).sum := by decide
  have hdescent : baseEnd_2072204 < baseStart_2072204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072221 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2072221 : Nat := 118140960795 + 2072221 * 2 ^ 59
def prefixEnd_2072221 : Nat := 4983230072969 + 3 ^ 40 * 2072221 * 2
def baseEnd_2072221 : Nat := 354681798446880719835845

theorem tailTrace_2072221 : CollatzResearch.WordTrace tailWord_2072221 prefixEnd_2072221 354681798446880719835845 := by
  unfold tailWord_2072221
  simp only [CollatzResearch.WordTrace]
  refine ⟨75580109025704699015920517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50386739350469799343947011 75580109025704699015920517)
  ·
    refine ⟨14171270442319631065485097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75580109025704699015920517 14171270442319631065485097)
    ·
      refine ⟨10628452831739723299113823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14171270442319631065485097 10628452831739723299113823)
      ·
        refine ⟨15942679247609584948670735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10628452831739723299113823 15942679247609584948670735)
        ·
          refine ⟨23914018871414377423006103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15942679247609584948670735 23914018871414377423006103)
          ·
            refine ⟨35871028307121566134509155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23914018871414377423006103 35871028307121566134509155)
            ·
              refine ⟨53806542460682349201763733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35871028307121566134509155 53806542460682349201763733)
              ·
                refine ⟨2522181677844485118832675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53806542460682349201763733 2522181677844485118832675)
                ·
                  refine ⟨3783272516766727678249013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522181677844485118832675 3783272516766727678249013)
                  ·
                    refine ⟨354681798446880719835845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3783272516766727678249013 354681798446880719835845)
                    ·
                      rfl

theorem cell23_2072221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2072221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072221 prefixEnd_2072221 := by exact prefixLift 2072221
  have htrace : WordTrace (prefixWord ++ tailWord_2072221) baseStart_2072221 baseEnd_2072221 := by
    simpa [prefixWord, tailWord_2072221, baseEnd_2072221] using wordTrace_append hprefix tailTrace_2072221
  have hstable : (prefixWord ++ tailWord_2072221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072221).length < 2 ^ (prefixWord ++ tailWord_2072221).sum := by decide
  have hdescent : baseEnd_2072221 < baseStart_2072221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072228 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_2072228 : Nat := 118140960795 + 2072228 * 2 ^ 59
def prefixEnd_2072228 : Nat := 4983230072969 + 3 ^ 40 * 2072228 * 2
def baseEnd_2072228 : Nat := 1064048989705223632120003

theorem tailTrace_2072228 : CollatzResearch.WordTrace tailWord_2072228 prefixEnd_2072228 1064048989705223632120003 := by
  unfold tailWord_2072228
  simp only [CollatzResearch.WordTrace]
  refine ⟨37790182168339669605712669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50386909557786226140950225 37790182168339669605712669)
  ·
    refine ⟨14171318313127376102142251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37790182168339669605712669 14171318313127376102142251)
    ·
      refine ⟨21256977469691064153213377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14171318313127376102142251 21256977469691064153213377)
      ·
        refine ⟨15942733102268298114910033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21256977469691064153213377 15942733102268298114910033)
        ·
          refine ⟨11957049826701223586182525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15942733102268298114910033 11957049826701223586182525)
          ·
            refine ⟨4483893685012958844818447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11957049826701223586182525 4483893685012958844818447)
            ·
              refine ⟨6725840527519438267227671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483893685012958844818447 6725840527519438267227671)
              ·
                refine ⟨10088760791279157400841507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6725840527519438267227671 10088760791279157400841507)
                ·
                  refine ⟨15133141186918736101262261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10088760791279157400841507 15133141186918736101262261)
                  ·
                    refine ⟨1418731986273631509493337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15133141186918736101262261 1418731986273631509493337)
                    ·
                      refine ⟨1064048989705223632120003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418731986273631509493337 1064048989705223632120003)
                      ·
                        rfl

theorem cell23_2072228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_2072228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072228 prefixEnd_2072228 := by exact prefixLift 2072228
  have htrace : WordTrace (prefixWord ++ tailWord_2072228) baseStart_2072228 baseEnd_2072228 := by
    simpa [prefixWord, tailWord_2072228, baseEnd_2072228] using wordTrace_append hprefix tailTrace_2072228
  have hstable : (prefixWord ++ tailWord_2072228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072228).length < 2 ^ (prefixWord ++ tailWord_2072228).sum := by decide
  have hdescent : baseEnd_2072228 < baseStart_2072228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072262 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2072262 : Nat := 118140960795 + 2072262 * 2 ^ 59
def prefixEnd_2072262 : Nat := 4983230072969 + 3 ^ 40 * 2072262 * 2
def baseEnd_2072262 : Nat := 1064066448047476499094847

theorem tailTrace_2072262 : CollatzResearch.WordTrace tailWord_2072262 prefixEnd_2072262 1064066448047476499094847 := by
  unfold tailWord_2072262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361925138079880094317595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50387736279037442012108693 2361925138079880094317595)
  ·
    refine ⟨3542887707119820141476393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2361925138079880094317595 3542887707119820141476393)
    ·
      refine ⟨2657165780339865106107295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3542887707119820141476393 2657165780339865106107295)
      ·
        refine ⟨3985748670509797659160943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657165780339865106107295 3985748670509797659160943)
        ·
          refine ⟨5978623005764696488741415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985748670509797659160943 5978623005764696488741415)
          ·
            refine ⟨8967934508647044733112123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5978623005764696488741415 8967934508647044733112123)
            ·
              refine ⟨13451901762970567099668185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8967934508647044733112123 13451901762970567099668185)
              ·
                refine ⟨10088926322227925324751139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13451901762970567099668185 10088926322227925324751139)
                ·
                  refine ⟨15133389483341887987126709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10088926322227925324751139 15133389483341887987126709)
                  ·
                    refine ⟨1418755264063301998793129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15133389483341887987126709 1418755264063301998793129)
                    ·
                      refine ⟨1064066448047476499094847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418755264063301998793129 1064066448047476499094847)
                      ·
                        rfl

theorem cell23_2072262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2072262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072262 prefixEnd_2072262 := by exact prefixLift 2072262
  have htrace : WordTrace (prefixWord ++ tailWord_2072262) baseStart_2072262 baseEnd_2072262 := by
    simpa [prefixWord, tailWord_2072262, baseEnd_2072262] using wordTrace_append hprefix tailTrace_2072262
  have hstable : (prefixWord ++ tailWord_2072262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072262).length < 2 ^ (prefixWord ++ tailWord_2072262).sum := by decide
  have hdescent : baseEnd_2072262 < baseStart_2072262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072264 : List Nat := [2, 1, 3, 1, 2, 2, 2, 10]
def baseStart_2072264 : Nat := 118140960795 + 2072264 * 2 ^ 59
def prefixEnd_2072264 : Nat := 4983230072969 + 3 ^ 40 * 2072264 * 2
def baseEnd_2072264 : Nat := 39409906481806870047031

theorem tailTrace_2072264 : CollatzResearch.WordTrace tailWord_2072264 prefixEnd_2072264 39409906481806870047031 := by
  unfold tailWord_2072264
  simp only [CollatzResearch.WordTrace]
  refine ⟨37790838682274458679867923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50387784909699278239823897 37790838682274458679867923)
  ·
    refine ⟨56686258023411688019801885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37790838682274458679867923 56686258023411688019801885)
    ·
      refine ⟨21257346758779383007425707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56686258023411688019801885 21257346758779383007425707)
      ·
        refine ⟨31886020138169074511138561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21257346758779383007425707 31886020138169074511138561)
        ·
          refine ⟨23914515103626805883353921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31886020138169074511138561 23914515103626805883353921)
          ·
            refine ⟨17935886327720104412515441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23914515103626805883353921 17935886327720104412515441)
            ·
              refine ⟨13451914745790078309386581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17935886327720104412515441 13451914745790078309386581)
              ·
                refine ⟨39409906481806870047031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13451914745790078309386581 39409906481806870047031)
                ·
                  rfl

theorem cell23_2072264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 10].length) (baseStart_2072264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072264 prefixEnd_2072264 := by exact prefixLift 2072264
  have htrace : WordTrace (prefixWord ++ tailWord_2072264) baseStart_2072264 baseEnd_2072264 := by
    simpa [prefixWord, tailWord_2072264, baseEnd_2072264] using wordTrace_append hprefix tailTrace_2072264
  have hstable : (prefixWord ++ tailWord_2072264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072264).length < 2 ^ (prefixWord ++ tailWord_2072264).sum := by decide
  have hdescent : baseEnd_2072264 < baseStart_2072264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072281 : List Nat := [1, 2, 1, 2, 3, 3, 4, 7]
def baseStart_2072281 : Nat := 118140960795 + 2072281 * 2 ^ 59
def prefixEnd_2072281 : Nat := 4983230072969 + 3 ^ 40 * 2072281 * 2
def baseEnd_2072281 : Nat := 39410229784441182398417

theorem tailTrace_2072281 : CollatzResearch.WordTrace tailWord_2072281 prefixEnd_2072281 39410229784441182398417 := by
  unfold tailWord_2072281
  simp only [CollatzResearch.WordTrace]
  refine ⟨75582297405487329263104697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50388198270324886175403131 75582297405487329263104697)
  ·
    refine ⟨56686723054115496947328523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75582297405487329263104697 56686723054115496947328523)
    ·
      refine ⟨85030084581173245420992785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56686723054115496947328523 85030084581173245420992785)
      ·
        refine ⟨63772563435879934065744589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85030084581173245420992785 63772563435879934065744589)
        ·
          refine ⟨23914711288454975274654221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63772563435879934065744589 23914711288454975274654221)
          ·
            refine ⟨8968016733170615727995333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23914711288454975274654221 8968016733170615727995333)
            ·
              refine ⟨1681503137469490448999125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8968016733170615727995333 1681503137469490448999125)
              ·
                refine ⟨39410229784441182398417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1681503137469490448999125 39410229784441182398417)
                ·
                  rfl

theorem cell23_2072281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 7].length) (baseStart_2072281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072281 prefixEnd_2072281 := by exact prefixLift 2072281
  have htrace : WordTrace (prefixWord ++ tailWord_2072281) baseStart_2072281 baseEnd_2072281 := by
    simpa [prefixWord, tailWord_2072281, baseEnd_2072281] using wordTrace_append hprefix tailTrace_2072281
  have hstable : (prefixWord ++ tailWord_2072281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072281).length < 2 ^ (prefixWord ++ tailWord_2072281).sum := by decide
  have hdescent : baseEnd_2072281 < baseStart_2072281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072295 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2072295 : Nat := 118140960795 + 2072295 * 2 ^ 59
def prefixEnd_2072295 : Nat := 4983230072969 + 3 ^ 40 * 2072295 * 2
def baseEnd_2072295 : Nat := 1064083392909074869982195

theorem tailTrace_2072295 : CollatzResearch.WordTrace tailWord_2072295 prefixEnd_2072295 1064083392909074869982195 := by
  unfold tailWord_2072295
  simp only [CollatzResearch.WordTrace]
  refine ⟨75582808027436609654114339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50388538684957739769409559 75582808027436609654114339)
  ·
    refine ⟨113374212041154914481171509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75582808027436609654114339 113374212041154914481171509)
    ·
      refine ⟨10628832378858273232609829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113374212041154914481171509 10628832378858273232609829)
      ·
        refine ⟨1992906071035926231114343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10628832378858273232609829 1992906071035926231114343)
        ·
          refine ⟨2989359106553889346671515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992906071035926231114343 2989359106553889346671515)
          ·
            refine ⟨4484038659830834020007273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989359106553889346671515 4484038659830834020007273)
            ·
              refine ⟨3363028994873125515005455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484038659830834020007273 3363028994873125515005455)
              ·
                refine ⟨5044543492309688272508183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363028994873125515005455 5044543492309688272508183)
                ·
                  refine ⟨7566815238464532408762275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044543492309688272508183 7566815238464532408762275)
                  ·
                    refine ⟨11350222857696798613143413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7566815238464532408762275 11350222857696798613143413)
                    ·
                      refine ⟨1064083392909074869982195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11350222857696798613143413 1064083392909074869982195)
                      ·
                        rfl

theorem cell23_2072295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2072295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072295 prefixEnd_2072295 := by exact prefixLift 2072295
  have htrace : WordTrace (prefixWord ++ tailWord_2072295) baseStart_2072295 baseEnd_2072295 := by
    simpa [prefixWord, tailWord_2072295, baseEnd_2072295] using wordTrace_append hprefix tailTrace_2072295
  have hstable : (prefixWord ++ tailWord_2072295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072295).length < 2 ^ (prefixWord ++ tailWord_2072295).sum := by decide
  have hdescent : baseEnd_2072295 < baseStart_2072295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072326 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2072326 : Nat := 118140960795 + 2072326 * 2 ^ 59
def prefixEnd_2072326 : Nat := 4983230072969 + 3 ^ 40 * 2072326 * 2
def baseEnd_2072326 : Nat := 1064099310809364248694553

theorem tailTrace_2072326 : CollatzResearch.WordTrace tailWord_2072326 prefixEnd_2072326 1064099310809364248694553 := by
  unfold tailWord_2072326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361998084072634435890401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50389292460216201298995221 2361998084072634435890401)
  ·
    refine ⟨1771498563054475826917801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2361998084072634435890401 1771498563054475826917801)
    ·
      refine ⟨1328623922290856870188351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1771498563054475826917801 1328623922290856870188351)
      ·
        refine ⟨1992935883436285305282527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328623922290856870188351 1992935883436285305282527)
        ·
          refine ⟨2989403825154427957923791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992935883436285305282527 2989403825154427957923791)
          ·
            refine ⟨4484105737731641936885687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989403825154427957923791 4484105737731641936885687)
            ·
              refine ⟨6726158606597462905328531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484105737731641936885687 6726158606597462905328531)
              ·
                refine ⟨10089237909896194357992797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726158606597462905328531 10089237909896194357992797)
                ·
                  refine ⟨3783464216211072884247299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10089237909896194357992797 3783464216211072884247299)
                  ·
                    refine ⟨5675196324316609326370949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3783464216211072884247299 5675196324316609326370949)
                    ·
                      refine ⟨1064099310809364248694553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5675196324316609326370949 1064099310809364248694553)
                      ·
                        rfl

theorem cell23_2072326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2072326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072326 prefixEnd_2072326 := by exact prefixLift 2072326
  have htrace : WordTrace (prefixWord ++ tailWord_2072326) baseStart_2072326 baseEnd_2072326 := by
    simpa [prefixWord, tailWord_2072326, baseEnd_2072326] using wordTrace_append hprefix tailTrace_2072326
  have hstable : (prefixWord ++ tailWord_2072326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072326).length < 2 ^ (prefixWord ++ tailWord_2072326).sum := by decide
  have hdescent : baseEnd_2072326 < baseStart_2072326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072351 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_2072351 : Nat := 118140960795 + 2072351 * 2 ^ 59
def prefixEnd_2072351 : Nat := 4983230072969 + 3 ^ 40 * 2072351 * 2
def baseEnd_2072351 : Nat := 1064112147825726650881937

theorem tailTrace_2072351 : CollatzResearch.WordTrace tailWord_2072351 prefixEnd_2072351 1064112147825726650881937 := by
  unfold tailWord_2072351
  simp only [CollatzResearch.WordTrace]
  refine ⟨75584850515233731218152907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50389900343489154145435271 75584850515233731218152907)
  ·
    refine ⟨113377275772850596827229361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75584850515233731218152907 113377275772850596827229361)
    ·
      refine ⟨85032956829637947620422021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113377275772850596827229361 85032956829637947620422021)
      ·
        refine ⟨15943679405557115178829129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85032956829637947620422021 15943679405557115178829129)
        ·
          refine ⟨11957759554167836384121847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15943679405557115178829129 11957759554167836384121847)
          ·
            refine ⟨17936639331251754576182771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957759554167836384121847 17936639331251754576182771)
            ·
              refine ⟨26904958996877631864274157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17936639331251754576182771 26904958996877631864274157)
              ·
                refine ⟨10089359623829111949102809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26904958996877631864274157 10089359623829111949102809)
                ·
                  refine ⟨7567019717871833961827107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10089359623829111949102809 7567019717871833961827107)
                  ·
                    refine ⟨11350529576807750942740661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7567019717871833961827107 11350529576807750942740661)
                    ·
                      refine ⟨1064112147825726650881937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11350529576807750942740661 1064112147825726650881937)
                      ·
                        rfl

theorem cell23_2072351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_2072351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072351 prefixEnd_2072351 := by exact prefixLift 2072351
  have htrace : WordTrace (prefixWord ++ tailWord_2072351) baseStart_2072351 baseEnd_2072351 := by
    simpa [prefixWord, tailWord_2072351, baseEnd_2072351] using wordTrace_append hprefix tailTrace_2072351
  have hstable : (prefixWord ++ tailWord_2072351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072351).length < 2 ^ (prefixWord ++ tailWord_2072351).sum := by decide
  have hdescent : baseEnd_2072351 < baseStart_2072351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072352 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 1, 3, 2]
def baseStart_2072352 : Nat := 118140960795 + 2072352 * 2 ^ 59
def prefixEnd_2072352 : Nat := 4983230072969 + 3 ^ 40 * 2072352 * 2
def baseEnd_2072352 : Nat := 1064112661306381146969433

theorem tailTrace_2072352 : CollatzResearch.WordTrace tailWord_2072352 prefixEnd_2072352 1064112661306381146969433 := by
  unfold tailWord_2072352
  simp only [CollatzResearch.WordTrace]
  refine ⟨37792443494115054194469655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50389924658820072259292873 37792443494115054194469655)
  ·
    refine ⟨56688665241172581291704483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37792443494115054194469655 56688665241172581291704483)
    ·
      refine ⟨85032997861758871937556725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56688665241172581291704483 85032997861758871937556725)
      ·
        refine ⟨7971843549539894244145943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85032997861758871937556725 7971843549539894244145943)
        ·
          refine ⟨11957765324309841366218915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7971843549539894244145943 11957765324309841366218915)
          ·
            refine ⟨17936647986464762049328373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957765324309841366218915 17936647986464762049328373)
            ·
              refine ⟨1681560748731071442124535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17936647986464762049328373 1681560748731071442124535)
              ·
                refine ⟨2522341123096607163186803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681560748731071442124535 2522341123096607163186803)
                ·
                  refine ⟨3783511684644910744780205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522341123096607163186803 3783511684644910744780205)
                  ·
                    refine ⟨1418816881741841529292577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783511684644910744780205 1418816881741841529292577)
                    ·
                      refine ⟨1064112661306381146969433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418816881741841529292577 1064112661306381146969433)
                      ·
                        rfl

theorem cell23_2072352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_2072352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072352 prefixEnd_2072352 := by exact prefixLift 2072352
  have htrace : WordTrace (prefixWord ++ tailWord_2072352) baseStart_2072352 baseEnd_2072352 := by
    simpa [prefixWord, tailWord_2072352, baseEnd_2072352] using wordTrace_append hprefix tailTrace_2072352
  have hstable : (prefixWord ++ tailWord_2072352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072352).length < 2 ^ (prefixWord ++ tailWord_2072352).sum := by decide
  have hdescent : baseEnd_2072352 < baseStart_2072352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072378 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_2072378 : Nat := 118140960795 + 2072378 * 2 ^ 59
def prefixEnd_2072378 : Nat := 4983230072969 + 3 ^ 40 * 2072378 * 2
def baseEnd_2072378 : Nat := 1064126011803398045244313

theorem tailTrace_2072378 : CollatzResearch.WordTrace tailWord_2072378 prefixEnd_2072378 1064126011803398045244313 := by
  unfold tailWord_2072378
  simp only [CollatzResearch.WordTrace]
  refine ⟨18896458821533978707346447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50390556857423943219590525 18896458821533978707346447)
  ·
    refine ⟨28344688232300968061019671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18896458821533978707346447 28344688232300968061019671)
    ·
      refine ⟨42517032348451452091529507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28344688232300968061019671 42517032348451452091529507)
      ·
        refine ⟨63775548522677178137294261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42517032348451452091529507 63775548522677178137294261)
        ·
          refine ⟨5978957674000985450371337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63775548522677178137294261 5978957674000985450371337)
          ·
            refine ⟨4484218255500739087778503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978957674000985450371337 4484218255500739087778503)
            ·
              refine ⟨6726327383251108631667755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484218255500739087778503 6726327383251108631667755)
              ·
                refine ⟨10089491074876662947501633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726327383251108631667755 10089491074876662947501633)
                ·
                  refine ⟨7567118306157497210626225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10089491074876662947501633 7567118306157497210626225)
                  ·
                    refine ⟨5675338729618122907969669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567118306157497210626225 5675338729618122907969669)
                    ·
                      refine ⟨1064126011803398045244313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5675338729618122907969669 1064126011803398045244313)
                      ·
                        rfl

theorem cell23_2072378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_2072378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072378 prefixEnd_2072378 := by exact prefixLift 2072378
  have htrace : WordTrace (prefixWord ++ tailWord_2072378) baseStart_2072378 baseEnd_2072378 := by
    simpa [prefixWord, tailWord_2072378, baseEnd_2072378] using wordTrace_append hprefix tailTrace_2072378
  have hstable : (prefixWord ++ tailWord_2072378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072378).length < 2 ^ (prefixWord ++ tailWord_2072378).sum := by decide
  have hdescent : baseEnd_2072378 < baseStart_2072378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072382 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_2072382 : Nat := 118140960795 + 2072382 * 2 ^ 59
def prefixEnd_2072382 : Nat := 4983230072969 + 3 ^ 40 * 2072382 * 2
def baseEnd_2072382 : Nat := 1064128065726016029594295

theorem tailTrace_2072382 : CollatzResearch.WordTrace tailWord_2072382 prefixEnd_2072382 1064128065726016029594295 := by
  unfold tailWord_2072382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9448247647265177939066425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50390654118747615675020933 9448247647265177939066425)
  ·
    refine ⟨7086185735448883454299819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9448247647265177939066425 7086185735448883454299819)
    ·
      refine ⟨10629278603173325181449729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7086185735448883454299819 10629278603173325181449729)
      ·
        refine ⟨7971958952379993886087297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10629278603173325181449729 7971958952379993886087297)
        ·
          refine ⟨5978969214284995414565473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7971958952379993886087297 5978969214284995414565473)
          ·
            refine ⟨4484226910713746560924105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978969214284995414565473 4484226910713746560924105)
            ·
              refine ⟨3363170183035309920693079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484226910713746560924105 3363170183035309920693079)
              ·
                refine ⟨5044755274552964881039619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363170183035309920693079 5044755274552964881039619)
                ·
                  refine ⟨7567132911829447321559429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044755274552964881039619 7567132911829447321559429)
                  ·
                    refine ⟨1418837420968021372792393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7567132911829447321559429 1418837420968021372792393)
                    ·
                      refine ⟨1064128065726016029594295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418837420968021372792393 1064128065726016029594295)
                      ·
                        rfl

theorem cell23_2072382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_2072382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072382 prefixEnd_2072382 := by exact prefixLift 2072382
  have htrace : WordTrace (prefixWord ++ tailWord_2072382) baseStart_2072382 baseEnd_2072382 := by
    simpa [prefixWord, tailWord_2072382, baseEnd_2072382] using wordTrace_append hprefix tailTrace_2072382
  have hstable : (prefixWord ++ tailWord_2072382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072382).length < 2 ^ (prefixWord ++ tailWord_2072382).sum := by decide
  have hdescent : baseEnd_2072382 < baseStart_2072382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072405 : List Nat := [1, 3, 2, 2, 2, 3, 2, 3, 5]
def baseStart_2072405 : Nat := 118140960795 + 2072405 * 2 ^ 59
def prefixEnd_2072405 : Nat := 4983230072969 + 3 ^ 40 * 2072405 * 2
def baseEnd_2072405 : Nat := 118237763975674382178521

theorem tailTrace_2072405 : CollatzResearch.WordTrace tailWord_2072405 prefixEnd_2072405 118237763975674382178521 := by
  unfold tailWord_2072405
  simp only [CollatzResearch.WordTrace]
  refine ⟨75586820057038098440618669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50391213371358732293745779 75586820057038098440618669)
  ·
    refine ⟨28345057521389286915232001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75586820057038098440618669 28345057521389286915232001)
    ·
      refine ⟨21258793141041965186424001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28345057521389286915232001 21258793141041965186424001)
      ·
        refine ⟨15944094855781473889818001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21258793141041965186424001 15944094855781473889818001)
        ·
          refine ⟨11958071141836105417363501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15944094855781473889818001 11958071141836105417363501)
          ·
            refine ⟨4484276678188539531511313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11958071141836105417363501 4484276678188539531511313)
            ·
              refine ⟨3363207508641404648633485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484276678188539531511313 3363207508641404648633485)
              ·
                refine ⟨1261202815740526743237557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3363207508641404648633485 1261202815740526743237557)
                ·
                  refine ⟨118237763975674382178521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1261202815740526743237557 118237763975674382178521)
                  ·
                    rfl

theorem cell23_2072405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_2072405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072405 prefixEnd_2072405 := by exact prefixLift 2072405
  have htrace : WordTrace (prefixWord ++ tailWord_2072405) baseStart_2072405 baseEnd_2072405 := by
    simpa [prefixWord, tailWord_2072405, baseEnd_2072405] using wordTrace_append hprefix tailTrace_2072405
  have hstable : (prefixWord ++ tailWord_2072405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072405).length < 2 ^ (prefixWord ++ tailWord_2072405).sum := by decide
  have hdescent : baseEnd_2072405 < baseStart_2072405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072448 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 3, 4]
def baseStart_2072448 : Nat := 118140960795 + 2072448 * 2 ^ 59
def prefixEnd_2072448 : Nat := 4983230072969 + 3 ^ 40 * 2072448 * 2
def baseEnd_2072448 : Nat := 354720651816404257122997

theorem tailTrace_2072448 : CollatzResearch.WordTrace tailWord_2072448 prefixEnd_2072448 354720651816404257122997 := by
  unfold tailWord_2072448
  simp only [CollatzResearch.WordTrace]
  refine ⟨37794194197941158392216999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50392258930588211189622665 37794194197941158392216999)
  ·
    refine ⟨56691291296911737588325499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37794194197941158392216999 56691291296911737588325499)
    ·
      refine ⟨85036936945367606382488249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56691291296911737588325499 85036936945367606382488249)
      ·
        refine ⟨63777702709025704786866187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85036936945367606382488249 63777702709025704786866187)
        ·
          refine ⟨95666554063538557180299281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63777702709025704786866187 95666554063538557180299281)
          ·
            refine ⟨71749915547653917885224461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95666554063538557180299281 71749915547653917885224461)
            ·
              refine ⟨26906218330370219206959173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71749915547653917885224461 26906218330370219206959173)
              ·
                refine ⟨5044915936944416101304845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26906218330370219206959173 5044915936944416101304845)
                ·
                  refine ⟨1891843476354156037989317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5044915936944416101304845 1891843476354156037989317)
                  ·
                    refine ⟨354720651816404257122997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1891843476354156037989317 354720651816404257122997)
                    ·
                      rfl

theorem cell23_2072448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 4].length) (baseStart_2072448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072448 prefixEnd_2072448 := by exact prefixLift 2072448
  have htrace : WordTrace (prefixWord ++ tailWord_2072448) baseStart_2072448 baseEnd_2072448 := by
    simpa [prefixWord, tailWord_2072448, baseEnd_2072448] using wordTrace_append hprefix tailTrace_2072448
  have hstable : (prefixWord ++ tailWord_2072448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072448).length < 2 ^ (prefixWord ++ tailWord_2072448).sum := by decide
  have hdescent : baseEnd_2072448 < baseStart_2072448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072472 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2072472 : Nat := 118140960795 + 2072472 * 2 ^ 59
def prefixEnd_2072472 : Nat := 4983230072969 + 3 ^ 40 * 2072472 * 2
def baseEnd_2072472 : Nat := 1064174278984920677468881

theorem tailTrace_2072472 : CollatzResearch.WordTrace tailWord_2072472 prefixEnd_2072472 1064174278984920677468881 := by
  unfold tailWord_2072472
  simp only [CollatzResearch.WordTrace]
  refine ⟨37794631873897684441653835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50392842498530245922205113 37794631873897684441653835)
  ·
    refine ⟨56691947810846526662480753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37794631873897684441653835 56691947810846526662480753)
    ·
      refine ⟨42518960858134894996860565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56691947810846526662480753 42518960858134894996860565)
      ·
        refine ⟨1993076290225073202977839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42518960858134894996860565 1993076290225073202977839)
        ·
          refine ⟨2989614435337609804466759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993076290225073202977839 2989614435337609804466759)
          ·
            refine ⟨4484421653006414706700139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989614435337609804466759 4484421653006414706700139)
            ·
              refine ⟨6726632479509622060050209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484421653006414706700139 6726632479509622060050209)
              ·
                refine ⟨5044974359632216545037657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6726632479509622060050209 5044974359632216545037657)
                ·
                  refine ⟨3783730769724162408778243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5044974359632216545037657 3783730769724162408778243)
                  ·
                    refine ⟨5675596154586243613167365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3783730769724162408778243 5675596154586243613167365)
                    ·
                      refine ⟨1064174278984920677468881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5675596154586243613167365 1064174278984920677468881)
                      ·
                        rfl

theorem cell23_2072472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2072472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072472 prefixEnd_2072472 := by exact prefixLift 2072472
  have htrace : WordTrace (prefixWord ++ tailWord_2072472) baseStart_2072472 baseEnd_2072472 := by
    simpa [prefixWord, tailWord_2072472, baseEnd_2072472] using wordTrace_append hprefix tailTrace_2072472
  have hstable : (prefixWord ++ tailWord_2072472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072472).length < 2 ^ (prefixWord ++ tailWord_2072472).sum := by decide
  have hdescent : baseEnd_2072472 < baseStart_2072472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072505 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2072505 : Nat := 118140960795 + 2072505 * 2 ^ 59
def prefixEnd_2072505 : Nat := 4983230072969 + 3 ^ 40 * 2072505 * 2
def baseEnd_2072505 : Nat := 1064191223846519048356229

theorem tailTrace_2072505 : CollatzResearch.WordTrace tailWord_2072505 prefixEnd_2072505 1064191223846519048356229 := by
  unfold tailWord_2072505
  simp only [CollatzResearch.WordTrace]
  refine ⟨75590467356675815519258969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50393644904450543679505979 75590467356675815519258969)
  ·
    refine ⟨56692850517506861639444227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75590467356675815519258969 56692850517506861639444227)
    ·
      refine ⟨85039275776260292459166341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56692850517506861639444227 85039275776260292459166341)
      ·
        refine ⟨15944864208048804836093689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85039275776260292459166341 15944864208048804836093689)
        ·
          refine ⟨11958648156036603627070267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15944864208048804836093689 11958648156036603627070267)
          ·
            refine ⟨17937972234054905440605401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11958648156036603627070267 17937972234054905440605401)
            ·
              refine ⟨13453479175541179080454051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17937972234054905440605401 13453479175541179080454051)
              ·
                refine ⟨20180218763311768620681077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13453479175541179080454051 20180218763311768620681077)
                ·
                  refine ⟨1891895509060478308188851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20180218763311768620681077 1891895509060478308188851)
                  ·
                    refine ⟨2837843263590717462283277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1891895509060478308188851 2837843263590717462283277)
                    ·
                      refine ⟨1064191223846519048356229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2837843263590717462283277 1064191223846519048356229)
                      ·
                        rfl

theorem cell23_2072505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2072505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072505 prefixEnd_2072505 := by exact prefixLift 2072505
  have htrace : WordTrace (prefixWord ++ tailWord_2072505) baseStart_2072505 baseEnd_2072505 := by
    simpa [prefixWord, tailWord_2072505, baseEnd_2072505] using wordTrace_append hprefix tailTrace_2072505
  have hstable : (prefixWord ++ tailWord_2072505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072505).length < 2 ^ (prefixWord ++ tailWord_2072505).sum := by decide
  have hdescent : baseEnd_2072505 < baseStart_2072505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072532 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2072532 : Nat := 118140960795 + 2072532 * 2 ^ 59
def prefixEnd_2072532 : Nat := 4983230072969 + 3 ^ 40 * 2072532 * 2
def baseEnd_2072532 : Nat := 1064205087824190442718605

theorem tailTrace_2072532 : CollatzResearch.WordTrace tailWord_2072532 prefixEnd_2072532 1064205087824190442718605 := by
  unfold tailWord_2072532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37795726063788999565245925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50394301418385332753661233 37795726063788999565245925)
  ·
    refine ⟨7086698636960437418483611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37795726063788999565245925 7086698636960437418483611)
    ·
      refine ⟨10630047955440656127725417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7086698636960437418483611 10630047955440656127725417)
      ·
        refine ⟨7972535966580492095794063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10630047955440656127725417 7972535966580492095794063)
        ·
          refine ⟨11958803949870738143691095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972535966580492095794063 11958803949870738143691095)
          ·
            refine ⟨17938205924806107215536643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11958803949870738143691095 17938205924806107215536643)
            ·
              refine ⟨26907308887209160823304965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17938205924806107215536643 26907308887209160823304965)
              ·
                refine ⟨5045120416351717654369681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26907308887209160823304965 5045120416351717654369681)
                ·
                  refine ⟨3783840312263788240777261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5045120416351717654369681 3783840312263788240777261)
                  ·
                    refine ⟨1418940117098920590291473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783840312263788240777261 1418940117098920590291473)
                    ·
                      refine ⟨1064205087824190442718605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418940117098920590291473 1064205087824190442718605)
                      ·
                        rfl

theorem cell23_2072532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2072532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072532 prefixEnd_2072532 := by exact prefixLift 2072532
  have htrace : WordTrace (prefixWord ++ tailWord_2072532) baseStart_2072532 baseEnd_2072532 := by
    simpa [prefixWord, tailWord_2072532, baseEnd_2072532] using wordTrace_append hprefix tailTrace_2072532
  have hstable : (prefixWord ++ tailWord_2072532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072532).length < 2 ^ (prefixWord ++ tailWord_2072532).sum := by decide
  have hdescent : baseEnd_2072532 < baseStart_2072532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072548 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_2072548 : Nat := 118140960795 + 2072548 * 2 ^ 59
def prefixEnd_2072548 : Nat := 4983230072969 + 3 ^ 40 * 2072548 * 2
def baseEnd_2072548 : Nat := 1064213303514662380118531

theorem tailTrace_2072548 : CollatzResearch.WordTrace tailWord_2072548 prefixEnd_2072548 1064213303514662380118531 := by
  unfold tailWord_2072548
  simp only [CollatzResearch.WordTrace]
  refine ⟨37796017847760016931537149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50394690463680022575382865 37796017847760016931537149)
  ·
    refine ⟨14173506692910006349326431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37796017847760016931537149 14173506692910006349326431)
    ·
      refine ⟨21260260039365009523989647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14173506692910006349326431 21260260039365009523989647)
      ·
        refine ⟨31890390059047514285984471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21260260039365009523989647 31890390059047514285984471)
        ·
          refine ⟨47835585088571271428976707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31890390059047514285984471 47835585088571271428976707)
          ·
            refine ⟨71753377632856907143465061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47835585088571271428976707 71753377632856907143465061)
            ·
              refine ⟨13453758306160670089399699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71753377632856907143465061 13453758306160670089399699)
              ·
                refine ⟨20180637459241005134099549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13453758306160670089399699 20180637459241005134099549)
                ·
                  refine ⟨7567739047215376925287331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20180637459241005134099549 7567739047215376925287331)
                  ·
                    refine ⟨11351608570823065387930997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7567739047215376925287331 11351608570823065387930997)
                    ·
                      refine ⟨1064213303514662380118531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11351608570823065387930997 1064213303514662380118531)
                      ·
                        rfl

theorem cell23_2072548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_2072548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072548 prefixEnd_2072548 := by exact prefixLift 2072548
  have htrace : WordTrace (prefixWord ++ tailWord_2072548) baseStart_2072548 baseEnd_2072548 := by
    simpa [prefixWord, tailWord_2072548, baseEnd_2072548] using wordTrace_append hprefix tailTrace_2072548
  have hstable : (prefixWord ++ tailWord_2072548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072548).length < 2 ^ (prefixWord ++ tailWord_2072548).sum := by decide
  have hdescent : baseEnd_2072548 < baseStart_2072548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072566 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_2072566 : Nat := 118140960795 + 2072566 * 2 ^ 59
def prefixEnd_2072566 : Nat := 4983230072969 + 3 ^ 40 * 2072566 * 2
def baseEnd_2072566 : Nat := 1064222546166443309693449

theorem tailTrace_2072566 : CollatzResearch.WordTrace tailWord_2072566 prefixEnd_2072566 1064222546166443309693449 := by
  unfold tailWord_2072566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724543263090926433576847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50395128139636548624819701 4724543263090926433576847)
  ·
    refine ⟨7086814894636389650365271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4724543263090926433576847 7086814894636389650365271)
    ·
      refine ⟨10630222341954584475547907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7086814894636389650365271 10630222341954584475547907)
      ·
        refine ⟨15945333512931876713321861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10630222341954584475547907 15945333512931876713321861)
        ·
          refine ⟨2989750033674726883747849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15945333512931876713321861 2989750033674726883747849)
          ·
            refine ⟨2242312525256045162810887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2989750033674726883747849 2242312525256045162810887)
            ·
              refine ⟨3363468787884067744216331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242312525256045162810887 3363468787884067744216331)
              ·
                refine ⟨5045203181826101616324497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363468787884067744216331 5045203181826101616324497)
                ·
                  refine ⟨3783902386369576212243373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5045203181826101616324497 3783902386369576212243373)
                  ·
                    refine ⟨1418963394888591079591265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3783902386369576212243373 1418963394888591079591265)
                    ·
                      refine ⟨1064222546166443309693449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1418963394888591079591265 1064222546166443309693449)
                      ·
                        rfl

theorem cell23_2072566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_2072566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072566 prefixEnd_2072566 := by exact prefixLift 2072566
  have htrace : WordTrace (prefixWord ++ tailWord_2072566) baseStart_2072566 baseEnd_2072566 := by
    simpa [prefixWord, tailWord_2072566, baseEnd_2072566] using wordTrace_append hprefix tailTrace_2072566
  have hstable : (prefixWord ++ tailWord_2072566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072566).length < 2 ^ (prefixWord ++ tailWord_2072566).sum := by decide
  have hdescent : baseEnd_2072566 < baseStart_2072566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072609 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_2072609 : Nat := 118140960795 + 2072609 * 2 ^ 59
def prefixEnd_2072609 : Nat := 4983230072969 + 3 ^ 40 * 2072609 * 2
def baseEnd_2072609 : Nat := 1064244625834586641455751

theorem tailTrace_2072609 : CollatzResearch.WordTrace tailWord_2072609 prefixEnd_2072609 1064244625834586641455751 := by
  unfold tailWord_2072609
  simp only [CollatzResearch.WordTrace]
  refine ⟨75594260548299041281044881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50396173698866027520696587 75594260548299041281044881)
  ·
    refine ⟨56695695411224280960783661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75594260548299041281044881 56695695411224280960783661)
    ·
      refine ⟨21260885779209105360293873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56695695411224280960783661 21260885779209105360293873)
      ·
        refine ⟨15945664334406829020220405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21260885779209105360293873 15945664334406829020220405)
        ·
          refine ⟨1494906031350640220645663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15945664334406829020220405 1494906031350640220645663)
          ·
            refine ⟨2242359047025960330968495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494906031350640220645663 2242359047025960330968495)
            ·
              refine ⟨3363538570538940496452743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242359047025960330968495 3363538570538940496452743)
              ·
                refine ⟨5045307855808410744679115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363538570538940496452743 5045307855808410744679115)
                ·
                  refine ⟨7567961783712616117018673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045307855808410744679115 7567961783712616117018673)
                  ·
                    refine ⟨5675971337784462087764005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567961783712616117018673 5675971337784462087764005)
                    ·
                      refine ⟨1064244625834586641455751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5675971337784462087764005 1064244625834586641455751)
                      ·
                        rfl

theorem cell23_2072609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_2072609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072609 prefixEnd_2072609 := by exact prefixLift 2072609
  have htrace : WordTrace (prefixWord ++ tailWord_2072609) baseStart_2072609 baseEnd_2072609 := by
    simpa [prefixWord, tailWord_2072609, baseEnd_2072609] using wordTrace_append hprefix tailTrace_2072609
  have hstable : (prefixWord ++ tailWord_2072609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072609).length < 2 ^ (prefixWord ++ tailWord_2072609).sum := by decide
  have hdescent : baseEnd_2072609 < baseStart_2072609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072616 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2072616 : Nat := 118140960795 + 2072616 * 2 ^ 59
def prefixEnd_2072616 : Nat := 4983230072969 + 3 ^ 40 * 2072616 * 2
def baseEnd_2072616 : Nat := 1064248220199168114068219

theorem tailTrace_2072616 : CollatzResearch.WordTrace tailWord_2072616 prefixEnd_2072616 1064248220199168114068219 := by
  unfold tailWord_2072616
  simp only [CollatzResearch.WordTrace]
  refine ⟨37797257929636840738274851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50396343906182454317699801 37797257929636840738274851)
  ·
    refine ⟨56695886894455261107412277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37797257929636840738274851 56695886894455261107412277)
    ·
      refine ⟨5315239396355180728819901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56695886894455261107412277 5315239396355180728819901)
      ·
        refine ⟨1993214773633192773307463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5315239396355180728819901 1993214773633192773307463)
        ·
          refine ⟨2989822160449789159961195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993214773633192773307463 2989822160449789159961195)
          ·
            refine ⟨4484733240674683739941793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989822160449789159961195 4484733240674683739941793)
            ·
              refine ⟨3363549930506012804956345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484733240674683739941793 3363549930506012804956345)
              ·
                refine ⟨2522662447879509603717259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363549930506012804956345 2522662447879509603717259)
                ·
                  refine ⟨3783993671819264405575889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522662447879509603717259 3783993671819264405575889)
                  ·
                    refine ⟨2837995253864448304181917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3783993671819264405575889 2837995253864448304181917)
                    ·
                      refine ⟨1064248220199168114068219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2837995253864448304181917 1064248220199168114068219)
                      ·
                        rfl

theorem cell23_2072616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2072616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072616 prefixEnd_2072616 := by exact prefixLift 2072616
  have htrace : WordTrace (prefixWord ++ tailWord_2072616) baseStart_2072616 baseEnd_2072616 := by
    simpa [prefixWord, tailWord_2072616, baseEnd_2072616] using wordTrace_append hprefix tailTrace_2072616
  have hstable : (prefixWord ++ tailWord_2072616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072616).length < 2 ^ (prefixWord ++ tailWord_2072616).sum := by decide
  have hdescent : baseEnd_2072616 < baseStart_2072616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072646 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2072646 : Nat := 118140960795 + 2072646 * 2 ^ 59
def prefixEnd_2072646 : Nat := 4983230072969 + 3 ^ 40 * 2072646 * 2
def baseEnd_2072646 : Nat := 1064263624618802996693081

theorem tailTrace_2072646 : CollatzResearch.WordTrace tailWord_2072646 prefixEnd_2072646 1064263624618802996693081 := by
  unfold tailWord_2072646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362362814036406143754431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50397073366109997733427861 2362362814036406143754431)
  ·
    refine ⟨3543544221054609215631647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2362362814036406143754431 3543544221054609215631647)
    ·
      refine ⟨5315316331581913823447471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3543544221054609215631647 5315316331581913823447471)
      ·
        refine ⟨7972974497372870735171207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315316331581913823447471 7972974497372870735171207)
        ·
          refine ⟨11959461746059306102756811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972974497372870735171207 11959461746059306102756811)
          ·
            refine ⟨17939192619088959154135217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11959461746059306102756811 17939192619088959154135217)
            ·
              refine ⟨13454394464316719365601413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17939192619088959154135217 13454394464316719365601413)
              ·
                refine ⟨2522698962059384881050265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13454394464316719365601413 2522698962059384881050265)
                ·
                  refine ⟨1892024221544538660787699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2522698962059384881050265 1892024221544538660787699)
                  ·
                    refine ⟨2838036332316807991181549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892024221544538660787699 2838036332316807991181549)
                    ·
                      refine ⟨1064263624618802996693081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2838036332316807991181549 1064263624618802996693081)
                      ·
                        rfl

theorem cell23_2072646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2072646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072646 prefixEnd_2072646 := by exact prefixLift 2072646
  have htrace : WordTrace (prefixWord ++ tailWord_2072646) baseStart_2072646 baseEnd_2072646 := by
    simpa [prefixWord, tailWord_2072646, baseEnd_2072646] using wordTrace_append hprefix tailTrace_2072646
  have hstable : (prefixWord ++ tailWord_2072646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072646).length < 2 ^ (prefixWord ++ tailWord_2072646).sum := by decide
  have hdescent : baseEnd_2072646 < baseStart_2072646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072648 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_2072648 : Nat := 118140960795 + 2072648 * 2 ^ 59
def prefixEnd_2072648 : Nat := 4983230072969 + 3 ^ 40 * 2072648 * 2
def baseEnd_2072648 : Nat := 1064264651580111988868071

theorem tailTrace_2072648 : CollatzResearch.WordTrace tailWord_2072648 prefixEnd_2072648 1064264651580111988868071 := by
  unfold tailWord_2072648
  simp only [CollatzResearch.WordTrace]
  refine ⟨37797841497578875470857299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50397121996771833961143065 37797841497578875470857299)
  ·
    refine ⟨56696762246368313206285949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37797841497578875470857299 56696762246368313206285949)
    ·
      refine ⟨21261285842388117452357231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56696762246368313206285949 21261285842388117452357231)
      ·
        refine ⟨31891928763582176178535847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21261285842388117452357231 31891928763582176178535847)
        ·
          refine ⟨47837893145373264267803771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31891928763582176178535847 47837893145373264267803771)
          ·
            refine ⟨71756839718059896401705657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47837893145373264267803771 71756839718059896401705657)
            ·
              refine ⟨53817629788544922301279243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71756839718059896401705657 53817629788544922301279243)
              ·
                refine ⟨80726444682817383451918865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53817629788544922301279243 80726444682817383451918865)
                ·
                  refine ⟨60544833512113037588939149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80726444682817383451918865 60544833512113037588939149)
                  ·
                    refine ⟨22704312567042389095852181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60544833512113037588939149 22704312567042389095852181)
                    ·
                      refine ⟨1064264651580111988868071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22704312567042389095852181 1064264651580111988868071)
                      ·
                        rfl

theorem cell23_2072648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_2072648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072648 prefixEnd_2072648 := by exact prefixLift 2072648
  have htrace : WordTrace (prefixWord ++ tailWord_2072648) baseStart_2072648 baseEnd_2072648 := by
    simpa [prefixWord, tailWord_2072648, baseEnd_2072648] using wordTrace_append hprefix tailTrace_2072648
  have hstable : (prefixWord ++ tailWord_2072648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072648).length < 2 ^ (prefixWord ++ tailWord_2072648).sum := by decide
  have hdescent : baseEnd_2072648 < baseStart_2072648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072709 : List Nat := [1, 3, 1, 1, 5, 1, 4, 2, 5]
def baseStart_2072709 : Nat := 118140960795 + 2072709 * 2 ^ 59
def prefixEnd_2072709 : Nat := 4983230072969 + 3 ^ 40 * 2072709 * 2
def baseEnd_2072709 : Nat := 118255108211115138911699

theorem tailTrace_2072709 : CollatzResearch.WordTrace tailWord_2072709 prefixEnd_2072709 118255108211115138911699 := by
  unfold tailWord_2072709
  simp only [CollatzResearch.WordTrace]
  refine ⟨75597907847936758359685181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50398605231957838906456787 75597907847936758359685181)
  ·
    refine ⟨28349215442976284384881943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75597907847936758359685181 28349215442976284384881943)
    ·
      refine ⟨42523823164464426577322915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28349215442976284384881943 42523823164464426577322915)
      ·
        refine ⟨63785734746696639865984373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42523823164464426577322915 63785734746696639865984373)
        ·
          refine ⟨5979912632502809987436035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63785734746696639865984373 5979912632502809987436035)
          ·
            refine ⟨8969868948754214981154053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979912632502809987436035 8969868948754214981154053)
            ·
              refine ⟨1681850427891415308966385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8969868948754214981154053 1681850427891415308966385)
              ·
                refine ⟨1261387820918561481724789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681850427891415308966385 1261387820918561481724789)
                ·
                  refine ⟨118255108211115138911699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1261387820918561481724789 118255108211115138911699)
                  ·
                    rfl

theorem cell23_2072709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_2072709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072709 prefixEnd_2072709 := by exact prefixLift 2072709
  have htrace : WordTrace (prefixWord ++ tailWord_2072709) baseStart_2072709 baseEnd_2072709 := by
    simpa [prefixWord, tailWord_2072709, baseEnd_2072709] using wordTrace_append hprefix tailTrace_2072709
  have hstable : (prefixWord ++ tailWord_2072709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072709).length < 2 ^ (prefixWord ++ tailWord_2072709).sum := by decide
  have hdescent : baseEnd_2072709 < baseStart_2072709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072725 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_2072725 : Nat := 118140960795 + 2072725 * 2 ^ 59
def prefixEnd_2072725 : Nat := 4983230072969 + 3 ^ 40 * 2072725 * 2
def baseEnd_2072725 : Nat := 1064304189590508187605217

theorem tailTrace_2072725 : CollatzResearch.WordTrace tailWord_2072725 prefixEnd_2072725 1064304189590508187605217 := by
  unfold tailWord_2072725
  simp only [CollatzResearch.WordTrace]
  refine ⟨75598491415878793092267629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50398994277252528728178419 75598491415878793092267629)
  ·
    refine ⟨28349434280954547409600361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75598491415878793092267629 28349434280954547409600361)
    ·
      refine ⟨21262075710715910557200271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28349434280954547409600361 21262075710715910557200271)
      ·
        refine ⟨31893113566073865835800407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21262075710715910557200271 31893113566073865835800407)
        ·
          refine ⟨47839670349110798753700611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31893113566073865835800407 47839670349110798753700611)
          ·
            refine ⟨71759505523666198130550917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47839670349110798753700611 71759505523666198130550917)
            ·
              refine ⟨13454907285687412149478297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71759505523666198130550917 13454907285687412149478297)
              ·
                refine ⟨10091180464265559112108723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13454907285687412149478297 10091180464265559112108723)
                ·
                  refine ⟨15136770696398338668163085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10091180464265559112108723 15136770696398338668163085)
                  ·
                    refine ⟨5676289011149377000561157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15136770696398338668163085 5676289011149377000561157)
                    ·
                      refine ⟨1064304189590508187605217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5676289011149377000561157 1064304189590508187605217)
                      ·
                        rfl

theorem cell23_2072725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_2072725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072725 prefixEnd_2072725 := by exact prefixLift 2072725
  have htrace : WordTrace (prefixWord ++ tailWord_2072725) baseStart_2072725 baseEnd_2072725 := by
    simpa [prefixWord, tailWord_2072725, baseEnd_2072725] using wordTrace_append hprefix tailTrace_2072725
  have hstable : (prefixWord ++ tailWord_2072725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072725).length < 2 ^ (prefixWord ++ tailWord_2072725).sum := by decide
  have hdescent : baseEnd_2072725 < baseStart_2072725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072762 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_2072762 : Nat := 118140960795 + 2072762 * 2 ^ 59
def prefixEnd_2072762 : Nat := 4983230072969 + 3 ^ 40 * 2072762 * 2
def baseEnd_2072762 : Nat := 1064323188374724542842547

theorem tailTrace_2072762 : CollatzResearch.WordTrace tailWord_2072762 prefixEnd_2072762 1064323188374724542842547 := by
  unfold tailWord_2072762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18899960229186187102841135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50399893944496498940909693 18899960229186187102841135)
  ·
    refine ⟨28349940343779280654261703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18899960229186187102841135 28349940343779280654261703)
    ·
      refine ⟨42524910515668920981392555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28349940343779280654261703 42524910515668920981392555)
      ·
        refine ⟨63787365773503381472088833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42524910515668920981392555 63787365773503381472088833)
        ·
          refine ⟨47840524330127536104066625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63787365773503381472088833 47840524330127536104066625)
          ·
            refine ⟨35880393247595652078049969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47840524330127536104066625 35880393247595652078049969)
            ·
              refine ⟨26910294935696739058537477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35880393247595652078049969 26910294935696739058537477)
              ·
                refine ⟨5045680300443138573475777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26910294935696739058537477 5045680300443138573475777)
                ·
                  refine ⟨3784260225332353930106833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5045680300443138573475777 3784260225332353930106833)
                  ·
                    refine ⟨2838195168999265447580125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3784260225332353930106833 2838195168999265447580125)
                    ·
                      refine ⟨1064323188374724542842547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2838195168999265447580125 1064323188374724542842547)
                      ·
                        rfl

theorem cell23_2072762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_2072762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072762 prefixEnd_2072762 := by exact prefixLift 2072762
  have htrace : WordTrace (prefixWord ++ tailWord_2072762) baseStart_2072762 baseEnd_2072762 := by
    simpa [prefixWord, tailWord_2072762, baseEnd_2072762] using wordTrace_append hprefix tailTrace_2072762
  have hstable : (prefixWord ++ tailWord_2072762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072762).length < 2 ^ (prefixWord ++ tailWord_2072762).sum := by decide
  have hdescent : baseEnd_2072762 < baseStart_2072762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072812 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_2072812 : Nat := 118140960795 + 2072812 * 2 ^ 59
def prefixEnd_2072812 : Nat := 4983230072969 + 3 ^ 40 * 2072812 * 2
def baseEnd_2072812 : Nat := 354782954135816449072439

theorem tailTrace_2072812 : CollatzResearch.WordTrace tailWord_2072812 prefixEnd_2072812 354782954135816449072439 := by
  unfold tailWord_2072812
  simp only [CollatzResearch.WordTrace]
  refine ⟨37800832283281803475342345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50401109711042404633789793 37800832283281803475342345)
  ·
    refine ⟨28350624212461352606506759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37800832283281803475342345 28350624212461352606506759)
    ·
      refine ⟨42525936318692028909760139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28350624212461352606506759 42525936318692028909760139)
      ·
        refine ⟨63788904478038043364640209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42525936318692028909760139 63788904478038043364640209)
        ·
          refine ⟨47841678358528532523480157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63788904478038043364640209 47841678358528532523480157)
          ·
            refine ⟨17940629384448199696305059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47841678358528532523480157 17940629384448199696305059)
            ·
              refine ⟨26910944076672299544457589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17940629384448199696305059 26910944076672299544457589)
              ·
                refine ⟨2522901007188028082292899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26910944076672299544457589 2522901007188028082292899)
                ·
                  refine ⟨3784351510782042123439349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522901007188028082292899 3784351510782042123439349)
                  ·
                    refine ⟨354782954135816449072439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3784351510782042123439349 354782954135816449072439)
                    ·
                      rfl

theorem cell23_2072812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_2072812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072812 prefixEnd_2072812 := by exact prefixLift 2072812
  have htrace : WordTrace (prefixWord ++ tailWord_2072812) baseStart_2072812 baseEnd_2072812 := by
    simpa [prefixWord, tailWord_2072812, baseEnd_2072812] using wordTrace_append hprefix tailTrace_2072812
  have hstable : (prefixWord ++ tailWord_2072812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072812).length < 2 ^ (prefixWord ++ tailWord_2072812).sum := by decide
  have hdescent : baseEnd_2072812 < baseStart_2072812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072819 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 2, 3, 2]
def baseStart_2072819 : Nat := 118140960795 + 2072819 * 2 ^ 59
def prefixEnd_2072819 : Nat := 4983230072969 + 3 ^ 40 * 2072819 * 2
def baseEnd_2072819 : Nat := 1064352456772030819829785

theorem tailTrace_2072819 : CollatzResearch.WordTrace tailWord_2072819 prefixEnd_2072819 1064352456772030819829785 := by
  unfold tailWord_2072819
  simp only [CollatzResearch.WordTrace]
  refine ⟨75601919877538247146189511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50401279918358831430793007 75601919877538247146189511)
  ·
    refine ⟨113402879816307370719284267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75601919877538247146189511 113402879816307370719284267)
    ·
      refine ⟨170104319724461056078926401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113402879816307370719284267 170104319724461056078926401)
      ·
        refine ⟨127578239793345792059194801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170104319724461056078926401 127578239793345792059194801)
        ·
          refine ⟨95683679845009344044396101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127578239793345792059194801 95683679845009344044396101)
          ·
            refine ⟨17940689970939252008324269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95683679845009344044396101 17940689970939252008324269)
            ·
              refine ⟨6727758739102219503121601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17940689970939252008324269 6727758739102219503121601)
              ·
                refine ⟨5045819054326664627341201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727758739102219503121601 5045819054326664627341201)
                ·
                  refine ⟨3784364290744998470505901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5045819054326664627341201 3784364290744998470505901)
                  ·
                    refine ⟨1419136609029374426439713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3784364290744998470505901 1419136609029374426439713)
                    ·
                      refine ⟨1064352456772030819829785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419136609029374426439713 1064352456772030819829785)
                      ·
                        rfl

theorem cell23_2072819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 3, 2].length) (baseStart_2072819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072819 prefixEnd_2072819 := by exact prefixLift 2072819
  have htrace : WordTrace (prefixWord ++ tailWord_2072819) baseStart_2072819 baseEnd_2072819 := by
    simpa [prefixWord, tailWord_2072819, baseEnd_2072819] using wordTrace_append hprefix tailTrace_2072819
  have hstable : (prefixWord ++ tailWord_2072819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072819).length < 2 ^ (prefixWord ++ tailWord_2072819).sum := by decide
  have hdescent : baseEnd_2072819 < baseStart_2072819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072825 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 5, 6]
def baseStart_2072825 : Nat := 118140960795 + 2072825 * 2 ^ 59
def prefixEnd_2072825 : Nat := 4983230072969 + 3 ^ 40 * 2072825 * 2
def baseEnd_2072825 : Nat := 354785179218652598784919

theorem tailTrace_2072825 : CollatzResearch.WordTrace tailWord_2072825 prefixEnd_2072825 354785179218652598784919 := by
  unfold tailWord_2072825
  simp only [CollatzResearch.WordTrace]
  refine ⟨75602138715516510170907929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50401425810344340113938619 75602138715516510170907929)
  ·
    refine ⟨56701604036637382628180947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75602138715516510170907929 56701604036637382628180947)
    ·
      refine ⟨85052406054956073942271421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56701604036637382628180947 85052406054956073942271421)
      ·
        refine ⟨31894652270608527728351783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85052406054956073942271421 31894652270608527728351783)
        ·
          refine ⟨47841978405912791592527675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31894652270608527728351783 47841978405912791592527675)
          ·
            refine ⟨71762967608869187388791513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47841978405912791592527675 71762967608869187388791513)
            ·
              refine ⟨53822225706651890541593635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71762967608869187388791513 53822225706651890541593635)
              ·
                refine ⟨80733338559977835812390453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53822225706651890541593635 80733338559977835812390453)
                ·
                  refine ⟨7568750489997922107411605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80733338559977835812390453 7568750489997922107411605)
                  ·
                    refine ⟨354785179218652598784919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7568750489997922107411605 354785179218652598784919)
                    ·
                      rfl

theorem cell23_2072825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_2072825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072825 prefixEnd_2072825 := by exact prefixLift 2072825
  have htrace : WordTrace (prefixWord ++ tailWord_2072825) baseStart_2072825 baseEnd_2072825 := by
    simpa [prefixWord, tailWord_2072825, baseEnd_2072825] using wordTrace_append hprefix tailTrace_2072825
  have hstable : (prefixWord ++ tailWord_2072825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072825).length < 2 ^ (prefixWord ++ tailWord_2072825).sum := by decide
  have hdescent : baseEnd_2072825 < baseStart_2072825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072826 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_2072826 : Nat := 118140960795 + 2072826 * 2 ^ 59
def prefixEnd_2072826 : Nat := 4983230072969 + 3 ^ 40 * 2072826 * 2
def baseEnd_2072826 : Nat := 1064356051136612292442253

theorem tailTrace_2072826 : CollatzResearch.WordTrace tailWord_2072826 prefixEnd_2072826 1064356051136612292442253 := by
  unfold tailWord_2072826
  simp only [CollatzResearch.WordTrace]
  refine ⟨18900543797128221835423583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50401450125675258227796221 18900543797128221835423583)
  ·
    refine ⟨28350815695692332753135375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18900543797128221835423583 28350815695692332753135375)
    ·
      refine ⟨42526223543538499129703063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28350815695692332753135375 42526223543538499129703063)
      ·
        refine ⟨63789335315307748694554595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42526223543538499129703063 63789335315307748694554595)
        ·
          refine ⟨95684002972961623041831893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63789335315307748694554595 95684002972961623041831893)
          ·
            refine ⟨2242593819678788040042935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 95684002972961623041831893 2242593819678788040042935)
            ·
              refine ⟨3363890729518182060064403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242593819678788040042935 3363890729518182060064403)
              ·
                refine ⟨5045836094277273090096605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363890729518182060064403 5045836094277273090096605)
                ·
                  refine ⟨1892188535353977408786227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5045836094277273090096605 1892188535353977408786227)
                  ·
                    refine ⟨2838282803030966113179341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892188535353977408786227 2838282803030966113179341)
                    ·
                      refine ⟨1064356051136612292442253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2838282803030966113179341 1064356051136612292442253)
                      ·
                        rfl

theorem cell23_2072826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_2072826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072826 prefixEnd_2072826 := by exact prefixLift 2072826
  have htrace : WordTrace (prefixWord ++ tailWord_2072826) baseStart_2072826 baseEnd_2072826 := by
    simpa [prefixWord, tailWord_2072826, baseEnd_2072826] using wordTrace_append hprefix tailTrace_2072826
  have hstable : (prefixWord ++ tailWord_2072826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072826).length < 2 ^ (prefixWord ++ tailWord_2072826).sum := by decide
  have hdescent : baseEnd_2072826 < baseStart_2072826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072849 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_2072849 : Nat := 118140960795 + 2072849 * 2 ^ 59
def prefixEnd_2072849 : Nat := 4983230072969 + 3 ^ 40 * 2072849 * 2
def baseEnd_2072849 : Nat := 1064367861191665702454647

theorem tailTrace_2072849 : CollatzResearch.WordTrace tailWord_2072849 prefixEnd_2072849 1064367861191665702454647 := by
  unfold tailWord_2072849
  simp only [CollatzResearch.WordTrace]
  refine ⟨75603014067429562269781601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50402009378286374846521067 75603014067429562269781601)
  ·
    refine ⟨56702260550572171702336201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75603014067429562269781601 56702260550572171702336201)
    ·
      refine ⟨42526695412929128776752151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56702260550572171702336201 42526695412929128776752151)
      ·
        refine ⟨63790043119393693165128227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42526695412929128776752151 63790043119393693165128227)
        ·
          refine ⟨95685064679090539747692341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63790043119393693165128227 95685064679090539747692341)
          ·
            refine ⟨8970474813664738101346157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95685064679090539747692341 8970474813664738101346157)
            ·
              refine ⟨3363928055124276788004809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8970474813664738101346157 3363928055124276788004809)
              ·
                refine ⟨2522946041343207591003607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363928055124276788004809 2522946041343207591003607)
                ·
                  refine ⟨3784419062014811386505411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522946041343207591003607 3784419062014811386505411)
                  ·
                    refine ⟨5676628593022217079758117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3784419062014811386505411 5676628593022217079758117)
                    ·
                      refine ⟨1064367861191665702454647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5676628593022217079758117 1064367861191665702454647)
                      ·
                        rfl

theorem cell23_2072849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_2072849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072849 prefixEnd_2072849 := by exact prefixLift 2072849
  have htrace : WordTrace (prefixWord ++ tailWord_2072849) baseStart_2072849 baseEnd_2072849 := by
    simpa [prefixWord, tailWord_2072849, baseEnd_2072849] using wordTrace_append hprefix tailTrace_2072849
  have hstable : (prefixWord ++ tailWord_2072849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072849).length < 2 ^ (prefixWord ++ tailWord_2072849).sum := by decide
  have hdescent : baseEnd_2072849 < baseStart_2072849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072872 : List Nat := [2, 1, 5, 1, 3, 11]
def baseStart_2072872 : Nat := 118140960795 + 2072872 * 2 ^ 59
def prefixEnd_2072872 : Nat := 4983230072969 + 3 ^ 40 * 2072872 * 2
def baseEnd_2072872 : Nat := 4380163256159337911387

theorem tailTrace_2072872 : CollatzResearch.WordTrace tailWord_2072872 prefixEnd_2072872 4380163256159337911387 := by
  unfold tailWord_2072872
  simp only [CollatzResearch.WordTrace]
  refine ⟨37801926473173118598934435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50402568630897491465245913 37801926473173118598934435)
  ·
    refine ⟨56702889709759677898401653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37801926473173118598934435 56702889709759677898401653)
    ·
      refine ⟨5315895910289969802975155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56702889709759677898401653 5315895910289969802975155)
      ·
        refine ⟨7973843865434954704462733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315895910289969802975155 7973843865434954704462733)
        ·
          refine ⟨2990191449538108014173525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7973843865434954704462733 2990191449538108014173525)
          ·
            refine ⟨4380163256159337911387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2990191449538108014173525 4380163256159337911387)
            ·
              rfl

theorem cell23_2072872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 11].length) (baseStart_2072872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072872 prefixEnd_2072872 := by exact prefixLift 2072872
  have htrace : WordTrace (prefixWord ++ tailWord_2072872) baseStart_2072872 baseEnd_2072872 := by
    simpa [prefixWord, tailWord_2072872, baseEnd_2072872] using wordTrace_append hprefix tailTrace_2072872
  have hstable : (prefixWord ++ tailWord_2072872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072872).length < 2 ^ (prefixWord ++ tailWord_2072872).sum := by decide
  have hdescent : baseEnd_2072872 < baseStart_2072872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072883 : List Nat := [1, 1, 1, 2, 5, 1, 3, 4, 1, 2, 2]
def baseStart_2072883 : Nat := 118140960795 + 2072883 * 2 ^ 59
def prefixEnd_2072883 : Nat := 4983230072969 + 3 ^ 40 * 2072883 * 2
def baseEnd_2072883 : Nat := 1064385319533918569429491

theorem tailTrace_2072883 : CollatzResearch.WordTrace tailWord_2072883 prefixEnd_2072883 1064385319533918569429491 := by
  unfold tailWord_2072883
  simp only [CollatzResearch.WordTrace]
  refine ⟨75604254149306386076519303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50402836099537590717679535 75604254149306386076519303)
  ·
    refine ⟨113406381223959579114778955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75604254149306386076519303 113406381223959579114778955)
    ·
      refine ⟨170109571835939368672168433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113406381223959579114778955 170109571835939368672168433)
      ·
        refine ⟨127582178876954526504126325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170109571835939368672168433 127582178876954526504126325)
        ·
          refine ⟨11960829269714486859761843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127582178876954526504126325 11960829269714486859761843)
          ·
            refine ⟨17941243904571730289642765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11960829269714486859761843 17941243904571730289642765)
            ·
              refine ⟨6727966464214398858616037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17941243904571730289642765 6727966464214398858616037)
              ·
                refine ⟨1261493712040199785990507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6727966464214398858616037 1261493712040199785990507)
                ·
                  refine ⟨1892240568060299678985761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261493712040199785990507 1892240568060299678985761)
                  ·
                    refine ⟨1419180426045224759239321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892240568060299678985761 1419180426045224759239321)
                    ·
                      refine ⟨1064385319533918569429491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419180426045224759239321 1064385319533918569429491)
                      ·
                        rfl

theorem cell23_2072883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 2, 2].length) (baseStart_2072883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072883 prefixEnd_2072883 := by exact prefixLift 2072883
  have htrace : WordTrace (prefixWord ++ tailWord_2072883) baseStart_2072883 baseEnd_2072883 := by
    simpa [prefixWord, tailWord_2072883, baseEnd_2072883] using wordTrace_append hprefix tailTrace_2072883
  have hstable : (prefixWord ++ tailWord_2072883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072883).length < 2 ^ (prefixWord ++ tailWord_2072883).sum := by decide
  have hdescent : baseEnd_2072883 < baseStart_2072883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072889 : List Nat := [1, 2, 1, 6, 1, 3, 1, 8]
def baseStart_2072889 : Nat := 118140960795 + 2072889 * 2 ^ 59
def prefixEnd_2072889 : Nat := 4983230072969 + 3 ^ 40 * 2072889 * 2
def baseEnd_2072889 : Nat := 39421792608068353553869

theorem tailTrace_2072889 : CollatzResearch.WordTrace tailWord_2072889 prefixEnd_2072889 39421792608068353553869 := by
  unfold tailWord_2072889
  simp only [CollatzResearch.WordTrace]
  refine ⟨75604472987284649101237721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50402981991523099400825147 75604472987284649101237721)
  ·
    refine ⟨56703354740463486825928291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75604472987284649101237721 56703354740463486825928291)
    ·
      refine ⟨85055032110695230238892437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56703354740463486825928291 85055032110695230238892437)
      ·
        refine ⟨3986954630188838917448083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85055032110695230238892437 3986954630188838917448083)
        ·
          refine ⟨5980431945283258376172125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3986954630188838917448083 5980431945283258376172125)
          ·
            refine ⟨2242661979481221891064547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5980431945283258376172125 2242661979481221891064547)
            ·
              refine ⟨3363992969221832836596821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242661979481221891064547 3363992969221832836596821)
              ·
                refine ⟨39421792608068353553869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3363992969221832836596821 39421792608068353553869)
                ·
                  rfl

theorem cell23_2072889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 8].length) (baseStart_2072889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072889 prefixEnd_2072889 := by exact prefixLift 2072889
  have htrace : WordTrace (prefixWord ++ tailWord_2072889) baseStart_2072889 baseEnd_2072889 := by
    simpa [prefixWord, tailWord_2072889, baseEnd_2072889] using wordTrace_append hprefix tailTrace_2072889
  have hstable : (prefixWord ++ tailWord_2072889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072889).length < 2 ^ (prefixWord ++ tailWord_2072889).sum := by decide
  have hdescent : baseEnd_2072889 < baseStart_2072889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072900 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_2072900 : Nat := 118140960795 + 2072900 * 2 ^ 59
def prefixEnd_2072900 : Nat := 4983230072969 + 3 ^ 40 * 2072900 * 2
def baseEnd_2072900 : Nat := 1064394048705045002916913

theorem tailTrace_2072900 : CollatzResearch.WordTrace tailWord_2072900 prefixEnd_2072900 1064394048705045002916913 := by
  unfold tailWord_2072900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37802437095122398989944077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50403249460163198653258769 37802437095122398989944077)
  ·
    refine ⟨14175913910670899621229029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37802437095122398989944077 14175913910670899621229029)
    ·
      refine ⟨2657983858250793678980443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14175913910670899621229029 2657983858250793678980443)
      ·
        refine ⟨3986975787376190518470665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657983858250793678980443 3986975787376190518470665)
        ·
          refine ⟨2990231840532142888852999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3986975787376190518470665 2990231840532142888852999)
          ·
            refine ⟨4485347760798214333279499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990231840532142888852999 4485347760798214333279499)
            ·
              refine ⟨6728021641197321499919249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485347760798214333279499 6728021641197321499919249)
              ·
                refine ⟨5046016230897991124939437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6728021641197321499919249 5046016230897991124939437)
                ·
                  refine ⟨1892256086586746671852289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5046016230897991124939437 1892256086586746671852289)
                  ·
                    refine ⟨1419192064940060003889217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892256086586746671852289 1419192064940060003889217)
                    ·
                      refine ⟨1064394048705045002916913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419192064940060003889217 1064394048705045002916913)
                      ·
                        rfl

theorem cell23_2072900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_2072900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072900 prefixEnd_2072900 := by exact prefixLift 2072900
  have htrace : WordTrace (prefixWord ++ tailWord_2072900) baseStart_2072900 baseEnd_2072900 := by
    simpa [prefixWord, tailWord_2072900, baseEnd_2072900] using wordTrace_append hprefix tailTrace_2072900
  have hstable : (prefixWord ++ tailWord_2072900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072900).length < 2 ^ (prefixWord ++ tailWord_2072900).sum := by decide
  have hdescent : baseEnd_2072900 < baseStart_2072900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072932 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_2072932 : Nat := 118140960795 + 2072932 * 2 ^ 59
def prefixEnd_2072932 : Nat := 4983230072969 + 3 ^ 40 * 2072932 * 2
def baseEnd_2072932 : Nat := 354803493361996292572255

theorem tailTrace_2072932 : CollatzResearch.WordTrace tailWord_2072932 prefixEnd_2072932 354803493361996292572255 := by
  unfold tailWord_2072932
  simp only [CollatzResearch.WordTrace]
  refine ⟨37803020663064433722526525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50404027550752578296702033 37803020663064433722526525)
  ·
    refine ⟨14176132748649162645947447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37803020663064433722526525 14176132748649162645947447)
    ·
      refine ⟨21264199122973743968921171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14176132748649162645947447 21264199122973743968921171)
      ·
        refine ⟨31896298684460615953381757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21264199122973743968921171 31896298684460615953381757)
        ·
          refine ⟨11961112006672730982518159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31896298684460615953381757 11961112006672730982518159)
          ·
            refine ⟨17941668010009096473777239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11961112006672730982518159 17941668010009096473777239)
            ·
              refine ⟨26912502015013644710665859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17941668010009096473777239 26912502015013644710665859)
              ·
                refine ⟨40368753022520467065998789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26912502015013644710665859 40368753022520467065998789)
                ·
                  refine ⟨7569141191722587574874773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40368753022520467065998789 7569141191722587574874773)
                  ·
                    refine ⟨354803493361996292572255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7569141191722587574874773 354803493361996292572255)
                    ·
                      rfl

theorem cell23_2072932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_2072932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072932 prefixEnd_2072932 := by exact prefixLift 2072932
  have htrace : WordTrace (prefixWord ++ tailWord_2072932) baseStart_2072932 baseEnd_2072932 := by
    simpa [prefixWord, tailWord_2072932, baseEnd_2072932] using wordTrace_append hprefix tailTrace_2072932
  have hstable : (prefixWord ++ tailWord_2072932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072932).length < 2 ^ (prefixWord ++ tailWord_2072932).sum := by decide
  have hdescent : baseEnd_2072932 < baseStart_2072932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072933 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_2072933 : Nat := 118140960795 + 2072933 * 2 ^ 59
def prefixEnd_2072933 : Nat := 4983230072969 + 3 ^ 40 * 2072933 * 2
def baseEnd_2072933 : Nat := 1064410993566643373804261

theorem tailTrace_2072933 : CollatzResearch.WordTrace tailWord_2072933 prefixEnd_2072933 1064410993566643373804261 := by
  unfold tailWord_2072933
  simp only [CollatzResearch.WordTrace]
  refine ⟨75606077799125244615839453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50404051866083496410559635 75606077799125244615839453)
  ·
    refine ⟨28352279174671966730939795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75606077799125244615839453 28352279174671966730939795)
    ·
      refine ⟨42528418762007950096409693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28352279174671966730939795 42528418762007950096409693)
      ·
        refine ⟨15948157035752981286153635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42528418762007950096409693 15948157035752981286153635)
        ·
          refine ⟨23922235553629471929230453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15948157035752981286153635 23922235553629471929230453)
          ·
            refine ⟨2242709583152762993365355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23922235553629471929230453 2242709583152762993365355)
            ·
              refine ⟨3364064374729144490048033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242709583152762993365355 3364064374729144490048033)
              ·
                refine ⟨2523048281046858367536025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3364064374729144490048033 2523048281046858367536025)
                ·
                  refine ⟨1892286210785143775652019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2523048281046858367536025 1892286210785143775652019)
                  ·
                    refine ⟨2838429316177715663478029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892286210785143775652019 2838429316177715663478029)
                    ·
                      refine ⟨1064410993566643373804261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2838429316177715663478029 1064410993566643373804261)
                      ·
                        rfl

theorem cell23_2072933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_2072933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072933 prefixEnd_2072933 := by exact prefixLift 2072933
  have htrace : WordTrace (prefixWord ++ tailWord_2072933) baseStart_2072933 baseEnd_2072933 := by
    simpa [prefixWord, tailWord_2072933, baseEnd_2072933] using wordTrace_append hprefix tailTrace_2072933
  have hstable : (prefixWord ++ tailWord_2072933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072933).length < 2 ^ (prefixWord ++ tailWord_2072933).sum := by decide
  have hdescent : baseEnd_2072933 < baseStart_2072933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072949 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2072949 : Nat := 118140960795 + 2072949 * 2 ^ 59
def prefixEnd_2072949 : Nat := 4983230072969 + 3 ^ 40 * 2072949 * 2
def baseEnd_2072949 : Nat := 354806403085705103734729

theorem tailTrace_2072949 : CollatzResearch.WordTrace tailWord_2072949 prefixEnd_2072949 354806403085705103734729 := by
  unfold tailWord_2072949
  simp only [CollatzResearch.WordTrace]
  refine ⟨75606661367067279348421901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50404440911378186232281267 75606661367067279348421901)
  ·
    refine ⟨28352498012650229755658213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75606661367067279348421901 28352498012650229755658213)
    ·
      refine ⟨5316093377371918079185915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28352498012650229755658213 5316093377371918079185915)
      ·
        refine ⟨7974140066057877118778873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316093377371918079185915 7974140066057877118778873)
        ·
          refine ⟨5980605049543407839084155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7974140066057877118778873 5980605049543407839084155)
          ·
            refine ⟨8970907574315111758626233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980605049543407839084155 8970907574315111758626233)
            ·
              refine ⟨6728180680736333818969675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8970907574315111758626233 6728180680736333818969675)
              ·
                refine ⟨10092271021104500728454513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728180680736333818969675 10092271021104500728454513)
                ·
                  refine ⟨7569203265828375546340885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10092271021104500728454513 7569203265828375546340885)
                  ·
                    refine ⟨354806403085705103734729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7569203265828375546340885 354806403085705103734729)
                    ·
                      rfl

theorem cell23_2072949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2072949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072949 prefixEnd_2072949 := by exact prefixLift 2072949
  have htrace : WordTrace (prefixWord ++ tailWord_2072949) baseStart_2072949 baseEnd_2072949 := by
    simpa [prefixWord, tailWord_2072949, baseEnd_2072949] using wordTrace_append hprefix tailTrace_2072949
  have hstable : (prefixWord ++ tailWord_2072949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072949).length < 2 ^ (prefixWord ++ tailWord_2072949).sum := by decide
  have hdescent : baseEnd_2072949 < baseStart_2072949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072950 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2072950 : Nat := 118140960795 + 2072950 * 2 ^ 59
def prefixEnd_2072950 : Nat := 4983230072969 + 3 ^ 40 * 2072950 * 2
def baseEnd_2072950 : Nat := 1064419722737769807291683

theorem tailTrace_2072950 : CollatzResearch.WordTrace tailWord_2072950 prefixEnd_2072950 1064419722737769807291683 := by
  unfold tailWord_2072950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725418615003978532450519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50404465226709104346138869 4725418615003978532450519)
  ·
    refine ⟨7088127922505967798675779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4725418615003978532450519 7088127922505967798675779)
    ·
      refine ⟨10632191883758951698013669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088127922505967798675779 10632191883758951698013669)
      ·
        refine ⟨1993535978204803443377563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10632191883758951698013669 1993535978204803443377563)
        ·
          refine ⟨2990303967307205165066345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993535978204803443377563 2990303967307205165066345)
          ·
            refine ⟨2242727975480403873799759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2990303967307205165066345 2242727975480403873799759)
            ·
              refine ⟨3364091963220605810699639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242727975480403873799759 3364091963220605810699639)
              ·
                refine ⟨5046137944830908716049459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364091963220605810699639 5046137944830908716049459)
                ·
                  refine ⟨7569206917246363074074189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046137944830908716049459 7569206917246363074074189)
                  ·
                    refine ⟨2838452593967386152777821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7569206917246363074074189 2838452593967386152777821)
                    ·
                      refine ⟨1064419722737769807291683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2838452593967386152777821 1064419722737769807291683)
                      ·
                        rfl

theorem cell23_2072950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2072950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072950 prefixEnd_2072950 := by exact prefixLift 2072950
  have htrace : WordTrace (prefixWord ++ tailWord_2072950) baseStart_2072950 baseEnd_2072950 := by
    simpa [prefixWord, tailWord_2072950, baseEnd_2072950] using wordTrace_append hprefix tailTrace_2072950
  have hstable : (prefixWord ++ tailWord_2072950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072950).length < 2 ^ (prefixWord ++ tailWord_2072950).sum := by decide
  have hdescent : baseEnd_2072950 < baseStart_2072950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2072990 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_2072990 : Nat := 118140960795 + 2072990 * 2 ^ 59
def prefixEnd_2072990 : Nat := 4983230072969 + 3 ^ 40 * 2072990 * 2
def baseEnd_2072990 : Nat := 1064440261963949650791499

theorem tailTrace_2072990 : CollatzResearch.WordTrace tailWord_2072990 prefixEnd_2072990 1064440261963949650791499 := by
  unfold tailWord_2072990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451019594989842918833053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50405437839945828900442949 9451019594989842918833053)
  ·
    refine ⟨3544132348121191094562395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9451019594989842918833053 3544132348121191094562395)
    ·
      refine ⟨5316198522181786641843593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3544132348121191094562395 5316198522181786641843593)
      ·
        refine ⟨3987148891636339981382695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5316198522181786641843593 3987148891636339981382695)
        ·
          refine ⟨5980723337454509972074043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3987148891636339981382695 5980723337454509972074043)
          ·
            refine ⟨8971085006181764958111065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980723337454509972074043 8971085006181764958111065)
            ·
              refine ⟨6728313754636323718583299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8971085006181764958111065 6728313754636323718583299)
              ·
                refine ⟨10092470631954485577874949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728313754636323718583299 10092470631954485577874949)
                ·
                  refine ⟨1892338243491466045851553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10092470631954485577874949 1892338243491466045851553)
                  ·
                    refine ⟨1419253682618599534388665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892338243491466045851553 1419253682618599534388665)
                    ·
                      refine ⟨1064440261963949650791499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419253682618599534388665 1064440261963949650791499)
                      ·
                        rfl

theorem cell23_2072990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_2072990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2072990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2072990 prefixEnd_2072990 := by exact prefixLift 2072990
  have htrace : WordTrace (prefixWord ++ tailWord_2072990) baseStart_2072990 baseEnd_2072990 := by
    simpa [prefixWord, tailWord_2072990, baseEnd_2072990] using wordTrace_append hprefix tailTrace_2072990
  have hstable : (prefixWord ++ tailWord_2072990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2072990).length < 2 ^ (prefixWord ++ tailWord_2072990).sum := by decide
  have hdescent : baseEnd_2072990 < baseStart_2072990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2072990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073096 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_2073096 : Nat := 118140960795 + 2073096 * 2 ^ 59
def prefixEnd_2073096 : Nat := 4983230072969 + 3 ^ 40 * 2073096 * 2
def baseEnd_2073096 : Nat := 1064494690913326236066011

theorem tailTrace_2073096 : CollatzResearch.WordTrace tailWord_2073096 prefixEnd_2073096 1064494690913326236066011 := by
  unfold tailWord_2073096
  simp only [CollatzResearch.WordTrace]
  refine ⟨37806011448767361727011571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50408015265023148969348761 37806011448767361727011571)
  ·
    refine ⟨56709017173151042590517357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37806011448767361727011571 56709017173151042590517357)
    ·
      refine ⟨21265881439931640971444009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56709017173151042590517357 21265881439931640971444009)
      ·
        refine ⟨15949411079948730728583007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21265881439931640971444009 15949411079948730728583007)
        ·
          refine ⟨23924116619923096092874511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15949411079948730728583007 23924116619923096092874511)
          ·
            refine ⟨35886174929884644139311767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23924116619923096092874511 35886174929884644139311767)
            ·
              refine ⟨53829262394826966208967651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35886174929884644139311767 53829262394826966208967651)
              ·
                refine ⟨80743893592240449313451477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53829262394826966208967651 80743893592240449313451477)
                ·
                  refine ⟨1892435006068135530784019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 80743893592240449313451477 1892435006068135530784019)
                  ·
                    refine ⟨2838652509102203296176029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892435006068135530784019 2838652509102203296176029)
                    ·
                      refine ⟨1064494690913326236066011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2838652509102203296176029 1064494690913326236066011)
                      ·
                        rfl

theorem cell23_2073096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_2073096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073096 prefixEnd_2073096 := by exact prefixLift 2073096
  have htrace : WordTrace (prefixWord ++ tailWord_2073096) baseStart_2073096 baseEnd_2073096 := by
    simpa [prefixWord, tailWord_2073096, baseEnd_2073096] using wordTrace_append hprefix tailTrace_2073096
  have hstable : (prefixWord ++ tailWord_2073096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073096).length < 2 ^ (prefixWord ++ tailWord_2073096).sum := by decide
  have hdescent : baseEnd_2073096 < baseStart_2073096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073136 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 4]
def baseStart_2073136 : Nat := 118140960795 + 2073136 * 2 ^ 59
def prefixEnd_2073136 : Nat := 4983230072969 + 3 ^ 40 * 2073136 * 2
def baseEnd_2073136 : Nat := 1064515230139506079565827

theorem tailTrace_2073136 : CollatzResearch.WordTrace tailWord_2073136 prefixEnd_2073136 1064515230139506079565827 := by
  unfold tailWord_2073136
  simp only [CollatzResearch.WordTrace]
  refine ⟨37806740908694905142739631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50408987878259873523652841 37806740908694905142739631)
  ·
    refine ⟨56710111363042357714109447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37806740908694905142739631 56710111363042357714109447)
    ·
      refine ⟨85065167044563536571164171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56710111363042357714109447 85065167044563536571164171)
      ·
        refine ⟨127597750566845304856746257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85065167044563536571164171 127597750566845304856746257)
        ·
          refine ⟨95698312925133978642559693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127597750566845304856746257 95698312925133978642559693)
          ·
            refine ⟨35886867346925241990959885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95698312925133978642559693 35886867346925241990959885)
            ·
              refine ⟨13457575255096965746609957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35886867346925241990959885 13457575255096965746609957)
              ·
                refine ⟨2523295360330681077489367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13457575255096965746609957 2523295360330681077489367)
                ·
                  refine ⟨3784943040496021616234051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523295360330681077489367 3784943040496021616234051)
                  ·
                    refine ⟨5677414560744032424351077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3784943040496021616234051 5677414560744032424351077)
                    ·
                      refine ⟨1064515230139506079565827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5677414560744032424351077 1064515230139506079565827)
                      ·
                        rfl

theorem cell23_2073136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 4].length) (baseStart_2073136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073136 prefixEnd_2073136 := by exact prefixLift 2073136
  have htrace : WordTrace (prefixWord ++ tailWord_2073136) baseStart_2073136 baseEnd_2073136 := by
    simpa [prefixWord, tailWord_2073136, baseEnd_2073136] using wordTrace_append hprefix tailTrace_2073136
  have hstable : (prefixWord ++ tailWord_2073136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073136).length < 2 ^ (prefixWord ++ tailWord_2073136).sum := by decide
  have hdescent : baseEnd_2073136 < baseStart_2073136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073139 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 5]
def baseStart_2073139 : Nat := 118140960795 + 2073139 * 2 ^ 59
def prefixEnd_2073139 : Nat := 4983230072969 + 3 ^ 40 * 2073139 * 2
def baseEnd_2073139 : Nat := 1064516770581469567828313

theorem tailTrace_2073139 : CollatzResearch.WordTrace tailWord_2073139 prefixEnd_2073139 1064516770581469567828313 := by
  unfold tailWord_2073139
  simp only [CollatzResearch.WordTrace]
  refine ⟨75613591236378941797838471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50409060824252627865225647 75613591236378941797838471)
  ·
    refine ⟨113420386854568412696757707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75613591236378941797838471 113420386854568412696757707)
    ·
      refine ⟨170130580281852619045136561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113420386854568412696757707 170130580281852619045136561)
      ·
        refine ⟨127597935211389464283852421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170130580281852619045136561 127597935211389464283852421)
        ·
          refine ⟨23924612852135524553222329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127597935211389464283852421 23924612852135524553222329)
          ·
            refine ⟨17943459639101643414916747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23924612852135524553222329 17943459639101643414916747)
            ·
              refine ⟨26915189458652465122375121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17943459639101643414916747 26915189458652465122375121)
              ·
                refine ⟨20186392093989348841781341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26915189458652465122375121 20186392093989348841781341)
                ·
                  refine ⟨7569897035246005815668003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20186392093989348841781341 7569897035246005815668003)
                  ·
                    refine ⟨11354845552869008723502005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7569897035246005815668003 11354845552869008723502005)
                    ·
                      refine ⟨1064516770581469567828313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11354845552869008723502005 1064516770581469567828313)
                      ·
                        rfl

theorem cell23_2073139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_2073139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073139 prefixEnd_2073139 := by exact prefixLift 2073139
  have htrace : WordTrace (prefixWord ++ tailWord_2073139) baseStart_2073139 baseEnd_2073139 := by
    simpa [prefixWord, tailWord_2073139, baseEnd_2073139] using wordTrace_append hprefix tailTrace_2073139
  have hstable : (prefixWord ++ tailWord_2073139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073139).length < 2 ^ (prefixWord ++ tailWord_2073139).sum := by decide
  have hdescent : baseEnd_2073139 < baseStart_2073139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073146 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_2073146 : Nat := 118140960795 + 2073146 * 2 ^ 59
def prefixEnd_2073146 : Nat := 4983230072969 + 3 ^ 40 * 2073146 * 2
def baseEnd_2073146 : Nat := 354840121648683680146927

theorem tailTrace_2073146 : CollatzResearch.WordTrace tailWord_2073146 prefixEnd_2073146 354840121648683680146927 := by
  unfold tailWord_2073146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18903461636838395498335823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50409231031569054662228861 18903461636838395498335823)
  ·
    refine ⟨28355192455257593247503735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18903461636838395498335823 28355192455257593247503735)
    ·
      refine ⟨42532788682886389871255603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28355192455257593247503735 42532788682886389871255603)
      ·
        refine ⟨63799183024329584806883405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42532788682886389871255603 63799183024329584806883405)
        ·
          refine ⟨23924693634123594302581277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63799183024329584806883405 23924693634123594302581277)
          ·
            refine ⟨8971760112796347863467979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23924693634123594302581277 8971760112796347863467979)
            ·
              refine ⟨13457640169194521795201969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8971760112796347863467979 13457640169194521795201969)
              ·
                refine ⟨10093230126895891346401477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13457640169194521795201969 10093230126895891346401477)
                ·
                  refine ⟨1892480648792979627450277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10093230126895891346401477 1892480648792979627450277)
                  ·
                    refine ⟨354840121648683680146927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1892480648792979627450277 354840121648683680146927)
                    ·
                      rfl

theorem cell23_2073146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_2073146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073146 prefixEnd_2073146 := by exact prefixLift 2073146
  have htrace : WordTrace (prefixWord ++ tailWord_2073146) baseStart_2073146 baseEnd_2073146 := by
    simpa [prefixWord, tailWord_2073146, baseEnd_2073146] using wordTrace_append hprefix tailTrace_2073146
  have hstable : (prefixWord ++ tailWord_2073146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073146).length < 2 ^ (prefixWord ++ tailWord_2073146).sum := by decide
  have hdescent : baseEnd_2073146 < baseStart_2073146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073153 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2073153 : Nat := 118140960795 + 2073153 * 2 ^ 59
def prefixEnd_2073153 : Nat := 4983230072969 + 3 ^ 40 * 2073153 * 2
def baseEnd_2073153 : Nat := 1064523959310632513053249

theorem tailTrace_2073153 : CollatzResearch.WordTrace tailWord_2073153 prefixEnd_2073153 1064523959310632513053249 := by
  unfold tailWord_2073153
  simp only [CollatzResearch.WordTrace]
  refine ⟨75614101858328222188848113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50409401238885481459232075 75614101858328222188848113)
  ·
    refine ⟨56710576393746166641636085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75614101858328222188848113 56710576393746166641636085)
    ·
      refine ⟨5316616536913703122653383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56710576393746166641636085 5316616536913703122653383)
      ·
        refine ⟨7974924805370554683980075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316616536913703122653383 7974924805370554683980075)
        ·
          refine ⟨11962387208055832025970113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974924805370554683980075 11962387208055832025970113)
          ·
            refine ⟨8971790406041874019477585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11962387208055832025970113 8971790406041874019477585)
            ·
              refine ⟨6728842804531405514608189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8971790406041874019477585 6728842804531405514608189)
              ·
                refine ⟨2523316051699277067978071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6728842804531405514608189 2523316051699277067978071)
                ·
                  refine ⟨3784974077548915601967107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523316051699277067978071 3784974077548915601967107)
                  ·
                    refine ⟨5677461116323373402950661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3784974077548915601967107 5677461116323373402950661)
                    ·
                      refine ⟨1064523959310632513053249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5677461116323373402950661 1064523959310632513053249)
                      ·
                        rfl

theorem cell23_2073153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2073153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073153 prefixEnd_2073153 := by exact prefixLift 2073153
  have htrace : WordTrace (prefixWord ++ tailWord_2073153) baseStart_2073153 baseEnd_2073153 := by
    simpa [prefixWord, tailWord_2073153, baseEnd_2073153] using wordTrace_append hprefix tailTrace_2073153
  have hstable : (prefixWord ++ tailWord_2073153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073153).length < 2 ^ (prefixWord ++ tailWord_2073153).sum := by decide
  have hdescent : baseEnd_2073153 < baseStart_2073153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073159 : List Nat := [1, 1, 4, 1, 4, 1, 11]
def baseStart_2073159 : Nat := 118140960795 + 2073159 * 2 ^ 59
def prefixEnd_2073159 : Nat := 4983230072969 + 3 ^ 40 * 2073159 * 2
def baseEnd_2073159 : Nat := 13142309138204438142941

theorem tailTrace_2073159 : CollatzResearch.WordTrace tailWord_2073159 prefixEnd_2073159 13142309138204438142941 := by
  unfold tailWord_2073159
  simp only [CollatzResearch.WordTrace]
  refine ⟨75614320696306485213566531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50409547130870990142377687 75614320696306485213566531)
  ·
    refine ⟨113421481044459727820349797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75614320696306485213566531 113421481044459727820349797)
    ·
      refine ⟨21266527695836198966315587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113421481044459727820349797 21266527695836198966315587)
      ·
        refine ⟨31899791543754298449473381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21266527695836198966315587 31899791543754298449473381)
        ·
          refine ⟨5981210914453930959276259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31899791543754298449473381 5981210914453930959276259)
          ·
            refine ⟨8971816371680896438914389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981210914453930959276259 8971816371680896438914389)
            ·
              refine ⟨13142309138204438142941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8971816371680896438914389 13142309138204438142941)
              ·
                rfl

theorem cell23_2073159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 11].length) (baseStart_2073159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073159 prefixEnd_2073159 := by exact prefixLift 2073159
  have htrace : WordTrace (prefixWord ++ tailWord_2073159) baseStart_2073159 baseEnd_2073159 := by
    simpa [prefixWord, tailWord_2073159, baseEnd_2073159] using wordTrace_append hprefix tailTrace_2073159
  have hstable : (prefixWord ++ tailWord_2073159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073159).length < 2 ^ (prefixWord ++ tailWord_2073159).sum := by decide
  have hdescent : baseEnd_2073159 < baseStart_2073159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073180 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2073180 : Nat := 118140960795 + 2073180 * 2 ^ 59
def prefixEnd_2073180 : Nat := 4983230072969 + 3 ^ 40 * 2073180 * 2
def baseEnd_2073180 : Nat := 354845941096101302471875

theorem tailTrace_2073180 : CollatzResearch.WordTrace tailWord_2073180 prefixEnd_2073180 354845941096101302471875 := by
  unfold tailWord_2073180
  simp only [CollatzResearch.WordTrace]
  refine ⟨37807543314615202900040497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50410057752820270533387329 37807543314615202900040497)
  ·
    refine ⟨28355657485961402175030373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37807543314615202900040497 28355657485961402175030373)
    ·
      refine ⟨5316685778617762907818195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28355657485961402175030373 5316685778617762907818195)
      ·
        refine ⟨7975028667926644361727293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316685778617762907818195 7975028667926644361727293)
        ·
          refine ⟨2990635750472491635647735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7975028667926644361727293 2990635750472491635647735)
          ·
            refine ⟨4485953625708737453471603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990635750472491635647735 4485953625708737453471603)
            ·
              refine ⟨6728930438563106180207405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485953625708737453471603 6728930438563106180207405)
              ·
                refine ⟨2523348914461164817577777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6728930438563106180207405 2523348914461164817577777)
                ·
                  refine ⟨1892511685845873613183333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2523348914461164817577777 1892511685845873613183333)
                  ·
                    refine ⟨354845941096101302471875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1892511685845873613183333 354845941096101302471875)
                    ·
                      rfl

theorem cell23_2073180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2073180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073180 prefixEnd_2073180 := by exact prefixLift 2073180
  have htrace : WordTrace (prefixWord ++ tailWord_2073180) baseStart_2073180 baseEnd_2073180 := by
    simpa [prefixWord, tailWord_2073180, baseEnd_2073180] using wordTrace_append hprefix tailTrace_2073180
  have hstable : (prefixWord ++ tailWord_2073180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073180).length < 2 ^ (prefixWord ++ tailWord_2073180).sum := by decide
  have hdescent : baseEnd_2073180 < baseStart_2073180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073199 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_2073199 : Nat := 118140960795 + 2073199 * 2 ^ 59
def prefixEnd_2073199 : Nat := 4983230072969 + 3 ^ 40 * 2073199 * 2
def baseEnd_2073199 : Nat := 1064547579420739333078037

theorem tailTrace_2073199 : CollatzResearch.WordTrace tailWord_2073199 prefixEnd_2073199 1064547579420739333078037 := by
  unfold tailWord_2073199
  simp only [CollatzResearch.WordTrace]
  refine ⟨75615779616161572045022651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50410519744107714696681767 75615779616161572045022651)
  ·
    refine ⟨113423669424242358067533977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75615779616161572045022651 113423669424242358067533977)
    ·
      refine ⟨85067752068181768550650483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113423669424242358067533977 85067752068181768550650483)
      ·
        refine ⟨127601628102272652825975725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85067752068181768550650483 127601628102272652825975725)
        ·
          refine ⟨47850610538352244809740897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127601628102272652825975725 47850610538352244809740897)
          ·
            refine ⟨35887957903764183607305673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47850610538352244809740897 35887957903764183607305673)
            ·
              refine ⟨26915968427823137705479255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35887957903764183607305673 26915968427823137705479255)
              ·
                refine ⟨40373952641734706558218883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26915968427823137705479255 40373952641734706558218883)
                ·
                  refine ⟨60560928962602059837328325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40373952641734706558218883 60560928962602059837328325)
                  ·
                    refine ⟨11355174180487886219499061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60560928962602059837328325 11355174180487886219499061)
                    ·
                      refine ⟨1064547579420739333078037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11355174180487886219499061 1064547579420739333078037)
                      ·
                        rfl

theorem cell23_2073199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_2073199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073199 prefixEnd_2073199 := by exact prefixLift 2073199
  have htrace : WordTrace (prefixWord ++ tailWord_2073199) baseStart_2073199 baseEnd_2073199 := by
    simpa [prefixWord, tailWord_2073199, baseEnd_2073199] using wordTrace_append hprefix tailTrace_2073199
  have hstable : (prefixWord ++ tailWord_2073199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073199).length < 2 ^ (prefixWord ++ tailWord_2073199).sum := by decide
  have hdescent : baseEnd_2073199 < baseStart_2073199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073220 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_2073220 : Nat := 118140960795 + 2073220 * 2 ^ 59
def prefixEnd_2073220 : Nat := 4983230072969 + 3 ^ 40 * 2073220 * 2
def baseEnd_2073220 : Nat := 1064558362514483750915441

theorem tailTrace_2073220 : CollatzResearch.WordTrace tailWord_2073220 prefixEnd_2073220 1064558362514483750915441 := by
  unfold tailWord_2073220
  simp only [CollatzResearch.WordTrace]
  refine ⟨37808272774542746315768557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50411030366056995087691409 37808272774542746315768557)
  ·
    refine ⟨14178102290453529868413209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37808272774542746315768557 14178102290453529868413209)
    ·
      refine ⟨10633576717840147401309907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14178102290453529868413209 10633576717840147401309907)
      ·
        refine ⟨15950365076760221101964861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633576717840147401309907 15950365076760221101964861)
        ·
          refine ⟨5981386903785082913236823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15950365076760221101964861 5981386903785082913236823)
          ·
            refine ⟨8972080355677624369855235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981386903785082913236823 8972080355677624369855235)
            ·
              refine ⟨13458120533516436554782853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972080355677624369855235 13458120533516436554782853)
              ·
                refine ⟨2523397600034331854021785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13458120533516436554782853 2523397600034331854021785)
                ·
                  refine ⟨1892548200025748890516339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2523397600034331854021785 1892548200025748890516339)
                  ·
                    refine ⟨2838822300038623335774509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892548200025748890516339 2838822300038623335774509)
                    ·
                      refine ⟨1064558362514483750915441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2838822300038623335774509 1064558362514483750915441)
                      ·
                        rfl

theorem cell23_2073220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_2073220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073220 prefixEnd_2073220 := by exact prefixLift 2073220
  have htrace : WordTrace (prefixWord ++ tailWord_2073220) baseStart_2073220 baseEnd_2073220 := by
    simpa [prefixWord, tailWord_2073220, baseEnd_2073220] using wordTrace_append hprefix tailTrace_2073220
  have hstable : (prefixWord ++ tailWord_2073220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073220).length < 2 ^ (prefixWord ++ tailWord_2073220).sum := by decide
  have hdescent : baseEnd_2073220 < baseStart_2073220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073277 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_2073277 : Nat := 118140960795 + 2073277 * 2 ^ 59
def prefixEnd_2073277 : Nat := 4983230072969 + 3 ^ 40 * 2073277 * 2
def baseEnd_2073277 : Nat := 1064587630911790027902679

theorem tailTrace_2073277 : CollatzResearch.WordTrace tailWord_2073277 prefixEnd_2073277 1064587630911790027902679 := by
  unfold tailWord_2073277
  simp only [CollatzResearch.WordTrace]
  refine ⟨75618624509878991366362085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50412416339919327577574723 75618624509878991366362085)
  ·
    refine ⟨14178492095602310881192891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75618624509878991366362085 14178492095602310881192891)
    ·
      refine ⟨21267738143403466321789337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14178492095602310881192891 21267738143403466321789337)
      ·
        refine ⟨15950803607552599741342003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21267738143403466321789337 15950803607552599741342003)
        ·
          refine ⟨23926205411328899612013005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15950803607552599741342003 23926205411328899612013005)
          ·
            refine ⟨8972327029248337354504877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23926205411328899612013005 8972327029248337354504877)
            ·
              refine ⟨3364622635968126507939329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8972327029248337354504877 3364622635968126507939329)
              ·
                refine ⟨2523466976976094880954497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3364622635968126507939329 2523466976976094880954497)
                ·
                  refine ⟨1892600232732071160715873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2523466976976094880954497 1892600232732071160715873)
                  ·
                    refine ⟨1419450174549053370536905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892600232732071160715873 1419450174549053370536905)
                    ·
                      refine ⟨1064587630911790027902679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419450174549053370536905 1064587630911790027902679)
                      ·
                        rfl

theorem cell23_2073277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_2073277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073277 prefixEnd_2073277 := by exact prefixLift 2073277
  have htrace : WordTrace (prefixWord ++ tailWord_2073277) baseStart_2073277 baseEnd_2073277 := by
    simpa [prefixWord, tailWord_2073277, baseEnd_2073277] using wordTrace_append hprefix tailTrace_2073277
  have hstable : (prefixWord ++ tailWord_2073277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073277).length < 2 ^ (prefixWord ++ tailWord_2073277).sum := by decide
  have hdescent : baseEnd_2073277 < baseStart_2073277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073294 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2]
def baseStart_2073294 : Nat := 118140960795 + 2073294 * 2 ^ 59
def prefixEnd_2073294 : Nat := 4983230072969 + 3 ^ 40 * 2073294 * 2
def baseEnd_2073294 : Nat := 1064596360082916461390101

theorem tailTrace_2073294 : CollatzResearch.WordTrace tailWord_2073294 prefixEnd_2073294 1064596360082916461390101 := by
  unfold tailWord_2073294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9452405568852175408716367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50412829700544935513153957 9452405568852175408716367)
  ·
    refine ⟨14178608353278263113074551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9452405568852175408716367 14178608353278263113074551)
    ·
      refine ⟨21267912529917394669611827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14178608353278263113074551 21267912529917394669611827)
      ·
        refine ⟨31901868794876092004417741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21267912529917394669611827 31901868794876092004417741)
        ·
          refine ⟨11963200798078534501656653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31901868794876092004417741 11963200798078534501656653)
          ·
            refine ⟨4486200299279450438121245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11963200798078534501656653 4486200299279450438121245)
            ·
              refine ⟨1682325112229793914295467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4486200299279450438121245 1682325112229793914295467)
              ·
                refine ⟨2523487668344690871443201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682325112229793914295467 2523487668344690871443201)
                ·
                  refine ⟨1892615751258518153582401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2523487668344690871443201 1892615751258518153582401)
                  ·
                    refine ⟨1419461813443888615186801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892615751258518153582401 1419461813443888615186801)
                    ·
                      refine ⟨1064596360082916461390101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419461813443888615186801 1064596360082916461390101)
                      ·
                        rfl

theorem cell23_2073294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_2073294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073294 prefixEnd_2073294 := by exact prefixLift 2073294
  have htrace : WordTrace (prefixWord ++ tailWord_2073294) baseStart_2073294 baseEnd_2073294 := by
    simpa [prefixWord, tailWord_2073294, baseEnd_2073294] using wordTrace_append hprefix tailTrace_2073294
  have hstable : (prefixWord ++ tailWord_2073294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073294).length < 2 ^ (prefixWord ++ tailWord_2073294).sum := by decide
  have hdescent : baseEnd_2073294 < baseStart_2073294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073370 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_2073370 : Nat := 118140960795 + 2073370 * 2 ^ 59
def prefixEnd_2073370 : Nat := 4983230072969 + 3 ^ 40 * 2073370 * 2
def baseEnd_2073370 : Nat := 1064635384612658164039751

theorem tailTrace_2073370 : CollatzResearch.WordTrace tailWord_2073370 prefixEnd_2073370 1064635384612658164039751 := by
  unfold tailWord_2073370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18905504124635517062374391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50414677665694712166331709 18905504124635517062374391)
  ·
    refine ⟨28358256186953275593561587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18905504124635517062374391 28358256186953275593561587)
    ·
      refine ⟨42537384280429913390342381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28358256186953275593561587 42537384280429913390342381)
      ·
        refine ⟨15951519105161217521378393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42537384280429913390342381 15951519105161217521378393)
        ·
          refine ⟨11963639328870913141033795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15951519105161217521378393 11963639328870913141033795)
          ·
            refine ⟨17945458993306369711550693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11963639328870913141033795 17945458993306369711550693)
            ·
              refine ⟨3364773561244944320915755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17945458993306369711550693 3364773561244944320915755)
              ·
                refine ⟨5047160341867416481373633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364773561244944320915755 5047160341867416481373633)
                ·
                  refine ⟨3785370256400562361030225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5047160341867416481373633 3785370256400562361030225)
                  ·
                    refine ⟨2839027692300421770772669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3785370256400562361030225 2839027692300421770772669)
                    ·
                      refine ⟨1064635384612658164039751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2839027692300421770772669 1064635384612658164039751)
                      ·
                        rfl

theorem cell23_2073370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_2073370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073370 prefixEnd_2073370 := by exact prefixLift 2073370
  have htrace : WordTrace (prefixWord ++ tailWord_2073370) baseStart_2073370 baseEnd_2073370 := by
    simpa [prefixWord, tailWord_2073370, baseEnd_2073370] using wordTrace_append hprefix tailTrace_2073370
  have hstable : (prefixWord ++ tailWord_2073370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073370).length < 2 ^ (prefixWord ++ tailWord_2073370).sum := by decide
  have hdescent : baseEnd_2073370 < baseStart_2073370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073390 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_2073390 : Nat := 118140960795 + 2073390 * 2 ^ 59
def prefixEnd_2073390 : Nat := 4983230072969 + 3 ^ 40 * 2073390 * 2
def baseEnd_2073390 : Nat := 118293961580638676198851

theorem tailTrace_2073390 : CollatzResearch.WordTrace tailWord_2073390 prefixEnd_2073390 118293961580638676198851 := by
  unfold tailWord_2073390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9452843244808701458153203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50415163972313074443483749 9452843244808701458153203)
  ·
    refine ⟨14179264867213052187229805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9452843244808701458153203 14179264867213052187229805)
    ·
      refine ⟨5317224325204894570211177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14179264867213052187229805 5317224325204894570211177)
      ·
        refine ⟨3987918243903670927658383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5317224325204894570211177 3987918243903670927658383)
        ·
          refine ⟨5981877365855506391487575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3987918243903670927658383 5981877365855506391487575)
          ·
            refine ⟨8972816048783259587231363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981877365855506391487575 8972816048783259587231363)
            ·
              refine ⟨13459224073174889380847045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972816048783259587231363 13459224073174889380847045)
              ·
                refine ⟨2523604513720291758908821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13459224073174889380847045 2523604513720291758908821)
                ·
                  refine ⟨118293961580638676198851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2523604513720291758908821 118293961580638676198851)
                  ·
                    rfl

theorem cell23_2073390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_2073390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073390 prefixEnd_2073390 := by exact prefixLift 2073390
  have htrace : WordTrace (prefixWord ++ tailWord_2073390) baseStart_2073390 baseEnd_2073390 := by
    simpa [prefixWord, tailWord_2073390, baseEnd_2073390] using wordTrace_append hprefix tailTrace_2073390
  have hstable : (prefixWord ++ tailWord_2073390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073390).length < 2 ^ (prefixWord ++ tailWord_2073390).sum := by decide
  have hdescent : baseEnd_2073390 < baseStart_2073390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073400 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_2073400 : Nat := 118140960795 + 2073400 * 2 ^ 59
def prefixEnd_2073400 : Nat := 4983230072969 + 3 ^ 40 * 2073400 * 2
def baseEnd_2073400 : Nat := 1064650789032293046664613

theorem tailTrace_2073400 : CollatzResearch.WordTrace tailWord_2073400 prefixEnd_2073400 1064650789032293046664613 := by
  unfold tailWord_2073400
  simp only [CollatzResearch.WordTrace]
  refine ⟨37811555344216691686544827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50415407125622255582059769 37811555344216691686544827)
  ·
    refine ⟨56717333016325037529817241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37811555344216691686544827 56717333016325037529817241)
    ·
      refine ⟨42537999762243778147362931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56717333016325037529817241 42537999762243778147362931)
      ·
        refine ⟨63806999643365667221044397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42537999762243778147362931 63806999643365667221044397)
        ·
          refine ⟨23927624866262125207891649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63806999643365667221044397 23927624866262125207891649)
          ·
            refine ⟨17945718649696593905918737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23927624866262125207891649 17945718649696593905918737)
            ·
              refine ⟨13459288987272445429439053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17945718649696593905918737 13459288987272445429439053)
              ·
                refine ⟨5047233370227167036039645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13459288987272445429439053 5047233370227167036039645)
                ·
                  refine ⟨1892712513835187638514867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5047233370227167036039645 1892712513835187638514867)
                  ·
                    refine ⟨2839068770752781457772301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892712513835187638514867 2839068770752781457772301)
                    ·
                      refine ⟨1064650789032293046664613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2839068770752781457772301 1064650789032293046664613)
                      ·
                        rfl

theorem cell23_2073400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_2073400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073400 prefixEnd_2073400 := by exact prefixLift 2073400
  have htrace : WordTrace (prefixWord ++ tailWord_2073400) baseStart_2073400 baseEnd_2073400 := by
    simpa [prefixWord, tailWord_2073400, baseEnd_2073400] using wordTrace_append hprefix tailTrace_2073400
  have hstable : (prefixWord ++ tailWord_2073400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073400).length < 2 ^ (prefixWord ++ tailWord_2073400).sum := by decide
  have hdescent : baseEnd_2073400 < baseStart_2073400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073421 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2073421 : Nat := 118140960795 + 2073421 * 2 ^ 59
def prefixEnd_2073421 : Nat := 4983230072969 + 3 ^ 40 * 2073421 * 2
def baseEnd_2073421 : Nat := 1064661572126037464502017

theorem tailTrace_2073421 : CollatzResearch.WordTrace tailWord_2073421 prefixEnd_2073421 1064661572126037464502017 := by
  unfold tailWord_2073421
  simp only [CollatzResearch.WordTrace]
  refine ⟨75623876621357303959604117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50415917747571535973069411 75623876621357303959604117)
  ·
    refine ⟨3544869216626123623106443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75623876621357303959604117 3544869216626123623106443)
    ·
      refine ⟨5317303824939185434659665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3544869216626123623106443 5317303824939185434659665)
      ·
        refine ⟨3987977868704389075994749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5317303824939185434659665 3987977868704389075994749)
        ·
          refine ⟨1495491700764145903498031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3987977868704389075994749 1495491700764145903498031)
          ·
            refine ⟨2243237551146218855247047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495491700764145903498031 2243237551146218855247047)
            ·
              refine ⟨3364856326719328282870571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243237551146218855247047 3364856326719328282870571)
              ·
                refine ⟨5047284490078992424305857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364856326719328282870571 5047284490078992424305857)
                ·
                  refine ⟨3785463367559244318229393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5047284490078992424305857 3785463367559244318229393)
                  ·
                    refine ⟨2839097525669433238672045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3785463367559244318229393 2839097525669433238672045)
                    ·
                      refine ⟨1064661572126037464502017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2839097525669433238672045 1064661572126037464502017)
                      ·
                        rfl

theorem cell23_2073421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2073421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073421 prefixEnd_2073421 := by exact prefixLift 2073421
  have htrace : WordTrace (prefixWord ++ tailWord_2073421) baseStart_2073421 baseEnd_2073421 := by
    simpa [prefixWord, tailWord_2073421, baseEnd_2073421] using wordTrace_append hprefix tailTrace_2073421
  have hstable : (prefixWord ++ tailWord_2073421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073421).length < 2 ^ (prefixWord ++ tailWord_2073421).sum := by decide
  have hdescent : baseEnd_2073421 < baseStart_2073421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073433 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 1, 6]
def baseStart_2073433 : Nat := 118140960795 + 2073433 * 2 ^ 59
def prefixEnd_2073433 : Nat := 4983230072969 + 3 ^ 40 * 2073433 * 2
def baseEnd_2073433 : Nat := 354889244631297139183987

theorem tailTrace_2073433 : CollatzResearch.WordTrace tailWord_2073433 prefixEnd_2073433 354889244631297139183987 := by
  unfold tailWord_2073433
  simp only [CollatzResearch.WordTrace]
  refine ⟨75624314297313830009040953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50416209531542553339360635 75624314297313830009040953)
  ·
    refine ⟨56718235722985372506780715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75624314297313830009040953 56718235722985372506780715)
    ·
      refine ⟨85077353584478058760171073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56718235722985372506780715 85077353584478058760171073)
      ·
        refine ⟨63808015188358544070128305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85077353584478058760171073 63808015188358544070128305)
        ·
          refine ⟨47856011391268908052596229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63808015188358544070128305 47856011391268908052596229)
          ·
            refine ⟨8973002135862920259861793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47856011391268908052596229 8973002135862920259861793)
            ·
              refine ⟨6729751601897190194896345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973002135862920259861793 6729751601897190194896345)
              ·
                refine ⟨5047313701422892646172259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6729751601897190194896345 5047313701422892646172259)
                ·
                  refine ⟨7570970552134338969258389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047313701422892646172259 7570970552134338969258389)
                  ·
                    refine ⟨354889244631297139183987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7570970552134338969258389 354889244631297139183987)
                    ·
                      rfl

theorem cell23_2073433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_2073433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073433 prefixEnd_2073433 := by exact prefixLift 2073433
  have htrace : WordTrace (prefixWord ++ tailWord_2073433) baseStart_2073433 baseEnd_2073433 := by
    simpa [prefixWord, tailWord_2073433, baseEnd_2073433] using wordTrace_append hprefix tailTrace_2073433
  have hstable : (prefixWord ++ tailWord_2073433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073433).length < 2 ^ (prefixWord ++ tailWord_2073433).sum := by decide
  have hdescent : baseEnd_2073433 < baseStart_2073433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073434 : List Nat := [3, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3]
def baseStart_2073434 : Nat := 118140960795 + 2073434 * 2 ^ 59
def prefixEnd_2073434 : Nat := 4983230072969 + 3 ^ 40 * 2073434 * 2
def baseEnd_2073434 : Nat := 1064668247374545913639457

theorem tailTrace_2073434 : CollatzResearch.WordTrace tailWord_2073434 prefixEnd_2073434 1064668247374545913639457 := by
  unfold tailWord_2073434
  simp only [CollatzResearch.WordTrace]
  refine ⟨18906087692577551794956839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50416233846873471453218237 18906087692577551794956839)
  ·
    refine ⟨28359131538866327692435259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18906087692577551794956839 28359131538866327692435259)
    ·
      refine ⟨42538697308299491538652889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28359131538866327692435259 42538697308299491538652889)
      ·
        refine ⟨31904022981224618653989667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42538697308299491538652889 31904022981224618653989667)
        ·
          refine ⟨47856034471836927980984501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31904022981224618653989667 47856034471836927980984501)
          ·
            refine ⟨4486503231734711998217297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47856034471836927980984501 4486503231734711998217297)
            ·
              refine ⟨3364877423801033998662973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4486503231734711998217297 3364877423801033998662973)
              ·
                refine ⟨1261829033925387749498615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3364877423801033998662973 1261829033925387749498615)
                ·
                  refine ⟨1892743550888081624247923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1261829033925387749498615 1892743550888081624247923)
                  ·
                    refine ⟨2839115326332122436371885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1892743550888081624247923 2839115326332122436371885)
                    ·
                      refine ⟨1064668247374545913639457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2839115326332122436371885 1064668247374545913639457)
                      ·
                        rfl

theorem cell23_2073434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_2073434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073434 prefixEnd_2073434 := by exact prefixLift 2073434
  have htrace : WordTrace (prefixWord ++ tailWord_2073434) baseStart_2073434 baseEnd_2073434 := by
    simpa [prefixWord, tailWord_2073434, baseEnd_2073434] using wordTrace_append hprefix tailTrace_2073434
  have hstable : (prefixWord ++ tailWord_2073434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073434).length < 2 ^ (prefixWord ++ tailWord_2073434).sum := by decide
  have hdescent : baseEnd_2073434 < baseStart_2073434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073440 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 4]
def baseStart_2073440 : Nat := 118140960795 + 2073440 * 2 ^ 59
def prefixEnd_2073440 : Nat := 4983230072969 + 3 ^ 40 * 2073440 * 2
def baseEnd_2073440 : Nat := 1064671328258472890164429

theorem tailTrace_2073440 : CollatzResearch.WordTrace tailWord_2073440 prefixEnd_2073440 1064671328258472890164429 := by
  unfold tailWord_2073440
  simp only [CollatzResearch.WordTrace]
  refine ⟨37812284804144235102272887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50416379738858980136363849 37812284804144235102272887)
  ·
    refine ⟨56718427206216352653409331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37812284804144235102272887 56718427206216352653409331)
    ·
      refine ⟨85077640809324528980113997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56718427206216352653409331 85077640809324528980113997)
      ·
        refine ⟨31904115303496698367542749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85077640809324528980113997 31904115303496698367542749)
        ·
          refine ⟨11964043238811261887828531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31904115303496698367542749 11964043238811261887828531)
          ·
            refine ⟨17946064858216892831742797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11964043238811261887828531 17946064858216892831742797)
            ·
              refine ⟨6729774321831334811903549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17946064858216892831742797 6729774321831334811903549)
              ·
                refine ⟨2523665370686750554463831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6729774321831334811903549 2523665370686750554463831)
                ·
                  refine ⟨3785498056030125831695747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523665370686750554463831 3785498056030125831695747)
                  ·
                    refine ⟨5678247084045188747543621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3785498056030125831695747 5678247084045188747543621)
                    ·
                      refine ⟨1064671328258472890164429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5678247084045188747543621 1064671328258472890164429)
                      ·
                        rfl

theorem cell23_2073440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_2073440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073440 prefixEnd_2073440 := by exact prefixLift 2073440
  have htrace : WordTrace (prefixWord ++ tailWord_2073440) baseStart_2073440 baseEnd_2073440 := by
    simpa [prefixWord, tailWord_2073440, baseEnd_2073440] using wordTrace_append hprefix tailTrace_2073440
  have hstable : (prefixWord ++ tailWord_2073440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073440).length < 2 ^ (prefixWord ++ tailWord_2073440).sum := by decide
  have hdescent : baseEnd_2073440 < baseStart_2073440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073453 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2073453 : Nat := 118140960795 + 2073453 * 2 ^ 59
def prefixEnd_2073453 : Nat := 4983230072969 + 3 ^ 40 * 2073453 * 2
def baseEnd_2073453 : Nat := 1064678003506981339301869

theorem tailTrace_2073453 : CollatzResearch.WordTrace tailWord_2073453 prefixEnd_2073453 1064678003506981339301869 := by
  unfold tailWord_2073453
  simp only [CollatzResearch.WordTrace]
  refine ⟨75625043757241373424769013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50416695838160915616512675 75625043757241373424769013)
  ·
    refine ⟨7089847852241378758572095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75625043757241373424769013 7089847852241378758572095)
    ·
      refine ⟨10634771778362068137858143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7089847852241378758572095 10634771778362068137858143)
      ·
        refine ⟨15952157667543102206787215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10634771778362068137858143 15952157667543102206787215)
        ·
          refine ⟨23928236501314653310180823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15952157667543102206787215 23928236501314653310180823)
          ·
            refine ⟨35892354751971979965271235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23928236501314653310180823 35892354751971979965271235)
            ·
              refine ⟨53838532127957969947906853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35892354751971979965271235 53838532127957969947906853)
              ·
                refine ⟨10094724773992119365232535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53838532127957969947906853 10094724773992119365232535)
                ·
                  refine ⟨15142087160988179047848803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10094724773992119365232535 15142087160988179047848803)
                  ·
                    refine ⟨22713130741482268571773205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15142087160988179047848803 22713130741482268571773205)
                    ·
                      refine ⟨1064678003506981339301869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22713130741482268571773205 1064678003506981339301869)
                      ·
                        rfl

theorem cell23_2073453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2073453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073453 prefixEnd_2073453 := by exact prefixLift 2073453
  have htrace : WordTrace (prefixWord ++ tailWord_2073453) baseStart_2073453 baseEnd_2073453 := by
    simpa [prefixWord, tailWord_2073453, baseEnd_2073453] using wordTrace_append hprefix tailTrace_2073453
  have hstable : (prefixWord ++ tailWord_2073453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073453).length < 2 ^ (prefixWord ++ tailWord_2073453).sum := by decide
  have hdescent : baseEnd_2073453 < baseStart_2073453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073457 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 3, 2, 2]
def baseStart_2073457 : Nat := 118140960795 + 2073457 * 2 ^ 59
def prefixEnd_2073457 : Nat := 4983230072969 + 3 ^ 40 * 2073457 * 2
def baseEnd_2073457 : Nat := 1064680057429599323651851

theorem tailTrace_2073457 : CollatzResearch.WordTrace tailWord_2073457 prefixEnd_2073457 1064680057429599323651851 := by
  unfold tailWord_2073457
  simp only [CollatzResearch.WordTrace]
  refine ⟨75625189649226882107914625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50416793099484588071943083 75625189649226882107914625)
  ·
    refine ⟨56718892236920161580935969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75625189649226882107914625 56718892236920161580935969)
    ·
      refine ⟨42539169177690121185701977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56718892236920161580935969 42539169177690121185701977)
      ·
        refine ⟨31904376883267590889276483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42539169177690121185701977 31904376883267590889276483)
        ·
          refine ⟨47856565324901386333914725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31904376883267590889276483 47856565324901386333914725)
          ·
            refine ⟨8973105998419009937609011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47856565324901386333914725 8973105998419009937609011)
            ·
              refine ⟨13459658997628514906413517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8973105998419009937609011 13459658997628514906413517)
              ·
                refine ⟨5047372124110693089905069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13459658997628514906413517 5047372124110693089905069)
                ·
                  refine ⟨1892764546541509908714401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5047372124110693089905069 1892764546541509908714401)
                  ·
                    refine ⟨1419573409906132431535801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1892764546541509908714401 1419573409906132431535801)
                    ·
                      refine ⟨1064680057429599323651851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419573409906132431535801 1064680057429599323651851)
                      ·
                        rfl

theorem cell23_2073457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_2073457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073457 prefixEnd_2073457 := by exact prefixLift 2073457
  have htrace : WordTrace (prefixWord ++ tailWord_2073457) baseStart_2073457 baseEnd_2073457 := by
    simpa [prefixWord, tailWord_2073457, baseEnd_2073457] using wordTrace_append hprefix tailTrace_2073457
  have hstable : (prefixWord ++ tailWord_2073457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073457).length < 2 ^ (prefixWord ++ tailWord_2073457).sum := by decide
  have hdescent : baseEnd_2073457 < baseStart_2073457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073477 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_2073477 : Nat := 118140960795 + 2073477 * 2 ^ 59
def prefixEnd_2073477 : Nat := 4983230072969 + 3 ^ 40 * 2073477 * 2
def baseEnd_2073477 : Nat := 1064690327042689245401759

theorem tailTrace_2073477 : CollatzResearch.WordTrace tailWord_2073477 prefixEnd_2073477 1064690327042689245401759 := by
  unfold tailWord_2073477
  simp only [CollatzResearch.WordTrace]
  refine ⟨75625919109154425523642685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50417279406102950349095123 75625919109154425523642685)
  ·
    refine ⟨28359719665932909571366007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75625919109154425523642685 28359719665932909571366007)
    ·
      refine ⟨42539579498899364357049011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28359719665932909571366007 42539579498899364357049011)
      ·
        refine ⟨63809369248349046535573517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42539579498899364357049011 63809369248349046535573517)
        ·
          refine ⟨23928513468130892450840069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63809369248349046535573517 23928513468130892450840069)
          ·
            refine ⟨4486596275274542334532513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23928513468130892450840069 4486596275274542334532513)
            ·
              refine ⟨3364947206455906750899385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4486596275274542334532513 3364947206455906750899385)
              ·
                refine ⟨2523710404841930063174539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3364947206455906750899385 2523710404841930063174539)
                ·
                  refine ⟨3785565607262895094761809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523710404841930063174539 3785565607262895094761809)
                  ·
                    refine ⟨2839174205447171321071357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3785565607262895094761809 2839174205447171321071357)
                    ·
                      refine ⟨1064690327042689245401759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2839174205447171321071357 1064690327042689245401759)
                      ·
                        rfl

theorem cell23_2073477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_2073477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073477 prefixEnd_2073477 := by exact prefixLift 2073477
  have htrace : WordTrace (prefixWord ++ tailWord_2073477) baseStart_2073477 baseEnd_2073477 := by
    simpa [prefixWord, tailWord_2073477, baseEnd_2073477] using wordTrace_append hprefix tailTrace_2073477
  have hstable : (prefixWord ++ tailWord_2073477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073477).length < 2 ^ (prefixWord ++ tailWord_2073477).sum := by decide
  have hdescent : baseEnd_2073477 < baseStart_2073477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073480 : List Nat := [2, 1, 3, 3, 2, 1, 4, 7]
def baseStart_2073480 : Nat := 118140960795 + 2073480 * 2 ^ 59
def prefixEnd_2073480 : Nat := 4983230072969 + 3 ^ 40 * 2073480 * 2
def baseEnd_2073480 : Nat := 39433032129061212357935

theorem tailTrace_2073480 : CollatzResearch.WordTrace tailWord_2073480 prefixEnd_2073480 39433032129061212357935 := by
  unfold tailWord_2073480
  simp only [CollatzResearch.WordTrace]
  refine ⟨37813014264071778518000947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50417352352095704690667929 37813014264071778518000947)
  ·
    refine ⟨56719521396107667777001421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37813014264071778518000947 56719521396107667777001421)
    ·
      refine ⟨21269820523540375416375533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56719521396107667777001421 21269820523540375416375533)
      ·
        refine ⟨7976182696327640781140825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21269820523540375416375533 7976182696327640781140825)
        ·
          refine ⟨5982137022245730585855619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7976182696327640781140825 5982137022245730585855619)
          ·
            refine ⟨8973205533368595878783429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982137022245730585855619 8973205533368595878783429)
            ·
              refine ⟨1682476037506611727271893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8973205533368595878783429 1682476037506611727271893)
              ·
                refine ⟨39433032129061212357935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1682476037506611727271893 39433032129061212357935)
                ·
                  rfl

theorem cell23_2073480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 7].length) (baseStart_2073480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073480 prefixEnd_2073480 := by exact prefixLift 2073480
  have htrace : WordTrace (prefixWord ++ tailWord_2073480) baseStart_2073480 baseEnd_2073480 := by
    simpa [prefixWord, tailWord_2073480, baseEnd_2073480] using wordTrace_append hprefix tailTrace_2073480
  have hstable : (prefixWord ++ tailWord_2073480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073480).length < 2 ^ (prefixWord ++ tailWord_2073480).sum := by decide
  have hdescent : baseEnd_2073480 < baseStart_2073480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073494 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2073494 : Nat := 118140960795 + 2073494 * 2 ^ 59
def prefixEnd_2073494 : Nat := 4983230072969 + 3 ^ 40 * 2073494 * 2
def baseEnd_2073494 : Nat := 1064699056213815678889181

theorem tailTrace_2073494 : CollatzResearch.WordTrace tailWord_2073494 prefixEnd_2073494 1064699056213815678889181 := by
  unfold tailWord_2073494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726658696880802339188221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50417692766728558284674357 4726658696880802339188221)
  ·
    refine ⟨1772497011330300877195583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4726658696880802339188221 1772497011330300877195583)
    ·
      refine ⟨2658745516995451315793375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772497011330300877195583 2658745516995451315793375)
      ·
        refine ⟨3988118275493176973690063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658745516995451315793375 3988118275493176973690063)
        ·
          refine ⟨5982177413239765460535095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988118275493176973690063 5982177413239765460535095)
          ·
            refine ⟨8973266119859648190802643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982177413239765460535095 8973266119859648190802643)
            ·
              refine ⟨13459899179789472286203965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8973266119859648190802643 13459899179789472286203965)
              ·
                refine ⟨5047462192421052107326487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13459899179789472286203965 5047462192421052107326487)
                ·
                  refine ⟨7571193288631578160989731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047462192421052107326487 7571193288631578160989731)
                  ·
                    refine ⟨11356789932947367241484597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7571193288631578160989731 11356789932947367241484597)
                    ·
                      refine ⟨1064699056213815678889181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11356789932947367241484597 1064699056213815678889181)
                      ·
                        rfl

theorem cell23_2073494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2073494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073494 prefixEnd_2073494 := by exact prefixLift 2073494
  have htrace : WordTrace (prefixWord ++ tailWord_2073494) baseStart_2073494 baseEnd_2073494 := by
    simpa [prefixWord, tailWord_2073494, baseEnd_2073494] using wordTrace_append hprefix tailTrace_2073494
  have hstable : (prefixWord ++ tailWord_2073494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073494).length < 2 ^ (prefixWord ++ tailWord_2073494).sum := by decide
  have hdescent : baseEnd_2073494 < baseStart_2073494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073513 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_2073513 : Nat := 118140960795 + 2073513 * 2 ^ 59
def prefixEnd_2073513 : Nat := 4983230072969 + 3 ^ 40 * 2073513 * 2
def baseEnd_2073513 : Nat := 1064708812346251104551593

theorem tailTrace_2073513 : CollatzResearch.WordTrace tailWord_2073513 prefixEnd_2073513 1064708812346251104551593 := by
  unfold tailWord_2073513
  simp only [CollatzResearch.WordTrace]
  refine ⟨75627232137024003671953193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50418154758016002447968795 75627232137024003671953193)
  ·
    refine ⟨56720424102768002753964895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75627232137024003671953193 56720424102768002753964895)
    ·
      refine ⟨85080636154152004130947343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56720424102768002753964895 85080636154152004130947343)
      ·
        refine ⟨127620954231228006196421015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85080636154152004130947343 127620954231228006196421015)
        ·
          refine ⟨191431431346842009294631523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127620954231228006196421015 191431431346842009294631523)
          ·
            refine ⟨287147147020263013941947285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191431431346842009294631523 287147147020263013941947285)
            ·
              refine ⟨13460022516574828778528779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287147147020263013941947285 13460022516574828778528779)
              ·
                refine ⟨20190033774862243167793169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13460022516574828778528779 20190033774862243167793169)
                ·
                  refine ⟨15142525331146682375844877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20190033774862243167793169 15142525331146682375844877)
                  ·
                    refine ⟨5678446999180005890941829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15142525331146682375844877 5678446999180005890941829)
                    ·
                      refine ⟨1064708812346251104551593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5678446999180005890941829 1064708812346251104551593)
                      ·
                        rfl

theorem cell23_2073513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_2073513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073513 prefixEnd_2073513 := by exact prefixLift 2073513
  have htrace : WordTrace (prefixWord ++ tailWord_2073513) baseStart_2073513 baseEnd_2073513 := by
    simpa [prefixWord, tailWord_2073513, baseEnd_2073513] using wordTrace_append hprefix tailTrace_2073513
  have hstable : (prefixWord ++ tailWord_2073513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073513).length < 2 ^ (prefixWord ++ tailWord_2073513).sum := by decide
  have hdescent : baseEnd_2073513 < baseStart_2073513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073547 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 1, 4, 2]
def baseStart_2073547 : Nat := 118140960795 + 2073547 * 2 ^ 59
def prefixEnd_2073547 : Nat := 4983230072969 + 3 ^ 40 * 2073547 * 2
def baseEnd_2073547 : Nat := 1064726270688503971526437

theorem tailTrace_2073547 : CollatzResearch.WordTrace tailWord_2073547 prefixEnd_2073547 1064726270688503971526437 := by
  unfold tailWord_2073547
  simp only [CollatzResearch.WordTrace]
  refine ⟨75628472218900827478690895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50418981479267218319127263 75628472218900827478690895)
  ·
    refine ⟨113442708328351241218036343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75628472218900827478690895 113442708328351241218036343)
    ·
      refine ⟨170164062492526861827054515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113442708328351241218036343 170164062492526861827054515)
      ·
        refine ⟨255246093738790292740581773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170164062492526861827054515 255246093738790292740581773)
        ·
          refine ⟨95717285152046359777718165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255246093738790292740581773 95717285152046359777718165)
          ·
            refine ⟨4486747741502173114580539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95717285152046359777718165 4486747741502173114580539)
            ·
              refine ⟨6730121612253259671870809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4486747741502173114580539 6730121612253259671870809)
              ·
                refine ⟨5047591209189944753903107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6730121612253259671870809 5047591209189944753903107)
                ·
                  refine ⟨7571386813784917130854661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047591209189944753903107 7571386813784917130854661)
                  ·
                    refine ⟨1419635027584671962035249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7571386813784917130854661 1419635027584671962035249)
                    ·
                      refine ⟨1064726270688503971526437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419635027584671962035249 1064726270688503971526437)
                      ·
                        rfl

theorem cell23_2073547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 4, 2].length) (baseStart_2073547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073547 prefixEnd_2073547 := by exact prefixLift 2073547
  have htrace : WordTrace (prefixWord ++ tailWord_2073547) baseStart_2073547 baseEnd_2073547 := by
    simpa [prefixWord, tailWord_2073547, baseEnd_2073547] using wordTrace_append hprefix tailTrace_2073547
  have hstable : (prefixWord ++ tailWord_2073547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073547).length < 2 ^ (prefixWord ++ tailWord_2073547).sum := by decide
  have hdescent : baseEnd_2073547 < baseStart_2073547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073550 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_2073550 : Nat := 118140960795 + 2073550 * 2 ^ 59
def prefixEnd_2073550 : Nat := 4983230072969 + 3 ^ 40 * 2073550 * 2
def baseEnd_2073550 : Nat := 1064727811130467459788923

theorem tailTrace_2073550 : CollatzResearch.WordTrace tailWord_2073550 prefixEnd_2073550 1064727811130467459788923 := by
  unfold tailWord_2073550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9453572704736244873881263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50419054425259972660700069 9453572704736244873881263)
  ·
    refine ⟨14180359057104367310821895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9453572704736244873881263 14180359057104367310821895)
    ·
      refine ⟨21270538585656550966232843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14180359057104367310821895 21270538585656550966232843)
      ·
        refine ⟨31905807878484826449349265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21270538585656550966232843 31905807878484826449349265)
        ·
          refine ⟨23929355908863619837011949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31905807878484826449349265 23929355908863619837011949)
          ·
            refine ⟨8973508465823857438879481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23929355908863619837011949 8973508465823857438879481)
            ·
              refine ⟨6730131349367893079159611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973508465823857438879481 6730131349367893079159611)
              ·
                refine ⟨10095197024051839618739417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730131349367893079159611 10095197024051839618739417)
                ·
                  refine ⟨7571397768038879714054563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10095197024051839618739417 7571397768038879714054563)
                  ·
                    refine ⟨11357096652058319571081845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7571397768038879714054563 11357096652058319571081845)
                    ·
                      refine ⟨1064727811130467459788923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11357096652058319571081845 1064727811130467459788923)
                      ·
                        rfl

theorem cell23_2073550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_2073550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073550 prefixEnd_2073550 := by exact prefixLift 2073550
  have htrace : WordTrace (prefixWord ++ tailWord_2073550) baseStart_2073550 baseEnd_2073550 := by
    simpa [prefixWord, tailWord_2073550, baseEnd_2073550] using wordTrace_append hprefix tailTrace_2073550
  have hstable : (prefixWord ++ tailWord_2073550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073550).length < 2 ^ (prefixWord ++ tailWord_2073550).sum := by decide
  have hdescent : baseEnd_2073550 < baseStart_2073550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073602 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2073602 : Nat := 118140960795 + 2073602 * 2 ^ 59
def prefixEnd_2073602 : Nat := 4983230072969 + 3 ^ 40 * 2073602 * 2
def baseEnd_2073602 : Nat := 1064754512124501256338685

theorem tailTrace_2073602 : CollatzResearch.WordTrace tailWord_2073602 prefixEnd_2073602 1064754512124501256338685 := by
  unfold tailWord_2073602
  simp only [CollatzResearch.WordTrace]
  refine ⟨18907619558425392967985765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50420318822467714581295373 18907619558425392967985765)
  ·
    refine ⟨3545178667204761181497331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18907619558425392967985765 3545178667204761181497331)
    ·
      refine ⟨5317768000807141772245997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545178667204761181497331 5317768000807141772245997)
      ·
        refine ⟨1994163000302678164592249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5317768000807141772245997 1994163000302678164592249)
        ·
          refine ⟨1495622250227008623444187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994163000302678164592249 1495622250227008623444187)
          ·
            refine ⟨2243433375340512935166281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495622250227008623444187 2243433375340512935166281)
            ·
              refine ⟨1682575031505384701374711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243433375340512935166281 1682575031505384701374711)
              ·
                refine ⟨2523862547258077052062067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682575031505384701374711 2523862547258077052062067)
                ·
                  refine ⟨3785793820887115578093101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523862547258077052062067 3785793820887115578093101)
                  ·
                    refine ⟨1419672682832668341784913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3785793820887115578093101 1419672682832668341784913)
                    ·
                      refine ⟨1064754512124501256338685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419672682832668341784913 1064754512124501256338685)
                      ·
                        rfl

theorem cell23_2073602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2073602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073602 prefixEnd_2073602 := by exact prefixLift 2073602
  have htrace : WordTrace (prefixWord ++ tailWord_2073602) baseStart_2073602 baseEnd_2073602 := by
    simpa [prefixWord, tailWord_2073602, baseEnd_2073602] using wordTrace_append hprefix tailTrace_2073602
  have hstable : (prefixWord ++ tailWord_2073602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073602).length < 2 ^ (prefixWord ++ tailWord_2073602).sum := by decide
  have hdescent : baseEnd_2073602 < baseStart_2073602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073637 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 2, 4, 2]
def baseStart_2073637 : Nat := 118140960795 + 2073637 * 2 ^ 59
def prefixEnd_2073637 : Nat := 4983230072969 + 3 ^ 40 * 2073637 * 2
def baseEnd_2073637 : Nat := 1064772483947408619401023

theorem tailTrace_2073637 : CollatzResearch.WordTrace tailWord_2073637 prefixEnd_2073637 1064772483947408619401023 := by
  unfold tailWord_2073637
  simp only [CollatzResearch.WordTrace]
  refine ⟨75631754788574772849467165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50421169859049848566311443 75631754788574772849467165)
  ·
    refine ⟨28361908045715539818550187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75631754788574772849467165 28361908045715539818550187)
    ·
      refine ⟨42542862068573309727825281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28361908045715539818550187 42542862068573309727825281)
      ·
        refine ⟨31907146551429982295868961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42542862068573309727825281 31907146551429982295868961)
        ·
          refine ⟨23930359913572486721901721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31907146551429982295868961 23930359913572486721901721)
          ·
            refine ⟨17947769935179365041426291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23930359913572486721901721 17947769935179365041426291)
            ·
              refine ⟨26921654902769047562139437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17947769935179365041426291 26921654902769047562139437)
              ·
                refine ⟨10095620588538392835802289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26921654902769047562139437 10095620588538392835802289)
                ·
                  refine ⟨7571715441403794626851717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10095620588538392835802289 7571715441403794626851717)
                  ·
                    refine ⟨1419696645263211492534697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7571715441403794626851717 1419696645263211492534697)
                    ·
                      refine ⟨1064772483947408619401023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419696645263211492534697 1064772483947408619401023)
                      ·
                        rfl

theorem cell23_2073637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_2073637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073637 prefixEnd_2073637 := by exact prefixLift 2073637
  have htrace : WordTrace (prefixWord ++ tailWord_2073637) baseStart_2073637 baseEnd_2073637 := by
    simpa [prefixWord, tailWord_2073637, baseEnd_2073637] using wordTrace_append hprefix tailTrace_2073637
  have hstable : (prefixWord ++ tailWord_2073637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073637).length < 2 ^ (prefixWord ++ tailWord_2073637).sum := by decide
  have hdescent : baseEnd_2073637 < baseStart_2073637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073650 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2073650 : Nat := 118140960795 + 2073650 * 2 ^ 59
def prefixEnd_2073650 : Nat := 4983230072969 + 3 ^ 40 * 2073650 * 2
def baseEnd_2073650 : Nat := 1064779159195917068538463

theorem tailTrace_2073650 : CollatzResearch.WordTrace tailWord_2073650 prefixEnd_2073650 1064779159195917068538463 := by
  unfold tailWord_2073650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18908057234381919017422601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50421485958351784046460269 18908057234381919017422601)
  ·
    refine ⟨14181042925786439263066951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18908057234381919017422601 14181042925786439263066951)
    ·
      refine ⟨21271564388679658894600427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14181042925786439263066951 21271564388679658894600427)
      ·
        refine ⟨31907346583019488341900641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21271564388679658894600427 31907346583019488341900641)
        ·
          refine ⟨23930509937264616256425481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31907346583019488341900641 23930509937264616256425481)
          ·
            refine ⟨17947882452948462192319111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23930509937264616256425481 17947882452948462192319111)
            ·
              refine ⟨26921823679422693288478667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17947882452948462192319111 26921823679422693288478667)
              ·
                refine ⟨40382735519134039932718001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26921823679422693288478667 40382735519134039932718001)
                ·
                  refine ⟨30287051639350529949538501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40382735519134039932718001 30287051639350529949538501)
                  ·
                    refine ⟨5678822182378224365538469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30287051639350529949538501 5678822182378224365538469)
                    ·
                      refine ⟨1064779159195917068538463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5678822182378224365538469 1064779159195917068538463)
                      ·
                        rfl

theorem cell23_2073650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2073650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073650 prefixEnd_2073650 := by exact prefixLift 2073650
  have htrace : WordTrace (prefixWord ++ tailWord_2073650) baseStart_2073650 baseEnd_2073650 := by
    simpa [prefixWord, tailWord_2073650, baseEnd_2073650] using wordTrace_append hprefix tailTrace_2073650
  have hstable : (prefixWord ++ tailWord_2073650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073650).length < 2 ^ (prefixWord ++ tailWord_2073650).sum := by decide
  have hdescent : baseEnd_2073650 < baseStart_2073650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073657 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2073657 : Nat := 118140960795 + 2073657 * 2 ^ 59
def prefixEnd_2073657 : Nat := 4983230072969 + 3 ^ 40 * 2073657 * 2
def baseEnd_2073657 : Nat := 1064782753560498541150931

theorem tailTrace_2073657 : CollatzResearch.WordTrace tailWord_2073657 prefixEnd_2073657 1064782753560498541150931 := by
  unfold tailWord_2073657
  simp only [CollatzResearch.WordTrace]
  refine ⟨75632484248502316265195225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50421656165668210843463483 75632484248502316265195225)
  ·
    refine ⟨56724363186376737198896419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75632484248502316265195225 56724363186376737198896419)
    ·
      refine ⟨85086544779565105798344629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56724363186376737198896419 85086544779565105798344629)
      ·
        refine ⟨7976863573084228668594809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85086544779565105798344629 7976863573084228668594809)
        ·
          refine ⟨5982647679813171501446107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7976863573084228668594809 5982647679813171501446107)
          ·
            refine ⟨8973971519719757252169161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982647679813171501446107 8973971519719757252169161)
            ·
              refine ⟨6730478639789817939126871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973971519719757252169161 6730478639789817939126871)
              ·
                refine ⟨10095717959684726908690307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730478639789817939126871 10095717959684726908690307)
                ·
                  refine ⟨15143576939527090363035461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10095717959684726908690307 15143576939527090363035461)
                  ·
                    refine ⟨2839420676161329443069149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15143576939527090363035461 2839420676161329443069149)
                    ·
                      refine ⟨1064782753560498541150931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2839420676161329443069149 1064782753560498541150931)
                      ·
                        rfl

theorem cell23_2073657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2073657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073657 prefixEnd_2073657 := by exact prefixLift 2073657
  have htrace : WordTrace (prefixWord ++ tailWord_2073657) baseStart_2073657 baseEnd_2073657 := by
    simpa [prefixWord, tailWord_2073657, baseEnd_2073657] using wordTrace_append hprefix tailTrace_2073657
  have hstable : (prefixWord ++ tailWord_2073657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073657).length < 2 ^ (prefixWord ++ tailWord_2073657).sum := by decide
  have hdescent : baseEnd_2073657 < baseStart_2073657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073660 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 8]
def baseStart_2073660 : Nat := 118140960795 + 2073660 * 2 ^ 59
def prefixEnd_2073660 : Nat := 4983230072969 + 3 ^ 40 * 2073660 * 2
def baseEnd_2073660 : Nat := 118309366000273558823713

theorem tailTrace_2073660 : CollatzResearch.WordTrace tailWord_2073660 prefixEnd_2073660 118309366000273558823713 := by
  unfold tailWord_2073660
  simp only [CollatzResearch.WordTrace]
  refine ⟨37816296833745723888777217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50421729111660965185036289 37816296833745723888777217)
  ·
    refine ⟨28362222625309292916582913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37816296833745723888777217 28362222625309292916582913)
    ·
      refine ⟨21271666968981969687437185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28362222625309292916582913 21271666968981969687437185)
      ·
        refine ⟨15953750226736477265577889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21271666968981969687437185 15953750226736477265577889)
        ·
          refine ⟨11965312670052357949183417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15953750226736477265577889 11965312670052357949183417)
          ·
            refine ⟨8973984502539268461887563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11965312670052357949183417 8973984502539268461887563)
            ·
              refine ⟨13460976753808902692831345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8973984502539268461887563 13460976753808902692831345)
              ·
                refine ⟨10095732565356677019623509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13460976753808902692831345 10095732565356677019623509)
                ·
                  refine ⟨118309366000273558823713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10095732565356677019623509 118309366000273558823713)
                  ·
                    rfl

theorem cell23_2073660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_2073660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073660 prefixEnd_2073660 := by exact prefixLift 2073660
  have htrace : WordTrace (prefixWord ++ tailWord_2073660) baseStart_2073660 baseEnd_2073660 := by
    simpa [prefixWord, tailWord_2073660, baseEnd_2073660] using wordTrace_append hprefix tailTrace_2073660
  have hstable : (prefixWord ++ tailWord_2073660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073660).length < 2 ^ (prefixWord ++ tailWord_2073660).sum := by decide
  have hdescent : baseEnd_2073660 < baseStart_2073660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073677 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2073677 : Nat := 118140960795 + 2073677 * 2 ^ 59
def prefixEnd_2073677 : Nat := 4983230072969 + 3 ^ 40 * 2073677 * 2
def baseEnd_2073677 : Nat := 118310335908176495877871

theorem tailTrace_2073677 : CollatzResearch.WordTrace tailWord_2073677 prefixEnd_2073677 118310335908176495877871 := by
  unfold tailWord_2073677
  simp only [CollatzResearch.WordTrace]
  refine ⟨75633213708429859680923285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50422142472286573120615523 75633213708429859680923285)
  ·
    refine ⟨3545306892582649672543279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75633213708429859680923285 3545306892582649672543279)
    ·
      refine ⟨5317960338873974508814919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545306892582649672543279 5317960338873974508814919)
      ·
        refine ⟨7976940508310961763222379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317960338873974508814919 7976940508310961763222379)
        ·
          refine ⟨11965410762466442644833569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7976940508310961763222379 11965410762466442644833569)
          ·
            refine ⟨8974058071849831983625177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11965410762466442644833569 8974058071849831983625177)
            ·
              refine ⟨6730543553887373987718883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8974058071849831983625177 6730543553887373987718883)
              ·
                refine ⟨10095815330831060981578325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730543553887373987718883 10095815330831060981578325)
                ·
                  refine ⟨118310335908176495877871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10095815330831060981578325 118310335908176495877871)
                  ·
                    rfl

theorem cell23_2073677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2073677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073677 prefixEnd_2073677 := by exact prefixLift 2073677
  have htrace : WordTrace (prefixWord ++ tailWord_2073677) baseStart_2073677 baseEnd_2073677 := by
    simpa [prefixWord, tailWord_2073677, baseEnd_2073677] using wordTrace_append hprefix tailTrace_2073677
  have hstable : (prefixWord ++ tailWord_2073677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073677).length < 2 ^ (prefixWord ++ tailWord_2073677).sum := by decide
  have hdescent : baseEnd_2073677 < baseStart_2073677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073697 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_2073697 : Nat := 118140960795 + 2073697 * 2 ^ 59
def prefixEnd_2073697 : Nat := 4983230072969 + 3 ^ 40 * 2073697 * 2
def baseEnd_2073697 : Nat := 1064803292786678384650747

theorem tailTrace_2073697 : CollatzResearch.WordTrace tailWord_2073697 prefixEnd_2073697 1064803292786678384650747 := by
  unfold tailWord_2073697
  simp only [CollatzResearch.WordTrace]
  refine ⟨75633943168357403096651345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50422628778904935397767563 75633943168357403096651345)
  ·
    refine ⟨56725457376268052322488509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75633943168357403096651345 56725457376268052322488509)
    ·
      refine ⟨21272046516100519620933191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56725457376268052322488509 21272046516100519620933191)
      ·
        refine ⟨31908069774150779431399787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21272046516100519620933191 31908069774150779431399787)
        ·
          refine ⟨47862104661226169147099681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31908069774150779431399787 47862104661226169147099681)
          ·
            refine ⟨35896578495919626860324761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47862104661226169147099681 35896578495919626860324761)
            ·
              refine ⟨26922433871939720145243571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35896578495919626860324761 26922433871939720145243571)
              ·
                refine ⟨40383650807909580217865357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26922433871939720145243571 40383650807909580217865357)
                ·
                  refine ⟨15143869052966092581699509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40383650807909580217865357 15143869052966092581699509)
                  ·
                    refine ⟨1419737723715571179534329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15143869052966092581699509 1419737723715571179534329)
                    ·
                      refine ⟨1064803292786678384650747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419737723715571179534329 1064803292786678384650747)
                      ·
                        rfl

theorem cell23_2073697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_2073697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073697 prefixEnd_2073697 := by exact prefixLift 2073697
  have htrace : WordTrace (prefixWord ++ tailWord_2073697) baseStart_2073697 baseEnd_2073697 := by
    simpa [prefixWord, tailWord_2073697, baseEnd_2073697] using wordTrace_append hprefix tailTrace_2073697
  have hstable : (prefixWord ++ tailWord_2073697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073697).length < 2 ^ (prefixWord ++ tailWord_2073697).sum := by decide
  have hdescent : baseEnd_2073697 < baseStart_2073697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073720 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 3, 6]
def baseStart_2073720 : Nat := 118140960795 + 2073720 * 2 ^ 59
def prefixEnd_2073720 : Nat := 4983230072969 + 3 ^ 40 * 2073720 * 2
def baseEnd_2073720 : Nat := 354938367613910598221047

theorem tailTrace_2073720 : CollatzResearch.WordTrace tailWord_2073720 prefixEnd_2073720 354938367613910598221047 := by
  unfold tailWord_2073720
  simp only [CollatzResearch.WordTrace]
  refine ⟨37817391023637039012369307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50423188031516052016492409 37817391023637039012369307)
  ·
    refine ⟨56726086535455558518553961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37817391023637039012369307 56726086535455558518553961)
    ·
      refine ⟨42544564901591668888915471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56726086535455558518553961 42544564901591668888915471)
      ·
        refine ⟨63816847352387503333373207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42544564901591668888915471 63816847352387503333373207)
        ·
          refine ⟨95725271028581255000059811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63816847352387503333373207 95725271028581255000059811)
          ·
            refine ⟨143587906542871882500089717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95725271028581255000059811 143587906542871882500089717)
            ·
              refine ⟨13461366238394238984383411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143587906542871882500089717 13461366238394238984383411)
              ·
                refine ⟨20192049357591358476575117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13461366238394238984383411 20192049357591358476575117)
                ·
                  refine ⟨7572018509096759428715669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20192049357591358476575117 7572018509096759428715669)
                  ·
                    refine ⟨354938367613910598221047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7572018509096759428715669 354938367613910598221047)
                    ·
                      rfl

theorem cell23_2073720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_2073720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073720 prefixEnd_2073720 := by exact prefixLift 2073720
  have htrace : WordTrace (prefixWord ++ tailWord_2073720) baseStart_2073720 baseEnd_2073720 := by
    simpa [prefixWord, tailWord_2073720, baseEnd_2073720] using wordTrace_append hprefix tailTrace_2073720
  have hstable : (prefixWord ++ tailWord_2073720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073720).length < 2 ^ (prefixWord ++ tailWord_2073720).sum := by decide
  have hdescent : baseEnd_2073720 < baseStart_2073720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073724 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_2073724 : Nat := 118140960795 + 2073724 * 2 ^ 59
def prefixEnd_2073724 : Nat := 4983230072969 + 3 ^ 40 * 2073724 * 2
def baseEnd_2073724 : Nat := 354939052254783259671041

theorem tailTrace_2073724 : CollatzResearch.WordTrace tailWord_2073724 prefixEnd_2073724 354939052254783259671041 := by
  unfold tailWord_2073724
  simp only [CollatzResearch.WordTrace]
  refine ⟨37817463969629793353942113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50423285292839724471922817 37817463969629793353942113)
  ·
    refine ⟨28363097977222345015456585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37817463969629793353942113 28363097977222345015456585)
    ·
      refine ⟨21272323482916758761592439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28363097977222345015456585 21272323482916758761592439)
      ·
        refine ⟨31908485224375138142388659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21272323482916758761592439 31908485224375138142388659)
        ·
          refine ⟨47862727836562707213582989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31908485224375138142388659 47862727836562707213582989)
          ·
            refine ⟨17948522938711015205093621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47862727836562707213582989 17948522938711015205093621)
            ·
              refine ⟨1682674025504157675477527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17948522938711015205093621 1682674025504157675477527)
              ·
                refine ⟨2524011038256236513216291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682674025504157675477527 2524011038256236513216291)
                ·
                  refine ⟨3786016557384354769824437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524011038256236513216291 3786016557384354769824437)
                  ·
                    refine ⟨354939052254783259671041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3786016557384354769824437 354939052254783259671041)
                    ·
                      rfl

theorem cell23_2073724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_2073724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073724 prefixEnd_2073724 := by exact prefixLift 2073724
  have htrace : WordTrace (prefixWord ++ tailWord_2073724) baseStart_2073724 baseEnd_2073724 := by
    simpa [prefixWord, tailWord_2073724, baseEnd_2073724] using wordTrace_append hprefix tailTrace_2073724
  have hstable : (prefixWord ++ tailWord_2073724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073724).length < 2 ^ (prefixWord ++ tailWord_2073724).sum := by decide
  have hdescent : baseEnd_2073724 < baseStart_2073724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073740 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2073740 : Nat := 118140960795 + 2073740 * 2 ^ 59
def prefixEnd_2073740 : Nat := 4983230072969 + 3 ^ 40 * 2073740 * 2
def baseEnd_2073740 : Nat := 1064825372454821716413049

theorem tailTrace_2073740 : CollatzResearch.WordTrace tailWord_2073740 prefixEnd_2073740 1064825372454821716413049 := by
  unfold tailWord_2073740
  simp only [CollatzResearch.WordTrace]
  refine ⟨37817755753600810720233337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50423674338134414293644449 37817755753600810720233337)
  ·
    refine ⟨28363316815200608040175003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37817755753600810720233337 28363316815200608040175003)
    ·
      refine ⟨42544975222800912060262505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28363316815200608040175003 42544975222800912060262505)
      ·
        refine ⟨31908731417100684045196879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42544975222800912060262505 31908731417100684045196879)
        ·
          refine ⟨47863097125651026067795319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31908731417100684045196879 47863097125651026067795319)
          ·
            refine ⟨71794645688476539101692979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47863097125651026067795319 71794645688476539101692979)
            ·
              refine ⟨107691968532714808652539469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71794645688476539101692979 107691968532714808652539469)
              ·
                refine ⟨40384488199768053244702301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107691968532714808652539469 40384488199768053244702301)
                ·
                  refine ⟨15144183074913019966763363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40384488199768053244702301 15144183074913019966763363)
                  ·
                    refine ⟨22716274612369529950145045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15144183074913019966763363 22716274612369529950145045)
                    ·
                      refine ⟨1064825372454821716413049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22716274612369529950145045 1064825372454821716413049)
                      ·
                        rfl

theorem cell23_2073740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2073740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073740 prefixEnd_2073740 := by exact prefixLift 2073740
  have htrace : WordTrace (prefixWord ++ tailWord_2073740) baseStart_2073740 baseEnd_2073740 := by
    simpa [prefixWord, tailWord_2073740, baseEnd_2073740] using wordTrace_append hprefix tailTrace_2073740
  have hstable : (prefixWord ++ tailWord_2073740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073740).length < 2 ^ (prefixWord ++ tailWord_2073740).sum := by decide
  have hdescent : baseEnd_2073740 < baseStart_2073740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073747 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 3]
def baseStart_2073747 : Nat := 118140960795 + 2073747 * 2 ^ 59
def prefixEnd_2073747 : Nat := 4983230072969 + 3 ^ 40 * 2073747 * 2
def baseEnd_2073747 : Nat := 1064828966819403189025517

theorem tailTrace_2073747 : CollatzResearch.WordTrace tailWord_2073747 prefixEnd_2073747 1064828966819403189025517 := by
  unfold tailWord_2073747
  simp only [CollatzResearch.WordTrace]
  refine ⟨75635766818176261635971495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50423844545450841090647663 75635766818176261635971495)
  ·
    refine ⟨113453650227264392453957243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75635766818176261635971495 113453650227264392453957243)
    ·
      refine ⟨170180475340896588680935865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113453650227264392453957243 170180475340896588680935865)
      ·
        refine ⟨127635356505672441510701899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170180475340896588680935865 127635356505672441510701899)
        ·
          refine ⟨191453034758508662266052849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127635356505672441510701899 191453034758508662266052849)
          ·
            refine ⟨143589776068881496699539637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191453034758508662266052849 143589776068881496699539637)
            ·
              refine ⟨13461541506457640315581841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143589776068881496699539637 13461541506457640315581841)
              ·
                refine ⟨10096156129843230236686381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13461541506457640315581841 10096156129843230236686381)
                ·
                  refine ⟨3786058548691211338757393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10096156129843230236686381 3786058548691211338757393)
                  ·
                    refine ⟨2839543911518408504068045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3786058548691211338757393 2839543911518408504068045)
                    ·
                      refine ⟨1064828966819403189025517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2839543911518408504068045 1064828966819403189025517)
                      ·
                        rfl

theorem cell23_2073747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_2073747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073747 prefixEnd_2073747 := by exact prefixLift 2073747
  have htrace : WordTrace (prefixWord ++ tailWord_2073747) baseStart_2073747 baseEnd_2073747 := by
    simpa [prefixWord, tailWord_2073747, baseEnd_2073747] using wordTrace_append hprefix tailTrace_2073747
  have hstable : (prefixWord ++ tailWord_2073747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073747).length < 2 ^ (prefixWord ++ tailWord_2073747).sum := by decide
  have hdescent : baseEnd_2073747 < baseStart_2073747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073754 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_2073754 : Nat := 118140960795 + 2073754 * 2 ^ 59
def prefixEnd_2073754 : Nat := 4983230072969 + 3 ^ 40 * 2073754 * 2
def baseEnd_2073754 : Nat := 354944187061328220545995

theorem tailTrace_2073754 : CollatzResearch.WordTrace tailWord_2073754 prefixEnd_2073754 354944187061328220545995 := by
  unfold tailWord_2073754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18909005532287725457869079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50424014752767267887650877 18909005532287725457869079)
  ·
    refine ⟨28363508298431588186803619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18909005532287725457869079 28363508298431588186803619)
    ·
      refine ⟨42545262447647382280205429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28363508298431588186803619 42545262447647382280205429)
      ·
        refine ⟨3988618354466942088769259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42545262447647382280205429 3988618354466942088769259)
        ·
          refine ⟨5982927531700413133153889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988618354466942088769259 5982927531700413133153889)
          ·
            refine ⟨4487195648775309849865417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5982927531700413133153889 4487195648775309849865417)
            ·
              refine ⟨3365396736581482387399063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4487195648775309849865417 3365396736581482387399063)
              ·
                refine ⟨5048095104872223581098595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365396736581482387399063 5048095104872223581098595)
                ·
                  refine ⟨7572142657308335371647893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048095104872223581098595 7572142657308335371647893)
                  ·
                    refine ⟨354944187061328220545995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7572142657308335371647893 354944187061328220545995)
                    ·
                      rfl

theorem cell23_2073754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_2073754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073754 prefixEnd_2073754 := by exact prefixLift 2073754
  have htrace : WordTrace (prefixWord ++ tailWord_2073754) baseStart_2073754 baseEnd_2073754 := by
    simpa [prefixWord, tailWord_2073754, baseEnd_2073754] using wordTrace_append hprefix tailTrace_2073754
  have hstable : (prefixWord ++ tailWord_2073754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073754).length < 2 ^ (prefixWord ++ tailWord_2073754).sum := by decide
  have hdescent : baseEnd_2073754 < baseStart_2073754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073761 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_2073761 : Nat := 118140960795 + 2073761 * 2 ^ 59
def prefixEnd_2073761 : Nat := 4983230072969 + 3 ^ 40 * 2073761 * 2
def baseEnd_2073761 : Nat := 1064836155548566134250453

theorem tailTrace_2073761 : CollatzResearch.WordTrace tailWord_2073761 prefixEnd_2073761 1064836155548566134250453 := by
  unfold tailWord_2073761
  simp only [CollatzResearch.WordTrace]
  refine ⟨75636277440125542026981137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50424184960083694684654091 75636277440125542026981137)
  ·
    refine ⟨56727208080094156520235853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75636277440125542026981137 56727208080094156520235853)
    ·
      refine ⟨21272703030035308695088445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56727208080094156520235853 21272703030035308695088445)
      ·
        refine ⟨7977263636263240760658167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21272703030035308695088445 7977263636263240760658167)
        ·
          refine ⟨11965895454394861140987251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977263636263240760658167 11965895454394861140987251)
          ·
            refine ⟨17948843181592291711480877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11965895454394861140987251 17948843181592291711480877)
            ·
              refine ⟨6730816193097109391805329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17948843181592291711480877 6730816193097109391805329)
              ·
                refine ⟨5048112144822832043853997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6730816193097109391805329 5048112144822832043853997)
                ·
                  refine ⟨1893042054308562016445249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5048112144822832043853997 1893042054308562016445249)
                  ·
                    refine ⟨1419781540731421512333937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1893042054308562016445249 1419781540731421512333937)
                    ·
                      refine ⟨1064836155548566134250453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419781540731421512333937 1064836155548566134250453)
                      ·
                        rfl

theorem cell23_2073761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_2073761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073761 prefixEnd_2073761 := by exact prefixLift 2073761
  have htrace : WordTrace (prefixWord ++ tailWord_2073761) baseStart_2073761 baseEnd_2073761 := by
    simpa [prefixWord, tailWord_2073761, baseEnd_2073761] using wordTrace_append hprefix tailTrace_2073761
  have hstable : (prefixWord ++ tailWord_2073761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073761).length < 2 ^ (prefixWord ++ tailWord_2073761).sum := by decide
  have hdescent : baseEnd_2073761 < baseStart_2073761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073764 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_2073764 : Nat := 118140960795 + 2073764 * 2 ^ 59
def prefixEnd_2073764 : Nat := 4983230072969 + 3 ^ 40 * 2073764 * 2
def baseEnd_2073764 : Nat := 1064837695990529622512939

theorem tailTrace_2073764 : CollatzResearch.WordTrace tailWord_2073764 prefixEnd_2073764 1064837695990529622512939 := by
  unfold tailWord_2073764
  simp only [CollatzResearch.WordTrace]
  refine ⟨37818193429557336769670173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50424257906076449026226897 37818193429557336769670173)
  ·
    refine ⟨14181822536084001288626315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37818193429557336769670173 14181822536084001288626315)
    ·
      refine ⟨21272733804126001932939473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14181822536084001288626315 21272733804126001932939473)
      ·
        refine ⟨15954550353094501449704605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21272733804126001932939473 15954550353094501449704605)
        ·
          refine ⟨5982956382410438043639227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15954550353094501449704605 5982956382410438043639227)
          ·
            refine ⟨8974434573615657065458841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982956382410438043639227 8974434573615657065458841)
            ·
              refine ⟨6730825930211742799094131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8974434573615657065458841 6730825930211742799094131)
              ·
                refine ⟨10096238895317614198641197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730825930211742799094131 10096238895317614198641197)
                ·
                  refine ⟨3786089585744105324490449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10096238895317614198641197 3786089585744105324490449)
                  ·
                    refine ⟨2839567189308078993367837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3786089585744105324490449 2839567189308078993367837)
                    ·
                      refine ⟨1064837695990529622512939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2839567189308078993367837 1064837695990529622512939)
                      ·
                        rfl

theorem cell23_2073764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_2073764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073764 prefixEnd_2073764 := by exact prefixLift 2073764
  have htrace : WordTrace (prefixWord ++ tailWord_2073764) baseStart_2073764 baseEnd_2073764 := by
    simpa [prefixWord, tailWord_2073764, baseEnd_2073764] using wordTrace_append hprefix tailTrace_2073764
  have hstable : (prefixWord ++ tailWord_2073764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073764).length < 2 ^ (prefixWord ++ tailWord_2073764).sum := by decide
  have hdescent : baseEnd_2073764 < baseStart_2073764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073778 : List Nat := [3, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_2073778 : Nat := 118140960795 + 2073778 * 2 ^ 59
def prefixEnd_2073778 : Nat := 4983230072969 + 3 ^ 40 * 2073778 * 2
def baseEnd_2073778 : Nat := 1064844884719692567737875

theorem tailTrace_2073778 : CollatzResearch.WordTrace tailWord_2073778 prefixEnd_2073778 1064844884719692567737875 := by
  unfold tailWord_2073778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18909224370265988482587497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50424598320709302620233325 18909224370265988482587497)
  ·
    refine ⟨14181918277699491361940623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18909224370265988482587497 14181918277699491361940623)
    ·
      refine ⟨21272877416549237042910935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14181918277699491361940623 21272877416549237042910935)
      ·
        refine ⟨31909316124823855564366403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21272877416549237042910935 31909316124823855564366403)
        ·
          refine ⟨47863974187235783346549605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31909316124823855564366403 47863974187235783346549605)
          ·
            refine ⟨8974495160106709377478051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47863974187235783346549605 8974495160106709377478051)
            ·
              refine ⟨13461742740160064066217077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8974495160106709377478051 13461742740160064066217077)
              ·
                refine ⟨1262038381890006006207851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13461742740160064066217077 1262038381890006006207851)
                ·
                  refine ⟨1893057572835009009311777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262038381890006006207851 1893057572835009009311777)
                  ·
                    refine ⟨1419793179626256756983833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1893057572835009009311777 1419793179626256756983833)
                    ·
                      refine ⟨1064844884719692567737875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419793179626256756983833 1064844884719692567737875)
                      ·
                        rfl

theorem cell23_2073778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_2073778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073778 prefixEnd_2073778 := by exact prefixLift 2073778
  have htrace : WordTrace (prefixWord ++ tailWord_2073778) baseStart_2073778 baseEnd_2073778 := by
    simpa [prefixWord, tailWord_2073778, baseEnd_2073778] using wordTrace_append hprefix tailTrace_2073778
  have hstable : (prefixWord ++ tailWord_2073778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073778).length < 2 ^ (prefixWord ++ tailWord_2073778).sum := by decide
  have hdescent : baseEnd_2073778 < baseStart_2073778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073805 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2073805 : Nat := 118140960795 + 2073805 * 2 ^ 59
def prefixEnd_2073805 : Nat := 4983230072969 + 3 ^ 40 * 2073805 * 2
def baseEnd_2073805 : Nat := 354952916232454654033417

theorem tailTrace_2073805 : CollatzResearch.WordTrace tailWord_2073805 prefixEnd_2073805 354952916232454654033417 := by
  unfold tailWord_2073805
  simp only [CollatzResearch.WordTrace]
  refine ⟨75637882251966137541582869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50425254834644091694388579 75637882251966137541582869)
  ·
    refine ⟨3545525730560912697261697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75637882251966137541582869 3545525730560912697261697)
    ·
      refine ⟨2659144297920684522946273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3545525730560912697261697 2659144297920684522946273)
      ·
        refine ⟨1994358223440513392209705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2659144297920684522946273 1994358223440513392209705)
        ·
          refine ⟨1495768667580385044157279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994358223440513392209705 1495768667580385044157279)
          ·
            refine ⟨2243653001370577566235919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495768667580385044157279 2243653001370577566235919)
            ·
              refine ⟨3365479502055866349353879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243653001370577566235919 3365479502055866349353879)
              ·
                refine ⟨5048219253083799524030819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365479502055866349353879 5048219253083799524030819)
                ·
                  refine ⟨7572328879625699286046229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048219253083799524030819 7572328879625699286046229)
                  ·
                    refine ⟨354952916232454654033417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7572328879625699286046229 354952916232454654033417)
                    ·
                      rfl

theorem cell23_2073805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2073805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073805 prefixEnd_2073805 := by exact prefixLift 2073805
  have htrace : WordTrace (prefixWord ++ tailWord_2073805) baseStart_2073805 baseEnd_2073805 := by
    simpa [prefixWord, tailWord_2073805, baseEnd_2073805] using wordTrace_append hprefix tailTrace_2073805
  have hstable : (prefixWord ++ tailWord_2073805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073805).length < 2 ^ (prefixWord ++ tailWord_2073805).sum := by decide
  have hdescent : baseEnd_2073805 < baseStart_2073805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073868 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 2, 2, 2]
def baseStart_2073868 : Nat := 118140960795 + 2073868 * 2 ^ 59
def prefixEnd_2073868 : Nat := 4983230072969 + 3 ^ 40 * 2073868 * 2
def baseEnd_2073868 : Nat := 1064891097978597215612461

theorem tailTrace_2073868 : CollatzResearch.WordTrace tailWord_2073868 prefixEnd_2073868 1064891097978597215612461 := by
  unfold tailWord_2073868
  simp only [CollatzResearch.WordTrace]
  refine ⟨37820090025368949650563129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50426786700491932867417505 37820090025368949650563129)
  ·
    refine ⟨28365067519026712237922347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37820090025368949650563129 28365067519026712237922347)
    ·
      refine ⟨42547601278540068356883521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28365067519026712237922347 42547601278540068356883521)
      ·
        refine ⟨31910700958905051267662641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42547601278540068356883521 31910700958905051267662641)
        ·
          refine ⟨23933025719178788450746981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31910700958905051267662641 23933025719178788450746981)
          ·
            refine ⟨4487442322346022834515059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23933025719178788450746981 4487442322346022834515059)
            ·
              refine ⟨6731163483519034251772589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487442322346022834515059 6731163483519034251772589)
              ·
                refine ⟨2524186306319637844414721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6731163483519034251772589 2524186306319637844414721)
                ·
                  refine ⟨1893139729739728383311041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2524186306319637844414721 1893139729739728383311041)
                  ·
                    refine ⟨1419854797304796287483281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1893139729739728383311041 1419854797304796287483281)
                    ·
                      refine ⟨1064891097978597215612461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419854797304796287483281 1064891097978597215612461)
                      ·
                        rfl

theorem cell23_2073868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_2073868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073868 prefixEnd_2073868 := by exact prefixLift 2073868
  have htrace : WordTrace (prefixWord ++ tailWord_2073868) baseStart_2073868 baseEnd_2073868 := by
    simpa [prefixWord, tailWord_2073868, baseEnd_2073868] using wordTrace_append hprefix tailTrace_2073868
  have hstable : (prefixWord ++ tailWord_2073868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073868).length < 2 ^ (prefixWord ++ tailWord_2073868).sum := by decide
  have hdescent : baseEnd_2073868 < baseStart_2073868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073941 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2073941 : Nat := 118140960795 + 2073941 * 2 ^ 59
def prefixEnd_2073941 : Nat := 4983230072969 + 3 ^ 40 * 2073941 * 2
def baseEnd_2073941 : Nat := 1064928582066375429999625

theorem tailTrace_2073941 : CollatzResearch.WordTrace tailWord_2073941 prefixEnd_2073941 1064928582066375429999625 := by
  unfold tailWord_2073941
  simp only [CollatzResearch.WordTrace]
  refine ⟨75642842579473432768533677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50428561719648955179022451 75642842579473432768533677)
  ·
    refine ⟨28366065967302537288200129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75642842579473432768533677 28366065967302537288200129)
    ·
      refine ⟨21274549475476902966150097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28366065967302537288200129 21274549475476902966150097)
      ·
        refine ⟨15955912106607677224612573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21274549475476902966150097 15955912106607677224612573)
        ·
          refine ⟨5983467039977878959229715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15955912106607677224612573 5983467039977878959229715)
          ·
            refine ⟨8975200559966818438844573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983467039977878959229715 8975200559966818438844573)
            ·
              refine ⟨3365700209987556914566715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8975200559966818438844573 3365700209987556914566715)
              ·
                refine ⟨5048550314981335371850073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365700209987556914566715 5048550314981335371850073)
                ·
                  refine ⟨3786412736236001528887555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048550314981335371850073 3786412736236001528887555)
                  ·
                    refine ⟨5679619104354002293331333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3786412736236001528887555 5679619104354002293331333)
                    ·
                      refine ⟨1064928582066375429999625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5679619104354002293331333 1064928582066375429999625)
                      ·
                        rfl

theorem cell23_2073941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2073941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073941 prefixEnd_2073941 := by exact prefixLift 2073941
  have htrace : WordTrace (prefixWord ++ tailWord_2073941) baseStart_2073941 baseEnd_2073941 := by
    simpa [prefixWord, tailWord_2073941, baseEnd_2073941] using wordTrace_append hprefix tailTrace_2073941
  have hstable : (prefixWord ++ tailWord_2073941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073941).length < 2 ^ (prefixWord ++ tailWord_2073941).sum := by decide
  have hdescent : baseEnd_2073941 < baseStart_2073941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073944 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_2073944 : Nat := 118140960795 + 2073944 * 2 ^ 59
def prefixEnd_2073944 : Nat := 4983230072969 + 3 ^ 40 * 2073944 * 2
def baseEnd_2073944 : Nat := 1064930122508338918262111

theorem tailTrace_2073944 : CollatzResearch.WordTrace tailWord_2073944 prefixEnd_2073944 1064930122508338918262111 := by
  unfold tailWord_2073944
  simp only [CollatzResearch.WordTrace]
  refine ⟨37821475999231282140446443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50428634665641709520595257 37821475999231282140446443)
  ·
    refine ⟨56732213998846923210669665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37821475999231282140446443 56732213998846923210669665)
    ·
      refine ⟨42549160499135192408002249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56732213998846923210669665 42549160499135192408002249)
      ·
        refine ⟨31911870374351394306001687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42549160499135192408002249 31911870374351394306001687)
        ·
          refine ⟨47867805561527091459002531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31911870374351394306001687 47867805561527091459002531)
          ·
            refine ⟨71801708342290637188503797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47867805561527091459002531 71801708342290637188503797)
            ·
              refine ⟨6731410157089747236422231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71801708342290637188503797 6731410157089747236422231)
              ·
                refine ⟨10097115235634620854633347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731410157089747236422231 10097115235634620854633347)
                ·
                  refine ⟨15145672853451931281950021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10097115235634620854633347 15145672853451931281950021)
                  ·
                    refine ⟨2839813660022237115365629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15145672853451931281950021 2839813660022237115365629)
                    ·
                      refine ⟨1064930122508338918262111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2839813660022237115365629 1064930122508338918262111)
                      ·
                        rfl

theorem cell23_2073944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_2073944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073944 prefixEnd_2073944 := by exact prefixLift 2073944
  have htrace : WordTrace (prefixWord ++ tailWord_2073944) baseStart_2073944 baseEnd_2073944 := by
    simpa [prefixWord, tailWord_2073944, baseEnd_2073944] using wordTrace_append hprefix tailTrace_2073944
  have hstable : (prefixWord ++ tailWord_2073944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073944).length < 2 ^ (prefixWord ++ tailWord_2073944).sum := by decide
  have hdescent : baseEnd_2073944 < baseStart_2073944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073954 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2073954 : Nat := 118140960795 + 2073954 * 2 ^ 59
def prefixEnd_2073954 : Nat := 4983230072969 + 3 ^ 40 * 2073954 * 2
def baseEnd_2073954 : Nat := 1064935257314883879137065

theorem tailTrace_2073954 : CollatzResearch.WordTrace tailWord_2073954 prefixEnd_2073954 1064935257314883879137065 := by
  unfold tailWord_2073954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18910829182106583997189229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50428877818950890659171277 18910829182106583997189229)
  ·
    refine ⟨7091560943289968998945961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18910829182106583997189229 7091560943289968998945961)
    ·
      refine ⟨5318670707467476749209471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7091560943289968998945961 5318670707467476749209471)
      ·
        refine ⟨7978006061201215123814207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318670707467476749209471 7978006061201215123814207)
        ·
          refine ⟨11967009091801822685721311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7978006061201215123814207 11967009091801822685721311)
          ·
            refine ⟨17950513637702734028581967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11967009091801822685721311 17950513637702734028581967)
            ·
              refine ⟨26925770456554101042872951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17950513637702734028581967 26925770456554101042872951)
              ·
                refine ⟨40388655684831151564309427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26925770456554101042872951 40388655684831151564309427)
                ·
                  refine ⟨60582983527246727346464141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40388655684831151564309427 60582983527246727346464141)
                  ·
                    refine ⟨22718618822717522754924053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60582983527246727346464141 22718618822717522754924053)
                    ·
                      refine ⟨1064935257314883879137065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22718618822717522754924053 1064935257314883879137065)
                      ·
                        rfl

theorem cell23_2073954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2073954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073954 prefixEnd_2073954 := by exact prefixLift 2073954
  have htrace : WordTrace (prefixWord ++ tailWord_2073954) baseStart_2073954 baseEnd_2073954 := by
    simpa [prefixWord, tailWord_2073954, baseEnd_2073954] using wordTrace_append hprefix tailTrace_2073954
  have hstable : (prefixWord ++ tailWord_2073954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073954).length < 2 ^ (prefixWord ++ tailWord_2073954).sum := by decide
  have hdescent : baseEnd_2073954 < baseStart_2073954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073964 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 8]
def baseStart_2073964 : Nat := 118140960795 + 2073964 * 2 ^ 59
def prefixEnd_2073964 : Nat := 4983230072969 + 3 ^ 40 * 2073964 * 2
def baseEnd_2073964 : Nat := 118326710235714315556891

theorem tailTrace_2073964 : CollatzResearch.WordTrace tailWord_2073964 prefixEnd_2073964 118326710235714315556891 := by
  unfold tailWord_2073964
  simp only [CollatzResearch.WordTrace]
  refine ⟨37821840729195053848310473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50429120972260071797747297 37821840729195053848310473)
  ·
    refine ⟨28366380546896290386232855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37821840729195053848310473 28366380546896290386232855)
    ·
      refine ⟨42549570820344435579349283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28366380546896290386232855 42549570820344435579349283)
      ·
        refine ⟨63824356230516653369023925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42549570820344435579349283 63824356230516653369023925)
        ·
          refine ⟨5983533396610936253345993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63824356230516653369023925 5983533396610936253345993)
          ·
            refine ⟨4487650047458202190009495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5983533396610936253345993 4487650047458202190009495)
            ·
              refine ⟨6731475071187303285014243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4487650047458202190009495 6731475071187303285014243)
              ·
                refine ⟨10097212606780954927521365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731475071187303285014243 10097212606780954927521365)
                ·
                  refine ⟨118326710235714315556891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10097212606780954927521365 118326710235714315556891)
                  ·
                    rfl

theorem cell23_2073964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_2073964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073964 prefixEnd_2073964 := by exact prefixLift 2073964
  have htrace : WordTrace (prefixWord ++ tailWord_2073964) baseStart_2073964 baseEnd_2073964 := by
    simpa [prefixWord, tailWord_2073964, baseEnd_2073964] using wordTrace_append hprefix tailTrace_2073964
  have hstable : (prefixWord ++ tailWord_2073964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073964).length < 2 ^ (prefixWord ++ tailWord_2073964).sum := by decide
  have hdescent : baseEnd_2073964 < baseStart_2073964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073967 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_2073967 : Nat := 118140960795 + 2073967 * 2 ^ 59
def prefixEnd_2073967 : Nat := 4983230072969 + 3 ^ 40 * 2073967 * 2
def baseEnd_2073967 : Nat := 1064941932563392328274505

theorem tailTrace_2073967 : CollatzResearch.WordTrace tailWord_2073967 prefixEnd_2073967 1064941932563392328274505 := by
  unfold tailWord_2073967
  simp only [CollatzResearch.WordTrace]
  refine ⟨75643790877379239208980155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50429193918252826139320103 75643790877379239208980155)
  ·
    refine ⟨113465686316068858813470233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75643790877379239208980155 113465686316068858813470233)
    ·
      refine ⟨85099264737051644110102675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113465686316068858813470233 85099264737051644110102675)
      ·
        refine ⟨127648897105577466165154013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85099264737051644110102675 127648897105577466165154013)
        ·
          refine ⟨47868336414591549811932755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127648897105577466165154013 47868336414591549811932755)
          ·
            refine ⟨71802504621887324717899133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47868336414591549811932755 71802504621887324717899133)
            ·
              refine ⟨26925939233207746769212175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71802504621887324717899133 26925939233207746769212175)
              ·
                refine ⟨40388908849811620153818263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26925939233207746769212175 40388908849811620153818263)
                ·
                  refine ⟨60583363274717430230727395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40388908849811620153818263 60583363274717430230727395)
                  ·
                    refine ⟨90875044912076145346091093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60583363274717430230727395 90875044912076145346091093)
                    ·
                      refine ⟨1064941932563392328274505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 90875044912076145346091093 1064941932563392328274505)
                      ·
                        rfl

theorem cell23_2073967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_2073967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073967 prefixEnd_2073967 := by exact prefixLift 2073967
  have htrace : WordTrace (prefixWord ++ tailWord_2073967) baseStart_2073967 baseEnd_2073967 := by
    simpa [prefixWord, tailWord_2073967, baseEnd_2073967] using wordTrace_append hprefix tailTrace_2073967
  have hstable : (prefixWord ++ tailWord_2073967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073967).length < 2 ^ (prefixWord ++ tailWord_2073967).sum := by decide
  have hdescent : baseEnd_2073967 < baseStart_2073967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2073981 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 6]
def baseStart_2073981 : Nat := 118140960795 + 2073981 * 2 ^ 59
def prefixEnd_2073981 : Nat := 4983230072969 + 3 ^ 40 * 2073981 * 2
def baseEnd_2073981 : Nat := 118327680143617252611049

theorem tailTrace_2073981 : CollatzResearch.WordTrace tailWord_2073981 prefixEnd_2073981 118327680143617252611049 := by
  unfold tailWord_2073981
  simp only [CollatzResearch.WordTrace]
  refine ⟨75644301499328519599989797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50429534332885679733326531 75644301499328519599989797)
  ·
    refine ⟨14183306531124097424998087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75644301499328519599989797 14183306531124097424998087)
    ·
      refine ⟨21274959796686146137497131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14183306531124097424998087 21274959796686146137497131)
      ·
        refine ⟨31912439695029219206245697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21274959796686146137497131 31912439695029219206245697)
        ·
          refine ⟨23934329771271914404684273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31912439695029219206245697 23934329771271914404684273)
          ·
            refine ⟨17950747328453935803513205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23934329771271914404684273 17950747328453935803513205)
            ·
              refine ⟨1682882562042556481579363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17950747328453935803513205 1682882562042556481579363)
              ·
                refine ⟨2524323843063834722369045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682882562042556481579363 2524323843063834722369045)
                ·
                  refine ⟨118327680143617252611049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2524323843063834722369045 118327680143617252611049)
                  ·
                    rfl

theorem cell23_2073981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_2073981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2073981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2073981 prefixEnd_2073981 := by exact prefixLift 2073981
  have htrace : WordTrace (prefixWord ++ tailWord_2073981) baseStart_2073981 baseEnd_2073981 := by
    simpa [prefixWord, tailWord_2073981, baseEnd_2073981] using wordTrace_append hprefix tailTrace_2073981
  have hstable : (prefixWord ++ tailWord_2073981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2073981).length < 2 ^ (prefixWord ++ tailWord_2073981).sum := by decide
  have hdescent : baseEnd_2073981 < baseStart_2073981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2073981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074018 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_2074018 : Nat := 118140960795 + 2074018 * 2 ^ 59
def prefixEnd_2074018 : Nat := 4983230072969 + 3 ^ 40 * 2074018 * 2
def baseEnd_2074018 : Nat := 1064968120076771628736771

theorem tailTrace_2074018 : CollatzResearch.WordTrace tailWord_2074018 prefixEnd_2074018 1064968120076771628736771 := by
  unfold tailWord_2074018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18911412750048618729771677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50430434000129649946057805 18911412750048618729771677)
  ·
    refine ⟨7091779781268232023664379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18911412750048618729771677 7091779781268232023664379)
    ·
      refine ⟨10637669671902348035496569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7091779781268232023664379 10637669671902348035496569)
      ·
        refine ⟨7978252253926761026622427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10637669671902348035496569 7978252253926761026622427)
        ·
          refine ⟨11967378380890141539933641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7978252253926761026622427 11967378380890141539933641)
          ·
            refine ⟨8975533785667606154950231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11967378380890141539933641 8975533785667606154950231)
            ·
              refine ⟨13463300678501409232425347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975533785667606154950231 13463300678501409232425347)
              ·
                refine ⟨20194951017752113848638021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13463300678501409232425347 20194951017752113848638021)
                ·
                  refine ⟨3786553315828521346619629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20194951017752113848638021 3786553315828521346619629)
                  ·
                    refine ⟨1419957493435695504982361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786553315828521346619629 1419957493435695504982361)
                    ·
                      refine ⟨1064968120076771628736771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419957493435695504982361 1064968120076771628736771)
                      ·
                        rfl

theorem cell23_2074018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_2074018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074018 prefixEnd_2074018 := by exact prefixLift 2074018
  have htrace : WordTrace (prefixWord ++ tailWord_2074018) baseStart_2074018 baseEnd_2074018 := by
    simpa [prefixWord, tailWord_2074018, baseEnd_2074018] using wordTrace_append hprefix tailTrace_2074018
  have hstable : (prefixWord ++ tailWord_2074018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074018).length < 2 ^ (prefixWord ++ tailWord_2074018).sum := by decide
  have hdescent : baseEnd_2074018 < baseStart_2074018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074034 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2074034 : Nat := 118140960795 + 2074034 * 2 ^ 59
def prefixEnd_2074034 : Nat := 4983230072969 + 3 ^ 40 * 2074034 * 2
def baseEnd_2074034 : Nat := 1064976335767243566136697

theorem tailTrace_2074034 : CollatzResearch.WordTrace tailWord_2074034 prefixEnd_2074034 1064976335767243566136697 := by
  unfold tailWord_2074034
  simp only [CollatzResearch.WordTrace]
  refine ⟨18911558642034127412917289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50430823045424339767779437 18911558642034127412917289)
  ·
    refine ⟨14183668981525595559687967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18911558642034127412917289 14183668981525595559687967)
    ·
      refine ⟨21275503472288393339531951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14183668981525595559687967 21275503472288393339531951)
      ·
        refine ⟨31913255208432590009297927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21275503472288393339531951 31913255208432590009297927)
        ·
          refine ⟨47869882812648885013946891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31913255208432590009297927 47869882812648885013946891)
          ·
            refine ⟨71804824218973327520920337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47869882812648885013946891 71804824218973327520920337)
            ·
              refine ⟨53853618164229995640690253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71804824218973327520920337 53853618164229995640690253)
              ·
                refine ⟨20195106811586248365258845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53853618164229995640690253 20195106811586248365258845)
                ·
                  refine ⟨7573165054344843136972067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20195106811586248365258845 7573165054344843136972067)
                  ·
                    refine ⟨11359747581517264705458101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7573165054344843136972067 11359747581517264705458101)
                    ·
                      refine ⟨1064976335767243566136697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11359747581517264705458101 1064976335767243566136697)
                      ·
                        rfl

theorem cell23_2074034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2074034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074034 prefixEnd_2074034 := by exact prefixLift 2074034
  have htrace : WordTrace (prefixWord ++ tailWord_2074034) baseStart_2074034 baseEnd_2074034 := by
    simpa [prefixWord, tailWord_2074034, baseEnd_2074034] using wordTrace_append hprefix tailTrace_2074034
  have hstable : (prefixWord ++ tailWord_2074034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074034).length < 2 ^ (prefixWord ++ tailWord_2074034).sum := by decide
  have hdescent : baseEnd_2074034 < baseStart_2074034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074048 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 3, 2, 2]
def baseStart_2074048 : Nat := 118140960795 + 2074048 * 2 ^ 59
def prefixEnd_2074048 : Nat := 4983230072969 + 3 ^ 40 * 2074048 * 2
def baseEnd_2074048 : Nat := 1064983524496406511361633

theorem tailTrace_2074048 : CollatzResearch.WordTrace tailWord_2074048 prefixEnd_2074048 1064983524496406511361633 := by
  unfold tailWord_2074048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37823372595042895021339399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50431163460057193361785865 37823372595042895021339399)
  ·
    refine ⟨56735058892564342532009099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37823372595042895021339399 56735058892564342532009099)
    ·
      refine ⟨85102588338846513798013649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56735058892564342532009099 85102588338846513798013649)
      ·
        refine ⟨63826941254134885348510237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85102588338846513798013649 63826941254134885348510237)
        ·
          refine ⟨23935102970300582005691339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63826941254134885348510237 23935102970300582005691339)
          ·
            refine ⟨35902654455450873008537009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23935102970300582005691339 35902654455450873008537009)
            ·
              refine ⟨26926990841588154756402757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35902654455450873008537009 26926990841588154756402757)
              ·
                refine ⟨5048810782797779016825517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26926990841588154756402757 5048810782797779016825517)
                ·
                  refine ⟨1893304043549167131309569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5048810782797779016825517 1893304043549167131309569)
                  ·
                    refine ⟨1419978032661875348482177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1893304043549167131309569 1419978032661875348482177)
                    ·
                      refine ⟨1064983524496406511361633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1419978032661875348482177 1064983524496406511361633)
                      ·
                        rfl

theorem cell23_2074048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_2074048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074048 prefixEnd_2074048 := by exact prefixLift 2074048
  have htrace : WordTrace (prefixWord ++ tailWord_2074048) baseStart_2074048 baseEnd_2074048 := by
    simpa [prefixWord, tailWord_2074048, baseEnd_2074048] using wordTrace_append hprefix tailTrace_2074048
  have hstable : (prefixWord ++ tailWord_2074048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074048).length < 2 ^ (prefixWord ++ tailWord_2074048).sum := by decide
  have hdescent : baseEnd_2074048 < baseStart_2074048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074098 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2074098 : Nat := 118140960795 + 2074098 * 2 ^ 59
def prefixEnd_2074098 : Nat := 4983230072969 + 3 ^ 40 * 2074098 * 2
def baseEnd_2074098 : Nat := 1065009198529131315736403

theorem tailTrace_2074098 : CollatzResearch.WordTrace tailWord_2074098 prefixEnd_2074098 1065009198529131315736403 := by
  unfold tailWord_2074098
  simp only [CollatzResearch.WordTrace]
  refine ⟨18912142209976162145499737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50432379226603099054665965 18912142209976162145499737)
  ·
    refine ⟨14184106657482121609124803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18912142209976162145499737 14184106657482121609124803)
    ·
      refine ⟨21276159986223182413687205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14184106657482121609124803 21276159986223182413687205)
      ·
        refine ⟨3989279997416846702566351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21276159986223182413687205 3989279997416846702566351)
        ·
          refine ⟨5983919996125270053849527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989279997416846702566351 5983919996125270053849527)
          ·
            refine ⟨8975879994187905080774291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983919996125270053849527 8975879994187905080774291)
            ·
              refine ⟨13463819991281857621161437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975879994187905080774291 13463819991281857621161437)
              ·
                refine ⟨5048932496730696607935539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13463819991281857621161437 5048932496730696607935539)
                ·
                  refine ⟨7573398745096044911903309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048932496730696607935539 7573398745096044911903309)
                  ·
                    refine ⟨2840024529411016841963741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7573398745096044911903309 2840024529411016841963741)
                    ·
                      refine ⟨1065009198529131315736403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2840024529411016841963741 1065009198529131315736403)
                      ·
                        rfl

theorem cell23_2074098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2074098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074098 prefixEnd_2074098 := by exact prefixLift 2074098
  have htrace : WordTrace (prefixWord ++ tailWord_2074098) baseStart_2074098 baseEnd_2074098 := by
    simpa [prefixWord, tailWord_2074098, baseEnd_2074098] using wordTrace_append hprefix tailTrace_2074098
  have hstable : (prefixWord ++ tailWord_2074098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074098).length < 2 ^ (prefixWord ++ tailWord_2074098).sum := by decide
  have hdescent : baseEnd_2074098 < baseStart_2074098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074108 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_2074108 : Nat := 118140960795 + 2074108 * 2 ^ 59
def prefixEnd_2074108 : Nat := 4983230072969 + 3 ^ 40 * 2074108 * 2
def baseEnd_2074108 : Nat := 1065014333335676276611357

theorem tailTrace_2074108 : CollatzResearch.WordTrace tailWord_2074108 prefixEnd_2074108 1065014333335676276611357 := by
  unfold tailWord_2074108
  simp only [CollatzResearch.WordTrace]
  refine ⟨37824466784934210144931489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50432622379912280193241985 37824466784934210144931489)
  ·
    refine ⟨28368350088700657608698617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37824466784934210144931489 28368350088700657608698617)
    ·
      refine ⟨21276262566525493206523963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28368350088700657608698617 21276262566525493206523963)
      ·
        refine ⟨31914393849788239809785945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21276262566525493206523963 31914393849788239809785945)
        ·
          refine ⟨23935795387341179857339459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31914393849788239809785945 23935795387341179857339459)
          ·
            refine ⟨35903693081011769786009189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23935795387341179857339459 35903693081011769786009189)
            ·
              refine ⟨6731942452689706834876723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35903693081011769786009189 6731942452689706834876723)
              ·
                refine ⟨10097913679034560252315085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731942452689706834876723 10097913679034560252315085)
                ·
                  refine ⟨3786717629637960094618157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10097913679034560252315085 3786717629637960094618157)
                  ·
                    refine ⟨1420019111114235035481809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3786717629637960094618157 1420019111114235035481809)
                    ·
                      refine ⟨1065014333335676276611357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420019111114235035481809 1065014333335676276611357)
                      ·
                        rfl

theorem cell23_2074108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_2074108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074108 prefixEnd_2074108 := by exact prefixLift 2074108
  have htrace : WordTrace (prefixWord ++ tailWord_2074108) baseStart_2074108 baseEnd_2074108 := by
    simpa [prefixWord, tailWord_2074108, baseEnd_2074108] using wordTrace_append hprefix tailTrace_2074108
  have hstable : (prefixWord ++ tailWord_2074108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074108).length < 2 ^ (prefixWord ++ tailWord_2074108).sum := by decide
  have hdescent : baseEnd_2074108 < baseStart_2074108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074132 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2074132 : Nat := 118140960795 + 2074132 * 2 ^ 59
def prefixEnd_2074132 : Nat := 4983230072969 + 3 ^ 40 * 2074132 * 2
def baseEnd_2074132 : Nat := 1065026656871384182711247

theorem tailTrace_2074132 : CollatzResearch.WordTrace tailWord_2074132 prefixEnd_2074132 1065026656871384182711247 := by
  unfold tailWord_2074132
  simp only [CollatzResearch.WordTrace]
  refine ⟨37824904460890736194368325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50433205947854314925824433 37824904460890736194368325)
  ·
    refine ⟨7092169586417013036444061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37824904460890736194368325 7092169586417013036444061)
    ·
      refine ⟨2659563594906379888666523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7092169586417013036444061 2659563594906379888666523)
      ·
        refine ⟨3989345392359569832999785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2659563594906379888666523 3989345392359569832999785)
        ·
          refine ⟨2992009044269677374749839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3989345392359569832999785 2992009044269677374749839)
          ·
            refine ⟨4488013566404516062124759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992009044269677374749839 4488013566404516062124759)
            ·
              refine ⟨6732020349606774093187139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488013566404516062124759 6732020349606774093187139)
              ·
                refine ⟨10098030524410161139780709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732020349606774093187139 10098030524410161139780709)
                ·
                  refine ⟨1893380723326905213708883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10098030524410161139780709 1893380723326905213708883)
                  ·
                    refine ⟨2840071084990357820563325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1893380723326905213708883 2840071084990357820563325)
                    ·
                      refine ⟨1065026656871384182711247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2840071084990357820563325 1065026656871384182711247)
                      ·
                        rfl

theorem cell23_2074132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2074132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074132 prefixEnd_2074132 := by exact prefixLift 2074132
  have htrace : WordTrace (prefixWord ++ tailWord_2074132) baseStart_2074132 baseEnd_2074132 := by
    simpa [prefixWord, tailWord_2074132, baseEnd_2074132] using wordTrace_append hprefix tailTrace_2074132
  have hstable : (prefixWord ++ tailWord_2074132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074132).length < 2 ^ (prefixWord ++ tailWord_2074132).sum := by decide
  have hdescent : baseEnd_2074132 < baseStart_2074132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074281 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 7, 5]
def baseStart_2074281 : Nat := 118140960795 + 2074281 * 2 ^ 59
def prefixEnd_2074281 : Nat := 4983230072969 + 3 ^ 40 * 2074281 * 2
def baseEnd_2074281 : Nat := 355034388496301366582687

theorem tailTrace_2074281 : CollatzResearch.WordTrace tailWord_2074281 prefixEnd_2074281 355034388496301366582687 := by
  unfold tailWord_2074281
  simp only [CollatzResearch.WordTrace]
  refine ⟨75655243398241670835910697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50436828932161113890607131 75655243398241670835910697)
  ·
    refine ⟨56741432548681253126933023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75655243398241670835910697 56741432548681253126933023)
    ·
      refine ⟨85112148823021879690399535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56741432548681253126933023 85112148823021879690399535)
      ·
        refine ⟨127668223234532819535599303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85112148823021879690399535 127668223234532819535599303)
        ·
          refine ⟨191502334851799229303398955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127668223234532819535599303 191502334851799229303398955)
          ·
            refine ⟨287253502277698843955098433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191502334851799229303398955 287253502277698843955098433)
            ·
              refine ⟨215440126708274132966323825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287253502277698843955098433 215440126708274132966323825)
              ·
                refine ⟨161580095031205599724742869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215440126708274132966323825 161580095031205599724742869)
                ·
                  refine ⟨3787033477293881243548661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 161580095031205599724742869 3787033477293881243548661)
                  ·
                    refine ⟨355034388496301366582687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3787033477293881243548661 355034388496301366582687)
                    ·
                      rfl

theorem cell23_2074281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_2074281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074281 prefixEnd_2074281 := by exact prefixLift 2074281
  have htrace : WordTrace (prefixWord ++ tailWord_2074281) baseStart_2074281 baseEnd_2074281 := by
    simpa [prefixWord, tailWord_2074281, baseEnd_2074281] using wordTrace_append hprefix tailTrace_2074281
  have hstable : (prefixWord ++ tailWord_2074281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074281).length < 2 ^ (prefixWord ++ tailWord_2074281).sum := by decide
  have hdescent : baseEnd_2074281 < baseStart_2074281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074306 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2074306 : Nat := 118140960795 + 2074306 * 2 ^ 59
def prefixEnd_2074306 : Nat := 4983230072969 + 3 ^ 40 * 2074306 * 2
def baseEnd_2074306 : Nat := 355038667501755500645149

theorem tailTrace_2074306 : CollatzResearch.WordTrace tailWord_2074306 prefixEnd_2074306 355038667501755500645149 := by
  unfold tailWord_2074306
  simp only [CollatzResearch.WordTrace]
  refine ⟨18914038805787775026392693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50437436815434066737047181 18914038805787775026392693)
  ·
    refine ⟨1773191138042603908724315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18914038805787775026392693 1773191138042603908724315)
    ·
      refine ⟨2659786707063905863086473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773191138042603908724315 2659786707063905863086473)
      ·
        refine ⟨1994840030297929397314855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2659786707063905863086473 1994840030297929397314855)
        ·
          refine ⟨2992260045446894095972283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994840030297929397314855 2992260045446894095972283)
          ·
            refine ⟨4488390068170341143958425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992260045446894095972283 4488390068170341143958425)
            ·
              refine ⟨3366292551127755857968819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4488390068170341143958425 3366292551127755857968819)
              ·
                refine ⟨5049438826691633786953229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366292551127755857968819 5049438826691633786953229)
                ·
                  refine ⟨1893539560009362670107461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5049438826691633786953229 1893539560009362670107461)
                  ·
                    refine ⟨355038667501755500645149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1893539560009362670107461 355038667501755500645149)
                    ·
                      rfl

theorem cell23_2074306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2074306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074306 prefixEnd_2074306 := by exact prefixLift 2074306
  have htrace : WordTrace (prefixWord ++ tailWord_2074306) baseStart_2074306 baseEnd_2074306 := by
    simpa [prefixWord, tailWord_2074306, baseEnd_2074306] using wordTrace_append hprefix tailTrace_2074306
  have hstable : (prefixWord ++ tailWord_2074306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074306).length < 2 ^ (prefixWord ++ tailWord_2074306).sum := by decide
  have hdescent : baseEnd_2074306 < baseStart_2074306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074312 : List Nat := [2, 1, 3, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_2074312 : Nat := 118140960795 + 2074312 * 2 ^ 59
def prefixEnd_2074312 : Nat := 4983230072969 + 3 ^ 40 * 2074312 * 2
def baseEnd_2074312 : Nat := 1065119083389193478460419

theorem tailTrace_2074312 : CollatzResearch.WordTrace tailWord_2074312 prefixEnd_2074312 1065119083389193478460419 := by
  unfold tailWord_2074312
  simp only [CollatzResearch.WordTrace]
  refine ⟨37828187030564681565144595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50437582707419575420192793 37828187030564681565144595)
  ·
    refine ⟨56742280545847022347716893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37828187030564681565144595 56742280545847022347716893)
    ·
      refine ⟨21278355204692633380393835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56742280545847022347716893 21278355204692633380393835)
      ·
        refine ⟨31917532807038950070590753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21278355204692633380393835 31917532807038950070590753)
        ·
          refine ⟨23938149605279212552943065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31917532807038950070590753 23938149605279212552943065)
          ·
            refine ⟨17953612203959409414707299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23938149605279212552943065 17953612203959409414707299)
            ·
              refine ⟨26930418305939114122060949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17953612203959409414707299 26930418305939114122060949)
              ·
                refine ⟨1262363358090895974471607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26930418305939114122060949 1262363358090895974471607)
                ·
                  refine ⟨1893545037136343961707411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262363358090895974471607 1893545037136343961707411)
                  ·
                    refine ⟨2840317555704515942561117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1893545037136343961707411 2840317555704515942561117)
                    ·
                      refine ⟨1065119083389193478460419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2840317555704515942561117 1065119083389193478460419)
                      ·
                        rfl

theorem cell23_2074312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_2074312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074312 prefixEnd_2074312 := by exact prefixLift 2074312
  have htrace : WordTrace (prefixWord ++ tailWord_2074312) baseStart_2074312 baseEnd_2074312 := by
    simpa [prefixWord, tailWord_2074312, baseEnd_2074312] using wordTrace_append hprefix tailTrace_2074312
  have hstable : (prefixWord ++ tailWord_2074312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074312).length < 2 ^ (prefixWord ++ tailWord_2074312).sum := by decide
  have hdescent : baseEnd_2074312 < baseStart_2074312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074335 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 4]
def baseStart_2074335 : Nat := 118140960795 + 2074335 * 2 ^ 59
def prefixEnd_2074335 : Nat := 4983230072969 + 3 ^ 40 * 2074335 * 2
def baseEnd_2074335 : Nat := 1065130893444246888472813

theorem tailTrace_2074335 : CollatzResearch.WordTrace tailWord_2074335 prefixEnd_2074335 1065130893444246888472813 := by
  unfold tailWord_2074335
  simp only [CollatzResearch.WordTrace]
  refine ⟨75657212940046038058376459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50438141960030692038917639 75657212940046038058376459)
  ·
    refine ⟨113485819410069057087564689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75657212940046038058376459 113485819410069057087564689)
    ·
      refine ⟨85114364557551792815673517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113485819410069057087564689 85114364557551792815673517)
      ·
        refine ⟨31917886709081922305877569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85114364557551792815673517 31917886709081922305877569)
        ·
          refine ⟨23938415031811441729408177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31917886709081922305877569 23938415031811441729408177)
          ·
            refine ⟨17953811273858581297056133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23938415031811441729408177 17953811273858581297056133)
            ·
              refine ⟨3366339613848483993198025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17953811273858581297056133 3366339613848483993198025)
              ·
                refine ⟨2524754710386362994898519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3366339613848483993198025 2524754710386362994898519)
                ·
                  refine ⟨3787132065579544492347779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524754710386362994898519 3787132065579544492347779)
                  ·
                    refine ⟨5680698098369316738521669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3787132065579544492347779 5680698098369316738521669)
                    ·
                      refine ⟨1065130893444246888472813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5680698098369316738521669 1065130893444246888472813)
                      ·
                        rfl

theorem cell23_2074335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_2074335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074335 prefixEnd_2074335 := by exact prefixLift 2074335
  have htrace : WordTrace (prefixWord ++ tailWord_2074335) baseStart_2074335 baseEnd_2074335 := by
    simpa [prefixWord, tailWord_2074335, baseEnd_2074335] using wordTrace_append hprefix tailTrace_2074335
  have hstable : (prefixWord ++ tailWord_2074335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074335).length < 2 ^ (prefixWord ++ tailWord_2074335).sum := by decide
  have hdescent : baseEnd_2074335 < baseStart_2074335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074348 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_2074348 : Nat := 118140960795 + 2074348 * 2 ^ 59
def prefixEnd_2074348 : Nat := 4983230072969 + 3 ^ 40 * 2074348 * 2
def baseEnd_2074348 : Nat := 1065137568692755337610253

theorem tailTrace_2074348 : CollatzResearch.WordTrace tailWord_2074348 prefixEnd_2074348 1065137568692755337610253 := by
  unfold tailWord_2074348
  simp only [CollatzResearch.WordTrace]
  refine ⟨37828843544499470639299849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50438458059332627519066465 37828843544499470639299849)
  ·
    refine ⟨28371632658374602979474887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37828843544499470639299849 28371632658374602979474887)
    ·
      refine ⟨42557448987561904469212331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28371632658374602979474887 42557448987561904469212331)
      ·
        refine ⟨63836173481342856703818497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42557448987561904469212331 63836173481342856703818497)
        ·
          refine ⟨47877130111007142527863873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63836173481342856703818497 47877130111007142527863873)
          ·
            refine ⟨35907847583255356895897905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47877130111007142527863873 35907847583255356895897905)
            ·
              refine ⟨26930885687441517671923429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35907847583255356895897905 26930885687441517671923429)
              ·
                refine ⟨5049541066395284563485643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26930885687441517671923429 5049541066395284563485643)
                ·
                  refine ⟨7574311599592926845228465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5049541066395284563485643 7574311599592926845228465)
                  ·
                    refine ⟨5680733699694695133921349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7574311599592926845228465 5680733699694695133921349)
                    ·
                      refine ⟨1065137568692755337610253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5680733699694695133921349 1065137568692755337610253)
                      ·
                        rfl

theorem cell23_2074348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_2074348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074348 prefixEnd_2074348 := by exact prefixLift 2074348
  have htrace : WordTrace (prefixWord ++ tailWord_2074348) baseStart_2074348 baseEnd_2074348 := by
    simpa [prefixWord, tailWord_2074348, baseEnd_2074348] using wordTrace_append hprefix tailTrace_2074348
  have hstable : (prefixWord ++ tailWord_2074348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074348).length < 2 ^ (prefixWord ++ tailWord_2074348).sum := by decide
  have hdescent : baseEnd_2074348 < baseStart_2074348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074355 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 3]
def baseStart_2074355 : Nat := 118140960795 + 2074355 * 2 ^ 59
def prefixEnd_2074355 : Nat := 4983230072969 + 3 ^ 40 * 2074355 * 2
def baseEnd_2074355 : Nat := 1065141163057336810222721

theorem tailTrace_2074355 : CollatzResearch.WordTrace tailWord_2074355 prefixEnd_2074355 1065141163057336810222721 := by
  unfold tailWord_2074355
  simp only [CollatzResearch.WordTrace]
  refine ⟨75657942399973581474104519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50438628266649054316069679 75657942399973581474104519)
  ·
    refine ⟨113486913599960372211156779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75657942399973581474104519 113486913599960372211156779)
    ·
      refine ⟨170230370399940558316735169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113486913599960372211156779 170230370399940558316735169)
      ·
        refine ⟨127672777799955418737551377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170230370399940558316735169 127672777799955418737551377)
        ·
          refine ⟨95754583349966564053163533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127672777799955418737551377 95754583349966564053163533)
          ·
            refine ⟨35907968756237461519936325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95754583349966564053163533 35907968756237461519936325)
            ·
              refine ⟨6732744141794524034988061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35907968756237461519936325 6732744141794524034988061)
              ·
                refine ⟨2524779053172946513120523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6732744141794524034988061 2524779053172946513120523)
                ·
                  refine ⟨3787168579759419769680785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524779053172946513120523 3787168579759419769680785)
                  ·
                    refine ⟨2840376434819564827260589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3787168579759419769680785 2840376434819564827260589)
                    ·
                      refine ⟨1065141163057336810222721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2840376434819564827260589 1065141163057336810222721)
                      ·
                        rfl

theorem cell23_2074355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 2, 3].length) (baseStart_2074355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074355 prefixEnd_2074355 := by exact prefixLift 2074355
  have htrace : WordTrace (prefixWord ++ tailWord_2074355) baseStart_2074355 baseEnd_2074355 := by
    simpa [prefixWord, tailWord_2074355, baseEnd_2074355] using wordTrace_append hprefix tailTrace_2074355
  have hstable : (prefixWord ++ tailWord_2074355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074355).length < 2 ^ (prefixWord ++ tailWord_2074355).sum := by decide
  have hdescent : baseEnd_2074355 < baseStart_2074355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074356 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2074356 : Nat := 118140960795 + 2074356 * 2 ^ 59
def prefixEnd_2074356 : Nat := 4983230072969 + 3 ^ 40 * 2074356 * 2
def baseEnd_2074356 : Nat := 1065141676537991306310217

theorem tailTrace_2074356 : CollatzResearch.WordTrace tailWord_2074356 prefixEnd_2074356 1065141676537991306310217 := by
  unfold tailWord_2074356
  simp only [CollatzResearch.WordTrace]
  refine ⟨37828989436484979322445461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50438652581979972429927281 37828989436484979322445461)
  ·
    refine ⟨1773233879835233405739631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37828989436484979322445461 1773233879835233405739631)
    ·
      refine ⟨2659850819752850108609447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773233879835233405739631 2659850819752850108609447)
      ·
        refine ⟨3989776229629275162914171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2659850819752850108609447 3989776229629275162914171)
        ·
          refine ⟨5984664344443912744371257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989776229629275162914171 5984664344443912744371257)
          ·
            refine ⟨4488498258332934558278443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5984664344443912744371257 4488498258332934558278443)
            ·
              refine ⟨6732747387499401837417665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488498258332934558278443 6732747387499401837417665)
              ·
                refine ⟨5049560540624551378063249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6732747387499401837417665 5049560540624551378063249)
                ·
                  refine ⟨3787170405468413533547437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5049560540624551378063249 3787170405468413533547437)
                  ·
                    refine ⟨1420188902050655075080289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3787170405468413533547437 1420188902050655075080289)
                    ·
                      refine ⟨1065141676537991306310217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420188902050655075080289 1065141676537991306310217)
                      ·
                        rfl

theorem cell23_2074356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2074356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074356 prefixEnd_2074356 := by exact prefixLift 2074356
  have htrace : WordTrace (prefixWord ++ tailWord_2074356) baseStart_2074356 baseEnd_2074356 := by
    simpa [prefixWord, tailWord_2074356, baseEnd_2074356] using wordTrace_append hprefix tailTrace_2074356
  have hstable : (prefixWord ++ tailWord_2074356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074356).length < 2 ^ (prefixWord ++ tailWord_2074356).sum := by decide
  have hdescent : baseEnd_2074356 < baseStart_2074356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074358 : List Nat := [5, 1, 1, 1, 1, 3, 11]
def baseStart_2074358 : Nat := 118140960795 + 2074358 * 2 ^ 59
def prefixEnd_2074358 : Nat := 4983230072969 + 3 ^ 40 * 2074358 * 2
def baseEnd_2074358 : Nat := 13149909919744448129447

theorem tailTrace_2074358 : CollatzResearch.WordTrace tailWord_2074358 prefixEnd_2074358 13149909919744448129447 := by
  unfold tailWord_2074358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728628238685169561653983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50438701212641808657642485 4728628238685169561653983)
  ·
    refine ⟨7092942358027754342480975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4728628238685169561653983 7092942358027754342480975)
    ·
      refine ⟨10639413537041631513721463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7092942358027754342480975 10639413537041631513721463)
      ·
        refine ⟨15959120305562447270582195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10639413537041631513721463 15959120305562447270582195)
        ·
          refine ⟨23938680458343670905873293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15959120305562447270582195 23938680458343670905873293)
          ·
            refine ⟨8977005171878876589702485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23938680458343670905873293 8977005171878876589702485)
            ·
              refine ⟨13149909919744448129447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8977005171878876589702485 13149909919744448129447)
              ·
                rfl

theorem cell23_2074358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 11].length) (baseStart_2074358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074358 prefixEnd_2074358 := by exact prefixLift 2074358
  have htrace : WordTrace (prefixWord ++ tailWord_2074358) baseStart_2074358 baseEnd_2074358 := by
    simpa [prefixWord, tailWord_2074358, baseEnd_2074358] using wordTrace_append hprefix tailTrace_2074358
  have hstable : (prefixWord ++ tailWord_2074358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074358).length < 2 ^ (prefixWord ++ tailWord_2074358).sum := by decide
  have hdescent : baseEnd_2074358 < baseStart_2074358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074368 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 3]
def baseStart_2074368 : Nat := 118140960795 + 2074368 * 2 ^ 59
def prefixEnd_2074368 : Nat := 4983230072969 + 3 ^ 40 * 2074368 * 2
def baseEnd_2074368 : Nat := 1065147838305845259360161

theorem tailTrace_2074368 : CollatzResearch.WordTrace tailWord_2074368 prefixEnd_2074368 1065147838305845259360161 := by
  unfold tailWord_2074368
  simp only [CollatzResearch.WordTrace]
  refine ⟨37829208274463242347163879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50438944365950989796218505 37829208274463242347163879)
  ·
    refine ⟨56743812411694863520745819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37829208274463242347163879 56743812411694863520745819)
    ·
      refine ⟨85115718617542295281118729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56743812411694863520745819 85115718617542295281118729)
      ·
        refine ⟨63836788963156721460839047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85115718617542295281118729 63836788963156721460839047)
        ·
          refine ⟨95755183444735082191258571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63836788963156721460839047 95755183444735082191258571)
          ·
            refine ⟨143632775167102623286887857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95755183444735082191258571 143632775167102623286887857)
            ·
              refine ⟨107724581375326967465165893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143632775167102623286887857 107724581375326967465165893)
              ·
                refine ⟨20198359007873806399718605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107724581375326967465165893 20198359007873806399718605)
                ·
                  refine ⟨7574384627952677399894477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20198359007873806399718605 7574384627952677399894477)
                  ·
                    refine ⟨2840394235482254024960429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7574384627952677399894477 2840394235482254024960429)
                    ·
                      refine ⟨1065147838305845259360161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2840394235482254024960429 1065147838305845259360161)
                      ·
                        rfl

theorem cell23_2074368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_2074368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074368 prefixEnd_2074368 := by exact prefixLift 2074368
  have htrace : WordTrace (prefixWord ++ tailWord_2074368) baseStart_2074368 baseEnd_2074368 := by
    simpa [prefixWord, tailWord_2074368, baseEnd_2074368] using wordTrace_append hprefix tailTrace_2074368
  have hstable : (prefixWord ++ tailWord_2074368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074368).length < 2 ^ (prefixWord ++ tailWord_2074368).sum := by decide
  have hdescent : baseEnd_2074368 < baseStart_2074368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074369 : List Nat := [1, 2, 4, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_2074369 : Nat := 118140960795 + 2074369 * 2 ^ 59
def prefixEnd_2074369 : Nat := 4983230072969 + 3 ^ 40 * 2074369 * 2
def baseEnd_2074369 : Nat := 1065148351786499755447657

theorem tailTrace_2074369 : CollatzResearch.WordTrace tailWord_2074369 prefixEnd_2074369 1065148351786499755447657 := by
  unfold tailWord_2074369
  simp only [CollatzResearch.WordTrace]
  refine ⟨75658453021922861865114161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50438968681281907910076107 75658453021922861865114161)
  ·
    refine ⟨56743839766442146398835621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75658453021922861865114161 56743839766442146398835621)
    ·
      refine ⟨10639469956207902449781679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56743839766442146398835621 10639469956207902449781679)
      ·
        refine ⟨15959204934311853674672519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10639469956207902449781679 15959204934311853674672519)
        ·
          refine ⟨23938807401467780512008779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15959204934311853674672519 23938807401467780512008779)
          ·
            refine ⟨35908211102201670768013169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23938807401467780512008779 35908211102201670768013169)
            ·
              refine ⟨26931158326651253076009877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35908211102201670768013169 26931158326651253076009877)
              ·
                refine ⟨1262398046561777487937963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26931158326651253076009877 1262398046561777487937963)
                ·
                  refine ⟨1893597069842666231906945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262398046561777487937963 1893597069842666231906945)
                  ·
                    refine ⟨1420197802381999673930209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1893597069842666231906945 1420197802381999673930209)
                    ·
                      refine ⟨1065148351786499755447657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420197802381999673930209 1065148351786499755447657)
                      ·
                        rfl

theorem cell23_2074369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_2074369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074369 prefixEnd_2074369 := by exact prefixLift 2074369
  have htrace : WordTrace (prefixWord ++ tailWord_2074369) baseStart_2074369 baseEnd_2074369 := by
    simpa [prefixWord, tailWord_2074369, baseEnd_2074369] using wordTrace_append hprefix tailTrace_2074369
  have hstable : (prefixWord ++ tailWord_2074369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074369).length < 2 ^ (prefixWord ++ tailWord_2074369).sum := by decide
  have hdescent : baseEnd_2074369 < baseStart_2074369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074375 : List Nat := [1, 1, 4, 4, 2, 1, 2, 8]
def baseStart_2074375 : Nat := 118140960795 + 2074375 * 2 ^ 59
def prefixEnd_2074375 : Nat := 4983230072969 + 3 ^ 40 * 2074375 * 2
def baseEnd_2074375 : Nat := 39450053061867656739727

theorem tailTrace_2074375 : CollatzResearch.WordTrace tailWord_2074375 prefixEnd_2074375 39450053061867656739727 := by
  unfold tailWord_2074375
  simp only [CollatzResearch.WordTrace]
  refine ⟨75658671859901124889832579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50439114573267416593221719 75658671859901124889832579)
  ·
    refine ⟨113488007789851687334748869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75658671859901124889832579 113488007789851687334748869)
    ·
      refine ⟨21279001460597191375265413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113488007789851687334748869 21279001460597191375265413)
      ·
        refine ⟨3989812773861973382862265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21279001460597191375265413 3989812773861973382862265)
        ·
          refine ⟨2992359580396480037146699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3989812773861973382862265 2992359580396480037146699)
          ·
            refine ⟨4488539370594720055720049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992359580396480037146699 4488539370594720055720049)
            ·
              refine ⟨3366404527946040041790037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4488539370594720055720049 3366404527946040041790037)
              ·
                refine ⟨39450053061867656739727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3366404527946040041790037 39450053061867656739727)
                ·
                  rfl

theorem cell23_2074375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 8].length) (baseStart_2074375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074375 prefixEnd_2074375 := by exact prefixLift 2074375
  have htrace : WordTrace (prefixWord ++ tailWord_2074375) baseStart_2074375 baseEnd_2074375 := by
    simpa [prefixWord, tailWord_2074375, baseEnd_2074375] using wordTrace_append hprefix tailTrace_2074375
  have hstable : (prefixWord ++ tailWord_2074375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074375).length < 2 ^ (prefixWord ++ tailWord_2074375).sum := by decide
  have hdescent : baseEnd_2074375 < baseStart_2074375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074395 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 3, 3, 2]
def baseStart_2074395 : Nat := 118140960795 + 2074395 * 2 ^ 59
def prefixEnd_2074395 : Nat := 4983230072969 + 3 ^ 40 * 2074395 * 2
def baseEnd_2074395 : Nat := 1065161702283516653722537

theorem tailTrace_2074395 : CollatzResearch.WordTrace tailWord_2074395 prefixEnd_2074395 1065161702283516653722537 := by
  unfold tailWord_2074395
  simp only [CollatzResearch.WordTrace]
  refine ⟨75659401319828668305560639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50439600879885778870373759 75659401319828668305560639)
  ·
    refine ⟨113489101979743002458340959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75659401319828668305560639 113489101979743002458340959)
    ·
      refine ⟨170233652969614503687511439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113489101979743002458340959 170233652969614503687511439)
      ·
        refine ⟨255350479454421755531267159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170233652969614503687511439 255350479454421755531267159)
        ·
          refine ⟨383025719181632633296900739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255350479454421755531267159 383025719181632633296900739)
          ·
            refine ⟨574538578772448949945351109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383025719181632633296900739 574538578772448949945351109)
            ·
              refine ⟨107725983519834178114753333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 574538578772448949945351109 107725983519834178114753333)
              ·
                refine ⟨10099310954984454198258125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107725983519834178114753333 10099310954984454198258125)
                ·
                  refine ⟨3787241608119170324346797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10099310954984454198258125 3787241608119170324346797)
                  ·
                    refine ⟨1420215603044688871630049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3787241608119170324346797 1420215603044688871630049)
                    ·
                      refine ⟨1065161702283516653722537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420215603044688871630049 1065161702283516653722537)
                      ·
                        rfl

theorem cell23_2074395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 3, 2].length) (baseStart_2074395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074395 prefixEnd_2074395 := by exact prefixLift 2074395
  have htrace : WordTrace (prefixWord ++ tailWord_2074395) baseStart_2074395 baseEnd_2074395 := by
    simpa [prefixWord, tailWord_2074395, baseEnd_2074395] using wordTrace_append hprefix tailTrace_2074395
  have hstable : (prefixWord ++ tailWord_2074395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074395).length < 2 ^ (prefixWord ++ tailWord_2074395).sum := by decide
  have hdescent : baseEnd_2074395 < baseStart_2074395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074419 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 3]
def baseStart_2074419 : Nat := 118140960795 + 2074419 * 2 ^ 59
def prefixEnd_2074419 : Nat := 4983230072969 + 3 ^ 40 * 2074419 * 2
def baseEnd_2074419 : Nat := 1065174025819224559822427

theorem tailTrace_2074419 : CollatzResearch.WordTrace tailWord_2074419 prefixEnd_2074419 1065174025819224559822427 := by
  unfold tailWord_2074419
  simp only [CollatzResearch.WordTrace]
  refine ⟨75660276671741720404434311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50440184447827813602956207 75660276671741720404434311)
  ·
    refine ⟨113490415007612580606651467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75660276671741720404434311 113490415007612580606651467)
    ·
      refine ⟨170235622511418870909977201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113490415007612580606651467 170235622511418870909977201)
      ·
        refine ⟨127676716883564153182482901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170235622511418870909977201 127676716883564153182482901)
        ·
          refine ⟨2992423051958534840214443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 127676716883564153182482901 2992423051958534840214443)
          ·
            refine ⟨4488634577937802260321665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992423051958534840214443 4488634577937802260321665)
            ·
              refine ⟨3366475933453351695241249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4488634577937802260321665 3366475933453351695241249)
              ·
                refine ⟨2524856950090013771430937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3366475933453351695241249 2524856950090013771430937)
                ·
                  refine ⟨1893642712567510328573203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2524856950090013771430937 1893642712567510328573203)
                  ·
                    refine ⟨2840464068851265492859805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1893642712567510328573203 2840464068851265492859805)
                    ·
                      refine ⟨1065174025819224559822427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2840464068851265492859805 1065174025819224559822427)
                      ·
                        rfl

theorem cell23_2074419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 1, 3].length) (baseStart_2074419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074419 prefixEnd_2074419 := by exact prefixLift 2074419
  have htrace : WordTrace (prefixWord ++ tailWord_2074419) baseStart_2074419 baseEnd_2074419 := by
    simpa [prefixWord, tailWord_2074419, baseEnd_2074419] using wordTrace_append hprefix tailTrace_2074419
  have hstable : (prefixWord ++ tailWord_2074419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074419).length < 2 ^ (prefixWord ++ tailWord_2074419).sum := by decide
  have hdescent : baseEnd_2074419 < baseStart_2074419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074420 : List Nat := [2, 5, 1, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_2074420 : Nat := 118140960795 + 2074420 * 2 ^ 59
def prefixEnd_2074420 : Nat := 4983230072969 + 3 ^ 40 * 2074420 * 2
def baseEnd_2074420 : Nat := 1065174539299879055909923

theorem tailTrace_2074420 : CollatzResearch.WordTrace tailWord_2074420 prefixEnd_2074420 1065174539299879055909923 := by
  unfold tailWord_2074420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37830156572369048787610357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50440208763158731716813809 37830156572369048787610357)
  ·
    refine ⟨3546577178659598323838471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37830156572369048787610357 3546577178659598323838471)
    ·
      refine ⟨5319865767989397485757707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546577178659598323838471 5319865767989397485757707)
      ·
        refine ⟨7979798651984096228636561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5319865767989397485757707 7979798651984096228636561)
        ·
          refine ⟨5984848988988072171477421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7979798651984096228636561 5984848988988072171477421)
          ·
            refine ⟨2244318370870527064304033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5984848988988072171477421 2244318370870527064304033)
            ·
              refine ⟨1683238778152895298228025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2244318370870527064304033 1683238778152895298228025)
              ·
                refine ⟨1262429083614671473671019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1683238778152895298228025 1262429083614671473671019)
                ·
                  refine ⟨1893643625422007210506529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262429083614671473671019 1893643625422007210506529)
                  ·
                    refine ⟨1420232719066505407879897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1893643625422007210506529 1420232719066505407879897)
                    ·
                      refine ⟨1065174539299879055909923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420232719066505407879897 1065174539299879055909923)
                      ·
                        rfl

theorem cell23_2074420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_2074420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074420 prefixEnd_2074420 := by exact prefixLift 2074420
  have htrace : WordTrace (prefixWord ++ tailWord_2074420) baseStart_2074420 baseEnd_2074420 := by
    simpa [prefixWord, tailWord_2074420, baseEnd_2074420] using wordTrace_append hprefix tailTrace_2074420
  have hstable : (prefixWord ++ tailWord_2074420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074420).length < 2 ^ (prefixWord ++ tailWord_2074420).sum := by decide
  have hdescent : baseEnd_2074420 < baseStart_2074420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074428 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2074428 : Nat := 118140960795 + 2074428 * 2 ^ 59
def prefixEnd_2074428 : Nat := 4983230072969 + 3 ^ 40 * 2074428 * 2
def baseEnd_2074428 : Nat := 1065178647145115024609885

theorem tailTrace_2074428 : CollatzResearch.WordTrace tailWord_2074428 prefixEnd_2074428 1065178647145115024609885 := by
  unfold tailWord_2074428
  simp only [CollatzResearch.WordTrace]
  refine ⟨37830302464354557470755969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50440403285806076627674625 37830302464354557470755969)
  ·
    refine ⟨28372726848265918103066977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37830302464354557470755969 28372726848265918103066977)
    ·
      refine ⟨21279545136199438577300233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28372726848265918103066977 21279545136199438577300233)
      ·
        refine ⟨15959658852149578932975175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21279545136199438577300233 15959658852149578932975175)
        ·
          refine ⟨23939488278224368399462763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15959658852149578932975175 23939488278224368399462763)
          ·
            refine ⟨35909232417336552599194145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23939488278224368399462763 35909232417336552599194145)
            ·
              refine ⟨26931924313002414449395609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35909232417336552599194145 26931924313002414449395609)
              ·
                refine ⟨20198943234751810837046707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26931924313002414449395609 20198943234751810837046707)
                ·
                  refine ⟨30298414852127716255570061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20198943234751810837046707 30298414852127716255570061)
                  ·
                    refine ⟨11361905569547893595838773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30298414852127716255570061 11361905569547893595838773)
                    ·
                      refine ⟨1065178647145115024609885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11361905569547893595838773 1065178647145115024609885)
                      ·
                        rfl

theorem cell23_2074428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2074428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074428 prefixEnd_2074428 := by exact prefixLift 2074428
  have htrace : WordTrace (prefixWord ++ tailWord_2074428) baseStart_2074428 baseEnd_2074428 := by
    simpa [prefixWord, tailWord_2074428, baseEnd_2074428] using wordTrace_append hprefix tailTrace_2074428
  have hstable : (prefixWord ++ tailWord_2074428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074428).length < 2 ^ (prefixWord ++ tailWord_2074428).sum := by decide
  have hdescent : baseEnd_2074428 < baseStart_2074428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074442 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_2074442 : Nat := 118140960795 + 2074442 * 2 ^ 59
def prefixEnd_2074442 : Nat := 4983230072969 + 3 ^ 40 * 2074442 * 2
def baseEnd_2074442 : Nat := 1065185835874277969834821

theorem tailTrace_2074442 : CollatzResearch.WordTrace tailWord_2074442 prefixEnd_2074442 1065185835874277969834821 := by
  unfold tailWord_2074442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18915278887664598833130395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50440743700438930221681053 18915278887664598833130395)
  ·
    refine ⟨28372918331496898249695593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18915278887664598833130395 28372918331496898249695593)
    ·
      refine ⟨21279688748622673687271695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28372918331496898249695593 21279688748622673687271695)
      ·
        refine ⟨31919533122934010530907543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21279688748622673687271695 31919533122934010530907543)
        ·
          refine ⟨47879299684401015796361315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31919533122934010530907543 47879299684401015796361315)
          ·
            refine ⟨71818949526601523694541973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47879299684401015796361315 71818949526601523694541973)
            ·
              refine ⟨3366513259059446423181655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71818949526601523694541973 3366513259059446423181655)
              ·
                refine ⟨5049769888589169634772483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3366513259059446423181655 5049769888589169634772483)
                ·
                  refine ⟨7574654832883754452158725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5049769888589169634772483 7574654832883754452158725)
                  ·
                    refine ⟨1420247781165703959779761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7574654832883754452158725 1420247781165703959779761)
                    ·
                      refine ⟨1065185835874277969834821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420247781165703959779761 1065185835874277969834821)
                      ·
                        rfl

theorem cell23_2074442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_2074442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074442 prefixEnd_2074442 := by exact prefixLift 2074442
  have htrace : WordTrace (prefixWord ++ tailWord_2074442) baseStart_2074442 baseEnd_2074442 := by
    simpa [prefixWord, tailWord_2074442, baseEnd_2074442] using wordTrace_append hprefix tailTrace_2074442
  have hstable : (prefixWord ++ tailWord_2074442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074442).length < 2 ^ (prefixWord ++ tailWord_2074442).sum := by decide
  have hdescent : baseEnd_2074442 < baseStart_2074442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074476 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 2, 2, 2]
def baseStart_2074476 : Nat := 118140960795 + 2074476 * 2 ^ 59
def prefixEnd_2074476 : Nat := 4983230072969 + 3 ^ 40 * 2074476 * 2
def baseEnd_2074476 : Nat := 1065203294216530836809665

theorem tailTrace_2074476 : CollatzResearch.WordTrace tailWord_2074476 prefixEnd_2074476 1065203294216530836809665 := by
  unfold tailWord_2074476
  simp only [CollatzResearch.WordTrace]
  refine ⟨37831177816267609569629641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50441570421690146092839521 37831177816267609569629641)
  ·
    refine ⟨28373383362200707177222231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37831177816267609569629641 28373383362200707177222231)
    ·
      refine ⟨42560075043301060765833347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28373383362200707177222231 42560075043301060765833347)
      ·
        refine ⟨63840112564951591148750021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42560075043301060765833347 63840112564951591148750021)
        ·
          refine ⟨11970021105928423340390629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63840112564951591148750021 11970021105928423340390629)
          ·
            refine ⟨2244378957361579376323243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11970021105928423340390629 2244378957361579376323243)
            ·
              refine ⟨3366568436042369064484865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244378957361579376323243 3366568436042369064484865)
              ·
                refine ⟨2524926327031776798363649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3366568436042369064484865 2524926327031776798363649)
                ·
                  refine ⟨1893694745273832598772737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2524926327031776798363649 1893694745273832598772737)
                  ·
                    refine ⟨1420271058955374449079553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1893694745273832598772737 1420271058955374449079553)
                    ·
                      refine ⟨1065203294216530836809665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420271058955374449079553 1065203294216530836809665)
                      ·
                        rfl

theorem cell23_2074476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_2074476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074476 prefixEnd_2074476 := by exact prefixLift 2074476
  have htrace : WordTrace (prefixWord ++ tailWord_2074476) baseStart_2074476 baseEnd_2074476 := by
    simpa [prefixWord, tailWord_2074476, baseEnd_2074476] using wordTrace_append hprefix tailTrace_2074476
  have hstable : (prefixWord ++ tailWord_2074476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074476).length < 2 ^ (prefixWord ++ tailWord_2074476).sum := by decide
  have hdescent : baseEnd_2074476 < baseStart_2074476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074488 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_2074488 : Nat := 118140960795 + 2074488 * 2 ^ 59
def prefixEnd_2074488 : Nat := 4983230072969 + 3 ^ 40 * 2074488 * 2
def baseEnd_2074488 : Nat := 1065209455984384789859609

theorem tailTrace_2074488 : CollatzResearch.WordTrace tailWord_2074488 prefixEnd_2074488 1065209455984384789859609 := by
  unfold tailWord_2074488
  simp only [CollatzResearch.WordTrace]
  refine ⟨37831396654245872594348059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50441862205661163459130745 37831396654245872594348059)
  ·
    refine ⟨56747094981368808891522089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37831396654245872594348059 56747094981368808891522089)
    ·
      refine ⟨42560321236026606668641567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56747094981368808891522089 42560321236026606668641567)
      ·
        refine ⟨63840481854039910002962351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42560321236026606668641567 63840481854039910002962351)
        ·
          refine ⟨95760722781059865004443527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63840481854039910002962351 95760722781059865004443527)
          ·
            refine ⟨143641084171589797506665291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95760722781059865004443527 143641084171589797506665291)
            ·
              refine ⟨215461626257384696259997937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143641084171589797506665291 215461626257384696259997937)
              ·
                refine ⟨161596219693038522194998453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215461626257384696259997937 161596219693038522194998453)
                ·
                  refine ⟨15149645596222361455781105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161596219693038522194998453 15149645596222361455781105)
                  ·
                    refine ⟨11362234197166771091835829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15149645596222361455781105 11362234197166771091835829)
                    ·
                      refine ⟨1065209455984384789859609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11362234197166771091835829 1065209455984384789859609)
                      ·
                        rfl

theorem cell23_2074488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_2074488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074488 prefixEnd_2074488 := by exact prefixLift 2074488
  have htrace : WordTrace (prefixWord ++ tailWord_2074488) baseStart_2074488 baseEnd_2074488 := by
    simpa [prefixWord, tailWord_2074488, baseEnd_2074488] using wordTrace_append hprefix tailTrace_2074488
  have hstable : (prefixWord ++ tailWord_2074488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074488).length < 2 ^ (prefixWord ++ tailWord_2074488).sum := by decide
  have hdescent : baseEnd_2074488 < baseStart_2074488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074508 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_2074508 : Nat := 118140960795 + 2074508 * 2 ^ 59
def prefixEnd_2074508 : Nat := 4983230072969 + 3 ^ 40 * 2074508 * 2
def baseEnd_2074508 : Nat := 355073241865824903869839

theorem tailTrace_2074508 : CollatzResearch.WordTrace tailWord_2074508 prefixEnd_2074508 355073241865824903869839 := by
  unfold tailWord_2074508
  simp only [CollatzResearch.WordTrace]
  refine ⟨37831761384209644302212089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50442348512279525736282785 37831761384209644302212089)
  ·
    refine ⟨28373821038157233226659067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37831761384209644302212089 28373821038157233226659067)
    ·
      refine ⟨42560731557235849839988601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28373821038157233226659067 42560731557235849839988601)
      ·
        refine ⟨31920548667926887379991451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42560731557235849839988601 31920548667926887379991451)
        ·
          refine ⟨47880823001890331069987177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31920548667926887379991451 47880823001890331069987177)
          ·
            refine ⟨35910617251417748302490383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47880823001890331069987177 35910617251417748302490383)
            ·
              refine ⟨53865925877126622453735575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35910617251417748302490383 53865925877126622453735575)
              ·
                refine ⟨80798888815689933680603363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53865925877126622453735575 80798888815689933680603363)
                ·
                  refine ⟨121198333223534900520905045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80798888815689933680603363 121198333223534900520905045)
                  ·
                    refine ⟨355073241865824903869839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 121198333223534900520905045 355073241865824903869839)
                    ·
                      rfl

theorem cell23_2074508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_2074508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074508 prefixEnd_2074508 := by exact prefixLift 2074508
  have htrace : WordTrace (prefixWord ++ tailWord_2074508) baseStart_2074508 baseEnd_2074508 := by
    simpa [prefixWord, tailWord_2074508, baseEnd_2074508] using wordTrace_append hprefix tailTrace_2074508
  have hstable : (prefixWord ++ tailWord_2074508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074508).length < 2 ^ (prefixWord ++ tailWord_2074508).sum := by decide
  have hdescent : baseEnd_2074508 < baseStart_2074508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074532 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_2074532 : Nat := 118140960795 + 2074532 * 2 ^ 59
def prefixEnd_2074532 : Nat := 4983230072969 + 3 ^ 40 * 2074532 * 2
def baseEnd_2074532 : Nat := 1065232049133182617709407

theorem tailTrace_2074532 : CollatzResearch.WordTrace tailWord_2074532 prefixEnd_2074532 1065232049133182617709407 := by
  unfold tailWord_2074532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37832199060166170351648925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50442932080221560468865233 37832199060166170351648925)
  ·
    refine ⟨14187074647562313881868347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37832199060166170351648925 14187074647562313881868347)
    ·
      refine ⟨21280611971343470822802521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14187074647562313881868347 21280611971343470822802521)
      ·
        refine ⟨15960458978507603117101891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21280611971343470822802521 15960458978507603117101891)
        ·
          refine ⟨23940688467761404675652837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15960458978507603117101891 23940688467761404675652837)
          ·
            refine ⟨4488879087705263376684907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23940688467761404675652837 4488879087705263376684907)
            ·
              refine ⟨6733318631557895065027361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488879087705263376684907 6733318631557895065027361)
              ·
                refine ⟨5049988973668421298770521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6733318631557895065027361 5049988973668421298770521)
                ·
                  refine ⟨3787491730251315974077891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5049988973668421298770521 3787491730251315974077891)
                  ·
                    refine ⟨5681237595376973961116837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3787491730251315974077891 5681237595376973961116837)
                    ·
                      refine ⟨1065232049133182617709407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5681237595376973961116837 1065232049133182617709407)
                      ·
                        rfl

theorem cell23_2074532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_2074532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074532 prefixEnd_2074532 := by exact prefixLift 2074532
  have htrace : WordTrace (prefixWord ++ tailWord_2074532) baseStart_2074532 baseEnd_2074532 := by
    simpa [prefixWord, tailWord_2074532, baseEnd_2074532] using wordTrace_append hprefix tailTrace_2074532
  have hstable : (prefixWord ++ tailWord_2074532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074532).length < 2 ^ (prefixWord ++ tailWord_2074532).sum := by decide
  have hdescent : baseEnd_2074532 < baseStart_2074532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074589 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 6]
def baseStart_2074589 : Nat := 118140960795 + 2074589 * 2 ^ 59
def prefixEnd_2074589 : Nat := 4983230072969 + 3 ^ 40 * 2074589 * 2
def baseEnd_2074589 : Nat := 118362368614498766077405

theorem tailTrace_2074589 : CollatzResearch.WordTrace tailWord_2074589 prefixEnd_2074589 118362368614498766077405 := by
  unfold tailWord_2074589
  simp only [CollatzResearch.WordTrace]
  refine ⟨75666477081125839438122821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50444318054083892958748547 75666477081125839438122821)
  ·
    refine ⟨14187464452711094894648029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75666477081125839438122821 14187464452711094894648029)
    ·
      refine ⟨5320299169766660585493011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14187464452711094894648029 5320299169766660585493011)
      ·
        refine ⟨7980448754649990878239517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320299169766660585493011 7980448754649990878239517)
        ·
          refine ⟨2992668282993746579339819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7980448754649990878239517 2992668282993746579339819)
          ·
            refine ⟨4489002424490619869009729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992668282993746579339819 4489002424490619869009729)
            ·
              refine ⟨3366751818367964901757297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489002424490619869009729 3366751818367964901757297)
              ·
                refine ⟨2525063863775973676317973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3366751818367964901757297 2525063863775973676317973)
                ·
                  refine ⟨118362368614498766077405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2525063863775973676317973 118362368614498766077405)
                  ·
                    rfl

theorem cell23_2074589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_2074589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074589 prefixEnd_2074589 := by exact prefixLift 2074589
  have htrace : WordTrace (prefixWord ++ tailWord_2074589) baseStart_2074589 baseEnd_2074589 := by
    simpa [prefixWord, tailWord_2074589, baseEnd_2074589] using wordTrace_append hprefix tailTrace_2074589
  have hstable : (prefixWord ++ tailWord_2074589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074589).length < 2 ^ (prefixWord ++ tailWord_2074589).sum := by decide
  have hdescent : baseEnd_2074589 < baseStart_2074589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074632 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 4, 4]
def baseStart_2074632 : Nat := 118140960795 + 2074632 * 2 ^ 59
def prefixEnd_2074632 : Nat := 4983230072969 + 3 ^ 40 * 2074632 * 2
def baseEnd_2074632 : Nat := 355094465732877408819649

theorem tailTrace_2074632 : CollatzResearch.WordTrace tailWord_2074632 prefixEnd_2074632 355094465732877408819649 := by
  unfold tailWord_2074632
  simp only [CollatzResearch.WordTrace]
  refine ⟨37834022709985028890969075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50445363613313371854625433 37834022709985028890969075)
  ·
    refine ⟨56751034064977543336453613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37834022709985028890969075 56751034064977543336453613)
    ·
      refine ⟨21281637774366578751170105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56751034064977543336453613 21281637774366578751170105)
      ·
        refine ⟨15961228330774934063377579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21281637774366578751170105 15961228330774934063377579)
        ·
          refine ⟨23941842496162401095066369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15961228330774934063377579 23941842496162401095066369)
          ·
            refine ⟨17956381872121800821299777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23941842496162401095066369 17956381872121800821299777)
            ·
              refine ⟨13467286404091350615974833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17956381872121800821299777 13467286404091350615974833)
              ·
                refine ⟨10100464803068512961981125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13467286404091350615974833 10100464803068512961981125)
                ·
                  refine ⟨1893837150575346180371461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10100464803068512961981125 1893837150575346180371461)
                  ·
                    refine ⟨355094465732877408819649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1893837150575346180371461 355094465732877408819649)
                    ·
                      rfl

theorem cell23_2074632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_2074632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074632 prefixEnd_2074632 := by exact prefixLift 2074632
  have htrace : WordTrace (prefixWord ++ tailWord_2074632) baseStart_2074632 baseEnd_2074632 := by
    simpa [prefixWord, tailWord_2074632, baseEnd_2074632] using wordTrace_append hprefix tailTrace_2074632
  have hstable : (prefixWord ++ tailWord_2074632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074632).length < 2 ^ (prefixWord ++ tailWord_2074632).sum := by decide
  have hdescent : baseEnd_2074632 < baseStart_2074632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074675 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 2, 7]
def baseStart_2074675 : Nat := 118140960795 + 2074675 * 2 ^ 59
def prefixEnd_2074675 : Nat := 4983230072969 + 3 ^ 40 * 2074675 * 2
def baseEnd_2074675 : Nat := 355101825622258519407083

theorem tailTrace_2074675 : CollatzResearch.WordTrace tailWord_2074675 prefixEnd_2074675 355101825622258519407083 := by
  unfold tailWord_2074675
  simp only [CollatzResearch.WordTrace]
  refine ⟨75669613758814276125753479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50446409172542850750502319 75669613758814276125753479)
  ·
    refine ⟨113504420638221414188630219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75669613758814276125753479 113504420638221414188630219)
    ·
      refine ⟨170256630957332121282945329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113504420638221414188630219 170256630957332121282945329)
      ·
        refine ⟨127692473217999090962208997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170256630957332121282945329 127692473217999090962208997)
        ·
          refine ⟨23942338728374829555414187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127692473217999090962208997 23942338728374829555414187)
          ·
            refine ⟨35913508092562244333121281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23942338728374829555414187 35913508092562244333121281)
            ·
              refine ⟨26935131069421683249840961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35913508092562244333121281 26935131069421683249840961)
              ·
                refine ⟨20201348302066262437380721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26935131069421683249840961 20201348302066262437380721)
                ·
                  refine ⟨15151011226549696828035541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20201348302066262437380721 15151011226549696828035541)
                  ·
                    refine ⟨355101825622258519407083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15151011226549696828035541 355101825622258519407083)
                    ·
                      rfl

theorem cell23_2074675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 7].length) (baseStart_2074675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074675 prefixEnd_2074675 := by exact prefixLift 2074675
  have htrace : WordTrace (prefixWord ++ tailWord_2074675) baseStart_2074675 baseEnd_2074675 := by
    simpa [prefixWord, tailWord_2074675, baseEnd_2074675] using wordTrace_append hprefix tailTrace_2074675
  have hstable : (prefixWord ++ tailWord_2074675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074675).length < 2 ^ (prefixWord ++ tailWord_2074675).sum := by decide
  have hdescent : baseEnd_2074675 < baseStart_2074675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074729 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 1, 4, 2]
def baseStart_2074729 : Nat := 118140960795 + 2074729 * 2 ^ 59
def prefixEnd_2074729 : Nat := 4983230072969 + 3 ^ 40 * 2074729 * 2
def baseEnd_2074729 : Nat := 1065333204822118346946001

theorem tailTrace_2074729 : CollatzResearch.WordTrace tailWord_2074729 prefixEnd_2074729 1065333204822118346946001 := by
  unfold tailWord_2074729
  simp only [CollatzResearch.WordTrace]
  refine ⟨75671583300618643348219241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50447722200412428898812827 75671583300618643348219241)
  ·
    refine ⟨56753687475463982511164431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75671583300618643348219241 56753687475463982511164431)
    ·
      refine ⟨85130531213195973766746647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56753687475463982511164431 85130531213195973766746647)
      ·
        refine ⟨127695796819793960650119971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85130531213195973766746647 127695796819793960650119971)
        ·
          refine ⟨191543695229690940975179957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127695796819793960650119971 191543695229690940975179957)
          ·
            refine ⟨17957221427783525716423121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191543695229690940975179957 17957221427783525716423121)
            ·
              refine ⟨13467916070837644287317341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17957221427783525716423121 13467916070837644287317341)
              ·
                refine ⟨5050468526564116607744003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13467916070837644287317341 5050468526564116607744003)
                ·
                  refine ⟨7575702789846174911616005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050468526564116607744003 7575702789846174911616005)
                  ·
                    refine ⟨1420444273096157795928001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7575702789846174911616005 1420444273096157795928001)
                    ·
                      refine ⟨1065333204822118346946001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420444273096157795928001 1065333204822118346946001)
                      ·
                        rfl

theorem cell23_2074729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 4, 2].length) (baseStart_2074729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074729 prefixEnd_2074729 := by exact prefixLift 2074729
  have htrace : WordTrace (prefixWord ++ tailWord_2074729) baseStart_2074729 baseEnd_2074729 := by
    simpa [prefixWord, tailWord_2074729, baseEnd_2074729] using wordTrace_append hprefix tailTrace_2074729
  have hstable : (prefixWord ++ tailWord_2074729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074729).length < 2 ^ (prefixWord ++ tailWord_2074729).sum := by decide
  have hdescent : baseEnd_2074729 < baseStart_2074729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074732 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_2074732 : Nat := 118140960795 + 2074732 * 2 ^ 59
def prefixEnd_2074732 : Nat := 4983230072969 + 3 ^ 40 * 2074732 * 2
def baseEnd_2074732 : Nat := 1065334745264081835208487

theorem tailTrace_2074732 : CollatzResearch.WordTrace tailWord_2074732 prefixEnd_2074732 1065334745264081835208487 := by
  unfold tailWord_2074732
  simp only [CollatzResearch.WordTrace]
  refine ⟨37835846359803887430289225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50447795146405183240385633 37835846359803887430289225)
  ·
    refine ⟨28376884769852915572716919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37835846359803887430289225 28376884769852915572716919)
    ·
      refine ⟨42565327154779373359075379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28376884769852915572716919 42565327154779373359075379)
      ·
        refine ⟨63847990732169060038613069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42565327154779373359075379 63847990732169060038613069)
        ·
          refine ⟨23942996524563397514479901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63847990732169060038613069 23942996524563397514479901)
          ·
            refine ⟨8978623696711274067929963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23942996524563397514479901 8978623696711274067929963)
            ·
              refine ⟨13467935545066911101894945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8978623696711274067929963 13467935545066911101894945)
              ·
                refine ⟨10100951658800183326421209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13467935545066911101894945 10100951658800183326421209)
                ·
                  refine ⟨7575713744100137494815907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10100951658800183326421209 7575713744100137494815907)
                  ·
                    refine ⟨11363570616150206242223861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7575713744100137494815907 11363570616150206242223861)
                    ·
                      refine ⟨1065334745264081835208487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11363570616150206242223861 1065334745264081835208487)
                      ·
                        rfl

theorem cell23_2074732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_2074732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074732 prefixEnd_2074732 := by exact prefixLift 2074732
  have htrace : WordTrace (prefixWord ++ tailWord_2074732) baseStart_2074732 baseEnd_2074732 := by
    simpa [prefixWord, tailWord_2074732, baseEnd_2074732] using wordTrace_append hprefix tailTrace_2074732
  have hstable : (prefixWord ++ tailWord_2074732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074732).length < 2 ^ (prefixWord ++ tailWord_2074732).sum := by decide
  have hdescent : baseEnd_2074732 < baseStart_2074732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074789 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 2, 5, 2]
def baseStart_2074789 : Nat := 118140960795 + 2074789 * 2 ^ 59
def prefixEnd_2074789 : Nat := 4983230072969 + 3 ^ 40 * 2074789 * 2
def baseEnd_2074789 : Nat := 1065364013661388112195725

theorem tailTrace_2074789 : CollatzResearch.WordTrace tailWord_2074789 prefixEnd_2074789 1065364013661388112195725 := by
  unfold tailWord_2074789
  simp only [CollatzResearch.WordTrace]
  refine ⟨75673771680401273595403421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50449181120267515730268947 75673771680401273595403421)
  ·
    refine ⟨28377664380150477598276283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75673771680401273595403421 28377664380150477598276283)
    ·
      refine ⟨42566496570225716397414425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28377664380150477598276283 42566496570225716397414425)
      ·
        refine ⟨31924872427669287298060819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42566496570225716397414425 31924872427669287298060819)
        ·
          refine ⟨47887308641503930947091229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31924872427669287298060819 47887308641503930947091229)
          ·
            refine ⟨17957740740563974105159211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47887308641503930947091229 17957740740563974105159211)
            ·
              refine ⟨26936611110845961157738817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17957740740563974105159211 26936611110845961157738817)
              ·
                refine ⟨20202458333134470868304113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26936611110845961157738817 20202458333134470868304113)
                ·
                  refine ⟨15151843749850853151228085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20202458333134470868304113 15151843749850853151228085)
                  ·
                    refine ⟨1420485351548517482927633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15151843749850853151228085 1420485351548517482927633)
                    ·
                      refine ⟨1065364013661388112195725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420485351548517482927633 1065364013661388112195725)
                      ·
                        rfl

theorem cell23_2074789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_2074789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074789 prefixEnd_2074789 := by exact prefixLift 2074789
  have htrace : WordTrace (prefixWord ++ tailWord_2074789) baseStart_2074789 baseEnd_2074789 := by
    simpa [prefixWord, tailWord_2074789, baseEnd_2074789] using wordTrace_append hprefix tailTrace_2074789
  have hstable : (prefixWord ++ tailWord_2074789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074789).length < 2 ^ (prefixWord ++ tailWord_2074789).sum := by decide
  have hdescent : baseEnd_2074789 < baseStart_2074789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074863 : List Nat := [1, 1, 2, 1, 6, 1, 3, 3, 1, 4]
def baseStart_2074863 : Nat := 118140960795 + 2074863 * 2 ^ 59
def prefixEnd_2074863 : Nat := 4983230072969 + 3 ^ 40 * 2074863 * 2
def baseEnd_2074863 : Nat := 355134003743273607556795

theorem tailTrace_2074863 : CollatzResearch.WordTrace tailWord_2074863 prefixEnd_2074863 355134003743273607556795 := by
  unfold tailWord_2074863
  simp only [CollatzResearch.WordTrace]
  refine ⟨75676470682133184233597243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50450980454755456155731495 75676470682133184233597243)
  ·
    refine ⟨113514706023199776350395865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75676470682133184233597243 113514706023199776350395865)
    ·
      refine ⟨85136029517399832262796899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113514706023199776350395865 85136029517399832262796899)
      ·
        refine ⟨127704044276099748394195349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85136029517399832262796899 127704044276099748394195349)
        ·
          refine ⟨5986127075442175705977907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127704044276099748394195349 5986127075442175705977907)
          ·
            refine ⟨8979190613163263558966861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986127075442175705977907 8979190613163263558966861)
            ·
              refine ⟨3367196479936223834612573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8979190613163263558966861 3367196479936223834612573)
              ·
                refine ⟨1262698679976083937979715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3367196479936223834612573 1262698679976083937979715)
                ·
                  refine ⟨1894048019964125906969573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262698679976083937979715 1894048019964125906969573)
                  ·
                    refine ⟨355134003743273607556795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1894048019964125906969573 355134003743273607556795)
                    ·
                      rfl

theorem cell23_2074863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 4].length) (baseStart_2074863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074863 prefixEnd_2074863 := by exact prefixLift 2074863
  have htrace : WordTrace (prefixWord ++ tailWord_2074863) baseStart_2074863 baseEnd_2074863 := by
    simpa [prefixWord, tailWord_2074863, baseEnd_2074863] using wordTrace_append hprefix tailTrace_2074863
  have hstable : (prefixWord ++ tailWord_2074863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074863).length < 2 ^ (prefixWord ++ tailWord_2074863).sum := by decide
  have hdescent : baseEnd_2074863 < baseStart_2074863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074906 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_2074906 : Nat := 118140960795 + 2074906 * 2 ^ 59
def prefixEnd_2074906 : Nat := 4983230072969 + 3 ^ 40 * 2074906 * 2
def baseEnd_2074906 : Nat := 355141363632654718144229

theorem tailTrace_2074906 : CollatzResearch.WordTrace tailWord_2074906 prefixEnd_2074906 355141363632654718144229 := by
  unfold tailWord_2074906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18919509755244350644353143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50452026013984935051608381 18919509755244350644353143)
  ·
    refine ⟨28379264632866525966529715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18919509755244350644353143 28379264632866525966529715)
    ·
      refine ⟨42568896949299788949794573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28379264632866525966529715 42568896949299788949794573)
      ·
        refine ⟨15963336355987420856172965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42568896949299788949794573 15963336355987420856172965)
        ·
          refine ⟨2993125566747641410532431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15963336355987420856172965 2993125566747641410532431)
          ·
            refine ⟨4489688350121462115798647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993125566747641410532431 4489688350121462115798647)
            ·
              refine ⟨6734532525182193173697971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489688350121462115798647 6734532525182193173697971)
              ·
                refine ⟨10101798787773289760546957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734532525182193173697971 10101798787773289760546957)
                ·
                  refine ⟨3788174545414983660205109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10101798787773289760546957 3788174545414983660205109)
                  ·
                    refine ⟨355141363632654718144229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3788174545414983660205109 355141363632654718144229)
                    ·
                      rfl

theorem cell23_2074906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_2074906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074906 prefixEnd_2074906 := by exact prefixLift 2074906
  have htrace : WordTrace (prefixWord ++ tailWord_2074906) baseStart_2074906 baseEnd_2074906 := by
    simpa [prefixWord, tailWord_2074906, baseEnd_2074906] using wordTrace_append hprefix tailTrace_2074906
  have hstable : (prefixWord ++ tailWord_2074906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074906).length < 2 ^ (prefixWord ++ tailWord_2074906).sum := by decide
  have hdescent : baseEnd_2074906 < baseStart_2074906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074936 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 2, 4]
def baseStart_2074936 : Nat := 118140960795 + 2074936 * 2 ^ 59
def prefixEnd_2074936 : Nat := 4983230072969 + 3 ^ 40 * 2074936 * 2
def baseEnd_2074936 : Nat := 355146498439199679019183

theorem tailTrace_2074936 : CollatzResearch.WordTrace tailWord_2074936 prefixEnd_2074936 355146498439199679019183 := by
  unfold tailWord_2074936
  simp only [CollatzResearch.WordTrace]
  refine ⟨37839566605434358850502331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50452755473912478467336441 37839566605434358850502331)
  ·
    refine ⟨56759349908151538275753497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37839566605434358850502331 56759349908151538275753497)
    ·
      refine ⟨42569512431113653706815123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56759349908151538275753497 42569512431113653706815123)
      ·
        refine ⟨63854268646670480560222685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42569512431113653706815123 63854268646670480560222685)
        ·
          refine ⟨23945350742501430210083507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63854268646670480560222685 23945350742501430210083507)
          ·
            refine ⟨35918026113752145315125261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23945350742501430210083507 35918026113752145315125261)
            ·
              refine ⟨13469259792657054493171973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35918026113752145315125261 13469259792657054493171973)
              ·
                refine ⟨2525486211123197717469745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13469259792657054493171973 2525486211123197717469745)
                ·
                  refine ⟨1894114658342398288102309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2525486211123197717469745 1894114658342398288102309)
                  ·
                    refine ⟨355146498439199679019183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1894114658342398288102309 355146498439199679019183)
                    ·
                      rfl

theorem cell23_2074936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_2074936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074936 prefixEnd_2074936 := by exact prefixLift 2074936
  have htrace : WordTrace (prefixWord ++ tailWord_2074936) baseStart_2074936 baseEnd_2074936 := by
    simpa [prefixWord, tailWord_2074936, baseEnd_2074936] using wordTrace_append hprefix tailTrace_2074936
  have hstable : (prefixWord ++ tailWord_2074936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074936).length < 2 ^ (prefixWord ++ tailWord_2074936).sum := by decide
  have hdescent : baseEnd_2074936 < baseStart_2074936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074937 : List Nat := [1, 2, 1, 6, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2074937 : Nat := 118140960795 + 2074937 * 2 ^ 59
def prefixEnd_2074937 : Nat := 4983230072969 + 3 ^ 40 * 2074937 * 2
def baseEnd_2074937 : Nat := 1065440008798253533145045

theorem tailTrace_2074937 : CollatzResearch.WordTrace tailWord_2074937 prefixEnd_2074937 1065440008798253533145045 := by
  unfold tailWord_2074937
  simp only [CollatzResearch.WordTrace]
  refine ⟨75679169683865094871791065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50452779789243396581194043 75679169683865094871791065)
  ·
    refine ⟨56759377262898821153843299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75679169683865094871791065 56759377262898821153843299)
    ·
      refine ⟨85139065894348231730764949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56759377262898821153843299 85139065894348231730764949)
      ·
        refine ⟨3990893713797573362379607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85139065894348231730764949 3990893713797573362379607)
        ·
          refine ⟨5986340570696360043569411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990893713797573362379607 5986340570696360043569411)
          ·
            refine ⟨8979510856044540065354117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986340570696360043569411 8979510856044540065354117)
            ·
              refine ⟨1683658285508351262253897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8979510856044540065354117 1683658285508351262253897)
              ·
                refine ⟨1262743714131263446690423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1683658285508351262253897 1262743714131263446690423)
                ·
                  refine ⟨1894115571196895170035635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1262743714131263446690423 1894115571196895170035635)
                  ·
                    refine ⟨2841173356795342755053453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1894115571196895170035635 2841173356795342755053453)
                    ·
                      refine ⟨1065440008798253533145045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2841173356795342755053453 1065440008798253533145045)
                      ·
                        rfl

theorem cell23_2074937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2074937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074937 prefixEnd_2074937 := by exact prefixLift 2074937
  have htrace : WordTrace (prefixWord ++ tailWord_2074937) baseStart_2074937 baseEnd_2074937 := by
    simpa [prefixWord, tailWord_2074937, baseEnd_2074937] using wordTrace_append hprefix tailTrace_2074937
  have hstable : (prefixWord ++ tailWord_2074937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074937).length < 2 ^ (prefixWord ++ tailWord_2074937).sum := by decide
  have hdescent : baseEnd_2074937 < baseStart_2074937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074943 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 3, 2, 2]
def baseStart_2074943 : Nat := 118140960795 + 2074943 * 2 ^ 59
def prefixEnd_2074943 : Nat := 4983230072969 + 3 ^ 40 * 2074943 * 2
def baseEnd_2074943 : Nat := 1065443089682180509670017

theorem tailTrace_2074943 : CollatzResearch.WordTrace tailWord_2074943 prefixEnd_2074943 1065443089682180509670017 := by
  unfold tailWord_2074943
  simp only [CollatzResearch.WordTrace]
  refine ⟨75679388521843357896509483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50452925681228905264339655 75679388521843357896509483)
  ·
    refine ⟨113519082782765036844764225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75679388521843357896509483 113519082782765036844764225)
    ·
      refine ⟨85139312087073777633573169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113519082782765036844764225 85139312087073777633573169)
      ·
        refine ⟨63854484065305333225179877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85139312087073777633573169 63854484065305333225179877)
        ·
          refine ⟨11972715762244749979721227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63854484065305333225179877 11972715762244749979721227)
          ·
            refine ⟨17959073643367124969581841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11972715762244749979721227 17959073643367124969581841)
            ·
              refine ⟨13469305232525343727186381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17959073643367124969581841 13469305232525343727186381)
              ·
                refine ⟨5050989462197003897694893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13469305232525343727186381 5050989462197003897694893)
                ·
                  refine ⟨1894121048323876461635585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5050989462197003897694893 1894121048323876461635585)
                  ·
                    refine ⟨1420590786242907346226689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1894121048323876461635585 1420590786242907346226689)
                    ·
                      refine ⟨1065443089682180509670017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420590786242907346226689 1065443089682180509670017)
                      ·
                        rfl

theorem cell23_2074943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_2074943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074943 prefixEnd_2074943 := by exact prefixLift 2074943
  have htrace : WordTrace (prefixWord ++ tailWord_2074943) baseStart_2074943 baseEnd_2074943 := by
    simpa [prefixWord, tailWord_2074943, baseEnd_2074943] using wordTrace_append hprefix tailTrace_2074943
  have hstable : (prefixWord ++ tailWord_2074943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074943).length < 2 ^ (prefixWord ++ tailWord_2074943).sum := by decide
  have hdescent : baseEnd_2074943 < baseStart_2074943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074956 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2074956 : Nat := 118140960795 + 2074956 * 2 ^ 59
def prefixEnd_2074956 : Nat := 4983230072969 + 3 ^ 40 * 2074956 * 2
def baseEnd_2074956 : Nat := 1065449764930688958807457

theorem tailTrace_2074956 : CollatzResearch.WordTrace tailWord_2074956 prefixEnd_2074956 1065449764930688958807457 := by
  unfold tailWord_2074956
  simp only [CollatzResearch.WordTrace]
  refine ⟨37839931335398130558366361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50453241780530840744488481 37839931335398130558366361)
  ·
    refine ⟨28379948501548597918774771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37839931335398130558366361 28379948501548597918774771)
    ·
      refine ⟨42569922752322896878162157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28379948501548597918774771 42569922752322896878162157)
      ·
        refine ⟨15963721032121086329310809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42569922752322896878162157 15963721032121086329310809)
        ·
          refine ⟨11972790774090814746983107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15963721032121086329310809 11972790774090814746983107)
          ·
            refine ⟨17959186161136222120474661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11972790774090814746983107 17959186161136222120474661)
            ·
              refine ⟨3367347405213041647588999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17959186161136222120474661 3367347405213041647588999)
              ·
                refine ⟨5051021107819562471383499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367347405213041647588999 5051021107819562471383499)
                ·
                  refine ⟨7576531661729343707075249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051021107819562471383499 7576531661729343707075249)
                  ·
                    refine ⟨5682398746297007780306437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7576531661729343707075249 5682398746297007780306437)
                    ·
                      refine ⟨1065449764930688958807457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5682398746297007780306437 1065449764930688958807457)
                      ·
                        rfl

theorem cell23_2074956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2074956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074956 prefixEnd_2074956 := by exact prefixLift 2074956
  have htrace : WordTrace (prefixWord ++ tailWord_2074956) baseStart_2074956 baseEnd_2074956 := by
    simpa [prefixWord, tailWord_2074956, baseEnd_2074956] using wordTrace_append hprefix tailTrace_2074956
  have hstable : (prefixWord ++ tailWord_2074956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074956).length < 2 ^ (prefixWord ++ tailWord_2074956).sum := by decide
  have hdescent : baseEnd_2074956 < baseStart_2074956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074974 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2074974 : Nat := 118140960795 + 2074974 * 2 ^ 59
def prefixEnd_2074974 : Nat := 4983230072969 + 3 ^ 40 * 2074974 * 2
def baseEnd_2074974 : Nat := 355153002527489962794125

theorem tailTrace_2074974 : CollatzResearch.WordTrace tailWord_2074974 prefixEnd_2074974 355153002527489962794125 := by
  unfold tailWord_2074974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460064898091381273860997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50453679456487366793925317 9460064898091381273860997)
  ·
    refine ⟨1773762168392133988848937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9460064898091381273860997 1773762168392133988848937)
    ·
      refine ⟨1330321626294100491636703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1773762168392133988848937 1330321626294100491636703)
      ·
        refine ⟨1995482439441150737455055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330321626294100491636703 1995482439441150737455055)
        ·
          refine ⟨2993223659161726106182583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995482439441150737455055 2993223659161726106182583)
          ·
            refine ⟨4489835488742589159273875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993223659161726106182583 4489835488742589159273875)
            ·
              refine ⟨6734753233113883738910813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489835488742589159273875 6734753233113883738910813)
              ·
                refine ⟨2525532462417706402091555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6734753233113883738910813 2525532462417706402091555)
                ·
                  refine ⟨3788298693626559603137333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525532462417706402091555 3788298693626559603137333)
                  ·
                    refine ⟨355153002527489962794125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3788298693626559603137333 355153002527489962794125)
                    ·
                      rfl

theorem cell23_2074974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2074974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074974 prefixEnd_2074974 := by exact prefixLift 2074974
  have htrace : WordTrace (prefixWord ++ tailWord_2074974) baseStart_2074974 baseEnd_2074974 := by
    simpa [prefixWord, tailWord_2074974, baseEnd_2074974] using wordTrace_append hprefix tailTrace_2074974
  have hstable : (prefixWord ++ tailWord_2074974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074974).length < 2 ^ (prefixWord ++ tailWord_2074974).sum := by decide
  have hdescent : baseEnd_2074974 < baseStart_2074974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2074999 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_2074999 : Nat := 118140960795 + 2074999 * 2 ^ 59
def prefixEnd_2074999 : Nat := 4983230072969 + 3 ^ 40 * 2074999 * 2
def baseEnd_2074999 : Nat := 1065471844598832290569759

theorem tailTrace_2074999 : CollatzResearch.WordTrace tailWord_2074999 prefixEnd_2074999 1065471844598832290569759 := by
  unfold tailWord_2074999
  simp only [CollatzResearch.WordTrace]
  refine ⟨75681431009640479460548051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50454287339760319640365367 75681431009640479460548051)
  ·
    refine ⟨113522146514460719190822077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75681431009640479460548051 113522146514460719190822077)
    ·
      refine ⟨42570804942922769696558279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113522146514460719190822077 42570804942922769696558279)
      ·
        refine ⟨63856207414384154544837419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42570804942922769696558279 63856207414384154544837419)
        ·
          refine ⟨95784311121576231817256129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63856207414384154544837419 95784311121576231817256129)
          ·
            refine ⟨71838233341182173862942097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95784311121576231817256129 71838233341182173862942097)
            ·
              refine ⟨53878675005886630397206573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71838233341182173862942097 53878675005886630397206573)
              ·
                refine ⟨20204503127207486398952465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53878675005886630397206573 20204503127207486398952465)
                ·
                  refine ⟨15153377345405614799214349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20204503127207486398952465 15153377345405614799214349)
                  ·
                    refine ⟨5682516504527105549705381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15153377345405614799214349 5682516504527105549705381)
                    ·
                      refine ⟨1065471844598832290569759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5682516504527105549705381 1065471844598832290569759)
                      ·
                        rfl

theorem cell23_2074999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_2074999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2074999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2074999 prefixEnd_2074999 := by exact prefixLift 2074999
  have htrace : WordTrace (prefixWord ++ tailWord_2074999) baseStart_2074999 baseEnd_2074999 := by
    simpa [prefixWord, tailWord_2074999, baseEnd_2074999] using wordTrace_append hprefix tailTrace_2074999
  have hstable : (prefixWord ++ tailWord_2074999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2074999).length < 2 ^ (prefixWord ++ tailWord_2074999).sum := by decide
  have hdescent : baseEnd_2074999 < baseStart_2074999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2074999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075020 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 1, 3, 2]
def baseStart_2075020 : Nat := 118140960795 + 2075020 * 2 ^ 59
def prefixEnd_2075020 : Nat := 4983230072969 + 3 ^ 40 * 2075020 * 2
def baseEnd_2075020 : Nat := 1065482627692576708407163

theorem tailTrace_2075020 : CollatzResearch.WordTrace tailWord_2075020 prefixEnd_2075020 1065482627692576708407163 := by
  unfold tailWord_2075020
  simp only [CollatzResearch.WordTrace]
  refine ⟨37841098471282200023531257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50454797961709600031375009 37841098471282200023531257)
  ·
    refine ⟨28380823853461650017648443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37841098471282200023531257 28380823853461650017648443)
    ·
      refine ⟨42571235780192475026472665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28380823853461650017648443 42571235780192475026472665)
      ·
        refine ⟨31928426835144356269854499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42571235780192475026472665 31928426835144356269854499)
        ·
          refine ⟨47892640252716534404781749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31928426835144356269854499 47892640252716534404781749)
          ·
            refine ⟨4489935023692175100448289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47892640252716534404781749 4489935023692175100448289)
            ·
              refine ⟨3367451267769131325336217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489935023692175100448289 3367451267769131325336217)
              ·
                refine ⟨2525588450826848494002163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3367451267769131325336217 2525588450826848494002163)
                ·
                  refine ⟨3788382676240272741003245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525588450826848494002163 3788382676240272741003245)
                  ·
                    refine ⟨1420643503590102277876217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3788382676240272741003245 1420643503590102277876217)
                    ·
                      refine ⟨1065482627692576708407163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420643503590102277876217 1065482627692576708407163)
                      ·
                        rfl

theorem cell23_2075020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_2075020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075020 prefixEnd_2075020 := by exact prefixLift 2075020
  have htrace : WordTrace (prefixWord ++ tailWord_2075020) baseStart_2075020 baseEnd_2075020 := by
    simpa [prefixWord, tailWord_2075020, baseEnd_2075020] using wordTrace_append hprefix tailTrace_2075020
  have hstable : (prefixWord ++ tailWord_2075020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075020).length < 2 ^ (prefixWord ++ tailWord_2075020).sum := by decide
  have hdescent : baseEnd_2075020 < baseStart_2075020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075033 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 6, 2, 2]
def baseStart_2075033 : Nat := 118140960795 + 2075033 * 2 ^ 59
def prefixEnd_2075033 : Nat := 4983230072969 + 3 ^ 40 * 2075033 * 2
def baseEnd_2075033 : Nat := 1065489302941085157544603

theorem tailTrace_2075033 : CollatzResearch.WordTrace tailWord_2075033 prefixEnd_2075033 1065489302941085157544603 := by
  unfold tailWord_2075033
  simp only [CollatzResearch.WordTrace]
  refine ⟨75682671091517303267285753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50455114061011535511523835 75682671091517303267285753)
  ·
    refine ⟨56762003318637977450464315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75682671091517303267285753 56762003318637977450464315)
    ·
      refine ⟨85143004977956966175696473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56762003318637977450464315 85143004977956966175696473)
      ·
        refine ⟨63857253733467724631772355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85143004977956966175696473 63857253733467724631772355)
        ·
          refine ⟨95785880600201586947658533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63857253733467724631772355 95785880600201586947658533)
          ·
            refine ⟨17959852612537797552685975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95785880600201586947658533 17959852612537797552685975)
            ·
              refine ⟨26939778918806696329028963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17959852612537797552685975 26939778918806696329028963)
              ·
                refine ⟨40409668378210044493543445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26939778918806696329028963 40409668378210044493543445)
                ·
                  refine ⟨1894203205228595835634849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40409668378210044493543445 1894203205228595835634849)
                  ·
                    refine ⟨1420652403921446876726137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1894203205228595835634849 1420652403921446876726137)
                    ·
                      refine ⟨1065489302941085157544603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420652403921446876726137 1065489302941085157544603)
                      ·
                        rfl

theorem cell23_2075033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_2075033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075033 prefixEnd_2075033 := by exact prefixLift 2075033
  have htrace : WordTrace (prefixWord ++ tailWord_2075033) baseStart_2075033 baseEnd_2075033 := by
    simpa [prefixWord, tailWord_2075033, baseEnd_2075033] using wordTrace_append hprefix tailTrace_2075033
  have hstable : (prefixWord ++ tailWord_2075033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075033).length < 2 ^ (prefixWord ++ tailWord_2075033).sum := by decide
  have hdescent : baseEnd_2075033 < baseStart_2075033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075066 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_2075066 : Nat := 118140960795 + 2075066 * 2 ^ 59
def prefixEnd_2075066 : Nat := 4983230072969 + 3 ^ 40 * 2075066 * 2
def baseEnd_2075066 : Nat := 1065506247802683528431951

theorem tailTrace_2075066 : CollatzResearch.WordTrace tailWord_2075066 prefixEnd_2075066 1065506247802683528431951 := by
  unfold tailWord_2075066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18920968675099437475809263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50455916466931833268824701 18920968675099437475809263)
  ·
    refine ⟨28381453012649156213713895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18920968675099437475809263 28381453012649156213713895)
    ·
      refine ⟨42572179518973734320570843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28381453012649156213713895 42572179518973734320570843)
      ·
        refine ⟨63858269278460601480856265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42572179518973734320570843 63858269278460601480856265)
        ·
          refine ⟨47893701958845451110642199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63858269278460601480856265 47893701958845451110642199)
          ·
            refine ⟨71840552938268176665963299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47893701958845451110642199 71840552938268176665963299)
            ·
              refine ⟨107760829407402264998944949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71840552938268176665963299 107760829407402264998944949)
              ·
                refine ⟨10102577756943962343651089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107760829407402264998944949 10102577756943962343651089)
                ·
                  refine ⟨7576933317707971757738317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10102577756943962343651089 7576933317707971757738317)
                  ·
                    refine ⟨2841349994140489409151869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7576933317707971757738317 2841349994140489409151869)
                    ·
                      refine ⟨1065506247802683528431951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2841349994140489409151869 1065506247802683528431951)
                      ·
                        rfl

theorem cell23_2075066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_2075066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075066 prefixEnd_2075066 := by exact prefixLift 2075066
  have htrace : WordTrace (prefixWord ++ tailWord_2075066) baseStart_2075066 baseEnd_2075066 := by
    simpa [prefixWord, tailWord_2075066, baseEnd_2075066] using wordTrace_append hprefix tailTrace_2075066
  have hstable : (prefixWord ++ tailWord_2075066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075066).length < 2 ^ (prefixWord ++ tailWord_2075066).sum := by decide
  have hdescent : baseEnd_2075066 < baseStart_2075066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075107 : List Nat := [1, 1, 1, 6, 3, 2, 2, 2, 5]
def baseStart_2075107 : Nat := 118140960795 + 2075107 * 2 ^ 59
def prefixEnd_2075107 : Nat := 4983230072969 + 3 ^ 40 * 2075107 * 2
def baseEnd_2075107 : Nat := 118391922278835318668807

theorem tailTrace_2075107 : CollatzResearch.WordTrace tailWord_2075107 prefixEnd_2075107 118391922278835318668807 := by
  unfold tailWord_2075107
  simp only [CollatzResearch.WordTrace]
  refine ⟨75685370093249213905479575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50456913395499475936986383 75685370093249213905479575)
  ·
    refine ⟨113528055139873820858219363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75685370093249213905479575 113528055139873820858219363)
    ·
      refine ⟨170292082709810731287329045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113528055139873820858219363 170292082709810731287329045)
      ·
        refine ⟨7982441377022378029093549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170292082709810731287329045 7982441377022378029093549)
        ·
          refine ⟨2993415516383391760910081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7982441377022378029093549 2993415516383391760910081)
          ·
            refine ⟨2245061637287543820682561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2993415516383391760910081 2245061637287543820682561)
            ·
              refine ⟨1683796227965657865511921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2245061637287543820682561 1683796227965657865511921)
              ·
                refine ⟨1262847170974243399133941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1683796227965657865511921 1262847170974243399133941)
                ·
                  refine ⟨118391922278835318668807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1262847170974243399133941 118391922278835318668807)
                  ·
                    rfl

theorem cell23_2075107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 5].length) (baseStart_2075107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075107 prefixEnd_2075107 := by exact prefixLift 2075107
  have htrace : WordTrace (prefixWord ++ tailWord_2075107) baseStart_2075107 baseEnd_2075107 := by
    simpa [prefixWord, tailWord_2075107, baseEnd_2075107] using wordTrace_append hprefix tailTrace_2075107
  have hstable : (prefixWord ++ tailWord_2075107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075107).length < 2 ^ (prefixWord ++ tailWord_2075107).sum := by decide
  have hdescent : baseEnd_2075107 < baseStart_2075107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075123 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 2, 4, 2]
def baseStart_2075123 : Nat := 118140960795 + 2075123 * 2 ^ 59
def prefixEnd_2075123 : Nat := 4983230072969 + 3 ^ 40 * 2075123 * 2
def baseEnd_2075123 : Nat := 1065535516199989805419189

theorem tailTrace_2075123 : CollatzResearch.WordTrace tailWord_2075123 prefixEnd_2075123 1065535516199989805419189 := by
  unfold tailWord_2075123
  simp only [CollatzResearch.WordTrace]
  refine ⟨75685953661191248638062023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50457302440794165758708015 75685953661191248638062023)
  ·
    refine ⟨113528930491786872957093035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75685953661191248638062023 113528930491786872957093035)
    ·
      refine ⟨170293395737680309435639553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113528930491786872957093035 170293395737680309435639553)
      ·
        refine ⟨127720046803260232076729665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170293395737680309435639553 127720046803260232076729665)
        ·
          refine ⟨95790035102445174057547249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127720046803260232076729665 95790035102445174057547249)
          ·
            refine ⟨71842526326833880543160437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95790035102445174057547249 71842526326833880543160437)
            ·
              refine ⟨6735236843140676300921291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71842526326833880543160437 6735236843140676300921291)
              ·
                refine ⟨10102855264711014451381937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735236843140676300921291 10102855264711014451381937)
                ·
                  refine ⟨7577141448533260838536453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10102855264711014451381937 7577141448533260838536453)
                  ·
                    refine ⟨1420714021599986407225585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7577141448533260838536453 1420714021599986407225585)
                    ·
                      refine ⟨1065535516199989805419189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420714021599986407225585 1065535516199989805419189)
                      ·
                        rfl

theorem cell23_2075123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 4, 2].length) (baseStart_2075123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075123 prefixEnd_2075123 := by exact prefixLift 2075123
  have htrace : WordTrace (prefixWord ++ tailWord_2075123) baseStart_2075123 baseEnd_2075123 := by
    simpa [prefixWord, tailWord_2075123, baseEnd_2075123] using wordTrace_append hprefix tailTrace_2075123
  have hstable : (prefixWord ++ tailWord_2075123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075123).length < 2 ^ (prefixWord ++ tailWord_2075123).sum := by decide
  have hdescent : baseEnd_2075123 < baseStart_2075123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075133 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_2075133 : Nat := 118140960795 + 2075133 * 2 ^ 59
def prefixEnd_2075133 : Nat := 4983230072969 + 3 ^ 40 * 2075133 * 2
def baseEnd_2075133 : Nat := 355180217002178255431381

theorem tailTrace_2075133 : CollatzResearch.WordTrace tailWord_2075133 prefixEnd_2075133 355180217002178255431381 := by
  unfold tailWord_2075133
  simp only [CollatzResearch.WordTrace]
  refine ⟨75686318391155020345926053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50457545594103346897284035 75686318391155020345926053)
  ·
    refine ⟨14191184698341566314861135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75686318391155020345926053 14191184698341566314861135)
    ·
      refine ⟨21286777047512349472291703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14191184698341566314861135 21286777047512349472291703)
      ·
        refine ⟨31930165571268524208437555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21286777047512349472291703 31930165571268524208437555)
        ·
          refine ⟨47895248356902786312656333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31930165571268524208437555 47895248356902786312656333)
          ·
            refine ⟨17960718133838544867246125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47895248356902786312656333 17960718133838544867246125)
            ·
              refine ⟨6735269300189454325217297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17960718133838544867246125 6735269300189454325217297)
              ·
                refine ⟨5051451975142090743912973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6735269300189454325217297 5051451975142090743912973)
                ·
                  refine ⟨1894294490678284028967365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5051451975142090743912973 1894294490678284028967365)
                  ·
                    refine ⟨355180217002178255431381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1894294490678284028967365 355180217002178255431381)
                    ·
                      rfl

theorem cell23_2075133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_2075133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075133 prefixEnd_2075133 := by exact prefixLift 2075133
  have htrace : WordTrace (prefixWord ++ tailWord_2075133) baseStart_2075133 baseEnd_2075133 := by
    simpa [prefixWord, tailWord_2075133, baseEnd_2075133] using wordTrace_append hprefix tailTrace_2075133
  have hstable : (prefixWord ++ tailWord_2075133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075133).length < 2 ^ (prefixWord ++ tailWord_2075133).sum := by decide
  have hdescent : baseEnd_2075133 < baseStart_2075133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075140 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2075140 : Nat := 118140960795 + 2075140 * 2 ^ 59
def prefixEnd_2075140 : Nat := 4983230072969 + 3 ^ 40 * 2075140 * 2
def baseEnd_2075140 : Nat := 1065544245371116238906611

theorem tailTrace_2075140 : CollatzResearch.WordTrace tailWord_2075140 prefixEnd_2075140 1065544245371116238906611 := by
  unfold tailWord_2075140
  simp only [CollatzResearch.WordTrace]
  refine ⟨37843286851064830270715437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50457715801419773694287249 37843286851064830270715437)
  ·
    refine ⟨14191232569149311351518289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37843286851064830270715437 14191232569149311351518289)
    ·
      refine ⟨10643424426861983513638717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14191232569149311351518289 10643424426861983513638717)
      ·
        refine ⟨3991284160073243817614519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10643424426861983513638717 3991284160073243817614519)
        ·
          refine ⟨5986926240109865726421779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991284160073243817614519 5986926240109865726421779)
          ·
            refine ⟨8980389360164798589632669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986926240109865726421779 8980389360164798589632669)
            ·
              refine ⟨3367646010061799471112251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8980389360164798589632669 3367646010061799471112251)
              ·
                refine ⟨5051469015092699206668377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367646010061799471112251 5051469015092699206668377)
                ·
                  refine ⟨3788601761319524405001283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5051469015092699206668377 3788601761319524405001283)
                  ·
                    refine ⟨5682902641979286607501925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3788601761319524405001283 5682902641979286607501925)
                    ·
                      refine ⟨1065544245371116238906611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5682902641979286607501925 1065544245371116238906611)
                      ·
                        rfl

theorem cell23_2075140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2075140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075140 prefixEnd_2075140 := by exact prefixLift 2075140
  have htrace : WordTrace (prefixWord ++ tailWord_2075140) baseStart_2075140 baseEnd_2075140 := by
    simpa [prefixWord, tailWord_2075140, baseEnd_2075140] using wordTrace_append hprefix tailTrace_2075140
  have hstable : (prefixWord ++ tailWord_2075140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075140).length < 2 ^ (prefixWord ++ tailWord_2075140).sum := by decide
  have hdescent : baseEnd_2075140 < baseStart_2075140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075146 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 8]
def baseStart_2075146 : Nat := 118140960795 + 2075146 * 2 ^ 59
def prefixEnd_2075146 : Nat := 4983230072969 + 3 ^ 40 * 2075146 * 2
def baseEnd_2075146 : Nat := 118394147361671468381287

theorem tailTrace_2075146 : CollatzResearch.WordTrace tailWord_2075146 prefixEnd_2075146 118394147361671468381287 := by
  unfold tailWord_2075146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18921698135026980891537323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50457861693405282377432861 18921698135026980891537323)
  ·
    refine ⟨28382547202540471337305985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18921698135026980891537323 28382547202540471337305985)
    ·
      refine ⟨21286910401905353502979489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28382547202540471337305985 21286910401905353502979489)
      ·
        refine ⟨15965182801429015127234617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21286910401905353502979489 15965182801429015127234617)
        ·
          refine ⟨11973887101071761345425963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15965182801429015127234617 11973887101071761345425963)
          ·
            refine ⟨17960830651607642018138945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973887101071761345425963 17960830651607642018138945)
            ·
              refine ⟨13470622988705731513604209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17960830651607642018138945 13470622988705731513604209)
              ·
                refine ⟨10102967241529298635203157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13470622988705731513604209 10102967241529298635203157)
                ·
                  refine ⟨118394147361671468381287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10102967241529298635203157 118394147361671468381287)
                  ·
                    rfl

theorem cell23_2075146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_2075146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075146 prefixEnd_2075146 := by exact prefixLift 2075146
  have htrace : WordTrace (prefixWord ++ tailWord_2075146) baseStart_2075146 baseEnd_2075146 := by
    simpa [prefixWord, tailWord_2075146, baseEnd_2075146] using wordTrace_append hprefix tailTrace_2075146
  have hstable : (prefixWord ++ tailWord_2075146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075146).length < 2 ^ (prefixWord ++ tailWord_2075146).sum := by decide
  have hdescent : baseEnd_2075146 < baseStart_2075146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075186 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2075186 : Nat := 118140960795 + 2075186 * 2 ^ 59
def prefixEnd_2075186 : Nat := 4983230072969 + 3 ^ 40 * 2075186 * 2
def baseEnd_2075186 : Nat := 1065567865481223058931399

theorem tailTrace_2075186 : CollatzResearch.WordTrace tailWord_2075186 prefixEnd_2075186 1065567865481223058931399 := by
  unfold tailWord_2075186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922062864990752599401353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50458834306642006931736941 18922062864990752599401353)
  ·
    refine ⟨14191547148743064449551015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18922062864990752599401353 14191547148743064449551015)
    ·
      refine ⟨21287320723114596674326523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14191547148743064449551015 21287320723114596674326523)
      ·
        refine ⟨31930981084671895011489785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21287320723114596674326523 31930981084671895011489785)
        ·
          refine ⟨23948235813503921258617339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31930981084671895011489785 23948235813503921258617339)
          ·
            refine ⟨35922353720255881887926009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23948235813503921258617339 35922353720255881887926009)
            ·
              refine ⟨26941765290191911415944507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35922353720255881887926009 26941765290191911415944507)
              ·
                refine ⟨40412647935287867123916761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26941765290191911415944507 40412647935287867123916761)
                ·
                  refine ⟨30309485951465900342937571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40412647935287867123916761 30309485951465900342937571)
                  ·
                    refine ⟨45464228927198850514406357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30309485951465900342937571 45464228927198850514406357)
                    ·
                      refine ⟨1065567865481223058931399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45464228927198850514406357 1065567865481223058931399)
                      ·
                        rfl

theorem cell23_2075186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2075186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075186 prefixEnd_2075186 := by exact prefixLift 2075186
  have htrace : WordTrace (prefixWord ++ tailWord_2075186) baseStart_2075186 baseEnd_2075186 := by
    simpa [prefixWord, tailWord_2075186, baseEnd_2075186] using wordTrace_append hprefix tailTrace_2075186
  have hstable : (prefixWord ++ tailWord_2075186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075186).length < 2 ^ (prefixWord ++ tailWord_2075186).sum := by decide
  have hdescent : baseEnd_2075186 < baseStart_2075186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075223 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 4, 4]
def baseStart_2075223 : Nat := 118140960795 + 2075223 * 2 ^ 59
def prefixEnd_2075223 : Nat := 4983230072969 + 3 ^ 40 * 2075223 * 2
def baseEnd_2075223 : Nat := 355195621421813138056243

theorem tailTrace_2075223 : CollatzResearch.WordTrace tailWord_2075223 prefixEnd_2075223 355195621421813138056243 := by
  unfold tailWord_2075223
  simp only [CollatzResearch.WordTrace]
  refine ⟨75689600960828965716702323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50459733973885977144468215 75689600960828965716702323)
  ·
    refine ⟨113534401441243448575053485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75689600960828965716702323 113534401441243448575053485)
    ·
      refine ⟨42575400540466293215645057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113534401441243448575053485 42575400540466293215645057)
      ·
        refine ⟨31931550405349719911733793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42575400540466293215645057 31931550405349719911733793)
        ·
          refine ⟨23948662804012289933800345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31931550405349719911733793 23948662804012289933800345)
          ·
            refine ⟨17961497103009217450350259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23948662804012289933800345 17961497103009217450350259)
            ·
              refine ⟨26942245654513826175525389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17961497103009217450350259 26942245654513826175525389)
              ·
                refine ⟨10103342120442684815822021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26942245654513826175525389 10103342120442684815822021)
                ·
                  refine ⟨1894376647583003402966629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10103342120442684815822021 1894376647583003402966629)
                  ·
                    refine ⟨355195621421813138056243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1894376647583003402966629 355195621421813138056243)
                    ·
                      rfl

theorem cell23_2075223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_2075223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075223 prefixEnd_2075223 := by exact prefixLift 2075223
  have htrace : WordTrace (prefixWord ++ tailWord_2075223) baseStart_2075223 baseEnd_2075223 := by
    simpa [prefixWord, tailWord_2075223, baseEnd_2075223] using wordTrace_append hprefix tailTrace_2075223
  have hstable : (prefixWord ++ tailWord_2075223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075223).length < 2 ^ (prefixWord ++ tailWord_2075223).sum := by decide
  have hdescent : baseEnd_2075223 < baseStart_2075223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075233 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_2075233 : Nat := 118140960795 + 2075233 * 2 ^ 59
def prefixEnd_2075233 : Nat := 4983230072969 + 3 ^ 40 * 2075233 * 2
def baseEnd_2075233 : Nat := 1065591999071984375043683

theorem tailTrace_2075233 : CollatzResearch.WordTrace tailWord_2075233 prefixEnd_2075233 1065591999071984375043683 := by
  unfold tailWord_2075233
  simp only [CollatzResearch.WordTrace]
  refine ⟨75689965690792737424566353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50459977127195158283044235 75689965690792737424566353)
  ·
    refine ⟨56767474268094553068424765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75689965690792737424566353 56767474268094553068424765)
    ·
      refine ⟨21287802850535457400659287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56767474268094553068424765 21287802850535457400659287)
      ·
        refine ⟨31931704275803186100988931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21287802850535457400659287 31931704275803186100988931)
        ·
          refine ⟨47897556413704779151483397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31931704275803186100988931 47897556413704779151483397)
          ·
            refine ⟨8980791827569646090903137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47897556413704779151483397 8980791827569646090903137)
            ·
              refine ⟨6735593870677234568177353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8980791827569646090903137 6735593870677234568177353)
              ·
                refine ⟨5051695403007925926133015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6735593870677234568177353 5051695403007925926133015)
                ·
                  refine ⟨7577543104511888889199523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051695403007925926133015 7577543104511888889199523)
                  ·
                    refine ⟨11366314656767833333799285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7577543104511888889199523 11366314656767833333799285)
                    ·
                      refine ⟨1065591999071984375043683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11366314656767833333799285 1065591999071984375043683)
                      ·
                        rfl

theorem cell23_2075233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_2075233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075233 prefixEnd_2075233 := by exact prefixLift 2075233
  have htrace : WordTrace (prefixWord ++ tailWord_2075233) baseStart_2075233 baseEnd_2075233 := by
    simpa [prefixWord, tailWord_2075233, baseEnd_2075233] using wordTrace_append hprefix tailTrace_2075233
  have hstable : (prefixWord ++ tailWord_2075233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075233).length < 2 ^ (prefixWord ++ tailWord_2075233).sum := by decide
  have hdescent : baseEnd_2075233 < baseStart_2075233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075256 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_2075256 : Nat := 118140960795 + 2075256 * 2 ^ 59
def prefixEnd_2075256 : Nat := 4983230072969 + 3 ^ 40 * 2075256 * 2
def baseEnd_2075256 : Nat := 1065603809127037785056077

theorem tailTrace_2075256 : CollatzResearch.WordTrace tailWord_2075256 prefixEnd_2075256 1065603809127037785056077 := by
  unfold tailWord_2075256
  simp only [CollatzResearch.WordTrace]
  refine ⟨37845402284854706176326811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50460536379806274901769081 37845402284854706176326811)
  ·
    refine ⟨56768103427282059264490217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37845402284854706176326811 56768103427282059264490217)
    ·
      refine ⟨42576077570461544448367663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56768103427282059264490217 42576077570461544448367663)
      ·
        refine ⟨63864116355692316672551495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42576077570461544448367663 63864116355692316672551495)
        ·
          refine ⟨95796174533538475008827243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63864116355692316672551495 95796174533538475008827243)
          ·
            refine ⟨143694261800307712513240865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95796174533538475008827243 143694261800307712513240865)
            ·
              refine ⟨107770696350230784384930649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143694261800307712513240865 107770696350230784384930649)
              ·
                refine ⟨80828022262673088288697987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107770696350230784384930649 80828022262673088288697987)
                ·
                  refine ⟨121242033394009632433046981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80828022262673088288697987 121242033394009632433046981)
                  ·
                    refine ⟨22732881261376806081196309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121242033394009632433046981 22732881261376806081196309)
                    ·
                      refine ⟨1065603809127037785056077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22732881261376806081196309 1065603809127037785056077)
                      ·
                        rfl

theorem cell23_2075256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_2075256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075256 prefixEnd_2075256 := by exact prefixLift 2075256
  have htrace : WordTrace (prefixWord ++ tailWord_2075256) baseStart_2075256 baseEnd_2075256 := by
    simpa [prefixWord, tailWord_2075256, baseEnd_2075256] using wordTrace_append hprefix tailTrace_2075256
  have hstable : (prefixWord ++ tailWord_2075256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075256).length < 2 ^ (prefixWord ++ tailWord_2075256).sum := by decide
  have hdescent : baseEnd_2075256 < baseStart_2075256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075297 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2075297 : Nat := 118140960795 + 2075297 * 2 ^ 59
def prefixEnd_2075297 : Nat := 4983230072969 + 3 ^ 40 * 2075297 * 2
def baseEnd_2075297 : Nat := 1065624861833872124643389

theorem tailTrace_2075297 : CollatzResearch.WordTrace tailWord_2075297 prefixEnd_2075297 1065624861833872124643389 := by
  unfold tailWord_2075297
  simp only [CollatzResearch.WordTrace]
  refine ⟨75692299962560876354896145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50461533308373917569930763 75692299962560876354896145)
  ·
    refine ⟨56769224971920657266172109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75692299962560876354896145 56769224971920657266172109)
    ·
      refine ⟨21288459364470246474814541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56769224971920657266172109 21288459364470246474814541)
      ·
        refine ⟨7983172261676342428055453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21288459364470246474814541 7983172261676342428055453)
        ·
          refine ⟨2993689598128628410520795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7983172261676342428055453 2993689598128628410520795)
          ·
            refine ⟨4490534397192942615781193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993689598128628410520795 4490534397192942615781193)
            ·
              refine ⟨3367900797894706961835895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490534397192942615781193 3367900797894706961835895)
              ·
                refine ⟨5051851196842060442753843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367900797894706961835895 5051851196842060442753843)
                ·
                  refine ⟨7577776795263090664130765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5051851196842060442753843 7577776795263090664130765)
                  ·
                    refine ⟨2841666298223658999049037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7577776795263090664130765 2841666298223658999049037)
                    ·
                      refine ⟨1065624861833872124643389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2841666298223658999049037 1065624861833872124643389)
                      ·
                        rfl

theorem cell23_2075297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2075297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075297 prefixEnd_2075297 := by exact prefixLift 2075297
  have htrace : WordTrace (prefixWord ++ tailWord_2075297) baseStart_2075297 baseEnd_2075297 := by
    simpa [prefixWord, tailWord_2075297, baseEnd_2075297] using wordTrace_append hprefix tailTrace_2075297
  have hstable : (prefixWord ++ tailWord_2075297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075297).length < 2 ^ (prefixWord ++ tailWord_2075297).sum := by decide
  have hdescent : baseEnd_2075297 < baseStart_2075297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075318 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2075318 : Nat := 118140960795 + 2075318 * 2 ^ 59
def prefixEnd_2075318 : Nat := 4983230072969 + 3 ^ 40 * 2075318 * 2
def baseEnd_2075318 : Nat := 1065635644927616542480793

theorem tailTrace_2075318 : CollatzResearch.WordTrace tailWord_2075318 prefixEnd_2075318 1065635644927616542480793 := by
  unfold tailWord_2075318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730816618467799808838163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50462043930323197960940405 4730816618467799808838163)
  ·
    refine ⟨7096224927701699713257245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4730816618467799808838163 7096224927701699713257245)
    ·
      refine ⟨2661084347888137392471467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7096224927701699713257245 2661084347888137392471467)
      ·
        refine ⟨3991626521832206088707201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661084347888137392471467 3991626521832206088707201)
        ·
          refine ⟨2993719891374154566530401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3991626521832206088707201 2993719891374154566530401)
          ·
            refine ⟨2245289918530615924897801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2993719891374154566530401 2245289918530615924897801)
            ·
              refine ⟨1683967438897961943673351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2245289918530615924897801 1683967438897961943673351)
              ·
                refine ⟨2525951158346942915510027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683967438897961943673351 2525951158346942915510027)
                ·
                  refine ⟨3788926737520414373265041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525951158346942915510027 3788926737520414373265041)
                  ·
                    refine ⟨2841695053140310779948781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3788926737520414373265041 2841695053140310779948781)
                    ·
                      refine ⟨1065635644927616542480793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2841695053140310779948781 1065635644927616542480793)
                      ·
                        rfl

theorem cell23_2075318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2075318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075318 prefixEnd_2075318 := by exact prefixLift 2075318
  have htrace : WordTrace (prefixWord ++ tailWord_2075318) baseStart_2075318 baseEnd_2075318 := by
    simpa [prefixWord, tailWord_2075318, baseEnd_2075318] using wordTrace_append hprefix tailTrace_2075318
  have hstable : (prefixWord ++ tailWord_2075318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075318).length < 2 ^ (prefixWord ++ tailWord_2075318).sum := by decide
  have hdescent : baseEnd_2075318 < baseStart_2075318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075383 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_2075383 : Nat := 118140960795 + 2075383 * 2 ^ 59
def prefixEnd_2075383 : Nat := 4983230072969 + 3 ^ 40 * 2075383 * 2
def baseEnd_2075383 : Nat := 1065669021170158788167993

theorem tailTrace_2075383 : CollatzResearch.WordTrace tailWord_2075383 prefixEnd_2075383 1065669021170158788167993 := by
  unfold tailWord_2075383
  simp only [CollatzResearch.WordTrace]
  refine ⟨75695436640249313042526803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50463624426832875361684535 75695436640249313042526803)
  ·
    refine ⟨113543154960373969563790205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75695436640249313042526803 113543154960373969563790205)
    ·
      refine ⟨42578683110140238586421327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113543154960373969563790205 42578683110140238586421327)
      ·
        refine ⟨63868024665210357879631991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42578683110140238586421327 63868024665210357879631991)
        ·
          refine ⟨95802036997815536819447987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63868024665210357879631991 95802036997815536819447987)
          ·
            refine ⟨143703055496723305229171981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95802036997815536819447987 143703055496723305229171981)
            ·
              refine ⟨53888645811271239460939493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143703055496723305229171981 53888645811271239460939493)
              ·
                refine ⟨10104121089613357398926155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53888645811271239460939493 10104121089613357398926155)
                ·
                  refine ⟨15156181634420036098389233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104121089613357398926155 15156181634420036098389233)
                  ·
                    refine ⟨11367136225815027073791925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15156181634420036098389233 11367136225815027073791925)
                    ·
                      refine ⟨1065669021170158788167993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11367136225815027073791925 1065669021170158788167993)
                      ·
                        rfl

theorem cell23_2075383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_2075383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075383 prefixEnd_2075383 := by exact prefixLift 2075383
  have htrace : WordTrace (prefixWord ++ tailWord_2075383) baseStart_2075383 baseEnd_2075383 := by
    simpa [prefixWord, tailWord_2075383, baseEnd_2075383] using wordTrace_append hprefix tailTrace_2075383
  have hstable : (prefixWord ++ tailWord_2075383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075383).length < 2 ^ (prefixWord ++ tailWord_2075383).sum := by decide
  have hdescent : baseEnd_2075383 < baseStart_2075383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075400 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2075400 : Nat := 118140960795 + 2075400 * 2 ^ 59
def prefixEnd_2075400 : Nat := 4983230072969 + 3 ^ 40 * 2075400 * 2
def baseEnd_2075400 : Nat := 1065677750341285221655415

theorem tailTrace_2075400 : CollatzResearch.WordTrace tailWord_2075400 prefixEnd_2075400 1065677750341285221655415 := by
  unfold tailWord_2075400
  simp only [CollatzResearch.WordTrace]
  refine ⟨37848028340593862472947827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50464037787458483297263769 37848028340593862472947827)
  ·
    refine ⟨56772042510890793709421741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37848028340593862472947827 56772042510890793709421741)
    ·
      refine ⟨21289515941584047641033153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56772042510890793709421741 21289515941584047641033153)
      ·
        refine ⟨15967136956188035730774865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21289515941584047641033153 15967136956188035730774865)
        ·
          refine ⟨11975352717141026798081149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15967136956188035730774865 11975352717141026798081149)
          ·
            refine ⟨4490757268927885049280431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11975352717141026798081149 4490757268927885049280431)
            ·
              refine ⟨6736135903391827573920647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490757268927885049280431 6736135903391827573920647)
              ·
                refine ⟨10104203855087741360880971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736135903391827573920647 10104203855087741360880971)
                ·
                  refine ⟨15156305782631612041321457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104203855087741360880971 15156305782631612041321457)
                  ·
                    refine ⟨11367229336973709030991093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15156305782631612041321457 11367229336973709030991093)
                    ·
                      refine ⟨1065677750341285221655415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11367229336973709030991093 1065677750341285221655415)
                      ·
                        rfl

theorem cell23_2075400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2075400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075400 prefixEnd_2075400 := by exact prefixLift 2075400
  have htrace : WordTrace (prefixWord ++ tailWord_2075400) baseStart_2075400 baseEnd_2075400 := by
    simpa [prefixWord, tailWord_2075400, baseEnd_2075400] using wordTrace_append hprefix tailTrace_2075400
  have hstable : (prefixWord ++ tailWord_2075400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075400).length < 2 ^ (prefixWord ++ tailWord_2075400).sum := by decide
  have hdescent : baseEnd_2075400 < baseStart_2075400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075483 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 10]
def baseStart_2075483 : Nat := 118140960795 + 2075483 * 2 ^ 59
def prefixEnd_2075483 : Nat := 4983230072969 + 3 ^ 40 * 2075483 * 2
def baseEnd_2075483 : Nat := 1065720369235608396917533

theorem tailTrace_2075483 : CollatzResearch.WordTrace tailWord_2075483 prefixEnd_2075483 1065720369235608396917533 := by
  unfold tailWord_2075483
  simp only [CollatzResearch.WordTrace]
  refine ⟨75699083939887030121167103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50466055959924686747444735 75699083939887030121167103)
  ·
    refine ⟨113548625909830545181750655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75699083939887030121167103 113548625909830545181750655)
    ·
      refine ⟨170322938864745817772625983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113548625909830545181750655 170322938864745817772625983)
      ·
        refine ⟨255484408297118726658938975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170322938864745817772625983 255484408297118726658938975)
        ·
          refine ⟨383226612445678089988408463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255484408297118726658938975 383226612445678089988408463)
          ·
            refine ⟨574839918668517134982612695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383226612445678089988408463 574839918668517134982612695)
            ·
              refine ⟨862259878002775702473919043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574839918668517134982612695 862259878002775702473919043)
              ·
                refine ⟨1293389817004163553710878565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862259878002775702473919043 1293389817004163553710878565)
                ·
                  refine ⟨242510590688280666320789731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1293389817004163553710878565 242510590688280666320789731)
                  ·
                    refine ⟨363765886032420999481184597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242510590688280666320789731 363765886032420999481184597)
                    ·
                      refine ⟨1065720369235608396917533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 363765886032420999481184597 1065720369235608396917533)
                      ·
                        rfl

theorem cell23_2075483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_2075483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075483 prefixEnd_2075483 := by exact prefixLift 2075483
  have htrace : WordTrace (prefixWord ++ tailWord_2075483) baseStart_2075483 baseEnd_2075483 := by
    simpa [prefixWord, tailWord_2075483, baseEnd_2075483] using wordTrace_append hprefix tailTrace_2075483
  have hstable : (prefixWord ++ tailWord_2075483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075483).length < 2 ^ (prefixWord ++ tailWord_2075483).sum := by decide
  have hdescent : baseEnd_2075483 < baseStart_2075483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075487 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 1, 5, 2]
def baseStart_2075487 : Nat := 118140960795 + 2075487 * 2 ^ 59
def prefixEnd_2075487 : Nat := 4983230072969 + 3 ^ 40 * 2075487 * 2
def baseEnd_2075487 : Nat := 1065722423158226381267515

theorem tailTrace_2075487 : CollatzResearch.WordTrace tailWord_2075487 prefixEnd_2075487 1065722423158226381267515 := by
  unfold tailWord_2075487
  simp only [CollatzResearch.WordTrace]
  refine ⟨75699229831872538804312715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50466153221248359202875143 75699229831872538804312715)
  ·
    refine ⟨113548844747808808206469073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75699229831872538804312715 113548844747808808206469073)
    ·
      refine ⟨85161633560856606154851805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113548844747808808206469073 85161633560856606154851805)
      ·
        refine ⟨31935612585321227308069427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85161633560856606154851805 31935612585321227308069427)
        ·
          refine ⟨47903418877981840962104141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31935612585321227308069427 47903418877981840962104141)
          ·
            refine ⟨17963782079243190360789053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47903418877981840962104141 17963782079243190360789053)
            ·
              refine ⟨6736418279716196385295895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17963782079243190360789053 6736418279716196385295895)
              ·
                refine ⟨10104627419574294577943843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736418279716196385295895 10104627419574294577943843)
                ·
                  refine ⟨15156941129361441866915765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104627419574294577943843 15156941129361441866915765)
                  ·
                    refine ⟨1420963230877635175023353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15156941129361441866915765 1420963230877635175023353)
                    ·
                      refine ⟨1065722423158226381267515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1420963230877635175023353 1065722423158226381267515)
                      ·
                        rfl

theorem cell23_2075487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_2075487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075487 prefixEnd_2075487 := by exact prefixLift 2075487
  have htrace : WordTrace (prefixWord ++ tailWord_2075487) baseStart_2075487 baseEnd_2075487 := by
    simpa [prefixWord, tailWord_2075487, baseEnd_2075487] using wordTrace_append hprefix tailTrace_2075487
  have hstable : (prefixWord ++ tailWord_2075487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075487).length < 2 ^ (prefixWord ++ tailWord_2075487).sum := by decide
  have hdescent : baseEnd_2075487 < baseStart_2075487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075520 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 3]
def baseStart_2075520 : Nat := 118140960795 + 2075520 * 2 ^ 59
def prefixEnd_2075520 : Nat := 4983230072969 + 3 ^ 40 * 2075520 * 2
def baseEnd_2075520 : Nat := 1065739368019824752154863

theorem tailTrace_2075520 : CollatzResearch.WordTrace tailWord_2075520 prefixEnd_2075520 1065739368019824752154863 := by
  unfold tailWord_2075520
  simp only [CollatzResearch.WordTrace]
  refine ⟨37850216720376492720132007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50466955627168656960176009 37850216720376492720132007)
  ·
    refine ⟨56775325080564739080198011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37850216720376492720132007 56775325080564739080198011)
    ·
      refine ⟨85162987620847108620297017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56775325080564739080198011 85162987620847108620297017)
      ·
        refine ⟨63872240715635331465222763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85162987620847108620297017 63872240715635331465222763)
        ·
          refine ⟨95808361073452997197834145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63872240715635331465222763 95808361073452997197834145)
          ·
            refine ⟨71856270805089747898375609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95808361073452997197834145 71856270805089747898375609)
            ·
              refine ⟨53892203103817310923781707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71856270805089747898375609 53892203103817310923781707)
              ·
                refine ⟨80838304655725966385672561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53892203103817310923781707 80838304655725966385672561)
                ·
                  refine ⟨60628728491794474789254421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80838304655725966385672561 60628728491794474789254421)
                  ·
                    refine ⟨2841971648052866005746301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60628728491794474789254421 2841971648052866005746301)
                    ·
                      refine ⟨1065739368019824752154863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2841971648052866005746301 1065739368019824752154863)
                      ·
                        rfl

theorem cell23_2075520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_2075520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075520 prefixEnd_2075520 := by exact prefixLift 2075520
  have htrace : WordTrace (prefixWord ++ tailWord_2075520) baseStart_2075520 baseEnd_2075520 := by
    simpa [prefixWord, tailWord_2075520, baseEnd_2075520] using wordTrace_append hprefix tailTrace_2075520
  have hstable : (prefixWord ++ tailWord_2075520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075520).length < 2 ^ (prefixWord ++ tailWord_2075520).sum := by decide
  have hdescent : baseEnd_2075520 < baseStart_2075520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075527 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 1, 6]
def baseStart_2075527 : Nat := 118140960795 + 2075527 * 2 ^ 59
def prefixEnd_2075527 : Nat := 4983230072969 + 3 ^ 40 * 2075527 * 2
def baseEnd_2075527 : Nat := 355247654128135408255777

theorem tailTrace_2075527 : CollatzResearch.WordTrace tailWord_2075527 prefixEnd_2075527 355247654128135408255777 := by
  unfold tailWord_2075527
  simp only [CollatzResearch.WordTrace]
  refine ⟨75700688751727625635768835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50467125834485083757179223 75700688751727625635768835)
  ·
    refine ⟨113551033127591438453653253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75700688751727625635768835 113551033127591438453653253)
    ·
      refine ⟨21290818711423394710059985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113551033127591438453653253 21290818711423394710059985)
      ·
        refine ⟨15968114033567546032544989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21290818711423394710059985 15968114033567546032544989)
        ·
          refine ⟨5988042762587829762204371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15968114033567546032544989 5988042762587829762204371)
          ·
            refine ⟨8982064143881744643306557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988042762587829762204371 8982064143881744643306557)
            ·
              refine ⟨3368274053955654241239959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8982064143881744643306557 3368274053955654241239959)
              ·
                refine ⟨5052411080933481361859939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368274053955654241239959 5052411080933481361859939)
                ·
                  refine ⟨7578616621400222042789909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052411080933481361859939 7578616621400222042789909)
                  ·
                    refine ⟨355247654128135408255777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7578616621400222042789909 355247654128135408255777)
                    ·
                      rfl

theorem cell23_2075527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_2075527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075527 prefixEnd_2075527 := by exact prefixLift 2075527
  have htrace : WordTrace (prefixWord ++ tailWord_2075527) baseStart_2075527 baseEnd_2075527 := by
    simpa [prefixWord, tailWord_2075527, baseEnd_2075527] using wordTrace_append hprefix tailTrace_2075527
  have hstable : (prefixWord ++ tailWord_2075527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075527).length < 2 ^ (prefixWord ++ tailWord_2075527).sum := by decide
  have hdescent : baseEnd_2075527 < baseStart_2075527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075554 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2075554 : Nat := 118140960795 + 2075554 * 2 ^ 59
def prefixEnd_2075554 : Nat := 4983230072969 + 3 ^ 40 * 2075554 * 2
def baseEnd_2075554 : Nat := 1065756826362077619129707

theorem tailTrace_2075554 : CollatzResearch.WordTrace tailWord_2075554 prefixEnd_2075554 1065756826362077619129707 := by
  unfold tailWord_2075554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18925418380657452311750429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50467782348419872831334477 18925418380657452311750429)
  ·
    refine ⟨7097031892746544616906411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18925418380657452311750429 7097031892746544616906411)
    ·
      refine ⟨10645547839119816925359617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7097031892746544616906411 10645547839119816925359617)
      ·
        refine ⟨7984160879339862694019713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10645547839119816925359617 7984160879339862694019713)
        ·
          refine ⟨5988120659504897020514785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7984160879339862694019713 5988120659504897020514785)
          ·
            refine ⟨4491090494628672765386089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5988120659504897020514785 4491090494628672765386089)
            ·
              refine ⟨3368317870971504574039567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491090494628672765386089 3368317870971504574039567)
              ·
                refine ⟨5052476806457256861059351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368317870971504574039567 5052476806457256861059351)
                ·
                  refine ⟨7578715209685885291589027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052476806457256861059351 7578715209685885291589027)
                  ·
                    refine ⟨11368072814528827937383541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7578715209685885291589027 11368072814528827937383541)
                    ·
                      refine ⟨1065756826362077619129707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11368072814528827937383541 1065756826362077619129707)
                      ·
                        rfl

theorem cell23_2075554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2075554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075554 prefixEnd_2075554 := by exact prefixLift 2075554
  have htrace : WordTrace (prefixWord ++ tailWord_2075554) baseStart_2075554 baseEnd_2075554 := by
    simpa [prefixWord, tailWord_2075554, baseEnd_2075554] using wordTrace_append hprefix tailTrace_2075554
  have hstable : (prefixWord ++ tailWord_2075554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075554).length < 2 ^ (prefixWord ++ tailWord_2075554).sum := by decide
  have hdescent : baseEnd_2075554 < baseStart_2075554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075600 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 4, 6]
def baseStart_2075600 : Nat := 118140960795 + 2075600 * 2 ^ 59
def prefixEnd_2075600 : Nat := 4983230072969 + 3 ^ 40 * 2075600 * 2
def baseEnd_2075600 : Nat := 355260148824061479718165

theorem tailTrace_2075600 : CollatzResearch.WordTrace tailWord_2075600 prefixEnd_2075600 355260148824061479718165 := by
  unfold tailWord_2075600
  simp only [CollatzResearch.WordTrace]
  refine ⟨37851675640231579551588127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50468900853642106068784169 37851675640231579551588127)
  ·
    refine ⟨56777513460347369327382191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37851675640231579551588127 56777513460347369327382191)
    ·
      refine ⟨85166270190521053991073287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56777513460347369327382191 85166270190521053991073287)
      ·
        refine ⟨127749405285781580986609931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85166270190521053991073287 127749405285781580986609931)
        ·
          refine ⟨191624107928672371479914897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127749405285781580986609931 191624107928672371479914897)
          ·
            refine ⟨143718080946504278609936173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191624107928672371479914897 143718080946504278609936173)
            ·
              refine ⟨53894280354939104478726065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143718080946504278609936173 53894280354939104478726065)
              ·
                refine ⟨40420710266204328359044549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53894280354939104478726065 40420710266204328359044549)
                ·
                  refine ⟨7578883174913311567320853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40420710266204328359044549 7578883174913311567320853)
                  ·
                    refine ⟨355260148824061479718165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7578883174913311567320853 355260148824061479718165)
                    ·
                      rfl

theorem cell23_2075600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_2075600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075600 prefixEnd_2075600 := by exact prefixLift 2075600
  have htrace : WordTrace (prefixWord ++ tailWord_2075600) baseStart_2075600 baseEnd_2075600 := by
    simpa [prefixWord, tailWord_2075600, baseEnd_2075600] using wordTrace_append hprefix tailTrace_2075600
  have hstable : (prefixWord ++ tailWord_2075600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075600).length < 2 ^ (prefixWord ++ tailWord_2075600).sum := by decide
  have hdescent : baseEnd_2075600 < baseStart_2075600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075618 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2075618 : Nat := 118140960795 + 2075618 * 2 ^ 59
def prefixEnd_2075618 : Nat := 4983230072969 + 3 ^ 40 * 2075618 * 2
def baseEnd_2075618 : Nat := 1065789689123965368729413

theorem tailTrace_2075618 : CollatzResearch.WordTrace tailWord_2075618 prefixEnd_2075618 1065789689123965368729413 := by
  unfold tailWord_2075618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18926001948599487044332877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50469338529598632118221005 18926001948599487044332877)
  ·
    refine ⟨7097250730724807641624829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18926001948599487044332877 7097250730724807641624829)
    ·
      refine ⟨2661469024021802865609311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7097250730724807641624829 2661469024021802865609311)
      ·
        refine ⟨3992203536032704298413967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661469024021802865609311 3992203536032704298413967)
        ·
          refine ⟨5988305304049056447620951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992203536032704298413967 5988305304049056447620951)
          ·
            refine ⟨8982457956073584671431427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5988305304049056447620951 8982457956073584671431427)
            ·
              refine ⟨13473686934110377007147141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8982457956073584671431427 13473686934110377007147141)
              ·
                refine ⟨2526316300145695688840089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13473686934110377007147141 2526316300145695688840089)
                ·
                  refine ⟨1894737225109271766630067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526316300145695688840089 1894737225109271766630067)
                  ·
                    refine ⟨2842105837663907649945101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1894737225109271766630067 2842105837663907649945101)
                    ·
                      refine ⟨1065789689123965368729413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2842105837663907649945101 1065789689123965368729413)
                      ·
                        rfl

theorem cell23_2075618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2075618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075618 prefixEnd_2075618 := by exact prefixLift 2075618
  have htrace : WordTrace (prefixWord ++ tailWord_2075618) baseStart_2075618 baseEnd_2075618 := by
    simpa [prefixWord, tailWord_2075618, baseEnd_2075618] using wordTrace_append hprefix tailTrace_2075618
  have hstable : (prefixWord ++ tailWord_2075618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075618).length < 2 ^ (prefixWord ++ tailWord_2075618).sum := by decide
  have hdescent : baseEnd_2075618 < baseStart_2075618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075641 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 2, 2, 2]
def baseStart_2075641 : Nat := 118140960795 + 2075641 * 2 ^ 59
def prefixEnd_2075641 : Nat := 4983230072969 + 3 ^ 40 * 2075641 * 2
def baseEnd_2075641 : Nat := 1065801499179018778741807

theorem tailTrace_2075641 : CollatzResearch.WordTrace tailWord_2075641 prefixEnd_2075641 1065801499179018778741807 := by
  unfold tailWord_2075641
  simp only [CollatzResearch.WordTrace]
  refine ⟨75704846673314623105418777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50469897782209748736945851 75704846673314623105418777)
  ·
    refine ⟨56778635004985967329064083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75704846673314623105418777 56778635004985967329064083)
    ·
      refine ⟨85167952507478950993596125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56778635004985967329064083 85167952507478950993596125)
      ·
        refine ⟨31937982190304606622598547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85167952507478950993596125 31937982190304606622598547)
        ·
          refine ⟨47906973285456909933897821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31937982190304606622598547 47906973285456909933897821)
          ·
            refine ⟨17965114982046341225211683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47906973285456909933897821 17965114982046341225211683)
            ·
              refine ⟨26947672473069511837817525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17965114982046341225211683 26947672473069511837817525)
              ·
                refine ⟨2526344294350266734795393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26947672473069511837817525 2526344294350266734795393)
                ·
                  refine ⟨1894758220762700051096545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526344294350266734795393 1894758220762700051096545)
                  ·
                    refine ⟨1421068665572025038322409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1894758220762700051096545 1421068665572025038322409)
                    ·
                      refine ⟨1065801499179018778741807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421068665572025038322409 1065801499179018778741807)
                      ·
                        rfl

theorem cell23_2075641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_2075641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075641 prefixEnd_2075641 := by exact prefixLift 2075641
  have htrace : WordTrace (prefixWord ++ tailWord_2075641) baseStart_2075641 baseEnd_2075641 := by
    simpa [prefixWord, tailWord_2075641, baseEnd_2075641] using wordTrace_append hprefix tailTrace_2075641
  have hstable : (prefixWord ++ tailWord_2075641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075641).length < 2 ^ (prefixWord ++ tailWord_2075641).sum := by decide
  have hdescent : baseEnd_2075641 < baseStart_2075641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075697 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2075697 : Nat := 118140960795 + 2075697 * 2 ^ 59
def prefixEnd_2075697 : Nat := 4983230072969 + 3 ^ 40 * 2075697 * 2
def baseEnd_2075697 : Nat := 1065830254095670559641549

theorem tailTrace_2075697 : CollatzResearch.WordTrace tailWord_2075697 prefixEnd_2075697 1065830254095670559641549 := by
  unfold tailWord_2075697
  simp only [CollatzResearch.WordTrace]
  refine ⟨75706889161111744669457345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50471259440741163112971563 75706889161111744669457345)
  ·
    refine ⟨56780166870833808502093009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75706889161111744669457345 56780166870833808502093009)
    ·
      refine ⟨42585125153125356376569757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56780166870833808502093009 42585125153125356376569757)
      ·
        refine ⟨15969421932422008641213659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42585125153125356376569757 15969421932422008641213659)
        ·
          refine ⟨23954132898633012961820489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15969421932422008641213659 23954132898633012961820489)
          ·
            refine ⟨17965599673974759721365367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23954132898633012961820489 17965599673974759721365367)
            ·
              refine ⟨26948399510962139582048051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17965599673974759721365367 26948399510962139582048051)
              ·
                refine ⟨40422599266443209373072077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26948399510962139582048051 40422599266443209373072077)
                ·
                  refine ⟨15158474724916203514902029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40422599266443209373072077 15158474724916203514902029)
                  ·
                    refine ⟨5684428021843576318088261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15158474724916203514902029 5684428021843576318088261)
                    ·
                      refine ⟨1065830254095670559641549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5684428021843576318088261 1065830254095670559641549)
                      ·
                        rfl

theorem cell23_2075697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2075697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075697 prefixEnd_2075697 := by exact prefixLift 2075697
  have htrace : WordTrace (prefixWord ++ tailWord_2075697) baseStart_2075697 baseEnd_2075697 := by
    simpa [prefixWord, tailWord_2075697, baseEnd_2075697] using wordTrace_append hprefix tailTrace_2075697
  have hstable : (prefixWord ++ tailWord_2075697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075697).length < 2 ^ (prefixWord ++ tailWord_2075697).sum := by decide
  have hdescent : baseEnd_2075697 < baseStart_2075697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075825 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 2, 3, 2]
def baseStart_2075825 : Nat := 118140960795 + 2075825 * 2 ^ 59
def prefixEnd_2075825 : Nat := 4983230072969 + 3 ^ 40 * 2075825 * 2
def baseEnd_2075825 : Nat := 1065895979619446058840961

theorem tailTrace_2075825 : CollatzResearch.WordTrace tailWord_2075825 prefixEnd_2075825 1065895979619446058840961 := by
  unfold tailWord_2075825
  simp only [CollatzResearch.WordTrace]
  refine ⟨75711557704648022530116929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50474371803098681686744619 75711557704648022530116929)
  ·
    refine ⟨56783668278486016897587697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75711557704648022530116929 56783668278486016897587697)
    ·
      refine ⟨42587751208864512673190773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56783668278486016897587697 42587751208864512673190773)
      ·
        refine ⟨3992601675831048063111635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42587751208864512673190773 3992601675831048063111635)
        ·
          refine ⟨5988902513746572094667453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992601675831048063111635 5988902513746572094667453)
          ·
            refine ⟨2245838442654964535500295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5988902513746572094667453 2245838442654964535500295)
            ·
              refine ⟨3368757663982446803250443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245838442654964535500295 3368757663982446803250443)
              ·
                refine ⟨5053136495973670204875665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368757663982446803250443 5053136495973670204875665)
                ·
                  refine ⟨3789852371980252653656749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5053136495973670204875665 3789852371980252653656749)
                  ·
                    refine ⟨1421194639492594745121281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789852371980252653656749 1421194639492594745121281)
                    ·
                      refine ⟨1065895979619446058840961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421194639492594745121281 1065895979619446058840961)
                      ·
                        rfl

theorem cell23_2075825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_2075825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075825 prefixEnd_2075825 := by exact prefixLift 2075825
  have htrace : WordTrace (prefixWord ++ tailWord_2075825) baseStart_2075825 baseEnd_2075825 := by
    simpa [prefixWord, tailWord_2075825, baseEnd_2075825] using wordTrace_append hprefix tailTrace_2075825
  have hstable : (prefixWord ++ tailWord_2075825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075825).length < 2 ^ (prefixWord ++ tailWord_2075825).sum := by decide
  have hdescent : baseEnd_2075825 < baseStart_2075825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075827 : List Nat := [1, 1, 1, 2, 3, 2, 2, 11]
def baseStart_2075827 : Nat := 118140960795 + 2075827 * 2 ^ 59
def prefixEnd_2075827 : Nat := 4983230072969 + 3 ^ 40 * 2075827 * 2
def baseEnd_2075827 : Nat := 39477666910398335222813

theorem tailTrace_2075827 : CollatzResearch.WordTrace tailWord_2075827 prefixEnd_2075827 39477666910398335222813 := by
  unfold tailWord_2075827
  simp only [CollatzResearch.WordTrace]
  refine ⟨75711630650640776871689735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50474420433760517914459823 75711630650640776871689735)
  ·
    refine ⟨113567445975961165307534603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75711630650640776871689735 113567445975961165307534603)
    ·
      refine ⟨170351168963941747961301905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113567445975961165307534603 170351168963941747961301905)
      ·
        refine ⟨127763376722956310970976429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170351168963941747961301905 127763376722956310970976429)
        ·
          refine ⟨47911266271108616614116161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127763376722956310970976429 47911266271108616614116161)
          ·
            refine ⟨35933449703331462460587121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47911266271108616614116161 35933449703331462460587121)
            ·
              refine ⟨26950087277498596845440341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35933449703331462460587121 26950087277498596845440341)
              ·
                refine ⟨39477666910398335222813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 26950087277498596845440341 39477666910398335222813)
                ·
                  rfl

theorem cell23_2075827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 11].length) (baseStart_2075827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075827 prefixEnd_2075827 := by exact prefixLift 2075827
  have htrace : WordTrace (prefixWord ++ tailWord_2075827) baseStart_2075827 baseEnd_2075827 := by
    simpa [prefixWord, tailWord_2075827, baseEnd_2075827] using wordTrace_append hprefix tailTrace_2075827
  have hstable : (prefixWord ++ tailWord_2075827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075827).length < 2 ^ (prefixWord ++ tailWord_2075827).sum := by decide
  have hdescent : baseEnd_2075827 < baseStart_2075827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075838 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_2075838 : Nat := 118140960795 + 2075838 * 2 ^ 59
def prefixEnd_2075838 : Nat := 4983230072969 + 3 ^ 40 * 2075838 * 2
def baseEnd_2075838 : Nat := 1065902654867954507978401

theorem tailTrace_2075838 : CollatzResearch.WordTrace tailWord_2075838 prefixEnd_2075838 1065902654867954507978401 := by
  unfold tailWord_2075838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464003981700115718792521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50474687902400617166893445 9464003981700115718792521)
  ·
    refine ⟨7098002986275086789094391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9464003981700115718792521 7098002986275086789094391)
    ·
      refine ⟨10647004479412630183641587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7098002986275086789094391 10647004479412630183641587)
      ·
        refine ⟨15970506719118945275462381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10647004479412630183641587 15970506719118945275462381)
        ·
          refine ⟨5988940019669604478298393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15970506719118945275462381 5988940019669604478298393)
          ·
            refine ⟨4491705014752203358723795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5988940019669604478298393 4491705014752203358723795)
            ·
              refine ⟨6737557522128305038085693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491705014752203358723795 6737557522128305038085693)
              ·
                refine ⟨2526584070798114389282135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6737557522128305038085693 2526584070798114389282135)
                ·
                  refine ⟨3789876106197171583923203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526584070798114389282135 3789876106197171583923203)
                  ·
                    refine ⟨5684814159295757375884805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3789876106197171583923203 5684814159295757375884805)
                    ·
                      refine ⟨1065902654867954507978401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5684814159295757375884805 1065902654867954507978401)
                      ·
                        rfl

theorem cell23_2075838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_2075838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075838 prefixEnd_2075838 := by exact prefixLift 2075838
  have htrace : WordTrace (prefixWord ++ tailWord_2075838) baseStart_2075838 baseEnd_2075838 := by
    simpa [prefixWord, tailWord_2075838, baseEnd_2075838] using wordTrace_append hprefix tailTrace_2075838
  have hstable : (prefixWord ++ tailWord_2075838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075838).length < 2 ^ (prefixWord ++ tailWord_2075838).sum := by decide
  have hdescent : baseEnd_2075838 < baseStart_2075838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075871 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 3]
def baseStart_2075871 : Nat := 118140960795 + 2075871 * 2 ^ 59
def prefixEnd_2075871 : Nat := 4983230072969 + 3 ^ 40 * 2075871 * 2
def baseEnd_2075871 : Nat := 1065919599729552878865749

theorem tailTrace_2075871 : CollatzResearch.WordTrace tailWord_2075871 prefixEnd_2075871 1065919599729552878865749 := by
  unfold tailWord_2075871
  simp only [CollatzResearch.WordTrace]
  refine ⟨75713235462481372386291467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50475490308320914924194311 75713235462481372386291467)
  ·
    refine ⟨113569853193722058579437201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75713235462481372386291467 113569853193722058579437201)
    ·
      refine ⟨85177389895291543934577901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113569853193722058579437201 85177389895291543934577901)
      ·
        refine ⟨31941521210734328975466713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85177389895291543934577901 31941521210734328975466713)
        ·
          refine ⟨23956140908050746731600035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31941521210734328975466713 23956140908050746731600035)
          ·
            refine ⟨35934211362076120097400053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23956140908050746731600035 35934211362076120097400053)
            ·
              refine ⟨3368832315194636259131255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35934211362076120097400053 3368832315194636259131255)
              ·
                refine ⟨5053248472791954388696883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368832315194636259131255 5053248472791954388696883)
                ·
                  refine ⟨7579872709187931583045325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053248472791954388696883 7579872709187931583045325)
                  ·
                    refine ⟨2842452265945474343641997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7579872709187931583045325 2842452265945474343641997)
                    ·
                      refine ⟨1065919599729552878865749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2842452265945474343641997 1065919599729552878865749)
                      ·
                        rfl

theorem cell23_2075871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_2075871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075871 prefixEnd_2075871 := by exact prefixLift 2075871
  have htrace : WordTrace (prefixWord ++ tailWord_2075871) baseStart_2075871 baseEnd_2075871 := by
    simpa [prefixWord, tailWord_2075871, baseEnd_2075871] using wordTrace_append hprefix tailTrace_2075871
  have hstable : (prefixWord ++ tailWord_2075871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075871).length < 2 ^ (prefixWord ++ tailWord_2075871).sum := by decide
  have hdescent : baseEnd_2075871 < baseStart_2075871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075884 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_2075884 : Nat := 118140960795 + 2075884 * 2 ^ 59
def prefixEnd_2075884 : Nat := 4983230072969 + 3 ^ 40 * 2075884 * 2
def baseEnd_2075884 : Nat := 1065926274978061328003189

theorem tailTrace_2075884 : CollatzResearch.WordTrace tailWord_2075884 prefixEnd_2075884 1065926274978061328003189 := by
  unfold tailWord_2075884
  simp only [CollatzResearch.WordTrace]
  refine ⟨37856854805717137803257353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50475806407622850404343137 37856854805717137803257353)
  ·
    refine ⟨28392641104287853352443015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37856854805717137803257353 28392641104287853352443015)
    ·
      refine ⟨42588961656431780028664523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28392641104287853352443015 42588961656431780028664523)
      ·
        refine ⟨63883442484647670042996785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42588961656431780028664523 63883442484647670042996785)
        ·
          refine ⟨47912581863485752532247589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63883442484647670042996785 47912581863485752532247589)
          ·
            refine ⟨8983609099403578599796423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47912581863485752532247589 8983609099403578599796423)
            ·
              refine ⟨13475413649105367899694635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983609099403578599796423 13475413649105367899694635)
              ·
                refine ⟨20213120473658051849541953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13475413649105367899694635 20213120473658051849541953)
                ·
                  refine ⟨15159840355243538887156465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20213120473658051849541953 15159840355243538887156465)
                  ·
                    refine ⟨11369880266432654165367349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15159840355243538887156465 11369880266432654165367349)
                    ·
                      refine ⟨1065926274978061328003189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11369880266432654165367349 1065926274978061328003189)
                      ·
                        rfl

theorem cell23_2075884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_2075884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075884 prefixEnd_2075884 := by exact prefixLift 2075884
  have htrace : WordTrace (prefixWord ++ tailWord_2075884) baseStart_2075884 baseEnd_2075884 := by
    simpa [prefixWord, tailWord_2075884, baseEnd_2075884] using wordTrace_append hprefix tailTrace_2075884
  have hstable : (prefixWord ++ tailWord_2075884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075884).length < 2 ^ (prefixWord ++ tailWord_2075884).sum := by decide
  have hdescent : baseEnd_2075884 < baseStart_2075884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075892 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2075892 : Nat := 118140960795 + 2075892 * 2 ^ 59
def prefixEnd_2075892 : Nat := 4983230072969 + 3 ^ 40 * 2075892 * 2
def baseEnd_2075892 : Nat := 1065930382823297296703153

theorem tailTrace_2075892 : CollatzResearch.WordTrace tailWord_2075892 prefixEnd_2075892 1065930382823297296703153 := by
  unfold tailWord_2075892
  simp only [CollatzResearch.WordTrace]
  refine ⟨37857000697702646486402965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50476000930270195315203953 37857000697702646486402965)
  ·
    refine ⟨1774546907704811554050139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37857000697702646486402965 1774546907704811554050139)
    ·
      refine ⟨2661820361557217331075209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774546907704811554050139 2661820361557217331075209)
      ·
        refine ⟨1996365271167912998306407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2661820361557217331075209 1996365271167912998306407)
        ·
          refine ⟨2994547906751869497459611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996365271167912998306407 2994547906751869497459611)
          ·
            refine ⟨4491821860127804246189417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994547906751869497459611 4491821860127804246189417)
            ·
              refine ⟨3368866395095853184642063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491821860127804246189417 3368866395095853184642063)
              ·
                refine ⟨5053299592643779776963095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368866395095853184642063 5053299592643779776963095)
                ·
                  refine ⟨7579949388965669665444643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5053299592643779776963095 7579949388965669665444643)
                  ·
                    refine ⟨11369924083448504498166965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7579949388965669665444643 11369924083448504498166965)
                    ·
                      refine ⟨1065930382823297296703153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11369924083448504498166965 1065930382823297296703153)
                      ·
                        rfl

theorem cell23_2075892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2075892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075892 prefixEnd_2075892 := by exact prefixLift 2075892
  have htrace : WordTrace (prefixWord ++ tailWord_2075892) baseStart_2075892 baseEnd_2075892 := by
    simpa [prefixWord, tailWord_2075892, baseEnd_2075892] using wordTrace_append hprefix tailTrace_2075892
  have hstable : (prefixWord ++ tailWord_2075892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075892).length < 2 ^ (prefixWord ++ tailWord_2075892).sum := by decide
  have hdescent : baseEnd_2075892 < baseStart_2075892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075898 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2]
def baseStart_2075898 : Nat := 118140960795 + 2075898 * 2 ^ 59
def prefixEnd_2075898 : Nat := 4983230072969 + 3 ^ 40 * 2075898 * 2
def baseEnd_2075898 : Nat := 1065933463707224273228125

theorem tailTrace_2075898 : CollatzResearch.WordTrace tailWord_2075898 prefixEnd_2075898 1065933463707224273228125 := by
  unfold tailWord_2075898
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928555058345888999381087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50476146822255703998349565 18928555058345888999381087)
  ·
    refine ⟨28392832587518833499071631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18928555058345888999381087 28392832587518833499071631)
    ·
      refine ⟨42589248881278250248607447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28392832587518833499071631 42589248881278250248607447)
      ·
        refine ⟨63883873321917375372911171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42589248881278250248607447 63883873321917375372911171)
        ·
          refine ⟨95825809982876063059366757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63883873321917375372911171 95825809982876063059366757)
          ·
            refine ⟨17967339371789261823631267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95825809982876063059366757 17967339371789261823631267)
            ·
              refine ⟨26951009057683892735446901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17967339371789261823631267 26951009057683892735446901)
              ·
                refine ⟨2526657099157864943948147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26951009057683892735446901 2526657099157864943948147)
                ·
                  refine ⟨3789985648736797415922221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526657099157864943948147 3789985648736797415922221)
                  ·
                    refine ⟨1421244618276299030970833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3789985648736797415922221 1421244618276299030970833)
                    ·
                      refine ⟨1065933463707224273228125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421244618276299030970833 1065933463707224273228125)
                      ·
                        rfl

theorem cell23_2075898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_2075898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075898 prefixEnd_2075898 := by exact prefixLift 2075898
  have htrace : WordTrace (prefixWord ++ tailWord_2075898) baseStart_2075898 baseEnd_2075898 := by
    simpa [prefixWord, tailWord_2075898, baseEnd_2075898] using wordTrace_append hprefix tailTrace_2075898
  have hstable : (prefixWord ++ tailWord_2075898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075898).length < 2 ^ (prefixWord ++ tailWord_2075898).sum := by decide
  have hdescent : baseEnd_2075898 < baseStart_2075898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075906 : List Nat := [3, 4, 1, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_2075906 : Nat := 118140960795 + 2075906 * 2 ^ 59
def prefixEnd_2075906 : Nat := 4983230072969 + 3 ^ 40 * 2075906 * 2
def baseEnd_2075906 : Nat := 1065937571552460241928089

theorem tailTrace_2075906 : CollatzResearch.WordTrace tailWord_2075906 prefixEnd_2075906 1065937571552460241928089 := by
  unfold tailWord_2075906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928628004338643340953893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50476341344903048909210381 18928628004338643340953893)
  ·
    refine ⟨3549117750813495626428855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18928628004338643340953893 3549117750813495626428855)
    ·
      refine ⟨5323676626220243439643283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549117750813495626428855 5323676626220243439643283)
      ·
        refine ⟨7985514939330365159464925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5323676626220243439643283 7985514939330365159464925)
        ·
          refine ⟨2994568102248886934799347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7985514939330365159464925 2994568102248886934799347)
          ·
            refine ⟨4491852153373330402199021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994568102248886934799347 4491852153373330402199021)
            ·
              refine ⟨1684444557514998900824633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4491852153373330402199021 1684444557514998900824633)
              ·
                refine ⟨1263333418136249175618475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684444557514998900824633 1263333418136249175618475)
                ·
                  refine ⟨1895000127204373763427713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263333418136249175618475 1895000127204373763427713)
                  ·
                    refine ⟨1421250095403280322570785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1895000127204373763427713 1421250095403280322570785)
                    ·
                      refine ⟨1065937571552460241928089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421250095403280322570785 1065937571552460241928089)
                      ·
                        rfl

theorem cell23_2075906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_2075906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075906 prefixEnd_2075906 := by exact prefixLift 2075906
  have htrace : WordTrace (prefixWord ++ tailWord_2075906) baseStart_2075906 baseEnd_2075906 := by
    simpa [prefixWord, tailWord_2075906, baseEnd_2075906] using wordTrace_append hprefix tailTrace_2075906
  have hstable : (prefixWord ++ tailWord_2075906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075906).length < 2 ^ (prefixWord ++ tailWord_2075906).sum := by decide
  have hdescent : baseEnd_2075906 < baseStart_2075906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075914 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2075914 : Nat := 118140960795 + 2075914 * 2 ^ 59
def prefixEnd_2075914 : Nat := 4983230072969 + 3 ^ 40 * 2075914 * 2
def baseEnd_2075914 : Nat := 1065941679397696210628051

theorem tailTrace_2075914 : CollatzResearch.WordTrace tailWord_2075914 prefixEnd_2075914 1065941679397696210628051 := by
  unfold tailWord_2075914
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928700950331397682526699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50476535867550393820071197 18928700950331397682526699)
  ·
    refine ⟨28393051425497096523790049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18928700950331397682526699 28393051425497096523790049)
    ·
      refine ⟨21294788569122822392842537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28393051425497096523790049 21294788569122822392842537)
      ·
        refine ⟨15971091426842116794631903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21294788569122822392842537 15971091426842116794631903)
        ·
          refine ⟨23956637140263175191947855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15971091426842116794631903 23956637140263175191947855)
          ·
            refine ⟨35934955710394762787921783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23956637140263175191947855 35934955710394762787921783)
            ·
              refine ⟨53902433565592144181882675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35934955710394762787921783 53902433565592144181882675)
              ·
                refine ⟨80853650348388216272824013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53902433565592144181882675 80853650348388216272824013)
                ·
                  refine ⟨30320118880645581102309005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80853650348388216272824013 30320118880645581102309005)
                  ·
                    refine ⟨11370044580242092913365877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30320118880645581102309005 11370044580242092913365877)
                    ·
                      refine ⟨1065941679397696210628051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11370044580242092913365877 1065941679397696210628051)
                      ·
                        rfl

theorem cell23_2075914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2075914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075914 prefixEnd_2075914 := by exact prefixLift 2075914
  have htrace : WordTrace (prefixWord ++ tailWord_2075914) baseStart_2075914 baseEnd_2075914 := by
    simpa [prefixWord, tailWord_2075914, baseEnd_2075914] using wordTrace_append hprefix tailTrace_2075914
  have hstable : (prefixWord ++ tailWord_2075914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075914).length < 2 ^ (prefixWord ++ tailWord_2075914).sum := by decide
  have hdescent : baseEnd_2075914 < baseStart_2075914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075949 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2075949 : Nat := 118140960795 + 2075949 * 2 ^ 59
def prefixEnd_2075949 : Nat := 4983230072969 + 3 ^ 40 * 2075949 * 2
def baseEnd_2075949 : Nat := 1065959651220603573690391

theorem tailTrace_2075949 : CollatzResearch.WordTrace tailWord_2075949 prefixEnd_2075949 1065959651220603573690391 := by
  unfold tailWord_2075949
  simp only [CollatzResearch.WordTrace]
  refine ⟨75716080356198791707630901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50477386904132527805087267 75716080356198791707630901)
  ·
    refine ⟨7098382533393636722590397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75716080356198791707630901 7098382533393636722590397)
    ·
      refine ⟨2661893450022613770971399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7098382533393636722590397 2661893450022613770971399)
      ·
        refine ⟨3992840175033920656457099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661893450022613770971399 3992840175033920656457099)
        ·
          refine ⟨5989260262550880984685649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992840175033920656457099 5989260262550880984685649)
          ·
            refine ⟨4491945196913160738514237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5989260262550880984685649 4491945196913160738514237)
            ·
              refine ⟨1684479448842435276942839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4491945196913160738514237 1684479448842435276942839)
              ·
                refine ⟨2526719173263652915414259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684479448842435276942839 2526719173263652915414259)
                ·
                  refine ⟨3790078759895479373121389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526719173263652915414259 3790078759895479373121389)
                  ·
                    refine ⟨1421279534960804764920521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3790078759895479373121389 1421279534960804764920521)
                    ·
                      refine ⟨1065959651220603573690391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421279534960804764920521 1065959651220603573690391)
                      ·
                        rfl

theorem cell23_2075949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2075949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075949 prefixEnd_2075949 := by exact prefixLift 2075949
  have htrace : WordTrace (prefixWord ++ tailWord_2075949) baseStart_2075949 baseEnd_2075949 := by
    simpa [prefixWord, tailWord_2075949, baseEnd_2075949] using wordTrace_append hprefix tailTrace_2075949
  have hstable : (prefixWord ++ tailWord_2075949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075949).length < 2 ^ (prefixWord ++ tailWord_2075949).sum := by decide
  have hdescent : baseEnd_2075949 < baseStart_2075949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075951 : List Nat := [1, 1, 2, 1, 2, 1, 3, 7, 5]
def baseStart_2075951 : Nat := 118140960795 + 2075951 * 2 ^ 59
def prefixEnd_2075951 : Nat := 4983230072969 + 3 ^ 40 * 2075951 * 2
def baseEnd_2075951 : Nat := 118440075353545840651709

theorem tailTrace_2075951 : CollatzResearch.WordTrace tailWord_2075951 prefixEnd_2075951 118440075353545840651709 := by
  unfold tailWord_2075951
  simp only [CollatzResearch.WordTrace]
  refine ⟨75716153302191546049203707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50477435534794364032802471 75716153302191546049203707)
  ·
    refine ⟨113574229953287319073805561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75716153302191546049203707 113574229953287319073805561)
    ·
      refine ⟨85180672464965489305354171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113574229953287319073805561 85180672464965489305354171)
      ·
        refine ⟨127771008697448233958031257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85180672464965489305354171 127771008697448233958031257)
        ·
          refine ⟨95828256523086175468523443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127771008697448233958031257 95828256523086175468523443)
          ·
            refine ⟨143742384784629263202785165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95828256523086175468523443 143742384784629263202785165)
            ·
              refine ⟨53903394294235973701044437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143742384784629263202785165 53903394294235973701044437)
              ·
                refine ⟨1263360803771155633618229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53903394294235973701044437 1263360803771155633618229)
                ·
                  refine ⟨118440075353545840651709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1263360803771155633618229 118440075353545840651709)
                  ·
                    rfl

theorem cell23_2075951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 5].length) (baseStart_2075951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075951 prefixEnd_2075951 := by exact prefixLift 2075951
  have htrace : WordTrace (prefixWord ++ tailWord_2075951) baseStart_2075951 baseEnd_2075951 := by
    simpa [prefixWord, tailWord_2075951, baseEnd_2075951] using wordTrace_append hprefix tailTrace_2075951
  have hstable : (prefixWord ++ tailWord_2075951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075951).length < 2 ^ (prefixWord ++ tailWord_2075951).sum := by decide
  have hdescent : baseEnd_2075951 < baseStart_2075951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2075988 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_2075988 : Nat := 118140960795 + 2075988 * 2 ^ 59
def prefixEnd_2075988 : Nat := 4983230072969 + 3 ^ 40 * 2075988 * 2
def baseEnd_2075988 : Nat := 1065979676966128921102711

theorem tailTrace_2075988 : CollatzResearch.WordTrace tailWord_2075988 prefixEnd_2075988 1065979676966128921102711 := by
  unfold tailWord_2075988
  simp only [CollatzResearch.WordTrace]
  refine ⟨37858751401528750684150309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50478335202038334245533745 37858751401528750684150309)
  ·
    refine ⟨7098515887786640753278183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37858751401528750684150309 7098515887786640753278183)
    ·
      refine ⟨10647773831679961129917275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7098515887786640753278183 10647773831679961129917275)
      ·
        refine ⟨15971660747519941694875913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10647773831679961129917275 15971660747519941694875913)
        ·
          refine ⟨11978745560639956271156935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15971660747519941694875913 11978745560639956271156935)
          ·
            refine ⟨17968118340959934406735403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11978745560639956271156935 17968118340959934406735403)
            ·
              refine ⟨26952177511439901610103105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17968118340959934406735403 26952177511439901610103105)
              ·
                refine ⟨20214133133579926207577329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26952177511439901610103105 20214133133579926207577329)
                ·
                  refine ⟨15160599850184944655682997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20214133133579926207577329 15160599850184944655682997)
                  ·
                    refine ⟨1421306235954838561470281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15160599850184944655682997 1421306235954838561470281)
                    ·
                      refine ⟨1065979676966128921102711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421306235954838561470281 1065979676966128921102711)
                      ·
                        rfl

theorem cell23_2075988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_2075988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2075988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2075988 prefixEnd_2075988 := by exact prefixLift 2075988
  have htrace : WordTrace (prefixWord ++ tailWord_2075988) baseStart_2075988 baseEnd_2075988 := by
    simpa [prefixWord, tailWord_2075988, baseEnd_2075988] using wordTrace_append hprefix tailTrace_2075988
  have hstable : (prefixWord ++ tailWord_2075988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2075988).length < 2 ^ (prefixWord ++ tailWord_2075988).sum := by decide
  have hdescent : baseEnd_2075988 < baseStart_2075988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2075988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076018 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_2076018 : Nat := 118140960795 + 2076018 * 2 ^ 59
def prefixEnd_2076018 : Nat := 4983230072969 + 3 ^ 40 * 2076018 * 2
def baseEnd_2076018 : Nat := 1065995081385763803727573

theorem tailTrace_2076018 : CollatzResearch.WordTrace tailWord_2076018 prefixEnd_2076018 1065995081385763803727573 := by
  unfold tailWord_2076018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18929649248237204122973177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50479064661965877661261805 18929649248237204122973177)
  ·
    refine ⟨14197236936177903092229883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18929649248237204122973177 14197236936177903092229883)
    ·
      refine ⟨21295855404266854638344825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14197236936177903092229883 21295855404266854638344825)
      ·
        refine ⟨15971891553200140978758619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21295855404266854638344825 15971891553200140978758619)
        ·
          refine ⟨23957837329800211468137929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15971891553200140978758619 23957837329800211468137929)
          ·
            refine ⟨17968377997350158601103447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23957837329800211468137929 17968377997350158601103447)
            ·
              refine ⟨26952566996025237901655171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17968377997350158601103447 26952566996025237901655171)
              ·
                refine ⟨40428850494037856852482757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26952566996025237901655171 40428850494037856852482757)
                ·
                  refine ⟨7580409467632098159840517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40428850494037856852482757 7580409467632098159840517)
                  ·
                    refine ⟨1421326775181018404970097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7580409467632098159840517 1421326775181018404970097)
                    ·
                      refine ⟨1065995081385763803727573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421326775181018404970097 1065995081385763803727573)
                      ·
                        rfl

theorem cell23_2076018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_2076018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076018 prefixEnd_2076018 := by exact prefixLift 2076018
  have htrace : WordTrace (prefixWord ++ tailWord_2076018) baseStart_2076018 baseEnd_2076018 := by
    simpa [prefixWord, tailWord_2076018, baseEnd_2076018] using wordTrace_append hprefix tailTrace_2076018
  have hstable : (prefixWord ++ tailWord_2076018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076018).length < 2 ^ (prefixWord ++ tailWord_2076018).sum := by decide
  have hdescent : baseEnd_2076018 < baseStart_2076018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076028 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_2076028 : Nat := 118140960795 + 2076028 * 2 ^ 59
def prefixEnd_2076028 : Nat := 4983230072969 + 3 ^ 40 * 2076028 * 2
def baseEnd_2076028 : Nat := 355333405397436254867509

theorem tailTrace_2076028 : CollatzResearch.WordTrace tailWord_2076028 prefixEnd_2076028 355333405397436254867509 := by
  unfold tailWord_2076028
  simp only [CollatzResearch.WordTrace]
  refine ⟨37859480861456294099878369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50479307815275058799837825 37859480861456294099878369)
  ·
    refine ⟨28394610646092220574908777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37859480861456294099878369 28394610646092220574908777)
    ·
      refine ⟨21295957984569165431181583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28394610646092220574908777 21295957984569165431181583)
      ·
        refine ⟨31943936976853748146772375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21295957984569165431181583 31943936976853748146772375)
        ·
          refine ⟨47915905465280622220158563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31943936976853748146772375 47915905465280622220158563)
          ·
            refine ⟨71873858197920933330237845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47915905465280622220158563 71873858197920933330237845)
            ·
              refine ⟨3369087103027543749854899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71873858197920933330237845 3369087103027543749854899)
              ·
                refine ⟨5053630654541315624782349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369087103027543749854899 5053630654541315624782349)
                ·
                  refine ⟨1895111495452993359293381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5053630654541315624782349 1895111495452993359293381)
                  ·
                    refine ⟨355333405397436254867509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1895111495452993359293381 355333405397436254867509)
                    ·
                      rfl

theorem cell23_2076028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_2076028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076028 prefixEnd_2076028 := by exact prefixLift 2076028
  have htrace : WordTrace (prefixWord ++ tailWord_2076028) baseStart_2076028 baseEnd_2076028 := by
    simpa [prefixWord, tailWord_2076028, baseEnd_2076028] using wordTrace_append hprefix tailTrace_2076028
  have hstable : (prefixWord ++ tailWord_2076028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076028).length < 2 ^ (prefixWord ++ tailWord_2076028).sum := by decide
  have hdescent : baseEnd_2076028 < baseStart_2076028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076072 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2076072 : Nat := 118140960795 + 2076072 * 2 ^ 59
def prefixEnd_2076072 : Nat := 4983230072969 + 3 ^ 40 * 2076072 * 2
def baseEnd_2076072 : Nat := 1066022809341106592452325

theorem tailTrace_2076072 : CollatzResearch.WordTrace tailWord_2076072 prefixEnd_2076072 1066022809341106592452325 := by
  unfold tailWord_2076072
  simp only [CollatzResearch.WordTrace]
  refine ⟨37860283267376591857179235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50480377689835455809572313 37860283267376591857179235)
  ·
    refine ⟨56790424901064887785768853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37860283267376591857179235 56790424901064887785768853)
    ·
      refine ⟨2662051167237416614957915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56790424901064887785768853 2662051167237416614957915)
      ·
        refine ⟨3993076750856124922436873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662051167237416614957915 3993076750856124922436873)
        ·
          refine ⟨2994807563142093691827655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993076750856124922436873 2994807563142093691827655)
          ·
            refine ⟨4492211344713140537741483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994807563142093691827655 4492211344713140537741483)
            ·
              refine ⟨6738317017069710806612225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492211344713140537741483 6738317017069710806612225)
              ·
                refine ⟨5053737762802283104959169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6738317017069710806612225 5053737762802283104959169)
                ·
                  refine ⟨3790303322101712328719377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5053737762802283104959169 3790303322101712328719377)
                  ·
                    refine ⟨2842727491576284246539533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790303322101712328719377 2842727491576284246539533)
                    ·
                      refine ⟨1066022809341106592452325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2842727491576284246539533 1066022809341106592452325)
                      ·
                        rfl

theorem cell23_2076072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2076072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076072 prefixEnd_2076072 := by exact prefixLift 2076072
  have htrace : WordTrace (prefixWord ++ tailWord_2076072) baseStart_2076072 baseEnd_2076072 := by
    simpa [prefixWord, tailWord_2076072, baseEnd_2076072] using wordTrace_append hprefix tailTrace_2076072
  have hstable : (prefixWord ++ tailWord_2076072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076072).length < 2 ^ (prefixWord ++ tailWord_2076072).sum := by decide
  have hdescent : baseEnd_2076072 < baseStart_2076072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076092 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 6]
def baseStart_2076092 : Nat := 118140960795 + 2076092 * 2 ^ 59
def prefixEnd_2076092 : Nat := 4983230072969 + 3 ^ 40 * 2076092 * 2
def baseEnd_2076092 : Nat := 118448119883799612689137

theorem tailTrace_2076092 : CollatzResearch.WordTrace tailWord_2076092 prefixEnd_2076092 118448119883799612689137 := by
  unfold tailWord_2076092
  simp only [CollatzResearch.WordTrace]
  refine ⟨37860647997340363565043265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50480863996453818086724353 37860647997340363565043265)
  ·
    refine ⟨28395485998005272673782449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37860647997340363565043265 28395485998005272673782449)
    ·
      refine ⟨21296614498503954505336837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28395485998005272673782449 21296614498503954505336837)
      ·
        refine ⟨3993115218469491469750657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21296614498503954505336837 3993115218469491469750657)
        ·
          refine ⟨2994836413852118602312993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3993115218469491469750657 2994836413852118602312993)
          ·
            refine ⟨2246127310389088951734745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2994836413852118602312993 2246127310389088951734745)
            ·
              refine ⟨1684595482791816713801059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246127310389088951734745 1684595482791816713801059)
              ·
                refine ⟨2526893224187725070701589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684595482791816713801059 2526893224187725070701589)
                ·
                  refine ⟨118448119883799612689137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2526893224187725070701589 118448119883799612689137)
                  ·
                    rfl

theorem cell23_2076092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_2076092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076092 prefixEnd_2076092 := by exact prefixLift 2076092
  have htrace : WordTrace (prefixWord ++ tailWord_2076092) baseStart_2076092 baseEnd_2076092 := by
    simpa [prefixWord, tailWord_2076092, baseEnd_2076092] using wordTrace_append hprefix tailTrace_2076092
  have hstable : (prefixWord ++ tailWord_2076092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076092).length < 2 ^ (prefixWord ++ tailWord_2076092).sum := by decide
  have hdescent : baseEnd_2076092 < baseStart_2076092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076111 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_2076111 : Nat := 118140960795 + 2076111 * 2 ^ 59
def prefixEnd_2076111 : Nat := 4983230072969 + 3 ^ 40 * 2076111 * 2
def baseEnd_2076111 : Nat := 1066042835086631939864645

theorem tailTrace_2076111 : CollatzResearch.WordTrace tailWord_2076111 prefixEnd_2076111 1066042835086631939864645 := by
  unfold tailWord_2076111
  simp only [CollatzResearch.WordTrace]
  refine ⟨75721988981611893375028187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50481325987741262250018791 75721988981611893375028187)
  ·
    refine ⟨113582983472417840062542281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75721988981611893375028187 113582983472417840062542281)
    ·
      refine ⟨85187237604313380046906711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113582983472417840062542281 85187237604313380046906711)
      ·
        refine ⟨127780856406470070070360067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85187237604313380046906711 127780856406470070070360067)
        ·
          refine ⟨191671284609705105105540101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127780856406470070070360067 191671284609705105105540101)
          ·
            refine ⟨35938365864319707207288769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191671284609705105105540101 35938365864319707207288769)
            ·
              refine ⟨26953774398239780405466577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35938365864319707207288769 26953774398239780405466577)
              ·
                refine ⟨20215330798679835304099933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26953774398239780405466577 20215330798679835304099933)
                ·
                  refine ⟨7580749049504938239037475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20215330798679835304099933 7580749049504938239037475)
                  ·
                    refine ⟨11371123574257407358556213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7580749049504938239037475 11371123574257407358556213)
                    ·
                      refine ⟨1066042835086631939864645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11371123574257407358556213 1066042835086631939864645)
                      ·
                        rfl

theorem cell23_2076111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_2076111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076111 prefixEnd_2076111 := by exact prefixLift 2076111
  have htrace : WordTrace (prefixWord ++ tailWord_2076111) baseStart_2076111 baseEnd_2076111 := by
    simpa [prefixWord, tailWord_2076111, baseEnd_2076111] using wordTrace_append hprefix tailTrace_2076111
  have hstable : (prefixWord ++ tailWord_2076111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076111).length < 2 ^ (prefixWord ++ tailWord_2076111).sum := by decide
  have hdescent : baseEnd_2076111 < baseStart_2076111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076131 : List Nat := [1, 1, 1, 6, 2, 12]
def baseStart_2076131 : Nat := 118140960795 + 2076131 * 2 ^ 59
def prefixEnd_2076131 : Nat := 4983230072969 + 3 ^ 40 * 2076131 * 2
def baseEnd_2076131 : Nat := 4387049813579102311171

theorem tailTrace_2076131 : CollatzResearch.WordTrace tailWord_2076131 prefixEnd_2076131 4387049813579102311171 := by
  unfold tailWord_2076131
  simp only [CollatzResearch.WordTrace]
  refine ⟨75722718441539436790756247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50481812294359624527170831 75722718441539436790756247)
  ·
    refine ⟨113584077662309155186134371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75722718441539436790756247 113584077662309155186134371)
    ·
      refine ⟨170376116493463732779201557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113584077662309155186134371 170376116493463732779201557)
      ·
        refine ⟨7986380460631112474025073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170376116493463732779201557 7986380460631112474025073)
        ·
          refine ⟨5989785345473334355518805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7986380460631112474025073 5989785345473334355518805)
          ·
            refine ⟨4387049813579102311171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5989785345473334355518805 4387049813579102311171)
            ·
              rfl

theorem cell23_2076131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 12].length) (baseStart_2076131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076131 prefixEnd_2076131 := by exact prefixLift 2076131
  have htrace : WordTrace (prefixWord ++ tailWord_2076131) baseStart_2076131 baseEnd_2076131 := by
    simpa [prefixWord, tailWord_2076131, baseEnd_2076131] using wordTrace_append hprefix tailTrace_2076131
  have hstable : (prefixWord ++ tailWord_2076131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076131).length < 2 ^ (prefixWord ++ tailWord_2076131).sum := by decide
  have hdescent : baseEnd_2076131 < baseStart_2076131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076135 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 2, 4]
def baseStart_2076135 : Nat := 118140960795 + 2076135 * 2 ^ 59
def prefixEnd_2076135 : Nat := 4983230072969 + 3 ^ 40 * 2076135 * 2
def baseEnd_2076135 : Nat := 355351719540779948654845

theorem tailTrace_2076135 : CollatzResearch.WordTrace tailWord_2076135 prefixEnd_2076135 355351719540779948654845 := by
  unfold tailWord_2076135
  simp only [CollatzResearch.WordTrace]
  refine ⟨75722864333524945473901859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50481909555683296982601239 75722864333524945473901859)
  ·
    refine ⟨113584296500287418210852789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75722864333524945473901859 113584296500287418210852789)
    ·
      refine ⟨10648527796901945457267449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113584296500287418210852789 10648527796901945457267449)
      ·
        refine ⟨7986395847676459092950587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10648527796901945457267449 7986395847676459092950587)
        ·
          refine ⟨11979593771514688639425881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7986395847676459092950587 11979593771514688639425881)
          ·
            refine ⟨8984695328636016479569411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11979593771514688639425881 8984695328636016479569411)
            ·
              refine ⟨13477042992954024719354117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8984695328636016479569411 13477042992954024719354117)
              ·
                refine ⟨2526945561178879634878897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13477042992954024719354117 2526945561178879634878897)
                ·
                  refine ⟨1895209170884159726159173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526945561178879634878897 1895209170884159726159173)
                  ·
                    refine ⟨355351719540779948654845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1895209170884159726159173 355351719540779948654845)
                    ·
                      rfl

theorem cell23_2076135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_2076135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076135 prefixEnd_2076135 := by exact prefixLift 2076135
  have htrace : WordTrace (prefixWord ++ tailWord_2076135) baseStart_2076135 baseEnd_2076135 := by
    simpa [prefixWord, tailWord_2076135, baseEnd_2076135] using wordTrace_append hprefix tailTrace_2076135
  have hstable : (prefixWord ++ tailWord_2076135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076135).length < 2 ^ (prefixWord ++ tailWord_2076135).sum := by decide
  have hdescent : baseEnd_2076135 < baseStart_2076135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076142 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_2076142 : Nat := 118140960795 + 2076142 * 2 ^ 59
def prefixEnd_2076142 : Nat := 4983230072969 + 3 ^ 40 * 2076142 * 2
def baseEnd_2076142 : Nat := 1066058752986921318577003

theorem tailTrace_2076142 : CollatzResearch.WordTrace tailWord_2076142 prefixEnd_2076142 1066058752986921318577003 := by
  unfold tailWord_2076142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465389955562448208675835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50482079762999723779604453 9465389955562448208675835)
  ·
    refine ⟨14198084933343672313013753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9465389955562448208675835 14198084933343672313013753)
    ·
      refine ⟨10648563700007754234760315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14198084933343672313013753 10648563700007754234760315)
      ·
        refine ⟨15972845550011631352140473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10648563700007754234760315 15972845550011631352140473)
        ·
          refine ⟨11979634162508723514105355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15972845550011631352140473 11979634162508723514105355)
          ·
            refine ⟨17969451243763085271158033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11979634162508723514105355 17969451243763085271158033)
            ·
              refine ⟨13477088432822313953368525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17969451243763085271158033 13477088432822313953368525)
              ·
                refine ⟨5053908162308367732513197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13477088432822313953368525 5053908162308367732513197)
                ·
                  refine ⟨1895215560865637899692449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5053908162308367732513197 1895215560865637899692449)
                  ·
                    refine ⟨1421411670649228424769337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1895215560865637899692449 1421411670649228424769337)
                    ·
                      refine ⟨1066058752986921318577003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421411670649228424769337 1066058752986921318577003)
                      ·
                        rfl

theorem cell23_2076142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_2076142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076142 prefixEnd_2076142 := by exact prefixLift 2076142
  have htrace : WordTrace (prefixWord ++ tailWord_2076142) baseStart_2076142 baseEnd_2076142 := by
    simpa [prefixWord, tailWord_2076142, baseEnd_2076142] using wordTrace_append hprefix tailTrace_2076142
  have hstable : (prefixWord ++ tailWord_2076142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076142).length < 2 ^ (prefixWord ++ tailWord_2076142).sum := by decide
  have hdescent : baseEnd_2076142 < baseStart_2076142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076162 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2076162 : Nat := 118140960795 + 2076162 * 2 ^ 59
def prefixEnd_2076162 : Nat := 4983230072969 + 3 ^ 40 * 2076162 * 2
def baseEnd_2076162 : Nat := 1066069022600011240326911

theorem tailTrace_2076162 : CollatzResearch.WordTrace tailWord_2076162 prefixEnd_2076162 1066069022600011240326911 := by
  unfold tailWord_2076162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18930962276106782271283685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50482566069618086056756493 18930962276106782271283685)
  ·
    refine ⟨3549555426770021675865691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18930962276106782271283685 3549555426770021675865691)
    ·
      refine ⟨5324333140155032513798537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549555426770021675865691 5324333140155032513798537)
      ·
        refine ⟨3993249855116274385348903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5324333140155032513798537 3993249855116274385348903)
        ·
          refine ⟨5989874782674411578023355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993249855116274385348903 5989874782674411578023355)
          ·
            refine ⟨8984812174011617367035033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989874782674411578023355 8984812174011617367035033)
            ·
              refine ⟨6738609130508713025276275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8984812174011617367035033 6738609130508713025276275)
              ·
                refine ⟨10107913695763069537914413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738609130508713025276275 10107913695763069537914413)
                ·
                  refine ⟨3790467635911151076717905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10107913695763069537914413 3790467635911151076717905)
                  ·
                    refine ⟨2842850726933363307538429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790467635911151076717905 2842850726933363307538429)
                    ·
                      refine ⟨1066069022600011240326911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2842850726933363307538429 1066069022600011240326911)
                      ·
                        rfl

theorem cell23_2076162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2076162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076162 prefixEnd_2076162 := by exact prefixLift 2076162
  have htrace : WordTrace (prefixWord ++ tailWord_2076162) baseStart_2076162 baseEnd_2076162 := by
    simpa [prefixWord, tailWord_2076162, baseEnd_2076162] using wordTrace_append hprefix tailTrace_2076162
  have hstable : (prefixWord ++ tailWord_2076162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076162).length < 2 ^ (prefixWord ++ tailWord_2076162).sum := by decide
  have hdescent : baseEnd_2076162 < baseStart_2076162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076173 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2076173 : Nat := 118140960795 + 2076173 * 2 ^ 59
def prefixEnd_2076173 : Nat := 4983230072969 + 3 ^ 40 * 2076173 * 2
def baseEnd_2076173 : Nat := 355358223629070232429787

theorem tailTrace_2076173 : CollatzResearch.WordTrace tailWord_2076173 prefixEnd_2076173 355358223629070232429787 := by
  unfold tailWord_2076173
  simp only [CollatzResearch.WordTrace]
  refine ⟨75724250307387277963785173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50482833538258185309190115 75724250307387277963785173)
  ·
    refine ⟨1774787116579389327276215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 75724250307387277963785173 1774787116579389327276215)
    ·
      refine ⟨2662180674869083990914323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774787116579389327276215 2662180674869083990914323)
      ·
        refine ⟨3993271012303625986371485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662180674869083990914323 3993271012303625986371485)
        ·
          refine ⟨1497476629613859744889307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3993271012303625986371485 1497476629613859744889307)
          ·
            refine ⟨2246214944420789617333961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497476629613859744889307 2246214944420789617333961)
            ·
              refine ⟨1684661208315592213000471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246214944420789617333961 1684661208315592213000471)
              ·
                refine ⟨2526991812473388319500707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684661208315592213000471 2526991812473388319500707)
                ·
                  refine ⟨3790487718710082479251061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2526991812473388319500707 3790487718710082479251061)
                  ·
                    refine ⟨355358223629070232429787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3790487718710082479251061 355358223629070232429787)
                    ·
                      rfl

theorem cell23_2076173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2076173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076173 prefixEnd_2076173 := by exact prefixLift 2076173
  have htrace : WordTrace (prefixWord ++ tailWord_2076173) baseStart_2076173 baseEnd_2076173 := by
    simpa [prefixWord, tailWord_2076173, baseEnd_2076173] using wordTrace_append hprefix tailTrace_2076173
  have hstable : (prefixWord ++ tailWord_2076173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076173).length < 2 ^ (prefixWord ++ tailWord_2076173).sum := by decide
  have hdescent : baseEnd_2076173 < baseStart_2076173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076192 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2076192 : Nat := 118140960795 + 2076192 * 2 ^ 59
def prefixEnd_2076192 : Nat := 4983230072969 + 3 ^ 40 * 2076192 * 2
def baseEnd_2076192 : Nat := 1066084427019646122951773

theorem tailTrace_2076192 : CollatzResearch.WordTrace tailWord_2076192 prefixEnd_2076192 1066084427019646122951773 := by
  unfold tailWord_2076192
  simp only [CollatzResearch.WordTrace]
  refine ⟨37862471647159222104363415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50483295529545629472484553 37862471647159222104363415)
  ·
    refine ⟨56793707470738833156545123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37862471647159222104363415 56793707470738833156545123)
    ·
      refine ⟨85190561206108249734817685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56793707470738833156545123 85190561206108249734817685)
      ·
        refine ⟨3993307556536324206319579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85190561206108249734817685 3993307556536324206319579)
        ·
          refine ⟨5989961334804486309479369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993307556536324206319579 5989961334804486309479369)
          ·
            refine ⟨4492471001103364732109527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5989961334804486309479369 4492471001103364732109527)
            ·
              refine ⟨6738706501655047098164291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4492471001103364732109527 6738706501655047098164291)
              ·
                refine ⟨10108059752482570647246437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6738706501655047098164291 10108059752482570647246437)
                ·
                  refine ⟨1895261203590481996358707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10108059752482570647246437 1895261203590481996358707)
                  ·
                    refine ⟨2842891805385722994538061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1895261203590481996358707 2842891805385722994538061)
                    ·
                      refine ⟨1066084427019646122951773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2842891805385722994538061 1066084427019646122951773)
                      ·
                        rfl

theorem cell23_2076192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2076192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076192 prefixEnd_2076192 := by exact prefixLift 2076192
  have htrace : WordTrace (prefixWord ++ tailWord_2076192) baseStart_2076192 baseEnd_2076192 := by
    simpa [prefixWord, tailWord_2076192, baseEnd_2076192] using wordTrace_append hprefix tailTrace_2076192
  have hstable : (prefixWord ++ tailWord_2076192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076192).length < 2 ^ (prefixWord ++ tailWord_2076192).sum := by decide
  have hdescent : baseEnd_2076192 < baseStart_2076192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076218 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_2076218 : Nat := 118140960795 + 2076218 * 2 ^ 59
def prefixEnd_2076218 : Nat := 4983230072969 + 3 ^ 40 * 2076218 * 2
def baseEnd_2076218 : Nat := 1066097777516663021226653

theorem tailTrace_2076218 : CollatzResearch.WordTrace tailWord_2076218 prefixEnd_2076218 1066097777516663021226653 := by
  unfold tailWord_2076218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18931472898056062662293327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50483927728149500432782205 18931472898056062662293327)
  ·
    refine ⟨28397209347084093993439991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18931472898056062662293327 28397209347084093993439991)
    ·
      refine ⟨42595814020626140990159987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28397209347084093993439991 42595814020626140990159987)
      ·
        refine ⟨63893721030939211485239981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42595814020626140990159987 63893721030939211485239981)
        ·
          refine ⟨23960145386602204306964993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63893721030939211485239981 23960145386602204306964993)
          ·
            refine ⟨17970109039951653230223745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23960145386602204306964993 17970109039951653230223745)
            ·
              refine ⟨13477581779963739922667809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17970109039951653230223745 13477581779963739922667809)
              ·
                refine ⟨10108186334972804942000857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13477581779963739922667809 10108186334972804942000857)
                ·
                  refine ⟨7581139751229603706500643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10108186334972804942000857 7581139751229603706500643)
                  ·
                    refine ⟨11371709626844405559750965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7581139751229603706500643 11371709626844405559750965)
                    ·
                      refine ⟨1066097777516663021226653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11371709626844405559750965 1066097777516663021226653)
                      ·
                        rfl

theorem cell23_2076218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_2076218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076218 prefixEnd_2076218 := by exact prefixLift 2076218
  have htrace : WordTrace (prefixWord ++ tailWord_2076218) baseStart_2076218 baseEnd_2076218 := by
    simpa [prefixWord, tailWord_2076218, baseEnd_2076218] using wordTrace_append hprefix tailTrace_2076218
  have hstable : (prefixWord ++ tailWord_2076218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076218).length < 2 ^ (prefixWord ++ tailWord_2076218).sum := by decide
  have hdescent : baseEnd_2076218 < baseStart_2076218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076266 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_2076266 : Nat := 118140960795 + 2076266 * 2 ^ 59
def prefixEnd_2076266 : Nat := 4983230072969 + 3 ^ 40 * 2076266 * 2
def baseEnd_2076266 : Nat := 1066122424588078833426433

theorem tailTrace_2076266 : CollatzResearch.WordTrace tailWord_2076266 prefixEnd_2076266 1066122424588078833426433 := by
  unfold tailWord_2076266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18931910574012588711730163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50485094864033569897947101 18931910574012588711730163)
  ·
    refine ⟨28397865861018883067595245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18931910574012588711730163 28397865861018883067595245)
    ·
      refine ⟨10649199697882081150348217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28397865861018883067595245 10649199697882081150348217)
      ·
        refine ⟨7986899773411560862761163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10649199697882081150348217 7986899773411560862761163)
        ·
          refine ⟨11980349660117341294141745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7986899773411560862761163 11980349660117341294141745)
          ·
            refine ⟨8985262245088005970606309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11980349660117341294141745 8985262245088005970606309)
            ·
              refine ⟨1684736670954001119488683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8985262245088005970606309 1684736670954001119488683)
              ·
                refine ⟨2527105006431001679233025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684736670954001119488683 2527105006431001679233025)
                ·
                  refine ⟨1895328754823251259424769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2527105006431001679233025 1895328754823251259424769)
                  ·
                    refine ⟨1421496566117438444568577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1895328754823251259424769 1421496566117438444568577)
                    ·
                      refine ⟨1066122424588078833426433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421496566117438444568577 1066122424588078833426433)
                      ·
                        rfl

theorem cell23_2076266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_2076266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076266 prefixEnd_2076266 := by exact prefixLift 2076266
  have htrace : WordTrace (prefixWord ++ tailWord_2076266) baseStart_2076266 baseEnd_2076266 := by
    simpa [prefixWord, tailWord_2076266, baseEnd_2076266] using wordTrace_append hprefix tailTrace_2076266
  have hstable : (prefixWord ++ tailWord_2076266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076266).length < 2 ^ (prefixWord ++ tailWord_2076266).sum := by decide
  have hdescent : baseEnd_2076266 < baseStart_2076266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076268 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_2076268 : Nat := 118140960795 + 2076268 * 2 ^ 59
def prefixEnd_2076268 : Nat := 4983230072969 + 3 ^ 40 * 2076268 * 2
def baseEnd_2076268 : Nat := 355374483849795941867141

theorem tailTrace_2076268 : CollatzResearch.WordTrace tailWord_2076268 prefixEnd_2076268 355374483849795941867141 := by
  unfold tailWord_2076268
  simp only [CollatzResearch.WordTrace]
  refine ⟨37863857621021554594246729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50485143494695406125662305 37863857621021554594246729)
  ·
    refine ⟨28397893215766165945685047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37863857621021554594246729 28397893215766165945685047)
    ·
      refine ⟨42596839823649248918527571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28397893215766165945685047 42596839823649248918527571)
      ·
        refine ⟨63895259735473873377791357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42596839823649248918527571 63895259735473873377791357)
        ·
          refine ⟨23960722400802702516671759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63895259735473873377791357 23960722400802702516671759)
          ·
            refine ⟨35941083601204053775007639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23960722400802702516671759 35941083601204053775007639)
            ·
              refine ⟨53911625401806080662511459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35941083601204053775007639 53911625401806080662511459)
              ·
                refine ⟨80867438102709120993767189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53911625401806080662511459 80867438102709120993767189)
                ·
                  refine ⟨3790661161064490046582837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80867438102709120993767189 3790661161064490046582837)
                  ·
                    refine ⟨355374483849795941867141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3790661161064490046582837 355374483849795941867141)
                    ·
                      rfl

theorem cell23_2076268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_2076268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076268 prefixEnd_2076268 := by exact prefixLift 2076268
  have htrace : WordTrace (prefixWord ++ tailWord_2076268) baseStart_2076268 baseEnd_2076268 := by
    simpa [prefixWord, tailWord_2076268, baseEnd_2076268] using wordTrace_append hprefix tailTrace_2076268
  have hstable : (prefixWord ++ tailWord_2076268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076268).length < 2 ^ (prefixWord ++ tailWord_2076268).sum := by decide
  have hdescent : baseEnd_2076268 < baseStart_2076268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076285 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_2076285 : Nat := 118140960795 + 2076285 * 2 ^ 59
def prefixEnd_2076285 : Nat := 4983230072969 + 3 ^ 40 * 2076285 * 2
def baseEnd_2076285 : Nat := 355377393573504753029615

theorem tailTrace_2076285 : CollatzResearch.WordTrace tailWord_2076285 prefixEnd_2076285 355377393573504753029615 := by
  unfold tailWord_2076285
  simp only [CollatzResearch.WordTrace]
  refine ⟨75728335282981521091862309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50485556855321014061241539 75728335282981521091862309)
  ·
    refine ⟨14199062865559035204724183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75728335282981521091862309 14199062865559035204724183)
    ·
      refine ⟨21298594298338552807086275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14199062865559035204724183 21298594298338552807086275)
      ·
        refine ⟨31947891447507829210629413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21298594298338552807086275 31947891447507829210629413)
        ·
          refine ⟨5990229646407717976993015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31947891447507829210629413 5990229646407717976993015)
          ·
            refine ⟨8985344469611576965489523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990229646407717976993015 8985344469611576965489523)
            ·
              refine ⟨13478016704417365448234285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985344469611576965489523 13478016704417365448234285)
              ·
                refine ⟨5054256264156512043087857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13478016704417365448234285 5054256264156512043087857)
                ·
                  refine ⟨3790692198117384032315893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5054256264156512043087857 3790692198117384032315893)
                  ·
                    refine ⟨355377393573504753029615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3790692198117384032315893 355377393573504753029615)
                    ·
                      rfl

theorem cell23_2076285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_2076285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076285 prefixEnd_2076285 := by exact prefixLift 2076285
  have htrace : WordTrace (prefixWord ++ tailWord_2076285) baseStart_2076285 baseEnd_2076285 := by
    simpa [prefixWord, tailWord_2076285, baseEnd_2076285] using wordTrace_append hprefix tailTrace_2076285
  have hstable : (prefixWord ++ tailWord_2076285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076285).length < 2 ^ (prefixWord ++ tailWord_2076285).sum := by decide
  have hdescent : baseEnd_2076285 < baseStart_2076285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076306 : List Nat := [3, 2, 3, 1, 3, 2, 2, 2, 5]
def baseStart_2076306 : Nat := 118140960795 + 2076306 * 2 ^ 59
def prefixEnd_2076306 : Nat := 4983230072969 + 3 ^ 40 * 2076306 * 2
def baseEnd_2076306 : Nat := 118460329312695408547361

theorem tailTrace_2076306 : CollatzResearch.WordTrace tailWord_2076306 prefixEnd_2076306 118460329312695408547361 := by
  unfold tailWord_2076306
  simp only [CollatzResearch.WordTrace]
  refine ⟨18932275303976360419594193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50486067477270294452251181 18932275303976360419594193)
  ·
    refine ⟨14199206477982270314695645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18932275303976360419594193 14199206477982270314695645)
    ·
      refine ⟨5324702429243351368010867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14199206477982270314695645 5324702429243351368010867)
      ·
        refine ⟨7987053643865027052016301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324702429243351368010867 7987053643865027052016301)
        ·
          refine ⟨2995145116449385144506113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7987053643865027052016301 2995145116449385144506113)
          ·
            refine ⟨2246358837337038858379585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2995145116449385144506113 2246358837337038858379585)
            ·
              refine ⟨1684769128002779143784689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246358837337038858379585 1684769128002779143784689)
              ·
                refine ⟨1263576846002084357838517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684769128002779143784689 1263576846002084357838517)
                ·
                  refine ⟨118460329312695408547361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1263576846002084357838517 118460329312695408547361)
                  ·
                    rfl

theorem cell23_2076306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_2076306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076306 prefixEnd_2076306 := by exact prefixLift 2076306
  have htrace : WordTrace (prefixWord ++ tailWord_2076306) baseStart_2076306 baseEnd_2076306 := by
    simpa [prefixWord, tailWord_2076306, baseEnd_2076306] using wordTrace_append hprefix tailTrace_2076306
  have hstable : (prefixWord ++ tailWord_2076306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076306).length < 2 ^ (prefixWord ++ tailWord_2076306).sum := by decide
  have hdescent : baseEnd_2076306 < baseStart_2076306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076325 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_2076325 : Nat := 118140960795 + 2076325 * 2 ^ 59
def prefixEnd_2076325 : Nat := 4983230072969 + 3 ^ 40 * 2076325 * 2
def baseEnd_2076325 : Nat := 1066152719946694102588661

theorem tailTrace_2076325 : CollatzResearch.WordTrace tailWord_2076325 prefixEnd_2076325 1066152719946694102588661 := by
  unfold tailWord_2076325
  simp only [CollatzResearch.WordTrace]
  refine ⟨75729794202836607923318429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50486529468557738615545619 75729794202836607923318429)
  ·
    refine ⟨28398672826063727971244411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75729794202836607923318429 28398672826063727971244411)
    ·
      refine ⟨42598009239095591956866617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28398672826063727971244411 42598009239095591956866617)
      ·
        refine ⟨31948506929321693967649963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42598009239095591956866617 31948506929321693967649963)
        ·
          refine ⟨47922760393982540951474945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31948506929321693967649963 47922760393982540951474945)
          ·
            refine ⟨35942070295486905713606209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47922760393982540951474945 35942070295486905713606209)
            ·
              refine ⟨26956552721615179285204657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35942070295486905713606209 26956552721615179285204657)
              ·
                refine ⟨20217414541211384463903493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26956552721615179285204657 20217414541211384463903493)
                ·
                  refine ⟨3790765226477134586981905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20217414541211384463903493 3790765226477134586981905)
                  ·
                    refine ⟨2843073919857850940236429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790765226477134586981905 2843073919857850940236429)
                    ·
                      refine ⟨1066152719946694102588661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2843073919857850940236429 1066152719946694102588661)
                      ·
                        rfl

theorem cell23_2076325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_2076325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076325 prefixEnd_2076325 := by exact prefixLift 2076325
  have htrace : WordTrace (prefixWord ++ tailWord_2076325) baseStart_2076325 baseEnd_2076325 := by
    simpa [prefixWord, tailWord_2076325, baseEnd_2076325] using wordTrace_append hprefix tailTrace_2076325
  have hstable : (prefixWord ++ tailWord_2076325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076325).length < 2 ^ (prefixWord ++ tailWord_2076325).sum := by decide
  have hdescent : baseEnd_2076325 < baseStart_2076325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076349 : List Nat := [1, 4, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_2076349 : Nat := 118140960795 + 2076349 * 2 ^ 59
def prefixEnd_2076349 : Nat := 4983230072969 + 3 ^ 40 * 2076349 * 2
def baseEnd_2076349 : Nat := 355388347827467336229517

theorem tailTrace_2076349 : CollatzResearch.WordTrace tailWord_2076349 prefixEnd_2076349 355388347827467336229517 := by
  unfold tailWord_2076349
  simp only [CollatzResearch.WordTrace]
  refine ⟨75730669554749660022192101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50487113036499773348128067 75730669554749660022192101)
  ·
    refine ⟨14199500541515561254161019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75730669554749660022192101 14199500541515561254161019)
    ·
      refine ⟨21299250812273341881241529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14199500541515561254161019 21299250812273341881241529)
      ·
        refine ⟨15974438109205006410931147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21299250812273341881241529 15974438109205006410931147)
        ·
          refine ⟨23961657163807509616396721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15974438109205006410931147 23961657163807509616396721)
          ·
            refine ⟨17971242872855632212297541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23961657163807509616396721 17971242872855632212297541)
            ·
              refine ⟨3369608038660431039805789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17971242872855632212297541 3369608038660431039805789)
              ·
                refine ⟨1263603014497661639927171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3369608038660431039805789 1263603014497661639927171)
                ·
                  refine ⟨1895404521746492459890757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263603014497661639927171 1895404521746492459890757)
                  ·
                    refine ⟨355388347827467336229517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1895404521746492459890757 355388347827467336229517)
                    ·
                      rfl

theorem cell23_2076349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_2076349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076349 prefixEnd_2076349 := by exact prefixLift 2076349
  have htrace : WordTrace (prefixWord ++ tailWord_2076349) baseStart_2076349 baseEnd_2076349 := by
    simpa [prefixWord, tailWord_2076349, baseEnd_2076349] using wordTrace_append hprefix tailTrace_2076349
  have hstable : (prefixWord ++ tailWord_2076349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076349).length < 2 ^ (prefixWord ++ tailWord_2076349).sum := by decide
  have hdescent : baseEnd_2076349 < baseStart_2076349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076368 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_2076368 : Nat := 118140960795 + 2076368 * 2 ^ 59
def prefixEnd_2076368 : Nat := 4983230072969 + 3 ^ 40 * 2076368 * 2
def baseEnd_2076368 : Nat := 1066174799614837434350963

theorem tailTrace_2076368 : CollatzResearch.WordTrace tailWord_2076368 prefixEnd_2076368 1066174799614837434350963 := by
  unfold tailWord_2076368
  simp only [CollatzResearch.WordTrace]
  refine ⟨37865681270840413133566879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50487575027787217511422505 37865681270840413133566879)
  ·
    refine ⟨56798521906260619700350319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37865681270840413133566879 56798521906260619700350319)
    ·
      refine ⟨85197782859390929550525479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56798521906260619700350319 85197782859390929550525479)
      ·
        refine ⟨127796674289086394325788219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85197782859390929550525479 127796674289086394325788219)
        ·
          refine ⟨191695011433629591488682329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127796674289086394325788219 191695011433629591488682329)
          ·
            refine ⟨143771258575222193616511747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191695011433629591488682329 143771258575222193616511747)
            ·
              refine ⟨215656887862833290424767621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143771258575222193616511747 215656887862833290424767621)
              ·
                refine ⟨40435666474281241954643929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215656887862833290424767621 40435666474281241954643929)
                ·
                  refine ⟨30326749855710931465982947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40435666474281241954643929 30326749855710931465982947)
                  ·
                    refine ⟨45490124783566397198974421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30326749855710931465982947 45490124783566397198974421)
                    ·
                      refine ⟨1066174799614837434350963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45490124783566397198974421 1066174799614837434350963)
                      ·
                        rfl

theorem cell23_2076368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_2076368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076368 prefixEnd_2076368 := by exact prefixLift 2076368
  have htrace : WordTrace (prefixWord ++ tailWord_2076368) baseStart_2076368 baseEnd_2076368 := by
    simpa [prefixWord, tailWord_2076368, baseEnd_2076368] using wordTrace_append hprefix tailTrace_2076368
  have hstable : (prefixWord ++ tailWord_2076368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076368).length < 2 ^ (prefixWord ++ tailWord_2076368).sum := by decide
  have hdescent : baseEnd_2076368 < baseStart_2076368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076392 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 1, 5]
def baseStart_2076392 : Nat := 118140960795 + 2076392 * 2 ^ 59
def prefixEnd_2076392 : Nat := 4983230072969 + 3 ^ 40 * 2076392 * 2
def baseEnd_2076392 : Nat := 355395707716848446816951

theorem tailTrace_2076392 : CollatzResearch.WordTrace tailWord_2076392 prefixEnd_2076392 355395707716848446816951 := by
  unfold tailWord_2076392
  simp only [CollatzResearch.WordTrace]
  refine ⟨37866118946796939183003715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50488158595729252244004953 37866118946796939183003715)
  ·
    refine ⟨56799178420195408774505573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37866118946796939183003715 56799178420195408774505573)
    ·
      refine ⟨10649845953786639145219795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56799178420195408774505573 10649845953786639145219795)
      ·
        refine ⟨15974768930679958717829693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10649845953786639145219795 15974768930679958717829693)
        ·
          refine ⟨5990538349004984519186135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15974768930679958717829693 5990538349004984519186135)
          ·
            refine ⟨8985807523507476778779203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990538349004984519186135 8985807523507476778779203)
            ·
              refine ⟨13478711285261215168168805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985807523507476778779203 13478711285261215168168805)
              ·
                refine ⟨2527258365986477844031651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13478711285261215168168805 2527258365986477844031651)
                ·
                  refine ⟨3790887548979716766047477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527258365986477844031651 3790887548979716766047477)
                  ·
                    refine ⟨355395707716848446816951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3790887548979716766047477 355395707716848446816951)
                    ·
                      rfl

theorem cell23_2076392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_2076392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076392 prefixEnd_2076392 := by exact prefixLift 2076392
  have htrace : WordTrace (prefixWord ++ tailWord_2076392) baseStart_2076392 baseEnd_2076392 := by
    simpa [prefixWord, tailWord_2076392, baseEnd_2076392] using wordTrace_append hprefix tailTrace_2076392
  have hstable : (prefixWord ++ tailWord_2076392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076392).length < 2 ^ (prefixWord ++ tailWord_2076392).sum := by decide
  have hdescent : baseEnd_2076392 < baseStart_2076392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076395 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 4]
def baseStart_2076395 : Nat := 118140960795 + 2076395 * 2 ^ 59
def prefixEnd_2076395 : Nat := 4983230072969 + 3 ^ 40 * 2076395 * 2
def baseEnd_2076395 : Nat := 1066188663592508828713339

theorem tailTrace_2076395 : CollatzResearch.WordTrace tailWord_2076395 prefixEnd_2076395 1066188663592508828713339 := by
  unfold tailWord_2076395
  simp only [CollatzResearch.WordTrace]
  refine ⟨75732347312583009878366639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50488231541722006585577759 75732347312583009878366639)
  ·
    refine ⟨113598520968874514817549959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75732347312583009878366639 113598520968874514817549959)
    ·
      refine ⟨170397781453311772226324939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113598520968874514817549959 170397781453311772226324939)
      ·
        refine ⟨255596672179967658339487409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170397781453311772226324939 255596672179967658339487409)
        ·
          refine ⟨191697504134975743754615557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255596672179967658339487409 191697504134975743754615557)
          ·
            refine ⟨35943282025307951953990417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191697504134975743754615557 35943282025307951953990417)
            ·
              refine ⟨26957461518980963965492813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35943282025307951953990417 26957461518980963965492813)
              ·
                refine ⟨10109048069617861487059805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26957461518980963965492813 10109048069617861487059805)
                ·
                  refine ⟨3790893026106698057647427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10109048069617861487059805 3790893026106698057647427)
                  ·
                    refine ⟨5686339539160047086471141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3790893026106698057647427 5686339539160047086471141)
                    ·
                      refine ⟨1066188663592508828713339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5686339539160047086471141 1066188663592508828713339)
                      ·
                        rfl

theorem cell23_2076395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 4].length) (baseStart_2076395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076395 prefixEnd_2076395 := by exact prefixLift 2076395
  have htrace : WordTrace (prefixWord ++ tailWord_2076395) baseStart_2076395 baseEnd_2076395 := by
    simpa [prefixWord, tailWord_2076395, baseEnd_2076395] using wordTrace_append hprefix tailTrace_2076395
  have hstable : (prefixWord ++ tailWord_2076395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076395).length < 2 ^ (prefixWord ++ tailWord_2076395).sum := by decide
  have hdescent : baseEnd_2076395 < baseStart_2076395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076412 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_2076412 : Nat := 118140960795 + 2076412 * 2 ^ 59
def prefixEnd_2076412 : Nat := 4983230072969 + 3 ^ 40 * 2076412 * 2
def baseEnd_2076412 : Nat := 1066197392763635262200761

theorem tailTrace_2076412 : CollatzResearch.WordTrace tailWord_2076412 prefixEnd_2076412 1066197392763635262200761 := by
  unfold tailWord_2076412
  simp only [CollatzResearch.WordTrace]
  refine ⟨37866483676760710890867745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50488644902347614521156993 37866483676760710890867745)
  ·
    refine ⟨28399862757570533168150809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37866483676760710890867745 28399862757570533168150809)
    ·
      refine ⟨21299897068177899876113107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28399862757570533168150809 21299897068177899876113107)
      ·
        refine ⟨31949845602266849814169661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21299897068177899876113107 31949845602266849814169661)
        ·
          refine ⟨11981192100850068680313623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31949845602266849814169661 11981192100850068680313623)
          ·
            refine ⟨17971788151275103020470435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11981192100850068680313623 17971788151275103020470435)
            ·
              refine ⟨26957682226912654530705653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17971788151275103020470435 26957682226912654530705653)
              ·
                refine ⟨2527282708773061362253655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26957682226912654530705653 2527282708773061362253655)
                ·
                  refine ⟨3790924063159592043380483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527282708773061362253655 3790924063159592043380483)
                  ·
                    refine ⟨5686386094739388065070725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3790924063159592043380483 5686386094739388065070725)
                    ·
                      refine ⟨1066197392763635262200761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5686386094739388065070725 1066197392763635262200761)
                      ·
                        rfl

theorem cell23_2076412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_2076412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076412 prefixEnd_2076412 := by exact prefixLift 2076412
  have htrace : WordTrace (prefixWord ++ tailWord_2076412) baseStart_2076412 baseEnd_2076412 := by
    simpa [prefixWord, tailWord_2076412, baseEnd_2076412] using wordTrace_append hprefix tailTrace_2076412
  have hstable : (prefixWord ++ tailWord_2076412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076412).length < 2 ^ (prefixWord ++ tailWord_2076412).sum := by decide
  have hdescent : baseEnd_2076412 < baseStart_2076412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076415 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_2076415 : Nat := 118140960795 + 2076415 * 2 ^ 59
def prefixEnd_2076415 : Nat := 4983230072969 + 3 ^ 40 * 2076415 * 2
def baseEnd_2076415 : Nat := 1066198933205598750463247

theorem tailTrace_2076415 : CollatzResearch.WordTrace tailWord_2076415 prefixEnd_2076415 1066198933205598750463247 := by
  unfold tailWord_2076415
  simp only [CollatzResearch.WordTrace]
  refine ⟨75733076772510553294094699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50488717848340368862729799 75733076772510553294094699)
  ·
    refine ⟨113599615158765829941142049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75733076772510553294094699 113599615158765829941142049)
    ·
      refine ⟨85199711369074372455856537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113599615158765829941142049 85199711369074372455856537)
      ·
        refine ⟨63899783526805779341892403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85199711369074372455856537 63899783526805779341892403)
        ·
          refine ⟨95849675290208669012838605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63899783526805779341892403 95849675290208669012838605)
          ·
            refine ⟨35943628233828250879814477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95849675290208669012838605 35943628233828250879814477)
            ·
              refine ⟨13478860587685594079930429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35943628233828250879814477 13478860587685594079930429)
              ·
                refine ⟨5054572720382097779973911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13478860587685594079930429 5054572720382097779973911)
                ·
                  refine ⟨7581859080573146669960867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054572720382097779973911 7581859080573146669960867)
                  ·
                    refine ⟨11372788620859720004941301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7581859080573146669960867 11372788620859720004941301)
                    ·
                      refine ⟨1066198933205598750463247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11372788620859720004941301 1066198933205598750463247)
                      ·
                        rfl

theorem cell23_2076415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_2076415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076415 prefixEnd_2076415 := by exact prefixLift 2076415
  have htrace : WordTrace (prefixWord ++ tailWord_2076415) baseStart_2076415 baseEnd_2076415 := by
    simpa [prefixWord, tailWord_2076415, baseEnd_2076415] using wordTrace_append hprefix tailTrace_2076415
  have hstable : (prefixWord ++ tailWord_2076415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076415).length < 2 ^ (prefixWord ++ tailWord_2076415).sum := by decide
  have hdescent : baseEnd_2076415 < baseStart_2076415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076423 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_2076423 : Nat := 118140960795 + 2076423 * 2 ^ 59
def prefixEnd_2076423 : Nat := 4983230072969 + 3 ^ 40 * 2076423 * 2
def baseEnd_2076423 : Nat := 1066203041050834719163211

theorem tailTrace_2076423 : CollatzResearch.WordTrace tailWord_2076423 prefixEnd_2076423 1066203041050834719163211 := by
  unfold tailWord_2076423
  simp only [CollatzResearch.WordTrace]
  refine ⟨75733368556481570660385923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50488912370987713773590615 75733368556481570660385923)
  ·
    refine ⟨113600052834722355990578885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75733368556481570660385923 113600052834722355990578885)
    ·
      refine ⟨21300009906510441748233541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113600052834722355990578885 21300009906510441748233541)
      ·
        refine ⟨3993751857470707827793789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21300009906510441748233541 3993751857470707827793789)
        ·
          refine ⟨1497656946551515435422671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3993751857470707827793789 1497656946551515435422671)
          ·
            refine ⟨2246485419827273153134007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497656946551515435422671 2246485419827273153134007)
            ·
              refine ⟨3369728129740909729701011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246485419827273153134007 3369728129740909729701011)
              ·
                refine ⟨5054592194611364594551517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369728129740909729701011 5054592194611364594551517)
                ·
                  refine ⟨1895472072979261722956819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5054592194611364594551517 1895472072979261722956819)
                  ·
                    refine ⟨2843208109468892584435229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1895472072979261722956819 2843208109468892584435229)
                    ·
                      refine ⟨1066203041050834719163211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2843208109468892584435229 1066203041050834719163211)
                      ·
                        rfl

theorem cell23_2076423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_2076423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076423 prefixEnd_2076423 := by exact prefixLift 2076423
  have htrace : WordTrace (prefixWord ++ tailWord_2076423) baseStart_2076423 baseEnd_2076423 := by
    simpa [prefixWord, tailWord_2076423, baseEnd_2076423] using wordTrace_append hprefix tailTrace_2076423
  have hstable : (prefixWord ++ tailWord_2076423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076423).length < 2 ^ (prefixWord ++ tailWord_2076423).sum := by decide
  have hdescent : baseEnd_2076423 < baseStart_2076423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076439 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 2, 4]
def baseStart_2076439 : Nat := 118140960795 + 2076439 * 2 ^ 59
def prefixEnd_2076439 : Nat := 4983230072969 + 3 ^ 40 * 2076439 * 2
def baseEnd_2076439 : Nat := 355403752247102218854379

theorem tailTrace_2076439 : CollatzResearch.WordTrace tailWord_2076439 prefixEnd_2076439 355403752247102218854379 := by
  unfold tailWord_2076439
  simp only [CollatzResearch.WordTrace]
  refine ⟨75733952124423605392968371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50489301416282403595312247 75733952124423605392968371)
  ·
    refine ⟨113600928186635408089452557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75733952124423605392968371 113600928186635408089452557)
    ·
      refine ⟨42600348069988278033544709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113600928186635408089452557 42600348069988278033544709)
      ·
        refine ⟨7987565263122802131289633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42600348069988278033544709 7987565263122802131289633)
        ·
          refine ⟨5990673947342101598467225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7987565263122802131289633 5990673947342101598467225)
          ·
            refine ⟨4493005460506576198850419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5990673947342101598467225 4493005460506576198850419)
            ·
              refine ⟨6739508190759864298275629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4493005460506576198850419 6739508190759864298275629)
              ·
                refine ⟨2527315571534949111853361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6739508190759864298275629 2527315571534949111853361)
                ·
                  refine ⟨1895486678651211833890021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2527315571534949111853361 1895486678651211833890021)
                  ·
                    refine ⟨355403752247102218854379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1895486678651211833890021 355403752247102218854379)
                    ·
                      rfl

theorem cell23_2076439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_2076439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076439 prefixEnd_2076439 := by exact prefixLift 2076439
  have htrace : WordTrace (prefixWord ++ tailWord_2076439) baseStart_2076439 baseEnd_2076439 := by
    simpa [prefixWord, tailWord_2076439, baseEnd_2076439] using wordTrace_append hprefix tailTrace_2076439
  have hstable : (prefixWord ++ tailWord_2076439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076439).length < 2 ^ (prefixWord ++ tailWord_2076439).sum := by decide
  have hdescent : baseEnd_2076439 < baseStart_2076439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076449 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_2076449 : Nat := 118140960795 + 2076449 * 2 ^ 59
def prefixEnd_2076449 : Nat := 4983230072969 + 3 ^ 40 * 2076449 * 2
def baseEnd_2076449 : Nat := 1066216391547851617438091

theorem tailTrace_2076449 : CollatzResearch.WordTrace tailWord_2076449 prefixEnd_2076449 1066216391547851617438091 := by
  unfold tailWord_2076449
  simp only [CollatzResearch.WordTrace]
  refine ⟨75734316854387377100832401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50489544569591584733888267 75734316854387377100832401)
  ·
    refine ⟨56800737640790532825624301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75734316854387377100832401 56800737640790532825624301)
    ·
      refine ⟨21300276615296449809609113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56800737640790532825624301 21300276615296449809609113)
      ·
        refine ⟨15975207461472337357206835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21300276615296449809609113 15975207461472337357206835)
        ·
          refine ⟨23962811192208506035810253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15975207461472337357206835 23962811192208506035810253)
          ·
            refine ⟨8986054197078189763428845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23962811192208506035810253 8986054197078189763428845)
            ·
              refine ⟨3369770323904321161285817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8986054197078189763428845 3369770323904321161285817)
              ·
                refine ⟨2527327742928240870964363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3369770323904321161285817 2527327742928240870964363)
                ·
                  refine ⟨3790991614392361306446545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527327742928240870964363 3790991614392361306446545)
                  ·
                    refine ⟨2843243710794270979834909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3790991614392361306446545 2843243710794270979834909)
                    ·
                      refine ⟨1066216391547851617438091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2843243710794270979834909 1066216391547851617438091)
                      ·
                        rfl

theorem cell23_2076449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_2076449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076449 prefixEnd_2076449 := by exact prefixLift 2076449
  have htrace : WordTrace (prefixWord ++ tailWord_2076449) baseStart_2076449 baseEnd_2076449 := by
    simpa [prefixWord, tailWord_2076449, baseEnd_2076449] using wordTrace_append hprefix tailTrace_2076449
  have hstable : (prefixWord ++ tailWord_2076449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076449).length < 2 ^ (prefixWord ++ tailWord_2076449).sum := by decide
  have hdescent : baseEnd_2076449 < baseStart_2076449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076466 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_2076466 : Nat := 118140960795 + 2076466 * 2 ^ 59
def prefixEnd_2076466 : Nat := 4983230072969 + 3 ^ 40 * 2076466 * 2
def baseEnd_2076466 : Nat := 1066225120718978050925513

theorem tailTrace_2076466 : CollatzResearch.WordTrace tailWord_2076466 prefixEnd_2076466 1066225120718978050925513 := by
  unfold tailWord_2076466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18933734223831447251050313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50489957930217192669467501 18933734223831447251050313)
  ·
    refine ⟨14200300667873585438287735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18933734223831447251050313 14200300667873585438287735)
    ·
      refine ⟨21300451001810378157431603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14200300667873585438287735 21300451001810378157431603)
      ·
        refine ⟨31950676502715567236147405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21300451001810378157431603 31950676502715567236147405)
        ·
          refine ⟨11981503688518337713555277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31950676502715567236147405 11981503688518337713555277)
          ·
            refine ⟨4493063883194376642583229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11981503688518337713555277 4493063883194376642583229)
            ·
              refine ⟨1684898956197891240968711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4493063883194376642583229 1684898956197891240968711)
              ·
                refine ⟨2527348434296836861453067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684898956197891240968711 2527348434296836861453067)
                ·
                  refine ⟨3791022651445255292179601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2527348434296836861453067 3791022651445255292179601)
                  ·
                    refine ⟨2843266988583941469134701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3791022651445255292179601 2843266988583941469134701)
                    ·
                      refine ⟨1066225120718978050925513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2843266988583941469134701 1066225120718978050925513)
                      ·
                        rfl

theorem cell23_2076466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_2076466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076466 prefixEnd_2076466 := by exact prefixLift 2076466
  have htrace : WordTrace (prefixWord ++ tailWord_2076466) baseStart_2076466 baseEnd_2076466 := by
    simpa [prefixWord, tailWord_2076466, baseEnd_2076466] using wordTrace_append hprefix tailTrace_2076466
  have hstable : (prefixWord ++ tailWord_2076466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076466).length < 2 ^ (prefixWord ++ tailWord_2076466).sum := by decide
  have hdescent : baseEnd_2076466 < baseStart_2076466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076485 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_2076485 : Nat := 118140960795 + 2076485 * 2 ^ 59
def prefixEnd_2076485 : Nat := 4983230072969 + 3 ^ 40 * 2076485 * 2
def baseEnd_2076485 : Nat := 1066234876851413476587925

theorem tailTrace_2076485 : CollatzResearch.WordTrace tailWord_2076485 prefixEnd_2076485 1066234876851413476587925 := by
  unfold tailWord_2076485
  simp only [CollatzResearch.WordTrace]
  refine ⟨75735629882256955249142909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50490419921504636832761939 75735629882256955249142909)
  ·
    refine ⟨28400861205846358218428591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75735629882256955249142909 28400861205846358218428591)
    ·
      refine ⟨42601291808769537327642887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28400861205846358218428591 42601291808769537327642887)
      ·
        refine ⟨63901937713154305991464331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42601291808769537327642887 63901937713154305991464331)
        ·
          refine ⟨95852906569731458987196497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63901937713154305991464331 95852906569731458987196497)
          ·
            refine ⟨71889679927298594240397373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95852906569731458987196497 71889679927298594240397373)
            ·
              refine ⟨26958629972736972840149015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71889679927298594240397373 26958629972736972840149015)
              ·
                refine ⟨40437944959105459260223523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26958629972736972840149015 40437944959105459260223523)
                ·
                  refine ⟨60656917438658188890335285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40437944959105459260223523 60656917438658188890335285)
                  ·
                    refine ⟨5686586009874205208468933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60656917438658188890335285 5686586009874205208468933)
                    ·
                      refine ⟨1066234876851413476587925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5686586009874205208468933 1066234876851413476587925)
                      ·
                        rfl

theorem cell23_2076485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_2076485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076485 prefixEnd_2076485 := by exact prefixLift 2076485
  have htrace : WordTrace (prefixWord ++ tailWord_2076485) baseStart_2076485 baseEnd_2076485 := by
    simpa [prefixWord, tailWord_2076485, baseEnd_2076485] using wordTrace_append hprefix tailTrace_2076485
  have hstable : (prefixWord ++ tailWord_2076485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076485).length < 2 ^ (prefixWord ++ tailWord_2076485).sum := by decide
  have hdescent : baseEnd_2076485 < baseStart_2076485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076486 : List Nat := [6, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2076486 : Nat := 118140960795 + 2076486 * 2 ^ 59
def prefixEnd_2076486 : Nat := 4983230072969 + 3 ^ 40 * 2076486 * 2
def baseEnd_2076486 : Nat := 39490199641928443432423

theorem tailTrace_2076486 : CollatzResearch.WordTrace tailWord_2076486 prefixEnd_2076486 39490199641928443432423 := by
  unfold tailWord_2076486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366739573601666638122791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50490444236835554946619541 2366739573601666638122791)
  ·
    refine ⟨3550109360402499957184187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366739573601666638122791 3550109360402499957184187)
    ·
      refine ⟨5325164040603749935776281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3550109360402499957184187 5325164040603749935776281)
      ·
        refine ⟨3993873030452812451832211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5325164040603749935776281 3993873030452812451832211)
        ·
          refine ⟨5990809545679218677748317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993873030452812451832211 5990809545679218677748317)
          ·
            refine ⟨2246553579629707004155619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5990809545679218677748317 2246553579629707004155619)
            ·
              refine ⟨3369830369444560506233429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246553579629707004155619 3369830369444560506233429)
              ·
                refine ⟨39490199641928443432423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3369830369444560506233429 39490199641928443432423)
                ·
                  rfl

theorem cell23_2076486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2076486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076486 prefixEnd_2076486 := by exact prefixLift 2076486
  have htrace : WordTrace (prefixWord ++ tailWord_2076486) baseStart_2076486 baseEnd_2076486 := by
    simpa [prefixWord, tailWord_2076486, baseEnd_2076486] using wordTrace_append hprefix tailTrace_2076486
  have hstable : (prefixWord ++ tailWord_2076486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076486).length < 2 ^ (prefixWord ++ tailWord_2076486).sum := by decide
  have hdescent : baseEnd_2076486 < baseStart_2076486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2076519 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_2076519 : Nat := 118140960795 + 2076519 * 2 ^ 59
def prefixEnd_2076519 : Nat := 4983230072969 + 3 ^ 40 * 2076519 * 2
def baseEnd_2076519 : Nat := 1066252335193666343562769

theorem tailTrace_2076519 : CollatzResearch.WordTrace tailWord_2076519 prefixEnd_2076519 1066252335193666343562769 := by
  unfold tailWord_2076519
  simp only [CollatzResearch.WordTrace]
  refine ⟨75736869964133779055880611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50491246642755852703920407 75736869964133779055880611)
  ·
    refine ⟨113605304946200668583820917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75736869964133779055880611 113605304946200668583820917)
    ·
      refine ⟨10650497338706312679733211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113605304946200668583820917 10650497338706312679733211)
      ·
        refine ⟨15975746008059469019599817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10650497338706312679733211 15975746008059469019599817)
        ·
          refine ⟨11981809506044601764699863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15975746008059469019599817 11981809506044601764699863)
          ·
            refine ⟨17972714259066902647049795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11981809506044601764699863 17972714259066902647049795)
            ·
              refine ⟨26959071388600353970574693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17972714259066902647049795 26959071388600353970574693)
              ·
                refine ⟨5054825885362566369482755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26959071388600353970574693 5054825885362566369482755)
                ·
                  refine ⟨7582238828043849554224133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5054825885362566369482755 7582238828043849554224133)
                  ·
                    refine ⟨1421669780258221791417025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7582238828043849554224133 1421669780258221791417025)
                    ·
                      refine ⟨1066252335193666343562769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1421669780258221791417025 1066252335193666343562769)
                      ·
                        rfl

theorem cell23_2076519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_2076519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2076519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2076519 prefixEnd_2076519 := by exact prefixLift 2076519
  have htrace : WordTrace (prefixWord ++ tailWord_2076519) baseStart_2076519 baseEnd_2076519 := by
    simpa [prefixWord, tailWord_2076519, baseEnd_2076519] using wordTrace_append hprefix tailTrace_2076519
  have hstable : (prefixWord ++ tailWord_2076519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2076519).length < 2 ^ (prefixWord ++ tailWord_2076519).sum := by decide
  have hdescent : baseEnd_2076519 < baseStart_2076519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2076519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
