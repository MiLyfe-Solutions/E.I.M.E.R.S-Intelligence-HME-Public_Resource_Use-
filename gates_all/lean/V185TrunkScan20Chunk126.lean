import V185TrunkScan20Chunk125

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_766269 : List Nat := [1, 4, 1, 14]
def baseStart_766269 : Nat := 118140960795 + 766269 * 2 ^ 59
def prefixEnd_766269 : Nat := 4983230072969 + 3 ^ 40 * 766269 * 2
def baseEnd_766269 : Nat := 1439284161463805039647

theorem tailTrace_766269 : CollatzResearch.WordTrace tailWord_766269 prefixEnd_766269 1439284161463805039647 := by
  unfold tailWord_766269
  simp only [CollatzResearch.WordTrace]
  refine ⟨27948126460945756171349861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18632084307297170780899907 27948126460945756171349861)
  ·
    refine ⟨5240273711427329282128099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27948126460945756171349861 5240273711427329282128099)
    ·
      refine ⟨7860410567140993923192149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240273711427329282128099 7860410567140993923192149)
      ·
        refine ⟨1439284161463805039647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 7860410567140993923192149 1439284161463805039647)
        ·
          rfl

theorem cell20_766269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 14].length) (baseStart_766269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766269 prefixEnd_766269 := by exact prefixLift 766269
  have htrace : WordTrace (prefixWord ++ tailWord_766269) baseStart_766269 baseEnd_766269 := by
    simpa [prefixWord, tailWord_766269, baseEnd_766269] using wordTrace_append hprefix tailTrace_766269
  have hstable : (prefixWord ++ tailWord_766269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766269).length < 2 ^ (prefixWord ++ tailWord_766269).sum := by decide
  have hdescent : baseEnd_766269 < baseStart_766269 := by decide
  rcases family_descends (prefixWord ++ tailWord_766269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766331 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_766331 : Nat := 118140960795 + 766331 * 2 ^ 59
def prefixEnd_766331 : Nat := 4983230072969 + 3 ^ 40 * 766331 * 2
def baseEnd_766331 : Nat := 349774349725107964567301

theorem tailTrace_766331 : CollatzResearch.WordTrace tailWord_766331 prefixEnd_766331 349774349725107964567301 := by
  unfold tailWord_766331
  simp only [CollatzResearch.WordTrace]
  refine ⟨27950387786721140760106847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18633591857814093840071231 27950387786721140760106847)
  ·
    refine ⟨41925581680081711140160271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27950387786721140760106847 41925581680081711140160271)
    ·
      refine ⟨62888372520122566710240407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41925581680081711140160271 62888372520122566710240407)
      ·
        refine ⟨94332558780183850065360611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62888372520122566710240407 94332558780183850065360611)
        ·
          refine ⟨141498838170275775098040917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94332558780183850065360611 141498838170275775098040917)
          ·
            refine ⟨1658189509807919239430167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 141498838170275775098040917 1658189509807919239430167)
            ·
              refine ⟨2487284264711878859145251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658189509807919239430167 2487284264711878859145251)
              ·
                refine ⟨3730926397067818288717877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487284264711878859145251 3730926397067818288717877)
                ·
                  refine ⟨349774349725107964567301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3730926397067818288717877 349774349725107964567301)
                  ·
                    rfl

theorem cell20_766331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_766331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766331 prefixEnd_766331 := by exact prefixLift 766331
  have htrace : WordTrace (prefixWord ++ tailWord_766331) baseStart_766331 baseEnd_766331 := by
    simpa [prefixWord, tailWord_766331, baseEnd_766331] using wordTrace_append hprefix tailTrace_766331
  have hstable : (prefixWord ++ tailWord_766331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766331).length < 2 ^ (prefixWord ++ tailWord_766331).sum := by decide
  have hdescent : baseEnd_766331 < baseStart_766331 := by decide
  rcases family_descends (prefixWord ++ tailWord_766331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766362 : List Nat := [3, 1, 1, 4, 1, 3, 1, 6]
def baseStart_766362 : Nat := 118140960795 + 766362 * 2 ^ 59
def prefixEnd_766362 : Nat := 4983230072969 + 3 ^ 40 * 766362 * 2
def baseEnd_766362 : Nat := 116596166323269878177947

theorem tailTrace_766362 : CollatzResearch.WordTrace tailWord_766362 prefixEnd_766362 116596166323269878177947 := by
  unfold tailWord_766362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987879612402208263621335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18634345633072555369656893 6987879612402208263621335)
  ·
    refine ⟨10481819418603312395432003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6987879612402208263621335 10481819418603312395432003)
    ·
      refine ⟨15722729127904968593148005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10481819418603312395432003 15722729127904968593148005)
      ·
        refine ⟨2948011711482181611215251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15722729127904968593148005 2948011711482181611215251)
        ·
          refine ⟨4422017567223272416822877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948011711482181611215251 4422017567223272416822877)
          ·
            refine ⟨1658256587708727156308579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4422017567223272416822877 1658256587708727156308579)
            ·
              refine ⟨2487384881563090734462869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658256587708727156308579 2487384881563090734462869)
              ·
                refine ⟨116596166323269878177947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2487384881563090734462869 116596166323269878177947)
                ·
                  rfl

theorem cell20_766362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_766362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766362 prefixEnd_766362 := by exact prefixLift 766362
  have htrace : WordTrace (prefixWord ++ tailWord_766362) baseStart_766362 baseEnd_766362 := by
    simpa [prefixWord, tailWord_766362, baseEnd_766362] using wordTrace_append hprefix tailTrace_766362
  have hstable : (prefixWord ++ tailWord_766362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766362).length < 2 ^ (prefixWord ++ tailWord_766362).sum := by decide
  have hdescent : baseEnd_766362 < baseStart_766362 := by decide
  rcases family_descends (prefixWord ++ tailWord_766362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766372 : List Nat := [2, 3, 1, 2, 1, 1, 5, 3, 2]
def baseStart_766372 : Nat := 118140960795 + 766372 * 2 ^ 59
def prefixEnd_766372 : Nat := 4983230072969 + 3 ^ 40 * 766372 * 2
def baseEnd_766372 : Nat := 349793063242294044200467

theorem tailTrace_766372 : CollatzResearch.WordTrace tailWord_766372 prefixEnd_766372 349793063242294044200467 := by
  unfold tailWord_766372
  simp only [CollatzResearch.WordTrace]
  refine ⟨13975941589786302381174685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18634588786381736508232913 13975941589786302381174685)
  ·
    refine ⟨5240978096169863392940507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13975941589786302381174685 5240978096169863392940507)
    ·
      refine ⟨7861467144254795089410761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240978096169863392940507 7861467144254795089410761)
      ·
        refine ⟨5896100358191096317058071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7861467144254795089410761 5896100358191096317058071)
        ·
          refine ⟨8844150537286644475587107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5896100358191096317058071 8844150537286644475587107)
          ·
            refine ⟨13266225805929966713380661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844150537286644475587107 13266225805929966713380661)
            ·
              refine ⟨1243708669305934379379437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13266225805929966713380661 1243708669305934379379437)
              ·
                refine ⟨466390750989725392267289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1243708669305934379379437 466390750989725392267289)
                ·
                  refine ⟨349793063242294044200467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466390750989725392267289 349793063242294044200467)
                  ·
                    rfl

theorem cell20_766372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_766372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766372 prefixEnd_766372 := by exact prefixLift 766372
  have htrace : WordTrace (prefixWord ++ tailWord_766372) baseStart_766372 baseEnd_766372 := by
    simpa [prefixWord, tailWord_766372, baseEnd_766372] using wordTrace_append hprefix tailTrace_766372
  have hstable : (prefixWord ++ tailWord_766372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766372).length < 2 ^ (prefixWord ++ tailWord_766372).sum := by decide
  have hdescent : baseEnd_766372 < baseStart_766372 := by decide
  rcases family_descends (prefixWord ++ tailWord_766372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766389 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 4]
def baseStart_766389 : Nat := 118140960795 + 766389 * 2 ^ 59
def prefixEnd_766389 : Nat := 4983230072969 + 3 ^ 40 * 766389 * 2
def baseEnd_766389 : Nat := 349800822505517540633731

theorem tailTrace_766389 : CollatzResearch.WordTrace tailWord_766389 prefixEnd_766389 349800822505517540633731 := by
  unfold tailWord_766389
  simp only [CollatzResearch.WordTrace]
  refine ⟨27952503220511016665718221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18635002147007344443812147 27952503220511016665718221)
  ·
    refine ⟨10482188707691631249644333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27952503220511016665718221 10482188707691631249644333)
    ·
      refine ⟨3930820765384361718616625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10482188707691631249644333 3930820765384361718616625)
      ·
        refine ⟨2948115574038271288962469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3930820765384361718616625 2948115574038271288962469)
        ·
          refine ⟨552771670132175866680463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2948115574038271288962469 552771670132175866680463)
          ·
            refine ⟨829157505198263800020695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552771670132175866680463 829157505198263800020695)
            ·
              refine ⟨1243736257797395700031043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829157505198263800020695 1243736257797395700031043)
              ·
                refine ⟨1865604386696093550046565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243736257797395700031043 1865604386696093550046565)
                ·
                  refine ⟨349800822505517540633731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865604386696093550046565 349800822505517540633731)
                  ·
                    rfl

theorem cell20_766389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_766389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766389 prefixEnd_766389 := by exact prefixLift 766389
  have htrace : WordTrace (prefixWord ++ tailWord_766389) baseStart_766389 baseEnd_766389 := by
    simpa [prefixWord, tailWord_766389, baseEnd_766389] using wordTrace_append hprefix tailTrace_766389
  have hstable : (prefixWord ++ tailWord_766389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766389).length < 2 ^ (prefixWord ++ tailWord_766389).sum := by decide
  have hdescent : baseEnd_766389 < baseStart_766389 := by decide
  rcases family_descends (prefixWord ++ tailWord_766389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766393 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_766393 : Nat := 118140960795 + 766393 * 2 ^ 59
def prefixEnd_766393 : Nat := 4983230072969 + 3 ^ 40 * 766393 * 2
def baseEnd_766393 : Nat := 349802648214511304500381

theorem tailTrace_766393 : CollatzResearch.WordTrace tailWord_766393 prefixEnd_766393 349802648214511304500381 := by
  unfold tailWord_766393
  simp only [CollatzResearch.WordTrace]
  refine ⟨27952649112496525348863833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18635099408331016899242555 27952649112496525348863833)
  ·
    refine ⟨20964486834372394011647875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27952649112496525348863833 20964486834372394011647875)
    ·
      refine ⟨31446730251558591017471813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20964486834372394011647875 31446730251558591017471813)
      ·
        refine ⟨5896261922167235815775965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31446730251558591017471813 5896261922167235815775965)
        ·
          refine ⟨2211098220812713430915987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5896261922167235815775965 2211098220812713430915987)
          ·
            refine ⟨3316647331219070146373981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211098220812713430915987 3316647331219070146373981)
            ·
              refine ⟨1243742749207151304890243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3316647331219070146373981 1243742749207151304890243)
              ·
                refine ⟨1865614123810726957335365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243742749207151304890243 1865614123810726957335365)
                ·
                  refine ⟨349802648214511304500381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865614123810726957335365 349802648214511304500381)
                  ·
                    rfl

theorem cell20_766393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_766393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766393 prefixEnd_766393 := by exact prefixLift 766393
  have htrace : WordTrace (prefixWord ++ tailWord_766393) baseStart_766393 baseEnd_766393 := by
    simpa [prefixWord, tailWord_766393, baseEnd_766393] using wordTrace_append hprefix tailTrace_766393
  have hstable : (prefixWord ++ tailWord_766393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766393).length < 2 ^ (prefixWord ++ tailWord_766393).sum := by decide
  have hdescent : baseEnd_766393 < baseStart_766393 := by decide
  rcases family_descends (prefixWord ++ tailWord_766393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766414 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_766414 : Nat := 118140960795 + 766414 * 2 ^ 59
def prefixEnd_766414 : Nat := 4983230072969 + 3 ^ 40 * 766414 * 2
def baseEnd_766414 : Nat := 349812233186728564800295

theorem tailTrace_766414 : CollatzResearch.WordTrace tailWord_766414 prefixEnd_766414 349812233186728564800295 := by
  unfold tailWord_766414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494176880677555741922287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18635610030280297290252197 3494176880677555741922287)
  ·
    refine ⟨5241265321016333612883431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3494176880677555741922287 5241265321016333612883431)
    ·
      refine ⟨7861897981524500419325147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241265321016333612883431 7861897981524500419325147)
      ·
        refine ⟨11792846972286750628987721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7861897981524500419325147 11792846972286750628987721)
        ·
          refine ⟨8844635229215062971740791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11792846972286750628987721 8844635229215062971740791)
          ·
            refine ⟨13266952843822594457611187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844635229215062971740791 13266952843822594457611187)
            ·
              refine ⟨19900429265733891686416781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13266952843822594457611187 19900429265733891686416781)
              ·
                refine ⟨7462660974650209382406293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19900429265733891686416781 7462660974650209382406293)
                ·
                  refine ⟨349812233186728564800295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7462660974650209382406293 349812233186728564800295)
                  ·
                    rfl

theorem cell20_766414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_766414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766414 prefixEnd_766414 := by exact prefixLift 766414
  have htrace : WordTrace (prefixWord ++ tailWord_766414) baseStart_766414 baseEnd_766414 := by
    simpa [prefixWord, tailWord_766414, baseEnd_766414] using wordTrace_append hprefix tailTrace_766414
  have hstable : (prefixWord ++ tailWord_766414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766414).length < 2 ^ (prefixWord ++ tailWord_766414).sum := by decide
  have hdescent : baseEnd_766414 < baseStart_766414 := by decide
  rcases family_descends (prefixWord ++ tailWord_766414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766434 : List Nat := [3, 3, 3, 2, 2, 7]
def baseStart_766434 : Nat := 118140960795 + 766434 * 2 ^ 59
def prefixEnd_766434 : Nat := 4983230072969 + 3 ^ 40 * 766434 * 2
def baseEnd_766434 : Nat := 12956346730803606819761

theorem tailTrace_766434 : CollatzResearch.WordTrace tailWord_766434 prefixEnd_766434 12956346730803606819761 := by
  unfold tailWord_766434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6988536126336997337776589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18636096336898659567404237 6988536126336997337776589)
  ·
    refine ⟨2620701047376374001666221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6988536126336997337776589 2620701047376374001666221)
    ·
      refine ⟨982762892766140250624833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2620701047376374001666221 982762892766140250624833)
      ·
        refine ⟨737072169574605187968625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 982762892766140250624833 737072169574605187968625)
        ·
          refine ⟨552804127180953890976469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737072169574605187968625 552804127180953890976469)
          ·
            refine ⟨12956346730803606819761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 552804127180953890976469 12956346730803606819761)
            ·
              rfl

theorem cell20_766434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 7].length) (baseStart_766434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766434 prefixEnd_766434 := by exact prefixLift 766434
  have htrace : WordTrace (prefixWord ++ tailWord_766434) baseStart_766434 baseEnd_766434 := by
    simpa [prefixWord, tailWord_766434, baseEnd_766434] using wordTrace_append hprefix tailTrace_766434
  have hstable : (prefixWord ++ tailWord_766434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766434).length < 2 ^ (prefixWord ++ tailWord_766434).sum := by decide
  have hdescent : baseEnd_766434 < baseStart_766434 := by decide
  rcases family_descends (prefixWord ++ tailWord_766434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766496 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 3]
def baseStart_766496 : Nat := 118140960795 + 766496 * 2 ^ 59
def prefixEnd_766496 : Nat := 4983230072969 + 3 ^ 40 * 766496 * 2
def baseEnd_766496 : Nat := 349849660221100724066627

theorem tailTrace_766496 : CollatzResearch.WordTrace tailWord_766496 prefixEnd_766496 349849660221100724066627 := by
  unfold tailWord_766496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13978202915561686969931671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18637603887415582626575561 13978202915561686969931671)
  ·
    refine ⟨20967304373342530454897507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13978202915561686969931671 20967304373342530454897507)
    ·
      refine ⟨31450956560013795682346261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20967304373342530454897507 31450956560013795682346261)
      ·
        refine ⟨1474263588750646672609981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31450956560013795682346261 1474263588750646672609981)
        ·
          refine ⟨552848845781492502228743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1474263588750646672609981 552848845781492502228743)
          ·
            refine ⟨829273268672238753343115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552848845781492502228743 829273268672238753343115)
            ·
              refine ⟨1243909903008358130014673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829273268672238753343115 1243909903008358130014673)
              ·
                refine ⟨932932427256268597511005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243909903008358130014673 932932427256268597511005)
                ·
                  refine ⟨349849660221100724066627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932932427256268597511005 349849660221100724066627)
                  ·
                    rfl

theorem cell20_766496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_766496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766496 prefixEnd_766496 := by exact prefixLift 766496
  have htrace : WordTrace (prefixWord ++ tailWord_766496) baseStart_766496 baseEnd_766496 := by
    simpa [prefixWord, tailWord_766496, baseEnd_766496] using wordTrace_append hprefix tailTrace_766496
  have hstable : (prefixWord ++ tailWord_766496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766496).length < 2 ^ (prefixWord ++ tailWord_766496).sum := by decide
  have hdescent : baseEnd_766496 < baseStart_766496 := by decide
  rcases family_descends (prefixWord ++ tailWord_766496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766497 : List Nat := [1, 2, 3, 2, 2, 1, 9]
def baseStart_766497 : Nat := 118140960795 + 766497 * 2 ^ 59
def prefixEnd_766497 : Nat := 4983230072969 + 3 ^ 40 * 766497 * 2
def baseEnd_766497 : Nat := 38872235183149907225921

theorem tailTrace_766497 : CollatzResearch.WordTrace tailWord_766497 prefixEnd_766497 38872235183149907225921 := by
  unfold tailWord_766497
  simp only [CollatzResearch.WordTrace]
  refine ⟨27956442304119751110649745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18637628202746500740433163 27956442304119751110649745)
  ·
    refine ⟨20967331728089813332987309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27956442304119751110649745 20967331728089813332987309)
    ·
      refine ⟨7862749398033679999870241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20967331728089813332987309 7862749398033679999870241)
      ·
        refine ⟨5897062048525259999902681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7862749398033679999870241 5897062048525259999902681)
        ·
          refine ⟨4422796536393944999927011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5897062048525259999902681 4422796536393944999927011)
          ·
            refine ⟨6634194804590917499890517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422796536393944999927011 6634194804590917499890517)
            ·
              refine ⟨38872235183149907225921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6634194804590917499890517 38872235183149907225921)
              ·
                rfl

theorem cell20_766497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 9].length) (baseStart_766497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766497 prefixEnd_766497 := by exact prefixLift 766497
  have htrace : WordTrace (prefixWord ++ tailWord_766497) baseStart_766497 baseEnd_766497 := by
    simpa [prefixWord, tailWord_766497, baseEnd_766497] using wordTrace_append hprefix tailTrace_766497
  have hstable : (prefixWord ++ tailWord_766497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766497).length < 2 ^ (prefixWord ++ tailWord_766497).sum := by decide
  have hdescent : baseEnd_766497 < baseStart_766497 := by decide
  rcases family_descends (prefixWord ++ tailWord_766497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766503 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 4]
def baseStart_766503 : Nat := 118140960795 + 766503 * 2 ^ 59
def prefixEnd_766503 : Nat := 4983230072969 + 3 ^ 40 * 766503 * 2
def baseEnd_766503 : Nat := 349852855211839810833265

theorem tailTrace_766503 : CollatzResearch.WordTrace tailWord_766503 prefixEnd_766503 349852855211839810833265 := by
  unfold tailWord_766503
  simp only [CollatzResearch.WordTrace]
  refine ⟨27956661142098014135368163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18637774094732009423578775 27956661142098014135368163)
  ·
    refine ⟨41934991713147021203052245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27956661142098014135368163 41934991713147021203052245)
    ·
      refine ⟨982851368276883309446537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 41934991713147021203052245 982851368276883309446537)
      ·
        refine ⟨737138526207662482084903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 982851368276883309446537 737138526207662482084903)
        ·
          refine ⟨1105707789311493723127355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737138526207662482084903 1105707789311493723127355)
          ·
            refine ⟨1658561683967240584691033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105707789311493723127355 1658561683967240584691033)
            ·
              refine ⟨1243921262975430438518275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658561683967240584691033 1243921262975430438518275)
              ·
                refine ⟨1865881894463145657777413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243921262975430438518275 1865881894463145657777413)
                ·
                  refine ⟨349852855211839810833265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865881894463145657777413 349852855211839810833265)
                  ·
                    rfl

theorem cell20_766503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 4].length) (baseStart_766503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766503 prefixEnd_766503 := by exact prefixLift 766503
  have htrace : WordTrace (prefixWord ++ tailWord_766503) baseStart_766503 baseEnd_766503 := by
    simpa [prefixWord, tailWord_766503, baseEnd_766503] using wordTrace_append hprefix tailTrace_766503
  have hstable : (prefixWord ++ tailWord_766503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766503).length < 2 ^ (prefixWord ++ tailWord_766503).sum := by decide
  have hdescent : baseEnd_766503 < baseStart_766503 := by decide
  rcases family_descends (prefixWord ++ tailWord_766503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766528 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_766528 : Nat := 118140960795 + 766528 * 2 ^ 59
def prefixEnd_766528 : Nat := 4983230072969 + 3 ^ 40 * 766528 * 2
def baseEnd_766528 : Nat := 349864265893050834999829

theorem tailTrace_766528 : CollatzResearch.WordTrace tailWord_766528 prefixEnd_766528 349864265893050834999829 := by
  unfold tailWord_766528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13978786483503721702514119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18638381978004962270018825 13978786483503721702514119)
  ·
    refine ⟨20968179725255582553771179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13978786483503721702514119 20968179725255582553771179)
    ·
      refine ⟨31452269587883373830656769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20968179725255582553771179 31452269587883373830656769)
      ·
        refine ⟨23589202190912530372992577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31452269587883373830656769 23589202190912530372992577)
        ·
          refine ⟨17691901643184397779744433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23589202190912530372992577 17691901643184397779744433)
          ·
            refine ⟨13268926232388298334808325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17691901643184397779744433 13268926232388298334808325)
            ·
              refine ⟨2487923668572805937776561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13268926232388298334808325 2487923668572805937776561)
              ·
                refine ⟨1865942751429604453332421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487923668572805937776561 1865942751429604453332421)
                ·
                  refine ⟨349864265893050834999829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1865942751429604453332421 349864265893050834999829)
                  ·
                    rfl

theorem cell20_766528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_766528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766528 prefixEnd_766528 := by exact prefixLift 766528
  have htrace : WordTrace (prefixWord ++ tailWord_766528) baseStart_766528 baseEnd_766528 := by
    simpa [prefixWord, tailWord_766528, baseEnd_766528] using wordTrace_append hprefix tailTrace_766528
  have hstable : (prefixWord ++ tailWord_766528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766528).length < 2 ^ (prefixWord ++ tailWord_766528).sum := by decide
  have hdescent : baseEnd_766528 < baseStart_766528 := by decide
  rcases family_descends (prefixWord ++ tailWord_766528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766541 : List Nat := [1, 6, 1, 1, 2, 1, 3, 3, 2]
def baseStart_766541 : Nat := 118140960795 + 766541 * 2 ^ 59
def prefixEnd_766541 : Nat := 4983230072969 + 3 ^ 40 * 766541 * 2
def baseEnd_766541 : Nat := 349870199447280567566443

theorem tailTrace_766541 : CollatzResearch.WordTrace tailWord_766541 prefixEnd_766541 349870199447280567566443 := by
  unfold tailWord_766541
  simp only [CollatzResearch.WordTrace]
  refine ⟨27958047115960346625251477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18638698077306897750167651 27958047115960346625251477)
  ·
    refine ⟨1310533458560641248058663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27958047115960346625251477 1310533458560641248058663)
    ·
      refine ⟨1965800187840961872087995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310533458560641248058663 1965800187840961872087995)
      ·
        refine ⟨2948700281761442808131993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965800187840961872087995 2948700281761442808131993)
        ·
          refine ⟨2211525211321082106098995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2948700281761442808131993 2211525211321082106098995)
          ·
            refine ⟨3317287816981623159148493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211525211321082106098995 3317287816981623159148493)
            ·
              refine ⟨1243982931368108684680685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3317287816981623159148493 1243982931368108684680685)
              ·
                refine ⟨466493599263040756755257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1243982931368108684680685 466493599263040756755257)
                ·
                  refine ⟨349870199447280567566443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466493599263040756755257 349870199447280567566443)
                  ·
                    rfl

theorem cell20_766541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_766541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766541 prefixEnd_766541 := by exact prefixLift 766541
  have htrace : WordTrace (prefixWord ++ tailWord_766541) baseStart_766541 baseEnd_766541 := by
    simpa [prefixWord, tailWord_766541, baseEnd_766541] using wordTrace_append hprefix tailTrace_766541
  have hstable : (prefixWord ++ tailWord_766541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766541).length < 2 ^ (prefixWord ++ tailWord_766541).sum := by decide
  have hdescent : baseEnd_766541 < baseStart_766541 := by decide
  rcases family_descends (prefixWord ++ tailWord_766541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766576 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_766576 : Nat := 118140960795 + 766576 * 2 ^ 59
def prefixEnd_766576 : Nat := 4983230072969 + 3 ^ 40 * 766576 * 2
def baseEnd_766576 : Nat := 349886174400976001399633

theorem tailTrace_766576 : CollatzResearch.WordTrace tailWord_766576 prefixEnd_766576 349886174400976001399633 := by
  unfold tailWord_766576
  simp only [CollatzResearch.WordTrace]
  refine ⟨13979661835416773801387791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18639549113889031735183721 13979661835416773801387791)
  ·
    refine ⟨20969492753125160702081687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13979661835416773801387791 20969492753125160702081687)
    ·
      refine ⟨31454239129687741053122531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20969492753125160702081687 31454239129687741053122531)
      ·
        refine ⟨47181358694531611579683797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31454239129687741053122531 47181358694531611579683797)
        ·
          refine ⟨1105813094403084646398839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47181358694531611579683797 1105813094403084646398839)
          ·
            refine ⟨1658719641604626969598259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105813094403084646398839 1658719641604626969598259)
            ·
              refine ⟨2488079462406940454397389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658719641604626969598259 2488079462406940454397389)
              ·
                refine ⟨933029798402602670399021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2488079462406940454397389 933029798402602670399021)
                ·
                  refine ⟨349886174400976001399633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933029798402602670399021 349886174400976001399633)
                  ·
                    rfl

theorem cell20_766576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_766576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766576 prefixEnd_766576 := by exact prefixLift 766576
  have htrace : WordTrace (prefixWord ++ tailWord_766576) baseStart_766576 baseEnd_766576 := by
    simpa [prefixWord, tailWord_766576, baseEnd_766576] using wordTrace_append hprefix tailTrace_766576
  have hstable : (prefixWord ++ tailWord_766576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766576).length < 2 ^ (prefixWord ++ tailWord_766576).sum := by decide
  have hdescent : baseEnd_766576 < baseStart_766576 := by decide
  rcases family_descends (prefixWord ++ tailWord_766576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766638 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_766638 : Nat := 118140960795 + 766638 * 2 ^ 59
def prefixEnd_766638 : Nat := 4983230072969 + 3 ^ 40 * 766638 * 2
def baseEnd_766638 : Nat := 349914472890379341332713

theorem tailTrace_766638 : CollatzResearch.WordTrace tailWord_766638 prefixEnd_766638 349914472890379341332713 := by
  unfold tailWord_766638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495198124576116523941571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18641056664405954794355045 3495198124576116523941571)
  ·
    refine ⟨5242797186864174785912357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3495198124576116523941571 5242797186864174785912357)
    ·
      refine ⟨983024472537032772358567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5242797186864174785912357 983024472537032772358567)
      ·
        refine ⟨1474536708805549158537851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983024472537032772358567 1474536708805549158537851)
        ·
          refine ⟨2211805063208323737806777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474536708805549158537851 2211805063208323737806777)
          ·
            refine ⟨1658853797406242803355083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2211805063208323737806777 1658853797406242803355083)
            ·
              refine ⟨2488280696109364205032625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658853797406242803355083 2488280696109364205032625)
              ·
                refine ⟨1866210522082023153774469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2488280696109364205032625 1866210522082023153774469)
                ·
                  refine ⟨349914472890379341332713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1866210522082023153774469 349914472890379341332713)
                  ·
                    rfl

theorem cell20_766638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_766638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766638 prefixEnd_766638 := by exact prefixLift 766638
  have htrace : WordTrace (prefixWord ++ tailWord_766638) baseStart_766638 baseEnd_766638 := by
    simpa [prefixWord, tailWord_766638, baseEnd_766638] using wordTrace_append hprefix tailTrace_766638
  have hstable : (prefixWord ++ tailWord_766638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766638).length < 2 ^ (prefixWord ++ tailWord_766638).sum := by decide
  have hdescent : baseEnd_766638 < baseStart_766638 := by decide
  rcases family_descends (prefixWord ++ tailWord_766638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766645 : List Nat := [1, 3, 3, 3, 1, 2, 3, 4]
def baseStart_766645 : Nat := 118140960795 + 766645 * 2 ^ 59
def prefixEnd_766645 : Nat := 4983230072969 + 3 ^ 40 * 766645 * 2
def baseEnd_766645 : Nat := 116639222627039476033117

theorem tailTrace_766645 : CollatzResearch.WordTrace tailWord_766645 prefixEnd_766645 116639222627039476033117 := by
  unfold tailWord_766645
  simp only [CollatzResearch.WordTrace]
  refine ⟨27961840307583572387037389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18641226871722381591358259 27961840307583572387037389)
  ·
    refine ⟨10485690115343839645139021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27961840307583572387037389 10485690115343839645139021)
    ·
      refine ⟨3932133793253939866927133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10485690115343839645139021 3932133793253939866927133)
      ·
        refine ⟨1474550172470227450097675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3932133793253939866927133 1474550172470227450097675)
        ·
          refine ⟨2211825258705341175146513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474550172470227450097675 2211825258705341175146513)
          ·
            refine ⟨1658868944029005881359885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2211825258705341175146513 1658868944029005881359885)
            ·
              refine ⟨622075854010877205509957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1658868944029005881359885 622075854010877205509957)
              ·
                refine ⟨116639222627039476033117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622075854010877205509957 116639222627039476033117)
                ·
                  rfl

theorem cell20_766645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 4].length) (baseStart_766645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766645 prefixEnd_766645 := by exact prefixLift 766645
  have htrace : WordTrace (prefixWord ++ tailWord_766645) baseStart_766645 baseEnd_766645 := by
    simpa [prefixWord, tailWord_766645, baseEnd_766645] using wordTrace_append hprefix tailTrace_766645
  have hstable : (prefixWord ++ tailWord_766645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766645).length < 2 ^ (prefixWord ++ tailWord_766645).sum := by decide
  have hdescent : baseEnd_766645 < baseStart_766645 := by decide
  rcases family_descends (prefixWord ++ tailWord_766645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766662 : List Nat := [6, 1, 2, 1, 2, 1, 7]
def baseStart_766662 : Nat := 118140960795 + 766662 * 2 ^ 59
def prefixEnd_766662 : Nat := 4983230072969 + 3 ^ 40 * 766662 * 2
def baseEnd_766662 : Nat := 38880603016037991614735

theorem tailTrace_766662 : CollatzResearch.WordTrace tailWord_766662 prefixEnd_766662 38880603016037991614735 := by
  unfold tailWord_766662
  simp only [CollatzResearch.WordTrace]
  refine ⟨873826885891312009075195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18641640232347989526937493 873826885891312009075195)
  ·
    refine ⟨1310740328836968013612793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 873826885891312009075195 1310740328836968013612793)
    ·
      refine ⟨983055246627726010209595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1310740328836968013612793 983055246627726010209595)
      ·
        refine ⟨1474582869941589015314393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983055246627726010209595 1474582869941589015314393)
        ·
          refine ⟨1105937152456191761485795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474582869941589015314393 1105937152456191761485795)
          ·
            refine ⟨1658905728684287642228693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105937152456191761485795 1658905728684287642228693)
            ·
              refine ⟨38880603016037991614735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1658905728684287642228693 38880603016037991614735)
              ·
                rfl

theorem cell20_766662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 7].length) (baseStart_766662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766662 prefixEnd_766662 := by exact prefixLift 766662
  have htrace : WordTrace (prefixWord ++ tailWord_766662) baseStart_766662 baseEnd_766662 := by
    simpa [prefixWord, tailWord_766662, baseEnd_766662] using wordTrace_append hprefix tailTrace_766662
  have hstable : (prefixWord ++ tailWord_766662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766662).length < 2 ^ (prefixWord ++ tailWord_766662).sum := by decide
  have hdescent : baseEnd_766662 < baseStart_766662 := by decide
  rcases family_descends (prefixWord ++ tailWord_766662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766669 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 5]
def baseStart_766669 : Nat := 118140960795 + 766669 * 2 ^ 59
def prefixEnd_766669 : Nat := 4983230072969 + 3 ^ 40 * 766669 * 2
def baseEnd_766669 : Nat := 349928622135081011299253

theorem tailTrace_766669 : CollatzResearch.WordTrace tailWord_766669 prefixEnd_766669 349928622135081011299253 := by
  unfold tailWord_766669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27962715659496624485911061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18641810439664416323940707 27962715659496624485911061)
  ·
    refine ⟨1310752296538904272777081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27962715659496624485911061 1310752296538904272777081)
    ·
      refine ⟨983064222404178204582811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1310752296538904272777081 983064222404178204582811)
      ·
        refine ⟨1474596333606267306874217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983064222404178204582811 1474596333606267306874217)
        ·
          refine ⟨1105947250204700480155663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474596333606267306874217 1105947250204700480155663)
          ·
            refine ⟨1658920875307050720233495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105947250204700480155663 1658920875307050720233495)
            ·
              refine ⟨2488381312960576080350243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658920875307050720233495 2488381312960576080350243)
              ·
                refine ⟨3732571969440864120525365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2488381312960576080350243 3732571969440864120525365)
                ·
                  refine ⟨349928622135081011299253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3732571969440864120525365 349928622135081011299253)
                  ·
                    rfl

theorem cell20_766669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_766669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766669 prefixEnd_766669 := by exact prefixLift 766669
  have htrace : WordTrace (prefixWord ++ tailWord_766669) baseStart_766669 baseEnd_766669 := by
    simpa [prefixWord, tailWord_766669, baseEnd_766669] using wordTrace_append hprefix tailTrace_766669
  have hstable : (prefixWord ++ tailWord_766669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766669).length < 2 ^ (prefixWord ++ tailWord_766669).sum := by decide
  have hdescent : baseEnd_766669 < baseStart_766669 := by decide
  rcases family_descends (prefixWord ++ tailWord_766669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766676 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_766676 : Nat := 118140960795 + 766676 * 2 ^ 59
def prefixEnd_766676 : Nat := 4983230072969 + 3 ^ 40 * 766676 * 2
def baseEnd_766676 : Nat := 349931817125820098065891

theorem tailTrace_766676 : CollatzResearch.WordTrace tailWord_766676 prefixEnd_766676 349931817125820098065891 := by
  unfold tailWord_766676
  simp only [CollatzResearch.WordTrace]
  refine ⟨13981485485235632340707941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18641980646980843120943921 13981485485235632340707941)
  ·
    refine ⟨2621528528481681063882739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13981485485235632340707941 2621528528481681063882739)
    ·
      refine ⟨3932292792722521595824109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621528528481681063882739 3932292792722521595824109)
      ·
        refine ⟨1474609797270945598434041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3932292792722521595824109 1474609797270945598434041)
        ·
          refine ⟨1105957347953209198825531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474609797270945598434041 1105957347953209198825531)
          ·
            refine ⟨1658936021929813798238297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105957347953209198825531 1658936021929813798238297)
            ·
              refine ⟨1244202016447360348678723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658936021929813798238297 1244202016447360348678723)
              ·
                refine ⟨1866303024671040523018085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244202016447360348678723 1866303024671040523018085)
                ·
                  refine ⟨349931817125820098065891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1866303024671040523018085 349931817125820098065891)
                  ·
                    rfl

theorem cell20_766676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_766676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766676 prefixEnd_766676 := by exact prefixLift 766676
  have htrace : WordTrace (prefixWord ++ tailWord_766676) baseStart_766676 baseEnd_766676 := by
    simpa [prefixWord, tailWord_766676, baseEnd_766676] using wordTrace_append hprefix tailTrace_766676
  have hstable : (prefixWord ++ tailWord_766676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766676).length < 2 ^ (prefixWord ++ tailWord_766676).sum := by decide
  have hdescent : baseEnd_766676 < baseStart_766676 := by decide
  rcases family_descends (prefixWord ++ tailWord_766676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766680 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_766680 : Nat := 118140960795 + 766680 * 2 ^ 59
def prefixEnd_766680 : Nat := 4983230072969 + 3 ^ 40 * 766680 * 2
def baseEnd_766680 : Nat := 349933642834813861932541

theorem tailTrace_766680 : CollatzResearch.WordTrace tailWord_766680 prefixEnd_766680 349933642834813861932541 := by
  unfold tailWord_766680
  simp only [CollatzResearch.WordTrace]
  refine ⟨13981558431228386682280747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18642077908304515576374329 13981558431228386682280747)
  ·
    refine ⟨20972337646842580023421121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13981558431228386682280747 20972337646842580023421121)
    ·
      refine ⟨15729253235131935017565841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20972337646842580023421121 15729253235131935017565841)
      ·
        refine ⟨11796939926348951263174381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15729253235131935017565841 11796939926348951263174381)
        ·
          refine ⟨4423852472380856723690393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11796939926348951263174381 4423852472380856723690393)
          ·
            refine ⟨3317889354285642542767795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4423852472380856723690393 3317889354285642542767795)
            ·
              refine ⟨4976834031428463814151693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317889354285642542767795 4976834031428463814151693)
              ·
                refine ⟨1866312761785673930306885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4976834031428463814151693 1866312761785673930306885)
                ·
                  refine ⟨349933642834813861932541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1866312761785673930306885 349933642834813861932541)
                  ·
                    rfl

theorem cell20_766680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_766680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766680 prefixEnd_766680 := by exact prefixLift 766680
  have htrace : WordTrace (prefixWord ++ tailWord_766680) baseStart_766680 baseEnd_766680 := by
    simpa [prefixWord, tailWord_766680, baseEnd_766680] using wordTrace_append hprefix tailTrace_766680
  have hstable : (prefixWord ++ tailWord_766680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766680).length < 2 ^ (prefixWord ++ tailWord_766680).sum := by decide
  have hdescent : baseEnd_766680 < baseStart_766680 := by decide
  rcases family_descends (prefixWord ++ tailWord_766680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766787 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 3]
def baseStart_766787 : Nat := 118140960795 + 766787 * 2 ^ 59
def prefixEnd_766787 : Nat := 4983230072969 + 3 ^ 40 * 766787 * 2
def baseEnd_766787 : Nat := 349982480550397045365437

theorem tailTrace_766787 : CollatzResearch.WordTrace tailWord_766787 prefixEnd_766787 349982480550397045365437 := by
  unfold tailWord_766787
  simp only [CollatzResearch.WordTrace]
  refine ⟨27967019473069130638706615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18644679648712753759137743 27967019473069130638706615)
  ·
    refine ⟨41950529209603695958059923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27967019473069130638706615 41950529209603695958059923)
    ·
      refine ⟨62925793814405543937089885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41950529209603695958059923 62925793814405543937089885)
      ·
        refine ⟨23597172680402078976408707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62925793814405543937089885 23597172680402078976408707)
        ·
          refine ⟨35395759020603118464613061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23597172680402078976408707 35395759020603118464613061)
          ·
            refine ⟨6636704816363084712114949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35395759020603118464613061 6636704816363084712114949)
            ·
              refine ⟨1244382153068078383521553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6636704816363084712114949 1244382153068078383521553)
              ·
                refine ⟨933286614801058787641165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244382153068078383521553 933286614801058787641165)
                ·
                  refine ⟨349982480550397045365437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933286614801058787641165 349982480550397045365437)
                  ·
                    rfl

theorem cell20_766787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_766787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766787 prefixEnd_766787 := by exact prefixLift 766787
  have htrace : WordTrace (prefixWord ++ tailWord_766787) baseStart_766787 baseEnd_766787 := by
    simpa [prefixWord, tailWord_766787, baseEnd_766787] using wordTrace_append hprefix tailTrace_766787
  have hstable : (prefixWord ++ tailWord_766787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766787).length < 2 ^ (prefixWord ++ tailWord_766787).sum := by decide
  have hdescent : baseEnd_766787 < baseStart_766787 := by decide
  rcases family_descends (prefixWord ++ tailWord_766787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766877 : List Nat := [1, 4, 2, 1, 2, 1, 3, 6]
def baseStart_766877 : Nat := 118140960795 + 766877 * 2 ^ 59
def prefixEnd_766877 : Nat := 4983230072969 + 3 ^ 40 * 766877 * 2
def baseEnd_766877 : Nat := 116674519667585577455023

theorem tailTrace_766877 : CollatzResearch.WordTrace tailWord_766877 prefixEnd_766877 116674519667585577455023 := by
  unfold tailWord_766877
  simp only [CollatzResearch.WordTrace]
  refine ⟨27970302042743076009482885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18646868028495384006321923 27970302042743076009482885)
  ·
    refine ⟨5244431633014326751778041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27970302042743076009482885 5244431633014326751778041)
    ·
      refine ⟨3933323724760745063833531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5244431633014326751778041 3933323724760745063833531)
      ·
        refine ⟨5899985587141117595750297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933323724760745063833531 5899985587141117595750297)
        ·
          refine ⟨4424989190355838196812723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5899985587141117595750297 4424989190355838196812723)
          ·
            refine ⟨6637483785533757295219085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424989190355838196812723 6637483785533757295219085)
            ·
              refine ⟨2489056419575158985707157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6637483785533757295219085 2489056419575158985707157)
              ·
                refine ⟨116674519667585577455023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2489056419575158985707157 116674519667585577455023)
                ·
                  rfl

theorem cell20_766877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_766877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766877 prefixEnd_766877 := by exact prefixLift 766877
  have htrace : WordTrace (prefixWord ++ tailWord_766877) baseStart_766877 baseEnd_766877 := by
    simpa [prefixWord, tailWord_766877, baseEnd_766877] using wordTrace_append hprefix tailTrace_766877
  have hstable : (prefixWord ++ tailWord_766877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766877).length < 2 ^ (prefixWord ++ tailWord_766877).sum := by decide
  have hdescent : baseEnd_766877 < baseStart_766877 := by decide
  rcases family_descends (prefixWord ++ tailWord_766877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766884 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_766884 : Nat := 118140960795 + 766884 * 2 ^ 59
def prefixEnd_766884 : Nat := 4983230072969 + 3 ^ 40 * 766884 * 2
def baseEnd_766884 : Nat := 350026753993495819131707

theorem tailTrace_766884 : CollatzResearch.WordTrace tailWord_766884 prefixEnd_766884 350026753993495819131707 := by
  unfold tailWord_766884
  simp only [CollatzResearch.WordTrace]
  refine ⟨13985278676858858102493853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18647038235811810803325137 13985278676858858102493853)
  ·
    refine ⟨5244479503822071788435195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13985278676858858102493853 5244479503822071788435195)
    ·
      refine ⟨7866719255733107682652793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5244479503822071788435195 7866719255733107682652793)
      ·
        refine ⟨5900039441799830761989595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7866719255733107682652793 5900039441799830761989595)
        ·
          refine ⟨8850059162699746142984393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5900039441799830761989595 8850059162699746142984393)
          ·
            refine ⟨6637544372024809607238295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8850059162699746142984393 6637544372024809607238295)
            ·
              refine ⟨9956316558037214410857443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637544372024809607238295 9956316558037214410857443)
              ·
                refine ⟨14934474837055821616286165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9956316558037214410857443 14934474837055821616286165)
                ·
                  refine ⟨350026753993495819131707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14934474837055821616286165 350026753993495819131707)
                  ·
                    rfl

theorem cell20_766884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_766884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766884 prefixEnd_766884 := by exact prefixLift 766884
  have htrace : WordTrace (prefixWord ++ tailWord_766884) baseStart_766884 baseEnd_766884 := by
    simpa [prefixWord, tailWord_766884, baseEnd_766884] using wordTrace_append hprefix tailTrace_766884
  have hstable : (prefixWord ++ tailWord_766884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766884).length < 2 ^ (prefixWord ++ tailWord_766884).sum := by decide
  have hdescent : baseEnd_766884 < baseStart_766884 := by decide
  rcases family_descends (prefixWord ++ tailWord_766884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766900 : List Nat := [2, 5, 2, 1, 1, 2, 3, 2, 2]
def baseStart_766900 : Nat := 118140960795 + 766900 * 2 ^ 59
def prefixEnd_766900 : Nat := 4983230072969 + 3 ^ 40 * 766900 * 2
def baseEnd_766900 : Nat := 350034056829470874598309

theorem tailTrace_766900 : CollatzResearch.WordTrace tailWord_766900 prefixEnd_766900 350034056829470874598309 := by
  unfold tailWord_766900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13985570460829875468785077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18647427281106500625046769 13985570460829875468785077)
  ·
    refine ⟨1311147230702800825198601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13985570460829875468785077 1311147230702800825198601)
    ·
      refine ⟨983360423027100618898951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1311147230702800825198601 983360423027100618898951)
      ·
        refine ⟨1475040634540650928348427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983360423027100618898951 1475040634540650928348427)
        ·
          refine ⟨2212560951810976392522641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475040634540650928348427 2212560951810976392522641)
          ·
            refine ⟨1659420713858232294391981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2212560951810976392522641 1659420713858232294391981)
            ·
              refine ⟨622282767696837110396993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1659420713858232294391981 622282767696837110396993)
              ·
                refine ⟨466712075772627832797745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622282767696837110396993 466712075772627832797745)
                ·
                  refine ⟨350034056829470874598309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466712075772627832797745 350034056829470874598309)
                  ·
                    rfl

theorem cell20_766900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_766900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766900 prefixEnd_766900 := by exact prefixLift 766900
  have htrace : WordTrace (prefixWord ++ tailWord_766900) baseStart_766900 baseEnd_766900 := by
    simpa [prefixWord, tailWord_766900, baseEnd_766900] using wordTrace_append hprefix tailTrace_766900
  have hstable : (prefixWord ++ tailWord_766900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766900).length < 2 ^ (prefixWord ++ tailWord_766900).sum := by decide
  have hdescent : baseEnd_766900 < baseStart_766900 := by decide
  rcases family_descends (prefixWord ++ tailWord_766900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766901 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 3]
def baseStart_766901 : Nat := 118140960795 + 766901 * 2 ^ 59
def prefixEnd_766901 : Nat := 4983230072969 + 3 ^ 40 * 766901 * 2
def baseEnd_766901 : Nat := 350034513256719315564971

theorem tailTrace_766901 : CollatzResearch.WordTrace tailWord_766901 prefixEnd_766901 350034513256719315564971 := by
  unfold tailWord_766901
  simp only [CollatzResearch.WordTrace]
  refine ⟨27971177394656128108356557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18647451596437418738904371 27971177394656128108356557)
  ·
    refine ⟨10489191522996048040633709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27971177394656128108356557 10489191522996048040633709)
    ·
      refine ⟨3933446821123518015237641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10489191522996048040633709 3933446821123518015237641)
      ·
        refine ⟨2950085115842638511428231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3933446821123518015237641 2950085115842638511428231)
        ·
          refine ⟨4425127673763957767142347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950085115842638511428231 4425127673763957767142347)
          ·
            refine ⟨6637691510645936650713521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425127673763957767142347 6637691510645936650713521)
            ·
              refine ⟨4978268632984452488035141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6637691510645936650713521 4978268632984452488035141)
              ·
                refine ⟨933425368684584841506589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4978268632984452488035141 933425368684584841506589)
                ·
                  refine ⟨350034513256719315564971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933425368684584841506589 350034513256719315564971)
                  ·
                    rfl

theorem cell20_766901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_766901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766901 prefixEnd_766901 := by exact prefixLift 766901
  have htrace : WordTrace (prefixWord ++ tailWord_766901) baseStart_766901 baseEnd_766901 := by
    simpa [prefixWord, tailWord_766901, baseEnd_766901] using wordTrace_append hprefix tailTrace_766901
  have hstable : (prefixWord ++ tailWord_766901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766901).length < 2 ^ (prefixWord ++ tailWord_766901).sum := by decide
  have hdescent : baseEnd_766901 < baseStart_766901 := by decide
  rcases family_descends (prefixWord ++ tailWord_766901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766904 : List Nat := [2, 1, 2, 1, 2, 5, 3, 2, 2]
def baseStart_766904 : Nat := 118140960795 + 766904 * 2 ^ 59
def prefixEnd_766904 : Nat := 4983230072969 + 3 ^ 40 * 766904 * 2
def baseEnd_766904 : Nat := 350035882538464638464959

theorem tailTrace_766904 : CollatzResearch.WordTrace tailWord_766904 prefixEnd_766904 350035882538464638464959 := by
  unfold tailWord_766904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13985643406822629810357883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18647524542430173080477177 13985643406822629810357883)
  ·
    refine ⟨20978465110233944715536825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13985643406822629810357883 20978465110233944715536825)
    ·
      refine ⟨15733848832675458536652619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20978465110233944715536825 15733848832675458536652619)
      ·
        refine ⟨23600773249013187804978929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15733848832675458536652619 23600773249013187804978929)
        ·
          refine ⟨17700579936759890853734197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23600773249013187804978929 17700579936759890853734197)
          ·
            refine ⟨1659429369071239767537581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17700579936759890853734197 1659429369071239767537581)
            ·
              refine ⟨622286013401714912826593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1659429369071239767537581 622286013401714912826593)
              ·
                refine ⟨466714510051286184619945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622286013401714912826593 466714510051286184619945)
                ·
                  refine ⟨350035882538464638464959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466714510051286184619945 350035882538464638464959)
                  ·
                    rfl

theorem cell20_766904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_766904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766904 prefixEnd_766904 := by exact prefixLift 766904
  have htrace : WordTrace (prefixWord ++ tailWord_766904) baseStart_766904 baseEnd_766904 := by
    simpa [prefixWord, tailWord_766904, baseEnd_766904] using wordTrace_append hprefix tailTrace_766904
  have hstable : (prefixWord ++ tailWord_766904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766904).length < 2 ^ (prefixWord ++ tailWord_766904).sum := by decide
  have hdescent : baseEnd_766904 < baseStart_766904 := by decide
  rcases family_descends (prefixWord ++ tailWord_766904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766929 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_766929 : Nat := 118140960795 + 766929 * 2 ^ 59
def prefixEnd_766929 : Nat := 4983230072969 + 3 ^ 40 * 766929 * 2
def baseEnd_766929 : Nat := 350047293219675662631523

theorem tailTrace_766929 : CollatzResearch.WordTrace tailWord_766929 prefixEnd_766929 350047293219675662631523 := by
  unfold tailWord_766929
  simp only [CollatzResearch.WordTrace]
  refine ⟨27972198638554688890375841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18648132425703125926917227 27972198638554688890375841)
  ·
    refine ⟨20979148978916016667781881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27972198638554688890375841 20979148978916016667781881)
    ·
      refine ⟨15734361734187012500836411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20979148978916016667781881 15734361734187012500836411)
      ·
        refine ⟨23601542601280518751254617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15734361734187012500836411 23601542601280518751254617)
        ·
          refine ⟨17701156950960389063440963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23601542601280518751254617 17701156950960389063440963)
          ·
            refine ⟨26551735426440583595161445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17701156950960389063440963 26551735426440583595161445)
            ·
              refine ⟨4978450392457609424092771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26551735426440583595161445 4978450392457609424092771)
              ·
                refine ⟨7467675588686414136139157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4978450392457609424092771 7467675588686414136139157)
                ·
                  refine ⟨350047293219675662631523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7467675588686414136139157 350047293219675662631523)
                  ·
                    rfl

theorem cell20_766929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_766929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766929 prefixEnd_766929 := by exact prefixLift 766929
  have htrace : WordTrace (prefixWord ++ tailWord_766929) baseStart_766929 baseEnd_766929 := by
    simpa [prefixWord, tailWord_766929, baseEnd_766929] using wordTrace_append hprefix tailTrace_766929
  have hstable : (prefixWord ++ tailWord_766929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766929).length < 2 ^ (prefixWord ++ tailWord_766929).sum := by decide
  have hdescent : baseEnd_766929 < baseStart_766929 := by decide
  rcases family_descends (prefixWord ++ tailWord_766929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766977 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 3]
def baseStart_766977 : Nat := 118140960795 + 766977 * 2 ^ 59
def prefixEnd_766977 : Nat := 4983230072969 + 3 ^ 40 * 766977 * 2
def baseEnd_766977 : Nat := 350069201727600829031327

theorem tailTrace_766977 : CollatzResearch.WordTrace tailWord_766977 prefixEnd_766977 350069201727600829031327 := by
  unfold tailWord_766977
  simp only [CollatzResearch.WordTrace]
  refine ⟨27973949342380793088123185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18649299561587195392082123 27973949342380793088123185)
  ·
    refine ⟨20980462006785594816092389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27973949342380793088123185 20980462006785594816092389)
    ·
      refine ⟨3933836626272299028017323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20980462006785594816092389 3933836626272299028017323)
      ·
        refine ⟨5900754939408448542025985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933836626272299028017323 5900754939408448542025985)
        ·
          refine ⟨4425566204556336406519489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5900754939408448542025985 4425566204556336406519489)
          ·
            refine ⟨3319174653417252304889617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4425566204556336406519489 3319174653417252304889617)
            ·
              refine ⟨2489380990062939228667213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319174653417252304889617 2489380990062939228667213)
              ·
                refine ⟨933517871273602210750205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2489380990062939228667213 933517871273602210750205)
                ·
                  refine ⟨350069201727600829031327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933517871273602210750205 350069201727600829031327)
                  ·
                    rfl

theorem cell20_766977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_766977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766977 prefixEnd_766977 := by exact prefixLift 766977
  have htrace : WordTrace (prefixWord ++ tailWord_766977) baseStart_766977 baseEnd_766977 := by
    simpa [prefixWord, tailWord_766977, baseEnd_766977] using wordTrace_append hprefix tailTrace_766977
  have hstable : (prefixWord ++ tailWord_766977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766977).length < 2 ^ (prefixWord ++ tailWord_766977).sum := by decide
  have hdescent : baseEnd_766977 < baseStart_766977 := by decide
  rcases family_descends (prefixWord ++ tailWord_766977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_766984 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_766984 : Nat := 118140960795 + 766984 * 2 ^ 59
def prefixEnd_766984 : Nat := 4983230072969 + 3 ^ 40 * 766984 * 2
def baseEnd_766984 : Nat := 350072396718339915797965

theorem tailTrace_766984 : CollatzResearch.WordTrace tailWord_766984 prefixEnd_766984 350072396718339915797965 := by
  unfold tailWord_766984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987102326677716641814003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18649469768903622189085337 13987102326677716641814003)
  ·
    refine ⟨20980653490016574962721005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13987102326677716641814003 20980653490016574962721005)
    ·
      refine ⟨7867745058756215611020377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20980653490016574962721005 7867745058756215611020377)
      ·
        refine ⟨5900808794067161708265283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7867745058756215611020377 5900808794067161708265283)
        ·
          refine ⟨8851213191100742562397925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5900808794067161708265283 8851213191100742562397925)
          ·
            refine ⟨1659602473331389230449611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8851213191100742562397925 1659602473331389230449611)
            ·
              refine ⟨2489403709997083845674417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659602473331389230449611 2489403709997083845674417)
              ·
                refine ⟨1867052782497812884255813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489403709997083845674417 1867052782497812884255813)
                ·
                  refine ⟨350072396718339915797965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867052782497812884255813 350072396718339915797965)
                  ·
                    rfl

theorem cell20_766984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_766984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_766984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_766984 prefixEnd_766984 := by exact prefixLift 766984
  have htrace : WordTrace (prefixWord ++ tailWord_766984) baseStart_766984 baseEnd_766984 := by
    simpa [prefixWord, tailWord_766984, baseEnd_766984] using wordTrace_append hprefix tailTrace_766984
  have hstable : (prefixWord ++ tailWord_766984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_766984).length < 2 ^ (prefixWord ++ tailWord_766984).sum := by decide
  have hdescent : baseEnd_766984 < baseStart_766984 := by decide
  rcases family_descends (prefixWord ++ tailWord_766984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767008 : List Nat := [2, 1, 1, 7, 1, 1, 7]
def baseStart_767008 : Nat := 118140960795 + 767008 * 2 ^ 59
def prefixEnd_767008 : Nat := 4983230072969 + 3 ^ 40 * 767008 * 2
def baseEnd_767008 : Nat := 38898150108033610999763

theorem tailTrace_767008 : CollatzResearch.WordTrace tailWord_767008 prefixEnd_767008 38898150108033610999763 := by
  unfold tailWord_767008
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987540002634242691250839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18650053336845656921667785 13987540002634242691250839)
  ·
    refine ⟨20981310003951364036876259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13987540002634242691250839 20981310003951364036876259)
    ·
      refine ⟨31471965005927046055314389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20981310003951364036876259 31471965005927046055314389)
      ·
        refine ⟨737624179826415141921431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 31471965005927046055314389 737624179826415141921431)
        ·
          refine ⟨1106436269739622712882147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737624179826415141921431 1106436269739622712882147)
          ·
            refine ⟨1659654404609434069323221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106436269739622712882147 1659654404609434069323221)
            ·
              refine ⟨38898150108033610999763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1659654404609434069323221 38898150108033610999763)
              ·
                rfl

theorem cell20_767008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 7].length) (baseStart_767008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767008 prefixEnd_767008 := by exact prefixLift 767008
  have htrace : WordTrace (prefixWord ++ tailWord_767008) baseStart_767008 baseEnd_767008 := by
    simpa [prefixWord, tailWord_767008, baseEnd_767008] using wordTrace_append hprefix tailTrace_767008
  have hstable : (prefixWord ++ tailWord_767008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767008).length < 2 ^ (prefixWord ++ tailWord_767008).sum := by decide
  have hdescent : baseEnd_767008 < baseStart_767008 := by decide
  rcases family_descends (prefixWord ++ tailWord_767008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767032 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_767032 : Nat := 118140960795 + 767032 * 2 ^ 59
def prefixEnd_767032 : Nat := 4983230072969 + 3 ^ 40 * 767032 * 2
def baseEnd_767032 : Nat := 350094305226265082197769

theorem tailTrace_767032 : CollatzResearch.WordTrace tailWord_767032 prefixEnd_767032 350094305226265082197769 := by
  unfold tailWord_767032
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987977678590768740687675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18650636904787691654250233 13987977678590768740687675)
  ·
    refine ⟨20981966517886153111031513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13987977678590768740687675 20981966517886153111031513)
    ·
      refine ⟨15736474888414614833273635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20981966517886153111031513 15736474888414614833273635)
      ·
        refine ⟨23604712332621922249910453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15736474888414614833273635 23604712332621922249910453)
        ·
          refine ⟨2212941781183305210929105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23604712332621922249910453 2212941781183305210929105)
          ·
            refine ⟨1659706335887478908196829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2212941781183305210929105 1659706335887478908196829)
            ·
              refine ⟨622389875957804590573811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1659706335887478908196829 622389875957804590573811)
              ·
                refine ⟨933584813936706885860717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622389875957804590573811 933584813936706885860717)
                ·
                  refine ⟨350094305226265082197769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933584813936706885860717 350094305226265082197769)
                  ·
                    rfl

theorem cell20_767032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_767032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767032 prefixEnd_767032 := by exact prefixLift 767032
  have htrace : WordTrace (prefixWord ++ tailWord_767032) baseStart_767032 baseEnd_767032 := by
    simpa [prefixWord, tailWord_767032, baseEnd_767032] using wordTrace_append hprefix tailTrace_767032
  have hstable : (prefixWord ++ tailWord_767032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767032).length < 2 ^ (prefixWord ++ tailWord_767032).sum := by decide
  have hdescent : baseEnd_767032 < baseStart_767032 := by decide
  rcases family_descends (prefixWord ++ tailWord_767032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767043 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_767043 : Nat := 118140960795 + 767043 * 2 ^ 59
def prefixEnd_767043 : Nat := 4983230072969 + 3 ^ 40 * 767043 * 2
def baseEnd_767043 : Nat := 350099325925997932831057

theorem tailTrace_767043 : CollatzResearch.WordTrace tailWord_767043 prefixEnd_767043 350099325925997932831057 := by
  unfold tailWord_767043
  simp only [CollatzResearch.WordTrace]
  refine ⟨27976356560141686360025783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18650904373427790906683855 27976356560141686360025783)
  ·
    refine ⟨41964534840212529540038675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27976356560141686360025783 41964534840212529540038675)
    ·
      refine ⟨62946802260318794310058013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41964534840212529540038675 62946802260318794310058013)
      ·
        refine ⟨23605050847619547866271755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62946802260318794310058013 23605050847619547866271755)
        ·
          refine ⟨35407576271429321799407633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23605050847619547866271755 35407576271429321799407633)
          ·
            refine ⟨26555682203571991349555725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35407576271429321799407633 26555682203571991349555725)
            ·
              refine ⟨9958380826339496756083397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26555682203571991349555725 9958380826339496756083397)
              ·
                refine ⟨1867196404938655641765637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9958380826339496756083397 1867196404938655641765637)
                ·
                  refine ⟨350099325925997932831057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867196404938655641765637 350099325925997932831057)
                  ·
                    rfl

theorem cell20_767043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_767043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767043 prefixEnd_767043 := by exact prefixLift 767043
  have htrace : WordTrace (prefixWord ++ tailWord_767043) baseStart_767043 baseEnd_767043 := by
    simpa [prefixWord, tailWord_767043, baseEnd_767043] using wordTrace_append hprefix tailTrace_767043
  have hstable : (prefixWord ++ tailWord_767043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767043).length < 2 ^ (prefixWord ++ tailWord_767043).sum := by decide
  have hdescent : baseEnd_767043 < baseStart_767043 := by decide
  rcases family_descends (prefixWord ++ tailWord_767043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767053 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_767053 : Nat := 118140960795 + 767053 * 2 ^ 59
def prefixEnd_767053 : Nat := 4983230072969 + 3 ^ 40 * 767053 * 2
def baseEnd_767053 : Nat := 350103890198482342497683

theorem tailTrace_767053 : CollatzResearch.WordTrace tailWord_767053 prefixEnd_767053 350103890198482342497683 := by
  unfold tailWord_767053
  simp only [CollatzResearch.WordTrace]
  refine ⟨27976721290105458067889813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18651147526736972045259875 27976721290105458067889813)
  ·
    refine ⟨1311408810473693346932335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27976721290105458067889813 1311408810473693346932335)
    ·
      refine ⟨1967113215710540020398503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311408810473693346932335 1967113215710540020398503)
      ·
        refine ⟨2950669823565810030597755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967113215710540020398503 2950669823565810030597755)
        ·
          refine ⟨4426004735348715045896633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950669823565810030597755 4426004735348715045896633)
          ·
            refine ⟨3319503551511536284422475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4426004735348715045896633 3319503551511536284422475)
            ·
              refine ⟨4979255327267304426633713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319503551511536284422475 4979255327267304426633713)
              ·
                refine ⟨3734441495450478319975285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4979255327267304426633713 3734441495450478319975285)
                ·
                  refine ⟨350103890198482342497683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3734441495450478319975285 350103890198482342497683)
                  ·
                    rfl

theorem cell20_767053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_767053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767053 prefixEnd_767053 := by exact prefixLift 767053
  have htrace : WordTrace (prefixWord ++ tailWord_767053) baseStart_767053 baseEnd_767053 := by
    simpa [prefixWord, tailWord_767053, baseEnd_767053] using wordTrace_append hprefix tailTrace_767053
  have hstable : (prefixWord ++ tailWord_767053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767053).length < 2 ^ (prefixWord ++ tailWord_767053).sum := by decide
  have hdescent : baseEnd_767053 < baseStart_767053 := by decide
  rcases family_descends (prefixWord ++ tailWord_767053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767105 : List Nat := [1, 2, 4, 2, 2, 1, 2, 6]
def baseStart_767105 : Nat := 118140960795 + 767105 * 2 ^ 59
def prefixEnd_767105 : Nat := 4983230072969 + 3 ^ 40 * 767105 * 2
def baseEnd_767105 : Nat := 116709208138467090921379

theorem tailTrace_767105 : CollatzResearch.WordTrace tailWord_767105 prefixEnd_767105 116709208138467090921379 := by
  unfold tailWord_767105
  simp only [CollatzResearch.WordTrace]
  refine ⟨27978617885917070948782769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18652411923944713965855179 27978617885917070948782769)
  ·
    refine ⟨20983963414437803211587077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27978617885917070948782769 20983963414437803211587077)
    ·
      refine ⟨3934493140207088102172577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20983963414437803211587077 3934493140207088102172577)
      ·
        refine ⟨2950869855155316076629433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3934493140207088102172577 2950869855155316076629433)
        ·
          refine ⟨2213152391366487057472075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2950869855155316076629433 2213152391366487057472075)
          ·
            refine ⟨3319728587049730586208113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213152391366487057472075 3319728587049730586208113)
            ·
              refine ⟨2489796440287297939656085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319728587049730586208113 2489796440287297939656085)
              ·
                refine ⟨116709208138467090921379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2489796440287297939656085 116709208138467090921379)
                ·
                  rfl

theorem cell20_767105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_767105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767105 prefixEnd_767105 := by exact prefixLift 767105
  have htrace : WordTrace (prefixWord ++ tailWord_767105) baseStart_767105 baseEnd_767105 := by
    simpa [prefixWord, tailWord_767105, baseEnd_767105] using wordTrace_append hprefix tailTrace_767105
  have hstable : (prefixWord ++ tailWord_767105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767105).length < 2 ^ (prefixWord ++ tailWord_767105).sum := by decide
  have hdescent : baseEnd_767105 < baseStart_767105 := by decide
  rcases family_descends (prefixWord ++ tailWord_767105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767132 : List Nat := [2, 2, 3, 2, 1, 2, 4, 2, 2]
def baseStart_767132 : Nat := 118140960795 + 767132 * 2 ^ 59
def prefixEnd_767132 : Nat := 4983230072969 + 3 ^ 40 * 767132 * 2
def baseEnd_767132 : Nat := 350139947951109178864027

theorem tailTrace_767132 : CollatzResearch.WordTrace tailWord_767132 prefixEnd_767132 350139947951109178864027 := by
  unfold tailWord_767132
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989801328409627280007825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18653068437879503040010433 13989801328409627280007825)
  ·
    refine ⟨10492350996307220460005869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13989801328409627280007825 10492350996307220460005869)
    ·
      refine ⟨3934631623615207672502201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10492350996307220460005869 3934631623615207672502201)
      ·
        refine ⟨2950973717711405754376651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3934631623615207672502201 2950973717711405754376651)
        ·
          refine ⟨4426460576567108631564977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950973717711405754376651 4426460576567108631564977)
          ·
            refine ⟨3319845432425331473673733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4426460576567108631564977 3319845432425331473673733)
            ·
              refine ⟨622471018579749651313825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3319845432425331473673733 622471018579749651313825)
              ·
                refine ⟨466853263934812238485369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622471018579749651313825 466853263934812238485369)
                ·
                  refine ⟨350139947951109178864027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466853263934812238485369 350139947951109178864027)
                  ·
                    rfl

theorem cell20_767132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_767132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767132 prefixEnd_767132 := by exact prefixLift 767132
  have htrace : WordTrace (prefixWord ++ tailWord_767132) baseStart_767132 baseEnd_767132 := by
    simpa [prefixWord, tailWord_767132, baseEnd_767132] using wordTrace_append hprefix tailTrace_767132
  have hstable : (prefixWord ++ tailWord_767132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767132).length < 2 ^ (prefixWord ++ tailWord_767132).sum := by decide
  have hdescent : baseEnd_767132 < baseStart_767132 := by decide
  rcases family_descends (prefixWord ++ tailWord_767132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767146 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_767146 : Nat := 118140960795 + 767146 * 2 ^ 59
def prefixEnd_767146 : Nat := 4983230072969 + 3 ^ 40 * 767146 * 2
def baseEnd_767146 : Nat := 350146337932587352397303

theorem tailTrace_767146 : CollatzResearch.WordTrace tailWord_767146 prefixEnd_767146 350146337932587352397303 := by
  unfold tailWord_767146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6995028319692133737756323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18653408852512356634016861 6995028319692133737756323)
  ·
    refine ⟨10492542479538200606634485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6995028319692133737756323 10492542479538200606634485)
    ·
      refine ⟨983675857456706306871983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10492542479538200606634485 983675857456706306871983)
      ·
        refine ⟨1475513786185059460307975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983675857456706306871983 1475513786185059460307975)
        ·
          refine ⟨2213270679277589190461963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475513786185059460307975 2213270679277589190461963)
          ·
            refine ⟨3319906018916383785692945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213270679277589190461963 3319906018916383785692945)
            ·
              refine ⟨2489929514187287839269709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319906018916383785692945 2489929514187287839269709)
              ·
                refine ⟨933723567820232939726141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2489929514187287839269709 933723567820232939726141)
                ·
                  refine ⟨350146337932587352397303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933723567820232939726141 350146337932587352397303)
                  ·
                    rfl

theorem cell20_767146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_767146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767146 prefixEnd_767146 := by exact prefixLift 767146
  have htrace : WordTrace (prefixWord ++ tailWord_767146) baseStart_767146 baseEnd_767146 := by
    simpa [prefixWord, tailWord_767146, baseEnd_767146] using wordTrace_append hprefix tailTrace_767146
  have hstable : (prefixWord ++ tailWord_767146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767146).length < 2 ^ (prefixWord ++ tailWord_767146).sum := by decide
  have hdescent : baseEnd_767146 < baseStart_767146 := by decide
  rcases family_descends (prefixWord ++ tailWord_767146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767209 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_767209 : Nat := 118140960795 + 767209 * 2 ^ 59
def prefixEnd_767209 : Nat := 4983230072969 + 3 ^ 40 * 767209 * 2
def baseEnd_767209 : Nat := 350175092849239133297045

theorem tailTrace_767209 : CollatzResearch.WordTrace tailWord_767209 prefixEnd_767209 350175092849239133297045 := by
  unfold tailWord_767209
  simp only [CollatzResearch.WordTrace]
  refine ⟨27982411077540296710568681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18654940718360197807045787 27982411077540296710568681)
  ·
    refine ⟨20986808308155222532926511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27982411077540296710568681 20986808308155222532926511)
    ·
      refine ⟨31480212462232833799389767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20986808308155222532926511 31480212462232833799389767)
      ·
        refine ⟨47220318693349250699084651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31480212462232833799389767 47220318693349250699084651)
        ·
          refine ⟨70830478040023876048626977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47220318693349250699084651 70830478040023876048626977)
          ·
            refine ⟨53122858530017907036470233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70830478040023876048626977 53122858530017907036470233)
            ·
              refine ⟨39842143897513430277352675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53122858530017907036470233 39842143897513430277352675)
              ·
                refine ⟨59763215846270145416029013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39842143897513430277352675 59763215846270145416029013)
                ·
                  refine ⟨350175092849239133297045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59763215846270145416029013 350175092849239133297045)
                  ·
                    rfl

theorem cell20_767209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_767209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767209 prefixEnd_767209 := by exact prefixLift 767209
  have htrace : WordTrace (prefixWord ++ tailWord_767209) baseStart_767209 baseEnd_767209 := by
    simpa [prefixWord, tailWord_767209, baseEnd_767209] using wordTrace_append hprefix tailTrace_767209
  have hstable : (prefixWord ++ tailWord_767209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767209).length < 2 ^ (prefixWord ++ tailWord_767209).sum := by decide
  have hdescent : baseEnd_767209 < baseStart_767209 := by decide
  rcases family_descends (prefixWord ++ tailWord_767209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767215 : List Nat := [1, 1, 2, 1, 8, 1, 2, 4]
def baseStart_767215 : Nat := 118140960795 + 767215 * 2 ^ 59
def prefixEnd_767215 : Nat := 4983230072969 + 3 ^ 40 * 767215 * 2
def baseEnd_767215 : Nat := 116725943804243259699007

theorem tailTrace_767215 : CollatzResearch.WordTrace tailWord_767215 prefixEnd_767215 116725943804243259699007 := by
  unfold tailWord_767215
  simp only [CollatzResearch.WordTrace]
  refine ⟨27982629915518559735287099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18655086610345706490191399 27982629915518559735287099)
  ·
    refine ⟨41973944873277839602930649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27982629915518559735287099 41973944873277839602930649)
    ·
      refine ⟨31480458654958379702197987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41973944873277839602930649 31480458654958379702197987)
      ·
        refine ⟨47220687982437569553296981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31480458654958379702197987 47220687982437569553296981)
        ·
          refine ⟨553367437294190268202699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 47220687982437569553296981 553367437294190268202699)
          ·
            refine ⟨830051155941285402304049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553367437294190268202699 830051155941285402304049)
            ·
              refine ⟨622538366955964051728037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830051155941285402304049 622538366955964051728037)
              ·
                refine ⟨116725943804243259699007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622538366955964051728037 116725943804243259699007)
                ·
                  rfl

theorem cell20_767215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 4].length) (baseStart_767215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767215 prefixEnd_767215 := by exact prefixLift 767215
  have htrace : WordTrace (prefixWord ++ tailWord_767215) baseStart_767215 baseEnd_767215 := by
    simpa [prefixWord, tailWord_767215, baseEnd_767215] using wordTrace_append hprefix tailTrace_767215
  have hstable : (prefixWord ++ tailWord_767215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767215).length < 2 ^ (prefixWord ++ tailWord_767215).sum := by decide
  have hdescent : baseEnd_767215 < baseStart_767215 := by decide
  rcases family_descends (prefixWord ++ tailWord_767215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767219 : List Nat := [1, 1, 1, 2, 2, 5, 4, 4]
def baseStart_767219 : Nat := 118140960795 + 767219 * 2 ^ 59
def prefixEnd_767219 : Nat := 4983230072969 + 3 ^ 40 * 767219 * 2
def baseEnd_767219 : Nat := 116726552373907847654557

theorem tailTrace_767219 : CollatzResearch.WordTrace tailWord_767219 prefixEnd_767219 116726552373907847654557 := by
  unfold tailWord_767219
  simp only [CollatzResearch.WordTrace]
  refine ⟨27982775807504068418432711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18655183871669378945621807 27982775807504068418432711)
  ·
    refine ⟨41974163711256102627649067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27982775807504068418432711 41974163711256102627649067)
    ·
      refine ⟨62961245566884153941473601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41974163711256102627649067 62961245566884153941473601)
      ·
        refine ⟨47220934175163115456105201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62961245566884153941473601 47220934175163115456105201)
        ·
          refine ⟨35415700631372336592078901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47220934175163115456105201 35415700631372336592078901)
          ·
            refine ⟨3320221934191156555507397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35415700631372336592078901 3320221934191156555507397)
            ·
              refine ⟨622541612660841854157637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3320221934191156555507397 622541612660841854157637)
              ·
                refine ⟨116726552373907847654557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622541612660841854157637 116726552373907847654557)
                ·
                  rfl

theorem cell20_767219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 4].length) (baseStart_767219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767219 prefixEnd_767219 := by exact prefixLift 767219
  have htrace : WordTrace (prefixWord ++ tailWord_767219) baseStart_767219 baseEnd_767219 := by
    simpa [prefixWord, tailWord_767219, baseEnd_767219] using wordTrace_append hprefix tailTrace_767219
  have hstable : (prefixWord ++ tailWord_767219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767219).length < 2 ^ (prefixWord ++ tailWord_767219).sum := by decide
  have hdescent : baseEnd_767219 < baseStart_767219 := by decide
  rcases family_descends (prefixWord ++ tailWord_767219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767246 : List Nat := [4, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_767246 : Nat := 118140960795 + 767246 * 2 ^ 59
def prefixEnd_767246 : Nat := 4983230072969 + 3 ^ 40 * 767246 * 2
def baseEnd_767246 : Nat := 350191980657431449063561

theorem tailTrace_767246 : CollatzResearch.WordTrace tailWord_767246 prefixEnd_767246 350191980657431449063561 := by
  unfold tailWord_767246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497970072300781503708199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18655840385604168019777061 3497970072300781503708199)
  ·
    refine ⟨5246955108451172255562299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3497970072300781503708199 5246955108451172255562299)
    ·
      refine ⟨7870432662676758383343449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5246955108451172255562299 7870432662676758383343449)
      ·
        refine ⟨5902824497007568787507587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7870432662676758383343449 5902824497007568787507587)
        ·
          refine ⟨8854236745511353181261381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5902824497007568787507587 8854236745511353181261381)
          ·
            refine ⟨1660169389783378721486509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8854236745511353181261381 1660169389783378721486509)
            ·
              refine ⟨622563521168767020557441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1660169389783378721486509 622563521168767020557441)
              ·
                refine ⟨466922640876575265418081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622563521168767020557441 466922640876575265418081)
                ·
                  refine ⟨350191980657431449063561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466922640876575265418081 350191980657431449063561)
                  ·
                    rfl

theorem cell20_767246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_767246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767246 prefixEnd_767246 := by exact prefixLift 767246
  have htrace : WordTrace (prefixWord ++ tailWord_767246) baseStart_767246 baseEnd_767246 := by
    simpa [prefixWord, tailWord_767246, baseEnd_767246] using wordTrace_append hprefix tailTrace_767246
  have hstable : (prefixWord ++ tailWord_767246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767246).length < 2 ^ (prefixWord ++ tailWord_767246).sum := by decide
  have hdescent : baseEnd_767246 < baseStart_767246 := by decide
  rcases family_descends (prefixWord ++ tailWord_767246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767288 : List Nat := [2, 1, 2, 1, 3, 1, 1, 7, 2]
def baseStart_767288 : Nat := 118140960795 + 767288 * 2 ^ 59
def prefixEnd_767288 : Nat := 4983230072969 + 3 ^ 40 * 767288 * 2
def baseEnd_767288 : Nat := 350211150601865969663389

theorem tailTrace_767288 : CollatzResearch.WordTrace tailWord_767288 prefixEnd_767288 350211150601865969663389 := by
  unfold tailWord_767288
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992646222127046601347259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18656861629502728801796345 13992646222127046601347259)
  ·
    refine ⟨20988969333190569902020889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13992646222127046601347259 20988969333190569902020889)
    ·
      refine ⟨15741726999892927426515667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20988969333190569902020889 15741726999892927426515667)
      ·
        refine ⟨23612590499839391139773501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15741726999892927426515667 23612590499839391139773501)
        ·
          refine ⟨8854721437439771677415063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23612590499839391139773501 8854721437439771677415063)
          ·
            refine ⟨13282082156159657516122595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8854721437439771677415063 13282082156159657516122595)
            ·
              refine ⟨19923123234239486274183893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13282082156159657516122595 19923123234239486274183893)
              ·
                refine ⟨466948200802487959551185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19923123234239486274183893 466948200802487959551185)
                ·
                  refine ⟨350211150601865969663389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466948200802487959551185 350211150601865969663389)
                  ·
                    rfl

theorem cell20_767288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_767288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767288 prefixEnd_767288 := by exact prefixLift 767288
  have htrace : WordTrace (prefixWord ++ tailWord_767288) baseStart_767288 baseEnd_767288 := by
    simpa [prefixWord, tailWord_767288, baseEnd_767288] using wordTrace_append hprefix tailTrace_767288
  have hstable : (prefixWord ++ tailWord_767288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767288).length < 2 ^ (prefixWord ++ tailWord_767288).sum := by decide
  have hdescent : baseEnd_767288 < baseStart_767288 := by decide
  rcases family_descends (prefixWord ++ tailWord_767288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767305 : List Nat := [1, 2, 1, 1, 2, 3, 6, 2, 2]
def baseStart_767305 : Nat := 118140960795 + 767305 * 2 ^ 59
def prefixEnd_767305 : Nat := 4983230072969 + 3 ^ 40 * 767305 * 2
def baseEnd_767305 : Nat := 350218909865089466096653

theorem tailTrace_767305 : CollatzResearch.WordTrace tailWord_767305 prefixEnd_767305 350218909865089466096653 := by
  unfold tailWord_767305
  simp only [CollatzResearch.WordTrace]
  refine ⟨27985912485192505106063369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18657274990128336737375579 27985912485192505106063369)
  ·
    refine ⟨20989434363894378829547527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27985912485192505106063369 20989434363894378829547527)
    ·
      refine ⟨31484151545841568244321291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20989434363894378829547527 31484151545841568244321291)
      ·
        refine ⟨47226227318762352366481937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31484151545841568244321291 47226227318762352366481937)
        ·
          refine ⟨35419670489071764274861453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47226227318762352366481937 35419670489071764274861453)
          ·
            refine ⟨13282376433401911603073045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35419670489071764274861453 13282376433401911603073045)
            ·
              refine ⟨622611395315714606394049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13282376433401911603073045 622611395315714606394049)
              ·
                refine ⟨466958546486785954795537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622611395315714606394049 466958546486785954795537)
                ·
                  refine ⟨350218909865089466096653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466958546486785954795537 350218909865089466096653)
                  ·
                    rfl

theorem cell20_767305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_767305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767305 prefixEnd_767305 := by exact prefixLift 767305
  have htrace : WordTrace (prefixWord ++ tailWord_767305) baseStart_767305 baseEnd_767305 := by
    simpa [prefixWord, tailWord_767305, baseEnd_767305] using wordTrace_append hprefix tailTrace_767305
  have hstable : (prefixWord ++ tailWord_767305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767305).length < 2 ^ (prefixWord ++ tailWord_767305).sum := by decide
  have hdescent : baseEnd_767305 < baseStart_767305 := by decide
  rcases family_descends (prefixWord ++ tailWord_767305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767333 : List Nat := [1, 3, 1, 3, 1, 2, 5, 4]
def baseStart_767333 : Nat := 118140960795 + 767333 * 2 ^ 59
def prefixEnd_767333 : Nat := 4983230072969 + 3 ^ 40 * 767333 * 2
def baseEnd_767333 : Nat := 116743896609348604387735

theorem tailTrace_767333 : CollatzResearch.WordTrace tailWord_767333 prefixEnd_767333 116743896609348604387735 := by
  unfold tailWord_767333
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986933729091065888082653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18657955819394043925388435 27986933729091065888082653)
  ·
    refine ⟨10495100148409149708030995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27986933729091065888082653 10495100148409149708030995)
    ·
      refine ⟨15742650222613724562046493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10495100148409149708030995 15742650222613724562046493)
      ·
        refine ⟨5903493833480146710767435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15742650222613724562046493 5903493833480146710767435)
        ·
          refine ⟨8855240750220220066151153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903493833480146710767435 8855240750220220066151153)
          ·
            refine ⟨6641430562665165049613365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8855240750220220066151153 6641430562665165049613365)
            ·
              refine ⟨622634115249859223401253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6641430562665165049613365 622634115249859223401253)
              ·
                refine ⟨116743896609348604387735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622634115249859223401253 116743896609348604387735)
                ·
                  rfl

theorem cell20_767333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 4].length) (baseStart_767333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767333 prefixEnd_767333 := by exact prefixLift 767333
  have htrace : WordTrace (prefixWord ++ tailWord_767333) baseStart_767333 baseEnd_767333 := by
    simpa [prefixWord, tailWord_767333, baseEnd_767333] using wordTrace_append hprefix tailTrace_767333
  have hstable : (prefixWord ++ tailWord_767333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767333).length < 2 ^ (prefixWord ++ tailWord_767333).sum := by decide
  have hdescent : baseEnd_767333 < baseStart_767333 := by decide
  rcases family_descends (prefixWord ++ tailWord_767333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767364 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_767364 : Nat := 118140960795 + 767364 * 2 ^ 59
def prefixEnd_767364 : Nat := 4983230072969 + 3 ^ 40 * 767364 * 2
def baseEnd_767364 : Nat := 350245839072747483129745

theorem tailTrace_767364 : CollatzResearch.WordTrace tailWord_767364 prefixEnd_767364 350245839072747483129745 := by
  unfold tailWord_767364
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994032195989379091230573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18658709594652505454974097 13994032195989379091230573)
  ·
    refine ⟨5247762073496017159211465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13994032195989379091230573 5247762073496017159211465)
    ·
      refine ⟨3935821555122012869408599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5247762073496017159211465 3935821555122012869408599)
      ·
        refine ⟨5903732332683019304112899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3935821555122012869408599 5903732332683019304112899)
        ·
          refine ⟨8855598499024528956169349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903732332683019304112899 8855598499024528956169349)
          ·
            refine ⟨1660424718567099179281753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8855598499024528956169349 1660424718567099179281753)
            ·
              refine ⟨1245318538925324384461315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660424718567099179281753 1245318538925324384461315)
              ·
                refine ⟨1867977808387986576691973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245318538925324384461315 1867977808387986576691973)
                ·
                  refine ⟨350245839072747483129745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867977808387986576691973 350245839072747483129745)
                  ·
                    rfl

theorem cell20_767364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_767364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767364 prefixEnd_767364 := by exact prefixLift 767364
  have htrace : WordTrace (prefixWord ++ tailWord_767364) baseStart_767364 baseEnd_767364 := by
    simpa [prefixWord, tailWord_767364, baseEnd_767364] using wordTrace_append hprefix tailTrace_767364
  have hstable : (prefixWord ++ tailWord_767364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767364).length < 2 ^ (prefixWord ++ tailWord_767364).sum := by decide
  have hdescent : baseEnd_767364 < baseStart_767364 := by decide
  rcases family_descends (prefixWord ++ tailWord_767364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767385 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_767385 : Nat := 118140960795 + 767385 * 2 ^ 59
def prefixEnd_767385 : Nat := 4983230072969 + 3 ^ 40 * 767385 * 2
def baseEnd_767385 : Nat := 350255424044964743429659

theorem tailTrace_767385 : CollatzResearch.WordTrace tailWord_767385 prefixEnd_767385 350255424044964743429659 := by
  unfold tailWord_767385
  simp only [CollatzResearch.WordTrace]
  refine ⟨27988830324902678768975609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18659220216601785845983739 27988830324902678768975609)
  ·
    refine ⟨20991622743677009076731707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27988830324902678768975609 20991622743677009076731707)
    ·
      refine ⟨31487434115515513615097561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20991622743677009076731707 31487434115515513615097561)
      ·
        refine ⟨23615575586636635211323171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31487434115515513615097561 23615575586636635211323171)
        ·
          refine ⟨35423363379954952816984757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23615575586636635211323171 35423363379954952816984757)
          ·
            refine ⟨3320940316870776826592321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35423363379954952816984757 3320940316870776826592321)
            ·
              refine ⟨2490705237653082619944241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3320940316870776826592321 2490705237653082619944241)
              ·
                refine ⟨1868028928239811964958181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490705237653082619944241 1868028928239811964958181)
                ·
                  refine ⟨350255424044964743429659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868028928239811964958181 350255424044964743429659)
                  ·
                    rfl

theorem cell20_767385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_767385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767385 prefixEnd_767385 := by exact prefixLift 767385
  have htrace : WordTrace (prefixWord ++ tailWord_767385) baseStart_767385 baseEnd_767385 := by
    simpa [prefixWord, tailWord_767385, baseEnd_767385] using wordTrace_append hprefix tailTrace_767385
  have hstable : (prefixWord ++ tailWord_767385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767385).length < 2 ^ (prefixWord ++ tailWord_767385).sum := by decide
  have hdescent : baseEnd_767385 < baseStart_767385 := by decide
  rcases family_descends (prefixWord ++ tailWord_767385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767388 : List Nat := [2, 2, 3, 4, 1, 1, 1, 6]
def baseStart_767388 : Nat := 118140960795 + 767388 * 2 ^ 59
def prefixEnd_767388 : Nat := 4983230072969 + 3 ^ 40 * 767388 * 2
def baseEnd_767388 : Nat := 116752264442236688776549

theorem tailTrace_767388 : CollatzResearch.WordTrace tailWord_767388 prefixEnd_767388 116752264442236688776549 := by
  unfold tailWord_767388
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994469871945905140667409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18659293162594540187556545 13994469871945905140667409)
  ·
    refine ⟨10495852403959428855500557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13994469871945905140667409 10495852403959428855500557)
    ·
      refine ⟨3935944651484785820812709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10495852403959428855500557 3935944651484785820812709)
      ·
        refine ⟨737989622153397341402383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3935944651484785820812709 737989622153397341402383)
        ·
          refine ⟨1106984433230096012103575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737989622153397341402383 1106984433230096012103575)
          ·
            refine ⟨1660476649845144018155363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106984433230096012103575 1660476649845144018155363)
            ·
              refine ⟨2490714974767716027233045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660476649845144018155363 2490714974767716027233045)
              ·
                refine ⟨116752264442236688776549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2490714974767716027233045 116752264442236688776549)
                ·
                  rfl

theorem cell20_767388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_767388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767388 prefixEnd_767388 := by exact prefixLift 767388
  have htrace : WordTrace (prefixWord ++ tailWord_767388) baseStart_767388 baseEnd_767388 := by
    simpa [prefixWord, tailWord_767388, baseEnd_767388] using wordTrace_append hprefix tailTrace_767388
  have hstable : (prefixWord ++ tailWord_767388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767388).length < 2 ^ (prefixWord ++ tailWord_767388).sum := by decide
  have hdescent : baseEnd_767388 < baseStart_767388 := by decide
  rcases family_descends (prefixWord ++ tailWord_767388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767392 : List Nat := [2, 1, 1, 4, 1, 2, 3, 6]
def baseStart_767392 : Nat := 118140960795 + 767392 * 2 ^ 59
def prefixEnd_767392 : Nat := 4983230072969 + 3 ^ 40 * 767392 * 2
def baseEnd_767392 : Nat := 116752873011901276732099

theorem tailTrace_767392 : CollatzResearch.WordTrace tailWord_767392 prefixEnd_767392 116752873011901276732099 := by
  unfold tailWord_767392
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994542817938659482240215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18659390423918212642986953 13994542817938659482240215)
  ·
    refine ⟨20991814226907989223360323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13994542817938659482240215 20991814226907989223360323)
    ·
      refine ⟨31487721340361983835040485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20991814226907989223360323 31487721340361983835040485)
      ·
        refine ⟨5903947751317871969070091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31487721340361983835040485 5903947751317871969070091)
        ·
          refine ⟨8855921626976807953605137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903947751317871969070091 8855921626976807953605137)
          ·
            refine ⟨6641941220232605965203853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8855921626976807953605137 6641941220232605965203853)
            ·
              refine ⟨2490727957587227236951445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6641941220232605965203853 2490727957587227236951445)
              ·
                refine ⟨116752873011901276732099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2490727957587227236951445 116752873011901276732099)
                ·
                  rfl

theorem cell20_767392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_767392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767392 prefixEnd_767392 := by exact prefixLift 767392
  have htrace : WordTrace (prefixWord ++ tailWord_767392) baseStart_767392 baseEnd_767392 := by
    simpa [prefixWord, tailWord_767392, baseEnd_767392] using wordTrace_append hprefix tailTrace_767392
  have hstable : (prefixWord ++ tailWord_767392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767392).length < 2 ^ (prefixWord ++ tailWord_767392).sum := by decide
  have hdescent : baseEnd_767392 < baseStart_767392 := by decide
  rcases family_descends (prefixWord ++ tailWord_767392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767474 : List Nat := [3, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_767474 : Nat := 118140960795 + 767474 * 2 ^ 59
def prefixEnd_767474 : Nat := 4983230072969 + 3 ^ 40 * 767474 * 2
def baseEnd_767474 : Nat := 350296046070075989462629

theorem tailTrace_767474 : CollatzResearch.WordTrace tailWord_767474 prefixEnd_767474 350296046070075989462629 := by
  unfold tailWord_767474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998019105395061742241369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18661384281053497979310317 6998019105395061742241369)
  ·
    refine ⟨5248514329046296306681027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6998019105395061742241369 5248514329046296306681027)
    ·
      refine ⟨7872771493569444460021541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5248514329046296306681027 7872771493569444460021541)
      ·
        refine ⟨1476144655044270836254039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7872771493569444460021541 1476144655044270836254039)
        ·
          refine ⟨2214216982566406254381059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476144655044270836254039 2214216982566406254381059)
          ·
            refine ⟨3321325473849609381571589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214216982566406254381059 3321325473849609381571589)
            ·
              refine ⟨622748526346801759044673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3321325473849609381571589 622748526346801759044673)
              ·
                refine ⟨467061394760101319283505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622748526346801759044673 467061394760101319283505)
                ·
                  refine ⟨350296046070075989462629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467061394760101319283505 350296046070075989462629)
                  ·
                    rfl

theorem cell20_767474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_767474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767474 prefixEnd_767474 := by exact prefixLift 767474
  have htrace : WordTrace (prefixWord ++ tailWord_767474) baseStart_767474 baseEnd_767474 := by
    simpa [prefixWord, tailWord_767474, baseEnd_767474] using wordTrace_append hprefix tailTrace_767474
  have hstable : (prefixWord ++ tailWord_767474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767474).length < 2 ^ (prefixWord ++ tailWord_767474).sum := by decide
  have hdescent : baseEnd_767474 < baseStart_767474 := by decide
  rcases family_descends (prefixWord ++ tailWord_767474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767485 : List Nat := [1, 4, 1, 1, 1, 6, 1, 5]
def baseStart_767485 : Nat := 118140960795 + 767485 * 2 ^ 59
def prefixEnd_767485 : Nat := 4983230072969 + 3 ^ 40 * 767485 * 2
def baseEnd_767485 : Nat := 116767022256602946698639

theorem tailTrace_767485 : CollatzResearch.WordTrace tailWord_767485 prefixEnd_767485 116767022256602946698639 := by
  unfold tailWord_767485
  simp only [CollatzResearch.WordTrace]
  refine ⟨27992477624540395847615909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18661651749693597231743939 27992477624540395847615909)
  ·
    refine ⟨5248589554601324221427983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27992477624540395847615909 5248589554601324221427983)
    ·
      refine ⟨7872884331901986332141975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5248589554601324221427983 7872884331901986332141975)
      ·
        refine ⟨11809326497852979498212963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7872884331901986332141975 11809326497852979498212963)
        ·
          refine ⟨17713989746779469247319445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11809326497852979498212963 17713989746779469247319445)
          ·
            refine ⟨830343269380287620968099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17713989746779469247319445 830343269380287620968099)
            ·
              refine ⟨1245514904070431431452149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830343269380287620968099 1245514904070431431452149)
              ·
                refine ⟨116767022256602946698639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1245514904070431431452149 116767022256602946698639)
                ·
                  rfl

theorem cell20_767485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_767485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767485 prefixEnd_767485 := by exact prefixLift 767485
  have htrace : WordTrace (prefixWord ++ tailWord_767485) baseStart_767485 baseEnd_767485 := by
    simpa [prefixWord, tailWord_767485, baseEnd_767485] using wordTrace_append hprefix tailTrace_767485
  have hstable : (prefixWord ++ tailWord_767485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767485).length < 2 ^ (prefixWord ++ tailWord_767485).sum := by decide
  have hdescent : baseEnd_767485 < baseStart_767485 := by decide
  rcases family_descends (prefixWord ++ tailWord_767485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767502 : List Nat := [4, 1, 1, 2, 4, 1, 3, 4]
def baseStart_767502 : Nat := 118140960795 + 767502 * 2 ^ 59
def prefixEnd_767502 : Nat := 4983230072969 + 3 ^ 40 * 767502 * 2
def baseEnd_767502 : Nat := 116769608677677445509727

theorem tailTrace_767502 : CollatzResearch.WordTrace tailWord_767502 prefixEnd_767502 116769608677677445509727 := by
  unfold tailWord_767502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499137208184850968873095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18662065110319205167323173 3499137208184850968873095)
  ·
    refine ⟨5248705812277276453309643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3499137208184850968873095 5248705812277276453309643)
    ·
      refine ⟨7873058718415914679964465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5248705812277276453309643 7873058718415914679964465)
      ·
        refine ⟨5904794038811936009973349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7873058718415914679964465 5904794038811936009973349)
        ·
          refine ⟨1107148882277238001870003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5904794038811936009973349 1107148882277238001870003)
          ·
            refine ⟨1660723323415857002805005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107148882277238001870003 1660723323415857002805005)
            ·
              refine ⟨622771246280946376051877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1660723323415857002805005 622771246280946376051877)
              ·
                refine ⟨116769608677677445509727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622771246280946376051877 116769608677677445509727)
                ·
                  rfl

theorem cell20_767502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_767502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767502 prefixEnd_767502 := by exact prefixLift 767502
  have htrace : WordTrace (prefixWord ++ tailWord_767502) baseStart_767502 baseEnd_767502 := by
    simpa [prefixWord, tailWord_767502, baseEnd_767502] using wordTrace_append hprefix tailTrace_767502
  have hstable : (prefixWord ++ tailWord_767502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767502).length < 2 ^ (prefixWord ++ tailWord_767502).sum := by decide
  have hdescent : baseEnd_767502 < baseStart_767502 := by decide
  rcases family_descends (prefixWord ++ tailWord_767502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767530 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_767530 : Nat := 118140960795 + 767530 * 2 ^ 59
def prefixEnd_767530 : Nat := 4983230072969 + 3 ^ 40 * 767530 * 2
def baseEnd_767530 : Nat := 350321605995988683595733

theorem tailTrace_767530 : CollatzResearch.WordTrace tailWord_767530 prefixEnd_767530 350321605995988683595733 := by
  unfold tailWord_767530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998529727344342133251011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18662745939584912355336029 6998529727344342133251011)
  ·
    refine ⟨10497794591016513199876517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6998529727344342133251011 10497794591016513199876517)
    ·
      refine ⟨1968336485815596224976847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10497794591016513199876517 1968336485815596224976847)
      ·
        refine ⟨2952504728723394337465271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968336485815596224976847 2952504728723394337465271)
        ·
          refine ⟨4428757093085091506197907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952504728723394337465271 4428757093085091506197907)
          ·
            refine ⟨6643135639627637259296861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428757093085091506197907 6643135639627637259296861)
            ·
              refine ⟨2491175864860363972236323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6643135639627637259296861 2491175864860363972236323)
              ·
                refine ⟨3736763797290545958354485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491175864860363972236323 3736763797290545958354485)
                ·
                  refine ⟨350321605995988683595733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3736763797290545958354485 350321605995988683595733)
                  ·
                    rfl

theorem cell20_767530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_767530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767530 prefixEnd_767530 := by exact prefixLift 767530
  have htrace : WordTrace (prefixWord ++ tailWord_767530) baseStart_767530 baseEnd_767530 := by
    simpa [prefixWord, tailWord_767530, baseEnd_767530] using wordTrace_append hprefix tailTrace_767530
  have hstable : (prefixWord ++ tailWord_767530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767530).length < 2 ^ (prefixWord ++ tailWord_767530).sum := by decide
  have hdescent : baseEnd_767530 < baseStart_767530 := by decide
  rcases family_descends (prefixWord ++ tailWord_767530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767574 : List Nat := [5, 2, 2, 2, 2, 1, 6]
def baseStart_767574 : Nat := 118140960795 + 767574 * 2 ^ 59
def prefixEnd_767574 : Nat := 4983230072969 + 3 ^ 40 * 767574 * 2
def baseEnd_767574 : Nat := 38926854310546676236543

theorem tailTrace_767574 : CollatzResearch.WordTrace tailWord_767574 prefixEnd_767574 38926854310546676236543 := by
  unfold tailWord_767574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1749732732576122752975361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18663815814145309365070517 1749732732576122752975361)
  ·
    refine ⟨1312299549432092064731521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1749732732576122752975361 1312299549432092064731521)
    ·
      refine ⟨984224662074069048548641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1312299549432092064731521 984224662074069048548641)
      ·
        refine ⟨738168496555551786411481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 984224662074069048548641 738168496555551786411481)
        ·
          refine ⟨553626372416663839808611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738168496555551786411481 553626372416663839808611)
          ·
            refine ⟨830439558624995759712917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553626372416663839808611 830439558624995759712917)
            ·
              refine ⟨38926854310546676236543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 830439558624995759712917 38926854310546676236543)
              ·
                rfl

theorem cell20_767574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 6].length) (baseStart_767574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767574 prefixEnd_767574 := by exact prefixLift 767574
  have htrace : WordTrace (prefixWord ++ tailWord_767574) baseStart_767574 baseEnd_767574 := by
    simpa [prefixWord, tailWord_767574, baseEnd_767574] using wordTrace_append hprefix tailTrace_767574
  have hstable : (prefixWord ++ tailWord_767574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767574).length < 2 ^ (prefixWord ++ tailWord_767574).sum := by decide
  have hdescent : baseEnd_767574 < baseStart_767574 := by decide
  rcases family_descends (prefixWord ++ tailWord_767574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767592 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_767592 : Nat := 118140960795 + 767592 * 2 ^ 59
def prefixEnd_767592 : Nat := 4983230072969 + 3 ^ 40 * 767592 * 2
def baseEnd_767592 : Nat := 350349904485392023528813

theorem tailTrace_767592 : CollatzResearch.WordTrace tailWord_767592 prefixEnd_767592 350349904485392023528813 := by
  unfold tailWord_767592
  simp only [CollatzResearch.WordTrace]
  refine ⟨13998190117576376560880515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18664253490101835414507353 13998190117576376560880515)
  ·
    refine ⟨20997285176364564841320773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13998190117576376560880515 20997285176364564841320773)
    ·
      refine ⟨3936990970568355907747645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20997285176364564841320773 3936990970568355907747645)
      ·
        refine ⟨1476371613963133465405367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3936990970568355907747645 1476371613963133465405367)
        ·
          refine ⟨2214557420944700198108051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476371613963133465405367 2214557420944700198108051)
          ·
            refine ⟨3321836131417050297162077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214557420944700198108051 3321836131417050297162077)
            ·
              refine ⟨1245688549281393861435779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3321836131417050297162077 1245688549281393861435779)
              ·
                refine ⟨1868532823922090792153669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245688549281393861435779 1868532823922090792153669)
                ·
                  refine ⟨350349904485392023528813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868532823922090792153669 350349904485392023528813)
                  ·
                    rfl

theorem cell20_767592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_767592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767592 prefixEnd_767592 := by exact prefixLift 767592
  have htrace : WordTrace (prefixWord ++ tailWord_767592) baseStart_767592 baseEnd_767592 := by
    simpa [prefixWord, tailWord_767592, baseEnd_767592] using wordTrace_append hprefix tailTrace_767592
  have hstable : (prefixWord ++ tailWord_767592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767592).length < 2 ^ (prefixWord ++ tailWord_767592).sum := by decide
  have hdescent : baseEnd_767592 < baseStart_767592 := by decide
  rcases family_descends (prefixWord ++ tailWord_767592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767602 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_767602 : Nat := 118140960795 + 767602 * 2 ^ 59
def prefixEnd_767602 : Nat := 4983230072969 + 3 ^ 40 * 767602 * 2
def baseEnd_767602 : Nat := 350354468757876433195439

theorem tailTrace_767602 : CollatzResearch.WordTrace tailWord_767602 prefixEnd_767602 350354468757876433195439 := by
  unfold tailWord_767602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6999186241279131207406265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18664496643411016553083373 6999186241279131207406265)
  ·
    refine ⟨5249389680959348405554699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6999186241279131207406265 5249389680959348405554699)
    ·
      refine ⟨7874084521439022608332049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5249389680959348405554699 7874084521439022608332049)
      ·
        refine ⟨5905563391079266956249037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7874084521439022608332049 5905563391079266956249037)
        ·
          refine ⟨2214586271654725108593389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5905563391079266956249037 2214586271654725108593389)
          ·
            refine ⟨830469851870521915722521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2214586271654725108593389 830469851870521915722521)
            ·
              refine ⟨622852388902891436791891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830469851870521915722521 622852388902891436791891)
              ·
                refine ⟨934278583354337155187837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622852388902891436791891 934278583354337155187837)
                ·
                  refine ⟨350354468757876433195439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 934278583354337155187837 350354468757876433195439)
                  ·
                    rfl

theorem cell20_767602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_767602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767602 prefixEnd_767602 := by exact prefixLift 767602
  have htrace : WordTrace (prefixWord ++ tailWord_767602) baseStart_767602 baseEnd_767602 := by
    simpa [prefixWord, tailWord_767602, baseEnd_767602] using wordTrace_append hprefix tailTrace_767602
  have hstable : (prefixWord ++ tailWord_767602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767602).length < 2 ^ (prefixWord ++ tailWord_767602).sum := by decide
  have hdescent : baseEnd_767602 < baseStart_767602 := by decide
  rcases family_descends (prefixWord ++ tailWord_767602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767702 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_767702 : Nat := 118140960795 + 767702 * 2 ^ 59
def prefixEnd_767702 : Nat := 4983230072969 + 3 ^ 40 * 767702 * 2
def baseEnd_767702 : Nat := 350400111482720529861697

theorem tailTrace_767702 : CollatzResearch.WordTrace tailWord_767702 prefixEnd_767702 350400111482720529861697 := by
  unfold tailWord_767702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1750024516547140119266585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18666928176502827938843573 1750024516547140119266585)
  ·
    refine ⟨1312518387410355089449939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1750024516547140119266585 1312518387410355089449939)
    ·
      refine ⟨1968777581115532634174909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312518387410355089449939 1968777581115532634174909)
      ·
        refine ⟨738291592918324737815591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1968777581115532634174909 738291592918324737815591)
        ·
          refine ⟨1107437389377487106723387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738291592918324737815591 1107437389377487106723387)
          ·
            refine ⟨1661156084066230660085081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107437389377487106723387 1661156084066230660085081)
            ·
              refine ⟨1245867063049672995063811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661156084066230660085081 1245867063049672995063811)
              ·
                refine ⟨1868800594574509492595717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245867063049672995063811 1868800594574509492595717)
                ·
                  refine ⟨350400111482720529861697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868800594574509492595717 350400111482720529861697)
                  ·
                    rfl

theorem cell20_767702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_767702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767702 prefixEnd_767702 := by exact prefixLift 767702
  have htrace : WordTrace (prefixWord ++ tailWord_767702) baseStart_767702 baseEnd_767702 := by
    simpa [prefixWord, tailWord_767702, baseEnd_767702] using wordTrace_append hprefix tailTrace_767702
  have hstable : (prefixWord ++ tailWord_767702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767702).length < 2 ^ (prefixWord ++ tailWord_767702).sum := by decide
  have hdescent : baseEnd_767702 < baseStart_767702 := by decide
  rcases family_descends (prefixWord ++ tailWord_767702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767703 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_767703 : Nat := 118140960795 + 767703 * 2 ^ 59
def prefixEnd_767703 : Nat := 4983230072969 + 3 ^ 40 * 767703 * 2
def baseEnd_767703 : Nat := 350400567909968970828359

theorem tailTrace_767703 : CollatzResearch.WordTrace tailWord_767703 prefixEnd_767703 350400567909968970828359 := by
  unfold tailWord_767703
  simp only [CollatzResearch.WordTrace]
  refine ⟨28000428737750619079051763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18666952491833746052701175 28000428737750619079051763)
  ·
    refine ⟨42000643106625928618577645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28000428737750619079051763 42000643106625928618577645)
    ·
      refine ⟨15750241164984723231966617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42000643106625928618577645 15750241164984723231966617)
      ·
        refine ⟨11812680873738542423974963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15750241164984723231966617 11812680873738542423974963)
        ·
          refine ⟨17719021310607813635962445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11812680873738542423974963 17719021310607813635962445)
          ·
            refine ⟨6644632991477930113485917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17719021310607813635962445 6644632991477930113485917)
            ·
              refine ⟨2491737371804223792557219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6644632991477930113485917 2491737371804223792557219)
              ·
                refine ⟨3737606057706335688835829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491737371804223792557219 3737606057706335688835829)
                ·
                  refine ⟨350400567909968970828359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3737606057706335688835829 350400567909968970828359)
                  ·
                    rfl

theorem cell20_767703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_767703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767703 prefixEnd_767703 := by exact prefixLift 767703
  have htrace : WordTrace (prefixWord ++ tailWord_767703) baseStart_767703 baseEnd_767703 := by
    simpa [prefixWord, tailWord_767703, baseEnd_767703] using wordTrace_append hprefix tailTrace_767703
  have hstable : (prefixWord ++ tailWord_767703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767703).length < 2 ^ (prefixWord ++ tailWord_767703).sum := by decide
  have hdescent : baseEnd_767703 < baseStart_767703 := by decide
  rcases family_descends (prefixWord ++ tailWord_767703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767706 : List Nat := [3, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_767706 : Nat := 118140960795 + 767706 * 2 ^ 59
def prefixEnd_767706 : Nat := 4983230072969 + 3 ^ 40 * 767706 * 2
def baseEnd_767706 : Nat := 350401937191714293728347

theorem tailTrace_767706 : CollatzResearch.WordTrace tailWord_767706 prefixEnd_767706 350401937191714293728347 := by
  unfold tailWord_767706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7000134539184937647852743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18667025437826500394273981 7000134539184937647852743)
  ·
    refine ⟨10500201808777406471779115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7000134539184937647852743 10500201808777406471779115)
    ·
      refine ⟨15750302713166109707668673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10500201808777406471779115 15750302713166109707668673)
      ·
        refine ⟨11812727034874582280751505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15750302713166109707668673 11812727034874582280751505)
        ·
          refine ⟨8859545276155936710563629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11812727034874582280751505 8859545276155936710563629)
          ·
            refine ⟨3322329478558476266461361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8859545276155936710563629 3322329478558476266461361)
            ·
              refine ⟨2491747108918857199846021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3322329478558476266461361 2491747108918857199846021)
              ·
                refine ⟨467202582922285724971129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2491747108918857199846021 467202582922285724971129)
                ·
                  refine ⟨350401937191714293728347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467202582922285724971129 350401937191714293728347)
                  ·
                    rfl

theorem cell20_767706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_767706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767706 prefixEnd_767706 := by exact prefixLift 767706
  have htrace : WordTrace (prefixWord ++ tailWord_767706) baseStart_767706 baseEnd_767706 := by
    simpa [prefixWord, tailWord_767706, baseEnd_767706] using wordTrace_append hprefix tailTrace_767706
  have hstable : (prefixWord ++ tailWord_767706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767706).length < 2 ^ (prefixWord ++ tailWord_767706).sum := by decide
  have hdescent : baseEnd_767706 < baseStart_767706 := by decide
  rcases family_descends (prefixWord ++ tailWord_767706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767751 : List Nat := [1, 1, 4, 4, 2, 2, 6]
def baseStart_767751 : Nat := 118140960795 + 767751 * 2 ^ 59
def prefixEnd_767751 : Nat := 4983230072969 + 3 ^ 40 * 767751 * 2
def baseEnd_767751 : Nat := 38935830713099348580907

theorem tailTrace_767751 : CollatzResearch.WordTrace tailWord_767751 prefixEnd_767751 38935830713099348580907 := by
  unfold tailWord_767751
  simp only [CollatzResearch.WordTrace]
  refine ⟨28002179441576723276799107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18668119627717815517866071 28002179441576723276799107)
  ·
    refine ⟨42003269162365084915198661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28002179441576723276799107 42003269162365084915198661)
    ·
      refine ⟨7875612967943453421599749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42003269162365084915198661 7875612967943453421599749)
      ·
        refine ⟨1476677431489397516549953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7875612967943453421599749 1476677431489397516549953)
        ·
          refine ⟨1107508073617048137412465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1476677431489397516549953 1107508073617048137412465)
          ·
            refine ⟨830631055212786103059349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107508073617048137412465 830631055212786103059349)
            ·
              refine ⟨38935830713099348580907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 830631055212786103059349 38935830713099348580907)
              ·
                rfl

theorem cell20_767751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 6].length) (baseStart_767751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767751 prefixEnd_767751 := by exact prefixLift 767751
  have htrace : WordTrace (prefixWord ++ tailWord_767751) baseStart_767751 baseEnd_767751 := by
    simpa [prefixWord, tailWord_767751, baseEnd_767751] using wordTrace_append hprefix tailTrace_767751
  have hstable : (prefixWord ++ tailWord_767751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767751).length < 2 ^ (prefixWord ++ tailWord_767751).sum := by decide
  have hdescent : baseEnd_767751 < baseStart_767751 := by decide
  rcases family_descends (prefixWord ++ tailWord_767751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767755 : List Nat := [1, 1, 1, 1, 5, 1, 10]
def baseStart_767755 : Nat := 118140960795 + 767755 * 2 ^ 59
def prefixEnd_767755 : Nat := 4983230072969 + 3 ^ 40 * 767755 * 2
def baseEnd_767755 : Nat := 38936033569654211232757

theorem tailTrace_767755 : CollatzResearch.WordTrace tailWord_767755 prefixEnd_767755 38936033569654211232757 := by
  unfold tailWord_767755
  simp only [CollatzResearch.WordTrace]
  refine ⟨28002325333562231959944719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18668216889041487973296479 28002325333562231959944719)
  ·
    refine ⟨42003488000343347939917079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28002325333562231959944719 42003488000343347939917079)
    ·
      refine ⟨63005232000515021909875619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42003488000343347939917079 63005232000515021909875619)
      ·
        refine ⟨94507848000772532864813429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63005232000515021909875619 94507848000772532864813429)
        ·
          refine ⟨8860110750072424956076259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94507848000772532864813429 8860110750072424956076259)
          ·
            refine ⟨13290166125108637434114389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8860110750072424956076259 13290166125108637434114389)
            ·
              refine ⟨38936033569654211232757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13290166125108637434114389 38936033569654211232757)
              ·
                rfl

theorem cell20_767755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 10].length) (baseStart_767755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767755 prefixEnd_767755 := by exact prefixLift 767755
  have htrace : WordTrace (prefixWord ++ tailWord_767755) baseStart_767755 baseEnd_767755 := by
    simpa [prefixWord, tailWord_767755, baseEnd_767755] using wordTrace_append hprefix tailTrace_767755
  have hstable : (prefixWord ++ tailWord_767755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767755).length < 2 ^ (prefixWord ++ tailWord_767755).sum := by decide
  have hdescent : baseEnd_767755 < baseStart_767755 := by decide
  rcases family_descends (prefixWord ++ tailWord_767755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767765 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_767765 : Nat := 118140960795 + 767765 * 2 ^ 59
def prefixEnd_767765 : Nat := 4983230072969 + 3 ^ 40 * 767765 * 2
def baseEnd_767765 : Nat := 350428866399372310761439

theorem tailTrace_767765 : CollatzResearch.WordTrace tailWord_767765 prefixEnd_767765 350428866399372310761439 := by
  unfold tailWord_767765
  simp only [CollatzResearch.WordTrace]
  refine ⟨28002690063526003667808749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18668460042350669111872499 28002690063526003667808749)
  ·
    refine ⟨10501008773822251375428281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28002690063526003667808749 10501008773822251375428281)
    ·
      refine ⟨7875756580366688531571211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10501008773822251375428281 7875756580366688531571211)
      ·
        refine ⟨11813634870550032797356817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7875756580366688531571211 11813634870550032797356817)
        ·
          refine ⟨8860226152912524598017613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11813634870550032797356817 8860226152912524598017613)
          ·
            refine ⟨3322584807342196724256605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8860226152912524598017613 3322584807342196724256605)
            ·
              refine ⟨1245969302753323771596227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3322584807342196724256605 1245969302753323771596227)
              ·
                refine ⟨1868953954129985657394341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245969302753323771596227 1868953954129985657394341)
                ·
                  refine ⟨350428866399372310761439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868953954129985657394341 350428866399372310761439)
                  ·
                    rfl

theorem cell20_767765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_767765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767765 prefixEnd_767765 := by exact prefixLift 767765
  have htrace : WordTrace (prefixWord ++ tailWord_767765) baseStart_767765 baseEnd_767765 := by
    simpa [prefixWord, tailWord_767765, baseEnd_767765] using wordTrace_append hprefix tailTrace_767765
  have hstable : (prefixWord ++ tailWord_767765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767765).length < 2 ^ (prefixWord ++ tailWord_767765).sum := by decide
  have hdescent : baseEnd_767765 < baseStart_767765 := by decide
  rcases family_descends (prefixWord ++ tailWord_767765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767772 : List Nat := [2, 2, 3, 1, 1, 2, 4, 5]
def baseStart_767772 : Nat := 118140960795 + 767772 * 2 ^ 59
def prefixEnd_767772 : Nat := 4983230072969 + 3 ^ 40 * 767772 * 2
def baseEnd_767772 : Nat := 116810687130037132509359

theorem tailTrace_767772 : CollatzResearch.WordTrace tailWord_767772 prefixEnd_767772 116810687130037132509359 := by
  unfold tailWord_767772
  simp only [CollatzResearch.WordTrace]
  refine ⟨14001472687250321931656785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18668630249667095908875713 14001472687250321931656785)
  ·
    refine ⟨10501104515437741448742589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14001472687250321931656785 10501104515437741448742589)
    ·
      refine ⟨3937914193289153043278471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10501104515437741448742589 3937914193289153043278471)
      ·
        refine ⟨5906871289933729564917707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937914193289153043278471 5906871289933729564917707)
        ·
          refine ⟨8860306934900594347376561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5906871289933729564917707 8860306934900594347376561)
          ·
            refine ⟨6645230201175445760532421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8860306934900594347376561 6645230201175445760532421)
            ·
              refine ⟨1245980662720396080099829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6645230201175445760532421 1245980662720396080099829)
              ·
                refine ⟨116810687130037132509359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1245980662720396080099829 116810687130037132509359)
                ·
                  rfl

theorem cell20_767772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_767772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767772 prefixEnd_767772 := by exact prefixLift 767772
  have htrace : WordTrace (prefixWord ++ tailWord_767772) baseStart_767772 baseEnd_767772 := by
    simpa [prefixWord, tailWord_767772, baseEnd_767772] using wordTrace_append hprefix tailTrace_767772
  have hstable : (prefixWord ++ tailWord_767772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767772).length < 2 ^ (prefixWord ++ tailWord_767772).sum := by decide
  have hdescent : baseEnd_767772 < baseStart_767772 := by decide
  rcases family_descends (prefixWord ++ tailWord_767772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767824 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_767824 : Nat := 118140960795 + 767824 * 2 ^ 59
def prefixEnd_767824 : Nat := 4983230072969 + 3 ^ 40 * 767824 * 2
def baseEnd_767824 : Nat := 350455795607030327794531

theorem tailTrace_767824 : CollatzResearch.WordTrace tailWord_767824 prefixEnd_767824 350455795607030327794531 := by
  unfold tailWord_767824
  simp only [CollatzResearch.WordTrace]
  refine ⟨14002420985156128372103263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18669894646874837829471017 14002420985156128372103263)
  ·
    refine ⟨21003631477734192558154895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14002420985156128372103263 21003631477734192558154895)
    ·
      refine ⟨31505447216601288837232343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21003631477734192558154895 31505447216601288837232343)
      ·
        refine ⟨47258170824901933255848515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31505447216601288837232343 47258170824901933255848515)
        ·
          refine ⟨70887256237352899883772773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47258170824901933255848515 70887256237352899883772773)
          ·
            refine ⟨13291360544503668728207395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70887256237352899883772773 13291360544503668728207395)
            ·
              refine ⟨19937040816755503092311093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13291360544503668728207395 19937040816755503092311093)
              ·
                refine ⟨1869097576570828414904165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19937040816755503092311093 1869097576570828414904165)
                ·
                  refine ⟨350455795607030327794531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1869097576570828414904165 350455795607030327794531)
                  ·
                    rfl

theorem cell20_767824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_767824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767824 prefixEnd_767824 := by exact prefixLift 767824
  have htrace : WordTrace (prefixWord ++ tailWord_767824) baseStart_767824 baseEnd_767824 := by
    simpa [prefixWord, tailWord_767824, baseEnd_767824] using wordTrace_append hprefix tailTrace_767824
  have hstable : (prefixWord ++ tailWord_767824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767824).length < 2 ^ (prefixWord ++ tailWord_767824).sum := by decide
  have hdescent : baseEnd_767824 < baseStart_767824 := by decide
  rcases family_descends (prefixWord ++ tailWord_767824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767934 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_767934 : Nat := 118140960795 + 767934 * 2 ^ 59
def prefixEnd_767934 : Nat := 4983230072969 + 3 ^ 40 * 767934 * 2
def baseEnd_767934 : Nat := 350506002604358834127415

theorem tailTrace_767934 : CollatzResearch.WordTrace tailWord_767934 prefixEnd_767934 350506002604358834127415 := by
  unfold tailWord_767934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3501106749989218191338857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18672569333275830353807237 3501106749989218191338857)
  ·
    refine ⟨2625830062491913643504143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3501106749989218191338857 2625830062491913643504143)
    ·
      refine ⟨3938745093737870465256215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2625830062491913643504143 3938745093737870465256215)
      ·
        refine ⟨5908117640606805697884323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3938745093737870465256215 5908117640606805697884323)
        ·
          refine ⟨8862176460910208546826485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5908117640606805697884323 8862176460910208546826485)
          ·
            refine ⟨830829043210332051264983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8862176460910208546826485 830829043210332051264983)
            ·
              refine ⟨1246243564815498076897475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830829043210332051264983 1246243564815498076897475)
              ·
                refine ⟨1869365347223247115346213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246243564815498076897475 1869365347223247115346213)
                ·
                  refine ⟨350506002604358834127415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1869365347223247115346213 350506002604358834127415)
                  ·
                    rfl

theorem cell20_767934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_767934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767934 prefixEnd_767934 := by exact prefixLift 767934
  have htrace : WordTrace (prefixWord ++ tailWord_767934) baseStart_767934 baseEnd_767934 := by
    simpa [prefixWord, tailWord_767934, baseEnd_767934] using wordTrace_append hprefix tailTrace_767934
  have hstable : (prefixWord ++ tailWord_767934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767934).length < 2 ^ (prefixWord ++ tailWord_767934).sum := by decide
  have hdescent : baseEnd_767934 < baseStart_767934 := by decide
  rcases family_descends (prefixWord ++ tailWord_767934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_767948 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_767948 : Nat := 118140960795 + 767948 * 2 ^ 59
def prefixEnd_767948 : Nat := 4983230072969 + 3 ^ 40 * 767948 * 2
def baseEnd_767948 : Nat := 350512392585837007660691

theorem tailTrace_767948 : CollatzResearch.WordTrace tailWord_767948 prefixEnd_767948 350512392585837007660691 := by
  unfold tailWord_767948
  simp only [CollatzResearch.WordTrace]
  refine ⟨14004682310931512960860249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18672909747908683947813665 14004682310931512960860249)
  ·
    refine ⟨10503511733198634720645187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14004682310931512960860249 10503511733198634720645187)
    ·
      refine ⟨15755267599797952080967781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10503511733198634720645187 15755267599797952080967781)
      ·
        refine ⟨2954112674962116015181459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15755267599797952080967781 2954112674962116015181459)
        ·
          refine ⟨4431169012443174022772189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954112674962116015181459 4431169012443174022772189)
          ·
            refine ⟨1661688379666190258539571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4431169012443174022772189 1661688379666190258539571)
            ·
              refine ⟨2492532569499285387809357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661688379666190258539571 2492532569499285387809357)
              ·
                refine ⟨934699713562232020428509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2492532569499285387809357 934699713562232020428509)
                ·
                  refine ⟨350512392585837007660691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 934699713562232020428509 350512392585837007660691)
                  ·
                    rfl

theorem cell20_767948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_767948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_767948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_767948 prefixEnd_767948 := by exact prefixLift 767948
  have htrace : WordTrace (prefixWord ++ tailWord_767948) baseStart_767948 baseEnd_767948 := by
    simpa [prefixWord, tailWord_767948, baseEnd_767948] using wordTrace_append hprefix tailTrace_767948
  have hstable : (prefixWord ++ tailWord_767948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_767948).length < 2 ^ (prefixWord ++ tailWord_767948).sum := by decide
  have hdescent : baseEnd_767948 < baseStart_767948 := by decide
  rcases family_descends (prefixWord ++ tailWord_767948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768076 : List Nat := [2, 2, 1, 3, 1, 1, 6, 4]
def baseStart_768076 : Nat := 118140960795 + 768076 * 2 ^ 59
def prefixEnd_768076 : Nat := 4983230072969 + 3 ^ 40 * 768076 * 2
def baseEnd_768076 : Nat := 116856938424545817131167

theorem tailTrace_768076 : CollatzResearch.WordTrace tailWord_768076 prefixEnd_768076 116856938424545817131167 := by
  unfold tailWord_768076
  simp only [CollatzResearch.WordTrace]
  refine ⟨14007016582699651891190041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18676022110266202521586721 14007016582699651891190041)
  ·
    refine ⟨10505262437024738918392531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14007016582699651891190041 10505262437024738918392531)
    ·
      refine ⟨15757893655537108377588797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10505262437024738918392531 15757893655537108377588797)
      ·
        refine ⟨5909210120826415641595799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15757893655537108377588797 5909210120826415641595799)
        ·
          refine ⟨8863815181239623462393699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909210120826415641595799 8863815181239623462393699)
          ·
            refine ⟨13295722771859435193590549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8863815181239623462393699 13295722771859435193590549)
            ·
              refine ⟨623237004930911024699557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13295722771859435193590549 623237004930911024699557)
              ·
                refine ⟨116856938424545817131167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623237004930911024699557 116856938424545817131167)
                ·
                  rfl

theorem cell20_768076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_768076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768076 prefixEnd_768076 := by exact prefixLift 768076
  have htrace : WordTrace (prefixWord ++ tailWord_768076) baseStart_768076 baseEnd_768076 := by
    simpa [prefixWord, tailWord_768076, baseEnd_768076] using wordTrace_append hprefix tailTrace_768076
  have hstable : (prefixWord ++ tailWord_768076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768076).length < 2 ^ (prefixWord ++ tailWord_768076).sum := by decide
  have hdescent : baseEnd_768076 < baseStart_768076 := by decide
  rcases family_descends (prefixWord ++ tailWord_768076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768082 : List Nat := [3, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_768082 : Nat := 118140960795 + 768082 * 2 ^ 59
def prefixEnd_768082 : Nat := 4983230072969 + 3 ^ 40 * 768082 * 2
def baseEnd_768082 : Nat := 350573553837128097193477

theorem tailTrace_768082 : CollatzResearch.WordTrace tailWord_768082 prefixEnd_768082 350573553837128097193477 := by
  unfold tailWord_768082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003563000844391701774625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18676168002251711204732333 7003563000844391701774625)
  ·
    refine ⟨5252672250633293776330969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7003563000844391701774625 5252672250633293776330969)
    ·
      refine ⟨3939504187974970332248227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5252672250633293776330969 3939504187974970332248227)
      ·
        refine ⟨5909256281962455498372341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939504187974970332248227 5909256281962455498372341)
        ·
          refine ⟨553992776433980202972407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5909256281962455498372341 553992776433980202972407)
          ·
            refine ⟨830989164650970304458611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553992776433980202972407 830989164650970304458611)
            ·
              refine ⟨1246483746976455456687917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830989164650970304458611 1246483746976455456687917)
              ·
                refine ⟨467431405116170796257969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1246483746976455456687917 467431405116170796257969)
                ·
                  refine ⟨350573553837128097193477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467431405116170796257969 350573553837128097193477)
                  ·
                    rfl

theorem cell20_768082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_768082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768082 prefixEnd_768082 := by exact prefixLift 768082
  have htrace : WordTrace (prefixWord ++ tailWord_768082) baseStart_768082 baseEnd_768082 := by
    simpa [prefixWord, tailWord_768082, baseEnd_768082] using wordTrace_append hprefix tailTrace_768082
  have hstable : (prefixWord ++ tailWord_768082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768082).length < 2 ^ (prefixWord ++ tailWord_768082).sum := by decide
  have hdescent : baseEnd_768082 < baseStart_768082 := by decide
  rcases family_descends (prefixWord ++ tailWord_768082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768093 : List Nat := [1, 4, 4, 1, 1, 3, 6]
def baseStart_768093 : Nat := 118140960795 + 768093 * 2 ^ 59
def prefixEnd_768093 : Nat := 4983230072969 + 3 ^ 40 * 768093 * 2
def baseEnd_768093 : Nat := 38953174948540105314085

theorem tailTrace_768093 : CollatzResearch.WordTrace tailWord_768093 prefixEnd_768093 38953174948540105314085 := by
  unfold tailWord_768093
  simp only [CollatzResearch.WordTrace]
  refine ⟨28014653206337715685748933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18676435470891810457165955 28014653206337715685748933)
  ·
    refine ⟨5252747476188321691077925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28014653206337715685748933 5252747476188321691077925)
    ·
      refine ⟨984890151785310317077111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5252747476188321691077925 984890151785310317077111)
      ·
        refine ⟨1477335227677965475615667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984890151785310317077111 1477335227677965475615667)
        ·
          refine ⟨2216002841516948213423501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477335227677965475615667 2216002841516948213423501)
          ·
            refine ⟨831001065568855580033813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2216002841516948213423501 831001065568855580033813)
            ·
              refine ⟨38953174948540105314085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 831001065568855580033813 38953174948540105314085)
              ·
                rfl

theorem cell20_768093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 6].length) (baseStart_768093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768093 prefixEnd_768093 := by exact prefixLift 768093
  have htrace : WordTrace (prefixWord ++ tailWord_768093) baseStart_768093 baseEnd_768093 := by
    simpa [prefixWord, tailWord_768093, baseEnd_768093] using wordTrace_append hprefix tailTrace_768093
  have hstable : (prefixWord ++ tailWord_768093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768093).length < 2 ^ (prefixWord ++ tailWord_768093).sum := by decide
  have hdescent : baseEnd_768093 < baseStart_768093 := by decide
  rcases family_descends (prefixWord ++ tailWord_768093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768114 : List Nat := [3, 2, 1, 2, 2, 3, 2, 5]
def baseStart_768114 : Nat := 118140960795 + 768114 * 2 ^ 59
def prefixEnd_768114 : Nat := 4983230072969 + 3 ^ 40 * 768114 * 2
def baseEnd_768114 : Nat := 116862719836359402708893

theorem tailTrace_768114 : CollatzResearch.WordTrace tailWord_768114 prefixEnd_768114 116862719836359402708893 := by
  unfold tailWord_768114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003854784815409068065849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18676946092841090848175597 7003854784815409068065849)
  ·
    refine ⟨5252891088611556801049387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7003854784815409068065849 5252891088611556801049387)
    ·
      refine ⟨7879336632917335201574081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5252891088611556801049387 7879336632917335201574081)
      ·
        refine ⟨5909502474688001401180561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7879336632917335201574081 5909502474688001401180561)
        ·
          refine ⟨4432126856016001050885421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5909502474688001401180561 4432126856016001050885421)
          ·
            refine ⟨1662047571006000394082033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4432126856016001050885421 1662047571006000394082033)
            ·
              refine ⟨1246535678254500295561525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1662047571006000394082033 1246535678254500295561525)
              ·
                refine ⟨116862719836359402708893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1246535678254500295561525 116862719836359402708893)
                ·
                  rfl

theorem cell20_768114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_768114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768114 prefixEnd_768114 := by exact prefixLift 768114
  have htrace : WordTrace (prefixWord ++ tailWord_768114) baseStart_768114 baseEnd_768114 := by
    simpa [prefixWord, tailWord_768114, baseEnd_768114] using wordTrace_append hprefix tailTrace_768114
  have hstable : (prefixWord ++ tailWord_768114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768114).length < 2 ^ (prefixWord ++ tailWord_768114).sum := by decide
  have hdescent : baseEnd_768114 < baseStart_768114 := by decide
  rcases family_descends (prefixWord ++ tailWord_768114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768135 : List Nat := [1, 1, 4, 2, 1, 1, 4, 6]
def baseStart_768135 : Nat := 118140960795 + 768135 * 2 ^ 59
def prefixEnd_768135 : Nat := 4983230072969 + 3 ^ 40 * 768135 * 2
def baseEnd_768135 : Nat := 116865914827098489475531

theorem tailTrace_768135 : CollatzResearch.WordTrace tailWord_768135 prefixEnd_768135 116865914827098489475531 := by
  unfold tailWord_768135
  simp only [CollatzResearch.WordTrace]
  refine ⟨28016185072185556858777859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18677456714790371239185239 28016185072185556858777859)
  ·
    refine ⟨42024277608278335288166789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28016185072185556858777859 42024277608278335288166789)
    ·
      refine ⟨7879552051552187866531273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42024277608278335288166789 7879552051552187866531273)
      ·
        refine ⟨5909664038664140899898455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7879552051552187866531273 5909664038664140899898455)
        ·
          refine ⟨8864496057996211349847683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909664038664140899898455 8864496057996211349847683)
          ·
            refine ⟨13296744086994317024771525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8864496057996211349847683 13296744086994317024771525)
            ·
              refine ⟨2493139516311434442144661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13296744086994317024771525 2493139516311434442144661)
              ·
                refine ⟨116865914827098489475531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2493139516311434442144661 116865914827098489475531)
                ·
                  rfl

theorem cell20_768135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_768135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768135 prefixEnd_768135 := by exact prefixLift 768135
  have htrace : WordTrace (prefixWord ++ tailWord_768135) baseStart_768135 baseEnd_768135 := by
    simpa [prefixWord, tailWord_768135, baseEnd_768135] using wordTrace_append hprefix tailTrace_768135
  have hstable : (prefixWord ++ tailWord_768135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768135).length < 2 ^ (prefixWord ++ tailWord_768135).sum := by decide
  have hdescent : baseEnd_768135 < baseStart_768135 := by decide
  rcases family_descends (prefixWord ++ tailWord_768135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768150 : List Nat := [5, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_768150 : Nat := 118140960795 + 768150 * 2 ^ 59
def prefixEnd_768150 : Nat := 4983230072969 + 3 ^ 40 * 768150 * 2
def baseEnd_768150 : Nat := 350604590890022082926533

theorem tailTrace_768150 : CollatzResearch.WordTrace tailWord_768150 prefixEnd_768150 350604590890022082926533 := by
  unfold tailWord_768150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1751045760445700901285869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18677821444754142947049269 1751045760445700901285869)
  ·
    refine ⟨656642160167137837982201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1751045760445700901285869 656642160167137837982201)
    ·
      refine ⟨492481620125353378486651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 656642160167137837982201 492481620125353378486651)
      ·
        refine ⟨738722430188030067729977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492481620125353378486651 738722430188030067729977)
        ·
          refine ⟨554041822641022550797483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738722430188030067729977 554041822641022550797483)
          ·
            refine ⟨831062733961533826196225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554041822641022550797483 831062733961533826196225)
            ·
              refine ⟨623297050471150369647169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831062733961533826196225 623297050471150369647169)
              ·
                refine ⟨467472787853362777235377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623297050471150369647169 467472787853362777235377)
                ·
                  refine ⟨350604590890022082926533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467472787853362777235377 350604590890022082926533)
                  ·
                    rfl

theorem cell20_768150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_768150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768150 prefixEnd_768150 := by exact prefixLift 768150
  have htrace : WordTrace (prefixWord ++ tailWord_768150) baseStart_768150 baseEnd_768150 := by
    simpa [prefixWord, tailWord_768150, baseEnd_768150] using wordTrace_append hprefix tailTrace_768150
  have hstable : (prefixWord ++ tailWord_768150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768150).length < 2 ^ (prefixWord ++ tailWord_768150).sum := by decide
  have hdescent : baseEnd_768150 < baseStart_768150 := by decide
  rcases family_descends (prefixWord ++ tailWord_768150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768152 : List Nat := [2, 1, 2, 4, 4, 7]
def baseStart_768152 : Nat := 118140960795 + 768152 * 2 ^ 59
def prefixEnd_768152 : Nat := 4983230072969 + 3 ^ 40 * 768152 * 2
def baseEnd_768152 : Nat := 12985389027574776476291

theorem tailTrace_768152 : CollatzResearch.WordTrace tailWord_768152 prefixEnd_768152 12985389027574776476291 := by
  unfold tailWord_768152
  simp only [CollatzResearch.WordTrace]
  refine ⟨14008402556561984381073355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18677870075415979174764473 14008402556561984381073355)
  ·
    refine ⟨21012603834842976571610033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14008402556561984381073355 21012603834842976571610033)
    ·
      refine ⟨15759452876132232428707525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21012603834842976571610033 15759452876132232428707525)
      ·
        refine ⟨2954897414274793580382661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15759452876132232428707525 2954897414274793580382661)
        ·
          refine ⟨554043265176523796321749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2954897414274793580382661 554043265176523796321749)
          ·
            refine ⟨12985389027574776476291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 554043265176523796321749 12985389027574776476291)
            ·
              rfl

theorem cell20_768152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 7].length) (baseStart_768152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768152 prefixEnd_768152 := by exact prefixLift 768152
  have htrace : WordTrace (prefixWord ++ tailWord_768152) baseStart_768152 baseEnd_768152 := by
    simpa [prefixWord, tailWord_768152, baseEnd_768152] using wordTrace_append hprefix tailTrace_768152
  have hstable : (prefixWord ++ tailWord_768152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768152).length < 2 ^ (prefixWord ++ tailWord_768152).sum := by decide
  have hdescent : baseEnd_768152 < baseStart_768152 := by decide
  rcases family_descends (prefixWord ++ tailWord_768152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768221 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_768221 : Nat := 118140960795 + 768221 * 2 ^ 59
def prefixEnd_768221 : Nat := 4983230072969 + 3 ^ 40 * 768221 * 2
def baseEnd_768221 : Nat := 350636997224661391559575

theorem tailTrace_768221 : CollatzResearch.WordTrace tailWord_768221 prefixEnd_768221 350636997224661391559575 := by
  unfold tailWord_768221
  simp only [CollatzResearch.WordTrace]
  refine ⟨28019321749873993546408517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18679547833249329030939011 28019321749873993546408517)
  ·
    refine ⟨5253622828101373789951597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28019321749873993546408517 5253622828101373789951597)
    ·
      refine ⟨1970108560538015171231849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5253622828101373789951597 1970108560538015171231849)
      ·
        refine ⟨1477581420403511378423887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1970108560538015171231849 1477581420403511378423887)
        ·
          refine ⟨2216372130605267067635831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477581420403511378423887 2216372130605267067635831)
          ·
            refine ⟨3324558195907900601453747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216372130605267067635831 3324558195907900601453747)
            ·
              refine ⟨4986837293861850902180621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3324558195907900601453747 4986837293861850902180621)
              ·
                refine ⟨1870063985198194088317733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4986837293861850902180621 1870063985198194088317733)
                ·
                  refine ⟨350636997224661391559575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870063985198194088317733 350636997224661391559575)
                  ·
                    rfl

theorem cell20_768221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_768221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768221 prefixEnd_768221 := by exact prefixLift 768221
  have htrace : WordTrace (prefixWord ++ tailWord_768221) baseStart_768221 baseEnd_768221 := by
    simpa [prefixWord, tailWord_768221, baseEnd_768221] using wordTrace_append hprefix tailTrace_768221
  have hstable : (prefixWord ++ tailWord_768221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768221).length < 2 ^ (prefixWord ++ tailWord_768221).sum := by decide
  have hdescent : baseEnd_768221 < baseStart_768221 := by decide
  rcases family_descends (prefixWord ++ tailWord_768221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768231 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 3]
def baseStart_768231 : Nat := 118140960795 + 768231 * 2 ^ 59
def prefixEnd_768231 : Nat := 4983230072969 + 3 ^ 40 * 768231 * 2
def baseEnd_768231 : Nat := 350641561497145801226201

theorem tailTrace_768231 : CollatzResearch.WordTrace tailWord_768231 prefixEnd_768231 350641561497145801226201 := by
  unfold tailWord_768231
  simp only [CollatzResearch.WordTrace]
  refine ⟨28019686479837765254272547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18679790986558510169515031 28019686479837765254272547)
  ·
    refine ⟨42029529719756647881408821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28019686479837765254272547 42029529719756647881408821)
    ·
      refine ⟨3940268411227185738882077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42029529719756647881408821 3940268411227185738882077)
      ·
        refine ⟨1477600654210194652080779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3940268411227185738882077 1477600654210194652080779)
        ·
          refine ⟨2216400981315291978121169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477600654210194652080779 2216400981315291978121169)
          ·
            refine ⟨1662300735986468983590877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2216400981315291978121169 1662300735986468983590877)
            ·
              refine ⟨623362775994925868846579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1662300735986468983590877 623362775994925868846579)
              ·
                refine ⟨935044163992388803269869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623362775994925868846579 935044163992388803269869)
                ·
                  refine ⟨350641561497145801226201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935044163992388803269869 350641561497145801226201)
                  ·
                    rfl

theorem cell20_768231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 3].length) (baseStart_768231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768231 prefixEnd_768231 := by exact prefixLift 768231
  have htrace : WordTrace (prefixWord ++ tailWord_768231) baseStart_768231 baseEnd_768231 := by
    simpa [prefixWord, tailWord_768231, baseEnd_768231] using wordTrace_append hprefix tailTrace_768231
  have hstable : (prefixWord ++ tailWord_768231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768231).length < 2 ^ (prefixWord ++ tailWord_768231).sum := by decide
  have hdescent : baseEnd_768231 < baseStart_768231 := by decide
  rcases family_descends (prefixWord ++ tailWord_768231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768256 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_768256 : Nat := 118140960795 + 768256 * 2 ^ 59
def prefixEnd_768256 : Nat := 4983230072969 + 3 ^ 40 * 768256 * 2
def baseEnd_768256 : Nat := 350652972178356825392765

theorem tailTrace_768256 : CollatzResearch.WordTrace tailWord_768256 prefixEnd_768256 350652972178356825392765 := by
  unfold tailWord_768256
  simp only [CollatzResearch.WordTrace]
  refine ⟨14010299152373597261966311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18680398869831463015955081 14010299152373597261966311)
  ·
    refine ⟨21015448728560395892949467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14010299152373597261966311 21015448728560395892949467)
    ·
      refine ⟨31523173092840593839424201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21015448728560395892949467 31523173092840593839424201)
      ·
        refine ⟨23642379819630445379568151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31523173092840593839424201 23642379819630445379568151)
        ·
          refine ⟨35463569729445668069352227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23642379819630445379568151 35463569729445668069352227)
          ·
            refine ⟨53195354594168502104028341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35463569729445668069352227 53195354594168502104028341)
            ·
              refine ⟨4987064493203297072252657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53195354594168502104028341 4987064493203297072252657)
              ·
                refine ⟨3740298369902472804189493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4987064493203297072252657 3740298369902472804189493)
                ·
                  refine ⟨350652972178356825392765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3740298369902472804189493 350652972178356825392765)
                  ·
                    rfl

theorem cell20_768256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_768256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768256 prefixEnd_768256 := by exact prefixLift 768256
  have htrace : WordTrace (prefixWord ++ tailWord_768256) baseStart_768256 baseEnd_768256 := by
    simpa [prefixWord, tailWord_768256, baseEnd_768256] using wordTrace_append hprefix tailTrace_768256
  have hstable : (prefixWord ++ tailWord_768256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768256).length < 2 ^ (prefixWord ++ tailWord_768256).sum := by decide
  have hdescent : baseEnd_768256 < baseStart_768256 := by decide
  rcases family_descends (prefixWord ++ tailWord_768256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768286 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_768286 : Nat := 118140960795 + 768286 * 2 ^ 59
def prefixEnd_768286 : Nat := 4983230072969 + 3 ^ 40 * 768286 * 2
def baseEnd_768286 : Nat := 350666664995810054392643

theorem tailTrace_768286 : CollatzResearch.WordTrace tailWord_768286 prefixEnd_768286 350666664995810054392643 := by
  unfold tailWord_768286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3502711561829813705940589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18681128329759006431683141 3502711561829813705940589)
  ·
    refine ⟨1313516835686180139727721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3502711561829813705940589 1313516835686180139727721)
    ·
      refine ⟨985137626764635104795791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1313516835686180139727721 985137626764635104795791)
      ·
        refine ⟨1477706440146952657193687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985137626764635104795791 1477706440146952657193687)
        ·
          refine ⟨2216559660220428985790531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477706440146952657193687 2216559660220428985790531)
          ·
            refine ⟨3324839490330643478685797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216559660220428985790531 3324839490330643478685797)
            ·
              refine ⟨623407404436995652253587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3324839490330643478685797 623407404436995652253587)
              ·
                refine ⟨935111106655493478380381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623407404436995652253587 935111106655493478380381)
                ·
                  refine ⟨350666664995810054392643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935111106655493478380381 350666664995810054392643)
                  ·
                    rfl

theorem cell20_768286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_768286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768286 prefixEnd_768286 := by exact prefixLift 768286
  have htrace : WordTrace (prefixWord ++ tailWord_768286) baseStart_768286 baseEnd_768286 := by
    simpa [prefixWord, tailWord_768286, baseEnd_768286] using wordTrace_append hprefix tailTrace_768286
  have hstable : (prefixWord ++ tailWord_768286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768286).length < 2 ^ (prefixWord ++ tailWord_768286).sum := by decide
  have hdescent : baseEnd_768286 < baseStart_768286 := by decide
  rcases family_descends (prefixWord ++ tailWord_768286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768287 : List Nat := [1, 1, 2, 4, 3, 1, 1, 7]
def baseStart_768287 : Nat := 118140960795 + 768287 * 2 ^ 59
def prefixEnd_768287 : Nat := 4983230072969 + 3 ^ 40 * 768287 * 2
def baseEnd_768287 : Nat := 116889040474352831786435

theorem tailTrace_768287 : CollatzResearch.WordTrace tailWord_768287 prefixEnd_768287 116889040474352831786435 := by
  unfold tailWord_768287
  simp only [CollatzResearch.WordTrace]
  refine ⟨28021728967634886818311115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18681152645089924545540743 28021728967634886818311115)
  ·
    refine ⟨42032593451452330227466673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28021728967634886818311115 42032593451452330227466673)
    ·
      refine ⟨31524445088589247670600005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42032593451452330227466673 31524445088589247670600005)
      ·
        refine ⟨5910833454110483938237501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31524445088589247670600005 5910833454110483938237501)
        ·
          refine ⟨2216562545291431476839063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5910833454110483938237501 2216562545291431476839063)
          ·
            refine ⟨3324843817937147215258595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216562545291431476839063 3324843817937147215258595)
            ·
              refine ⟨4987265726905720822887893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3324843817937147215258595 4987265726905720822887893)
              ·
                refine ⟨116889040474352831786435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4987265726905720822887893 116889040474352831786435)
                ·
                  rfl

theorem cell20_768287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_768287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768287 prefixEnd_768287 := by exact prefixLift 768287
  have htrace : WordTrace (prefixWord ++ tailWord_768287) baseStart_768287 baseEnd_768287 := by
    simpa [prefixWord, tailWord_768287, baseEnd_768287] using wordTrace_append hprefix tailTrace_768287
  have hstable : (prefixWord ++ tailWord_768287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768287).length < 2 ^ (prefixWord ++ tailWord_768287).sum := by decide
  have hdescent : baseEnd_768287 < baseStart_768287 := by decide
  rcases family_descends (prefixWord ++ tailWord_768287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768290 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_768290 : Nat := 118140960795 + 768290 * 2 ^ 59
def prefixEnd_768290 : Nat := 4983230072969 + 3 ^ 40 * 768290 * 2
def baseEnd_768290 : Nat := 350668490704803818259293

theorem tailTrace_768290 : CollatzResearch.WordTrace tailWord_768290 prefixEnd_768290 350668490704803818259293 := by
  unfold tailWord_768290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7005459596656004582667581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18681225591082678887113549 7005459596656004582667581)
  ·
    refine ⟨2627047348746001718500343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7005459596656004582667581 2627047348746001718500343)
    ·
      refine ⟨3940571023119002577750515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2627047348746001718500343 3940571023119002577750515)
      ·
        refine ⟨5910856534678503866625773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940571023119002577750515 5910856534678503866625773)
        ·
          refine ⟨2216571200504438949984665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5910856534678503866625773 2216571200504438949984665)
          ·
            refine ⟨1662428400378329212488499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2216571200504438949984665 1662428400378329212488499)
            ·
              refine ⟨2493642600567493818732749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662428400378329212488499 2493642600567493818732749)
              ·
                refine ⟨935115975212810182024781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2493642600567493818732749 935115975212810182024781)
                ·
                  refine ⟨350668490704803818259293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935115975212810182024781 350668490704803818259293)
                  ·
                    rfl

theorem cell20_768290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_768290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768290 prefixEnd_768290 := by exact prefixLift 768290
  have htrace : WordTrace (prefixWord ++ tailWord_768290) baseStart_768290 baseEnd_768290 := by
    simpa [prefixWord, tailWord_768290, baseEnd_768290] using wordTrace_append hprefix tailTrace_768290
  have hstable : (prefixWord ++ tailWord_768290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768290).length < 2 ^ (prefixWord ++ tailWord_768290).sum := by decide
  have hdescent : baseEnd_768290 < baseStart_768290 := by decide
  rcases family_descends (prefixWord ++ tailWord_768290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768356 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_768356 : Nat := 118140960795 + 768356 * 2 ^ 59
def prefixEnd_768356 : Nat := 4983230072969 + 3 ^ 40 * 768356 * 2
def baseEnd_768356 : Nat := 350698614903200922059023

theorem tailTrace_768356 : CollatzResearch.WordTrace tailWord_768356 prefixEnd_768356 350698614903200922059023 := by
  unfold tailWord_768356
  simp only [CollatzResearch.WordTrace]
  refine ⟨14012122802192455801286461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18682830402923274401715281 14012122802192455801286461)
  ·
    refine ⟨5254546050822170925482423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14012122802192455801286461 5254546050822170925482423)
    ·
      refine ⟨7881819076233256388223635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5254546050822170925482423 7881819076233256388223635)
      ·
        refine ⟨11822728614349884582335453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7881819076233256388223635 11822728614349884582335453)
        ·
          refine ⟨4433523230381206718375795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11822728614349884582335453 4433523230381206718375795)
          ·
            refine ⟨6650284845571810077563693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4433523230381206718375795 6650284845571810077563693)
            ·
              refine ⟨2493856817089428779086385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6650284845571810077563693 2493856817089428779086385)
              ·
                refine ⟨1870392612817071584314789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2493856817089428779086385 1870392612817071584314789)
                ·
                  refine ⟨350698614903200922059023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1870392612817071584314789 350698614903200922059023)
                  ·
                    rfl

theorem cell20_768356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_768356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768356 prefixEnd_768356 := by exact prefixLift 768356
  have htrace : WordTrace (prefixWord ++ tailWord_768356) baseStart_768356 baseEnd_768356 := by
    simpa [prefixWord, tailWord_768356, baseEnd_768356] using wordTrace_append hprefix tailTrace_768356
  have hstable : (prefixWord ++ tailWord_768356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768356).length < 2 ^ (prefixWord ++ tailWord_768356).sum := by decide
  have hdescent : baseEnd_768356 < baseStart_768356 := by decide
  rcases family_descends (prefixWord ++ tailWord_768356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768377 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_768377 : Nat := 118140960795 + 768377 * 2 ^ 59
def prefixEnd_768377 : Nat := 4983230072969 + 3 ^ 40 * 768377 * 2
def baseEnd_768377 : Nat := 350708199875418182358937

theorem tailTrace_768377 : CollatzResearch.WordTrace tailWord_768377 prefixEnd_768377 350708199875418182358937 := by
  unfold tailWord_768377
  simp only [CollatzResearch.WordTrace]
  refine ⟨28025011537308832189087385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18683341024872554792724923 28025011537308832189087385)
  ·
    refine ⟨21018758652981624141815539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28025011537308832189087385 21018758652981624141815539)
    ·
      refine ⟨31528137979472436212723309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21018758652981624141815539 31528137979472436212723309)
      ·
        refine ⟨11823051742302163579771241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31528137979472436212723309 11823051742302163579771241)
        ·
          refine ⟨8867288806726622684828431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11823051742302163579771241 8867288806726622684828431)
          ·
            refine ⟨13300933210089934027242647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8867288806726622684828431 13300933210089934027242647)
            ·
              refine ⟨19951399815134901040863971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13300933210089934027242647 19951399815134901040863971)
              ·
                refine ⟨29927099722702351561295957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19951399815134901040863971 29927099722702351561295957)
                ·
                  refine ⟨350708199875418182358937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29927099722702351561295957 350708199875418182358937)
                  ·
                    rfl

theorem cell20_768377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_768377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768377 prefixEnd_768377 := by exact prefixLift 768377
  have htrace : WordTrace (prefixWord ++ tailWord_768377) baseStart_768377 baseEnd_768377 := by
    simpa [prefixWord, tailWord_768377, baseEnd_768377] using wordTrace_append hprefix tailTrace_768377
  have hstable : (prefixWord ++ tailWord_768377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768377).length < 2 ^ (prefixWord ++ tailWord_768377).sum := by decide
  have hdescent : baseEnd_768377 < baseStart_768377 := by decide
  rcases family_descends (prefixWord ++ tailWord_768377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768387 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 5]
def baseStart_768387 : Nat := 118140960795 + 768387 * 2 ^ 59
def prefixEnd_768387 : Nat := 4983230072969 + 3 ^ 40 * 768387 * 2
def baseEnd_768387 : Nat := 350712764147902592025563

theorem tailTrace_768387 : CollatzResearch.WordTrace tailWord_768387 prefixEnd_768387 350712764147902592025563 := by
  unfold tailWord_768387
  simp only [CollatzResearch.WordTrace]
  refine ⟨28025376267272603896951415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18683584178181735931300943 28025376267272603896951415)
  ·
    refine ⟨42038064400908905845427123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28025376267272603896951415 42038064400908905845427123)
    ·
      refine ⟨63057096601363358768140685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42038064400908905845427123 63057096601363358768140685)
      ·
        refine ⟨23646411225511259538052757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63057096601363358768140685 23646411225511259538052757)
        ·
          refine ⟨1108425526195840290846223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23646411225511259538052757 1108425526195840290846223)
          ·
            refine ⟨1662638289293760436269335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108425526195840290846223 1662638289293760436269335)
            ·
              refine ⟨2493957433940640654404003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662638289293760436269335 2493957433940640654404003)
              ·
                refine ⟨3740936150910960981606005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493957433940640654404003 3740936150910960981606005)
                ·
                  refine ⟨350712764147902592025563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3740936150910960981606005 350712764147902592025563)
                  ·
                    rfl

theorem cell20_768387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_768387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768387 prefixEnd_768387 := by exact prefixLift 768387
  have htrace : WordTrace (prefixWord ++ tailWord_768387) baseStart_768387 baseEnd_768387 := by
    simpa [prefixWord, tailWord_768387, baseEnd_768387] using wordTrace_append hprefix tailTrace_768387
  have hstable : (prefixWord ++ tailWord_768387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768387).length < 2 ^ (prefixWord ++ tailWord_768387).sum := by decide
  have hdescent : baseEnd_768387 < baseStart_768387 := by decide
  rcases family_descends (prefixWord ++ tailWord_768387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768414 : List Nat := [4, 3, 1, 2, 1, 3, 2, 4]
def baseStart_768414 : Nat := 118140960795 + 768414 * 2 ^ 59
def prefixEnd_768414 : Nat := 4983230072969 + 3 ^ 40 * 768414 * 2
def baseEnd_768414 : Nat := 116908362561203499375151

theorem tailTrace_768414 : CollatzResearch.WordTrace tailWord_768414 prefixEnd_768414 116908362561203499375151 := by
  unfold tailWord_768414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503295129771848438523037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18684240692116525005456197 3503295129771848438523037)
  ·
    refine ⟨1313735673664443164446139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3503295129771848438523037 1313735673664443164446139)
    ·
      refine ⟨1970603510496664746669209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1313735673664443164446139 1970603510496664746669209)
      ·
        refine ⟨1477952632872498560001907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1970603510496664746669209 1477952632872498560001907)
        ·
          refine ⟨2216928949308747840002861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477952632872498560001907 2216928949308747840002861)
          ·
            refine ⟨831348355990780440001073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2216928949308747840002861 831348355990780440001073)
            ·
              refine ⟨623511266993085330000805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831348355990780440001073 623511266993085330000805)
              ·
                refine ⟨116908362561203499375151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623511266993085330000805 116908362561203499375151)
                ·
                  rfl

theorem cell20_768414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_768414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768414 prefixEnd_768414 := by exact prefixLift 768414
  have htrace : WordTrace (prefixWord ++ tailWord_768414) baseStart_768414 baseEnd_768414 := by
    simpa [prefixWord, tailWord_768414, baseEnd_768414] using wordTrace_append hprefix tailTrace_768414
  have hstable : (prefixWord ++ tailWord_768414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768414).length < 2 ^ (prefixWord ++ tailWord_768414).sum := by decide
  have hdescent : baseEnd_768414 < baseStart_768414 := by decide
  rcases family_descends (prefixWord ++ tailWord_768414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768439 : List Nat := [1, 1, 3, 1, 3, 5, 6]
def baseStart_768439 : Nat := 118140960795 + 768439 * 2 ^ 59
def prefixEnd_768439 : Nat := 4983230072969 + 3 ^ 40 * 768439 * 2
def baseEnd_768439 : Nat := 38970722040535724699113

theorem tailTrace_768439 : CollatzResearch.WordTrace tailWord_768439 prefixEnd_768439 38970722040535724699113 := by
  unfold tailWord_768439
  simp only [CollatzResearch.WordTrace]
  refine ⟨28027272863084216777844371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18684848575389477851896247 28027272863084216777844371)
  ·
    refine ⟨42040909294626325166766557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28027272863084216777844371 42040909294626325166766557)
    ·
      refine ⟨15765340985484871937537459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42040909294626325166766557 15765340985484871937537459)
      ·
        refine ⟨23648011478227307906306189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15765340985484871937537459 23648011478227307906306189)
        ·
          refine ⟨8868004304335240464864821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23648011478227307906306189 8868004304335240464864821)
          ·
            refine ⟨831375403531428793581077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8868004304335240464864821 831375403531428793581077)
            ·
              refine ⟨38970722040535724699113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 831375403531428793581077 38970722040535724699113)
              ·
                rfl

theorem cell20_768439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 6].length) (baseStart_768439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768439 prefixEnd_768439 := by exact prefixLift 768439
  have htrace : WordTrace (prefixWord ++ tailWord_768439) baseStart_768439 baseEnd_768439 := by
    simpa [prefixWord, tailWord_768439, baseEnd_768439] using wordTrace_append hprefix tailTrace_768439
  have hstable : (prefixWord ++ tailWord_768439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768439).length < 2 ^ (prefixWord ++ tailWord_768439).sum := by decide
  have hdescent : baseEnd_768439 < baseStart_768439 := by decide
  rcases family_descends (prefixWord ++ tailWord_768439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768477 : List Nat := [1, 4, 3, 1, 1, 1, 1, 8]
def baseStart_768477 : Nat := 118140960795 + 768477 * 2 ^ 59
def prefixEnd_768477 : Nat := 4983230072969 + 3 ^ 40 * 768477 * 2
def baseEnd_768477 : Nat := 116917947533420759675065

theorem tailTrace_768477 : CollatzResearch.WordTrace tailWord_768477 prefixEnd_768477 116917947533420759675065 := by
  unfold tailWord_768477
  simp only [CollatzResearch.WordTrace]
  refine ⟨28028658836946549267727685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18685772557964366178485123 28028658836946549267727685)
  ·
    refine ⟨5255373531927477987698941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28028658836946549267727685 5255373531927477987698941)
    ·
      refine ⟨1970765074472804245387103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5255373531927477987698941 1970765074472804245387103)
      ·
        refine ⟨2956147611709206368080655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970765074472804245387103 2956147611709206368080655)
        ·
          refine ⟨4434221417563809552120983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956147611709206368080655 4434221417563809552120983)
          ·
            refine ⟨6651332126345714328181475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434221417563809552120983 6651332126345714328181475)
            ·
              refine ⟨9976998189518571492272213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651332126345714328181475 9976998189518571492272213)
              ·
                refine ⟨116917947533420759675065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9976998189518571492272213 116917947533420759675065)
                ·
                  rfl

theorem cell20_768477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_768477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768477 prefixEnd_768477 := by exact prefixLift 768477
  have htrace : WordTrace (prefixWord ++ tailWord_768477) baseStart_768477 baseEnd_768477 := by
    simpa [prefixWord, tailWord_768477, baseEnd_768477] using wordTrace_append hprefix tailTrace_768477
  have hstable : (prefixWord ++ tailWord_768477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768477).length < 2 ^ (prefixWord ++ tailWord_768477).sum := by decide
  have hdescent : baseEnd_768477 < baseStart_768477 := by decide
  rcases family_descends (prefixWord ++ tailWord_768477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768487 : List Nat := [1, 1, 5, 2, 1, 1, 2, 5, 2]
def baseStart_768487 : Nat := 118140960795 + 768487 * 2 ^ 59
def prefixEnd_768487 : Nat := 4983230072969 + 3 ^ 40 * 768487 * 2
def baseEnd_768487 : Nat := 350758406872746688691821

theorem tailTrace_768487 : CollatzResearch.WordTrace tailWord_768487 prefixEnd_768487 350758406872746688691821 := by
  unfold tailWord_768487
  simp only [CollatzResearch.WordTrace]
  refine ⟨28029023566910320975591715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18686015711273547317061143 28029023566910320975591715)
  ·
    refine ⟨42043535350365481463387573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28029023566910320975591715 42043535350365481463387573)
    ·
      refine ⟨3941581439096763887192585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42043535350365481463387573 3941581439096763887192585)
      ·
        refine ⟨2956186079322572915394439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3941581439096763887192585 2956186079322572915394439)
        ·
          refine ⟨4434279118983859373091659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956186079322572915394439 4434279118983859373091659)
          ·
            refine ⟨6651418678475789059637489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434279118983859373091659 6651418678475789059637489)
            ·
              refine ⟨4988564008856841794728117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6651418678475789059637489 4988564008856841794728117)
              ·
                refine ⟨467677875830328918255761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4988564008856841794728117 467677875830328918255761)
                ·
                  refine ⟨350758406872746688691821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467677875830328918255761 350758406872746688691821)
                  ·
                    rfl

theorem cell20_768487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 2].length) (baseStart_768487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768487 prefixEnd_768487 := by exact prefixLift 768487
  have htrace : WordTrace (prefixWord ++ tailWord_768487) baseStart_768487 baseEnd_768487 := by
    simpa [prefixWord, tailWord_768487, baseEnd_768487] using wordTrace_append hprefix tailTrace_768487
  have hstable : (prefixWord ++ tailWord_768487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768487).length < 2 ^ (prefixWord ++ tailWord_768487).sum := by decide
  have hdescent : baseEnd_768487 < baseStart_768487 := by decide
  rcases family_descends (prefixWord ++ tailWord_768487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768591 : List Nat := [1, 1, 2, 1, 1, 2, 8, 4]
def baseStart_768591 : Nat := 118140960795 + 768591 * 2 ^ 59
def prefixEnd_768591 : Nat := 4983230072969 + 3 ^ 40 * 768591 * 2
def baseEnd_768591 : Nat := 116935291768861516408243

theorem tailTrace_768591 : CollatzResearch.WordTrace tailWord_768591 prefixEnd_768591 116935291768861516408243 := by
  unfold tailWord_768591
  simp only [CollatzResearch.WordTrace]
  refine ⟨28032816758533546737377627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18688544505689031158251751 28032816758533546737377627)
  ·
    refine ⟨42049225137800320106066441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28032816758533546737377627 42049225137800320106066441)
    ·
      refine ⟨31536918853350240079549831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42049225137800320106066441 31536918853350240079549831)
      ·
        refine ⟨47305378280025360119324747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31536918853350240079549831 47305378280025360119324747)
        ·
          refine ⟨70958067420038040178987121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47305378280025360119324747 70958067420038040178987121)
          ·
            refine ⟨53218550565028530134240341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70958067420038040178987121 53218550565028530134240341)
            ·
              refine ⟨623654889433928087510629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 53218550565028530134240341 623654889433928087510629)
              ·
                refine ⟨116935291768861516408243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623654889433928087510629 116935291768861516408243)
                ·
                  rfl

theorem cell20_768591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 4].length) (baseStart_768591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768591 prefixEnd_768591 := by exact prefixLift 768591
  have htrace : WordTrace (prefixWord ++ tailWord_768591) baseStart_768591 baseEnd_768591 := by
    simpa [prefixWord, tailWord_768591, baseEnd_768591] using wordTrace_append hprefix tailTrace_768591
  have hstable : (prefixWord ++ tailWord_768591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768591).length < 2 ^ (prefixWord ++ tailWord_768591).sum := by decide
  have hdescent : baseEnd_768591 < baseStart_768591 := by decide
  rcases family_descends (prefixWord ++ tailWord_768591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768618 : List Nat := [3, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_768618 : Nat := 118140960795 + 768618 * 2 ^ 59
def prefixEnd_768618 : Nat := 4983230072969 + 3 ^ 40 * 768618 * 2
def baseEnd_768618 : Nat := 350818198842292455324619

theorem tailTrace_768618 : CollatzResearch.WordTrace tailWord_768618 prefixEnd_768618 350818198842292455324619 := by
  unfold tailWord_768618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7008450382358932587152627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18689201019623820232407005 7008450382358932587152627)
  ·
    refine ⟨10512675573538398880728941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7008450382358932587152627 10512675573538398880728941)
    ·
      refine ⟨3942253340076899580273353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10512675573538398880728941 3942253340076899580273353)
      ·
        refine ⟨2956690005057674685205015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3942253340076899580273353 2956690005057674685205015)
        ·
          refine ⟨4435035007586512027807523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956690005057674685205015 4435035007586512027807523)
          ·
            refine ⟨6652552511379768041711285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435035007586512027807523 6652552511379768041711285)
            ·
              refine ⟨623676797941853253910433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6652552511379768041711285 623676797941853253910433)
              ·
                refine ⟨467757598456389940432825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623676797941853253910433 467757598456389940432825)
                ·
                  refine ⟨350818198842292455324619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467757598456389940432825 350818198842292455324619)
                  ·
                    rfl

theorem cell20_768618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_768618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768618 prefixEnd_768618 := by exact prefixLift 768618
  have htrace : WordTrace (prefixWord ++ tailWord_768618) baseStart_768618 baseEnd_768618 := by
    simpa [prefixWord, tailWord_768618, baseEnd_768618] using wordTrace_append hprefix tailTrace_768618
  have hstable : (prefixWord ++ tailWord_768618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768618).length < 2 ^ (prefixWord ++ tailWord_768618).sum := by decide
  have hdescent : baseEnd_768618 < baseStart_768618 := by decide
  rcases family_descends (prefixWord ++ tailWord_768618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768643 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_768643 : Nat := 118140960795 + 768643 * 2 ^ 59
def prefixEnd_768643 : Nat := 4983230072969 + 3 ^ 40 * 768643 * 2
def baseEnd_768643 : Nat := 350829609523503479491183

theorem tailTrace_768643 : CollatzResearch.WordTrace tailWord_768643 prefixEnd_768643 350829609523503479491183 := by
  unfold tailWord_768643
  simp only [CollatzResearch.WordTrace]
  refine ⟨28034713354345159618270583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18689808902896773078847055 28034713354345159618270583)
  ·
    refine ⟨42052070031517739427405875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28034713354345159618270583 42052070031517739427405875)
    ·
      refine ⟨63078105047276609141108813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42052070031517739427405875 63078105047276609141108813)
      ·
        refine ⟨23654289392728728427915805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63078105047276609141108813 23654289392728728427915805)
        ·
          refine ⟨8870358522273273160468427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23654289392728728427915805 8870358522273273160468427)
          ·
            refine ⟨13305537783409909740702641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8870358522273273160468427 13305537783409909740702641)
            ·
              refine ⟨9979153337557432305526981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13305537783409909740702641 9979153337557432305526981)
              ·
                refine ⟨1871091250792018557286309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9979153337557432305526981 1871091250792018557286309)
                ·
                  refine ⟨350829609523503479491183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871091250792018557286309 350829609523503479491183)
                  ·
                    rfl

theorem cell20_768643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_768643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768643 prefixEnd_768643 := by exact prefixLift 768643
  have htrace : WordTrace (prefixWord ++ tailWord_768643) baseStart_768643 baseEnd_768643 := by
    simpa [prefixWord, tailWord_768643, baseEnd_768643] using wordTrace_append hprefix tailTrace_768643
  have hstable : (prefixWord ++ tailWord_768643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768643).length < 2 ^ (prefixWord ++ tailWord_768643).sum := by decide
  have hdescent : baseEnd_768643 < baseStart_768643 := by decide
  rcases family_descends (prefixWord ++ tailWord_768643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768670 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_768670 : Nat := 118140960795 + 768670 * 2 ^ 59
def prefixEnd_768670 : Nat := 4983230072969 + 3 ^ 40 * 768670 * 2
def baseEnd_768670 : Nat := 350841933059211385591073

theorem tailTrace_768670 : CollatzResearch.WordTrace tailWord_768670 prefixEnd_768670 350841933059211385591073 := by
  unfold tailWord_768670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504462265655917903687933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18690465416831562153002309 3504462265655917903687933)
  ·
    refine ⟨1314173349620969213882975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3504462265655917903687933 1314173349620969213882975)
    ·
      refine ⟨1971260024431453820824463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314173349620969213882975 1971260024431453820824463)
      ·
        refine ⟨2956890036647180731236695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971260024431453820824463 2956890036647180731236695)
        ·
          refine ⟨4435335054970771096855043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956890036647180731236695 4435335054970771096855043)
          ·
            refine ⟨6653002582456156645282565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435335054970771096855043 6653002582456156645282565)
            ·
              refine ⟨1247437984210529370990481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6653002582456156645282565 1247437984210529370990481)
              ·
                refine ⟨935578488157897028242861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247437984210529370990481 935578488157897028242861)
                ·
                  refine ⟨350841933059211385591073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935578488157897028242861 350841933059211385591073)
                  ·
                    rfl

theorem cell20_768670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_768670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768670 prefixEnd_768670 := by exact prefixLift 768670
  have htrace : WordTrace (prefixWord ++ tailWord_768670) baseStart_768670 baseEnd_768670 := by
    simpa [prefixWord, tailWord_768670, baseEnd_768670] using wordTrace_append hprefix tailTrace_768670
  have hstable : (prefixWord ++ tailWord_768670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768670).length < 2 ^ (prefixWord ++ tailWord_768670).sum := by decide
  have hdescent : baseEnd_768670 < baseStart_768670 := by decide
  rcases family_descends (prefixWord ++ tailWord_768670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768673 : List Nat := [1, 2, 3, 3, 3, 2, 2, 2, 2]
def baseStart_768673 : Nat := 118140960795 + 768673 * 2 ^ 59
def prefixEnd_768673 : Nat := 4983230072969 + 3 ^ 40 * 768673 * 2
def baseEnd_768673 : Nat := 350843302340956708491061

theorem tailTrace_768673 : CollatzResearch.WordTrace tailWord_768673 prefixEnd_768673 350843302340956708491061 := by
  unfold tailWord_768673
  simp only [CollatzResearch.WordTrace]
  refine ⟨28035807544236474741862673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18690538362824316494575115 28035807544236474741862673)
  ·
    refine ⟨21026855658177356056397005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28035807544236474741862673 21026855658177356056397005)
    ·
      refine ⟨7885070871816508521148877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21026855658177356056397005 7885070871816508521148877)
      ·
        refine ⟨2956901576931190695430829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7885070871816508521148877 2956901576931190695430829)
        ·
          refine ⟨1108838091349196510786561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2956901576931190695430829 1108838091349196510786561)
          ·
            refine ⟨831628568511897383089921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108838091349196510786561 831628568511897383089921)
            ·
              refine ⟨623721426383923037317441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831628568511897383089921 623721426383923037317441)
              ·
                refine ⟨467791069787942277988081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623721426383923037317441 467791069787942277988081)
                ·
                  refine ⟨350843302340956708491061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467791069787942277988081 350843302340956708491061)
                  ·
                    rfl

theorem cell20_768673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_768673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768673 prefixEnd_768673 := by exact prefixLift 768673
  have htrace : WordTrace (prefixWord ++ tailWord_768673) baseStart_768673 baseEnd_768673 := by
    simpa [prefixWord, tailWord_768673, baseEnd_768673] using wordTrace_append hprefix tailTrace_768673
  have hstable : (prefixWord ++ tailWord_768673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768673).length < 2 ^ (prefixWord ++ tailWord_768673).sum := by decide
  have hdescent : baseEnd_768673 < baseStart_768673 := by decide
  rcases family_descends (prefixWord ++ tailWord_768673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768694 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_768694 : Nat := 118140960795 + 768694 * 2 ^ 59
def prefixEnd_768694 : Nat := 4983230072969 + 3 ^ 40 * 768694 * 2
def baseEnd_768694 : Nat := 350852887313173968790975

theorem tailTrace_768694 : CollatzResearch.WordTrace tailWord_768694 prefixEnd_768694 350852887313173968790975 := by
  unfold tailWord_768694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1752285842322524708023571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18691048984773596885584757 1752285842322524708023571)
  ·
    refine ⟨2628428763483787062035357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1752285842322524708023571 2628428763483787062035357)
    ·
      refine ⟨985660786306420148263259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2628428763483787062035357 985660786306420148263259)
      ·
        refine ⟨1478491179459630222394889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985660786306420148263259 1478491179459630222394889)
        ·
          refine ⟨1108868384594722666796167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478491179459630222394889 1108868384594722666796167)
          ·
            refine ⟨1663302576892084000194251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108868384594722666796167 1663302576892084000194251)
            ·
              refine ⟨2494953865338126000291377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663302576892084000194251 2494953865338126000291377)
              ·
                refine ⟨1871215399003594500218533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494953865338126000291377 1871215399003594500218533)
                ·
                  refine ⟨350852887313173968790975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871215399003594500218533 350852887313173968790975)
                  ·
                    rfl

theorem cell20_768694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_768694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768694 prefixEnd_768694 := by exact prefixLift 768694
  have htrace : WordTrace (prefixWord ++ tailWord_768694) baseStart_768694 baseEnd_768694 := by
    simpa [prefixWord, tailWord_768694, baseEnd_768694] using wordTrace_append hprefix tailTrace_768694
  have hstable : (prefixWord ++ tailWord_768694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768694).length < 2 ^ (prefixWord ++ tailWord_768694).sum := by decide
  have hdescent : baseEnd_768694 < baseStart_768694 := by decide
  rcases family_descends (prefixWord ++ tailWord_768694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768725 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 3]
def baseStart_768725 : Nat := 118140960795 + 768725 * 2 ^ 59
def prefixEnd_768725 : Nat := 4983230072969 + 3 ^ 40 * 768725 * 2
def baseEnd_768725 : Nat := 350867036557875638757515

theorem tailTrace_768725 : CollatzResearch.WordTrace tailWord_768725 prefixEnd_768725 350867036557875638757515 := by
  unfold tailWord_768725
  simp only [CollatzResearch.WordTrace]
  refine ⟨28037704140048087622755629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18691802760032058415170419 28037704140048087622755629)
  ·
    refine ⟨10514139052518032858533361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28037704140048087622755629 10514139052518032858533361)
    ·
      refine ⟨7885604289388524643900021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10514139052518032858533361 7885604289388524643900021)
      ·
        refine ⟨739275402130174185365627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7885604289388524643900021 739275402130174185365627)
        ·
          refine ⟨1108913103195261278048441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739275402130174185365627 1108913103195261278048441)
          ·
            refine ⟨831684827396445958536331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108913103195261278048441 831684827396445958536331)
            ·
              refine ⟨1247527241094668937804497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831684827396445958536331 1247527241094668937804497)
              ·
                refine ⟨935645430821001703353373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247527241094668937804497 935645430821001703353373)
                ·
                  refine ⟨350867036557875638757515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935645430821001703353373 350867036557875638757515)
                  ·
                    rfl

theorem cell20_768725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_768725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768725 prefixEnd_768725 := by exact prefixLift 768725
  have htrace : WordTrace (prefixWord ++ tailWord_768725) baseStart_768725 baseEnd_768725 := by
    simpa [prefixWord, tailWord_768725, baseEnd_768725] using wordTrace_append hprefix tailTrace_768725
  have hstable : (prefixWord ++ tailWord_768725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768725).length < 2 ^ (prefixWord ++ tailWord_768725).sum := by decide
  have hdescent : baseEnd_768725 < baseStart_768725 := by decide
  rcases family_descends (prefixWord ++ tailWord_768725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768732 : List Nat := [2, 2, 5, 1, 1, 1, 2, 4, 2]
def baseStart_768732 : Nat := 118140960795 + 768732 * 2 ^ 59
def prefixEnd_768732 : Nat := 4983230072969 + 3 ^ 40 * 768732 * 2
def baseEnd_768732 : Nat := 350870231548614725524153

theorem tailTrace_768732 : CollatzResearch.WordTrace tailWord_768732 prefixEnd_768732 350870231548614725524153 := by
  unfold tailWord_768732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14018979725511363909130225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18691972967348485212173633 14018979725511363909130225)
  ·
    refine ⟨10514234794133522931847669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14018979725511363909130225 10514234794133522931847669)
    ·
      refine ⟨985709511950017774860719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10514234794133522931847669 985709511950017774860719)
      ·
        refine ⟨1478564267925026662291079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985709511950017774860719 1478564267925026662291079)
        ·
          refine ⟨2217846401887539993436619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478564267925026662291079 2217846401887539993436619)
          ·
            refine ⟨3326769602831309990154929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217846401887539993436619 3326769602831309990154929)
            ·
              refine ⟨2495077202123482492616197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3326769602831309990154929 2495077202123482492616197)
              ·
                refine ⟨467826975398152967365537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2495077202123482492616197 467826975398152967365537)
                ·
                  refine ⟨350870231548614725524153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467826975398152967365537 350870231548614725524153)
                  ·
                    rfl

theorem cell20_768732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_768732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768732 prefixEnd_768732 := by exact prefixLift 768732
  have htrace : WordTrace (prefixWord ++ tailWord_768732) baseStart_768732 baseEnd_768732 := by
    simpa [prefixWord, tailWord_768732, baseEnd_768732] using wordTrace_append hprefix tailTrace_768732
  have hstable : (prefixWord ++ tailWord_768732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768732).length < 2 ^ (prefixWord ++ tailWord_768732).sum := by decide
  have hdescent : baseEnd_768732 < baseStart_768732 := by decide
  rcases family_descends (prefixWord ++ tailWord_768732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768770 : List Nat := [3, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_768770 : Nat := 118140960795 + 768770 * 2 ^ 59
def prefixEnd_768770 : Nat := 4983230072969 + 3 ^ 40 * 768770 * 2
def baseEnd_768770 : Nat := 350887575784055482257331

theorem tailTrace_768770 : CollatzResearch.WordTrace tailWord_768770 prefixEnd_768770 350887575784055482257331 := by
  unfold tailWord_768770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009836356221265077035941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18692896949923373538762509 7009836356221265077035941)
  ·
    refine ⟨1314344316791487201944239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7009836356221265077035941 1314344316791487201944239)
    ·
      refine ⟨1971516475187230802916359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314344316791487201944239 1971516475187230802916359)
      ·
        refine ⟨2957274712780846204374539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971516475187230802916359 2957274712780846204374539)
        ·
          refine ⟨4435912069171269306561809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957274712780846204374539 4435912069171269306561809)
          ·
            refine ⟨3326934051878451979921357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4435912069171269306561809 3326934051878451979921357)
            ·
              refine ⟨1247600269454419492470509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3326934051878451979921357 1247600269454419492470509)
              ·
                refine ⟨467850101045407309676441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1247600269454419492470509 467850101045407309676441)
                ·
                  refine ⟨350887575784055482257331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467850101045407309676441 350887575784055482257331)
                  ·
                    rfl

theorem cell20_768770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_768770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768770 prefixEnd_768770 := by exact prefixLift 768770
  have htrace : WordTrace (prefixWord ++ tailWord_768770) baseStart_768770 baseEnd_768770 := by
    simpa [prefixWord, tailWord_768770, baseEnd_768770] using wordTrace_append hprefix tailTrace_768770
  have hstable : (prefixWord ++ tailWord_768770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768770).length < 2 ^ (prefixWord ++ tailWord_768770).sum := by decide
  have hdescent : baseEnd_768770 < baseStart_768770 := by decide
  rcases family_descends (prefixWord ++ tailWord_768770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768791 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 4]
def baseStart_768791 : Nat := 118140960795 + 768791 * 2 ^ 59
def prefixEnd_768791 : Nat := 4983230072969 + 3 ^ 40 * 768791 * 2
def baseEnd_768791 : Nat := 350897160756272742557245

theorem tailTrace_768791 : CollatzResearch.WordTrace tailWord_768791 prefixEnd_768791 350897160756272742557245 := by
  unfold tailWord_768791
  simp only [CollatzResearch.WordTrace]
  refine ⟨28040111357808980894658227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18693407571872653929772151 28040111357808980894658227)
  ·
    refine ⟨42060167036713471341987341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28040111357808980894658227 42060167036713471341987341)
    ·
      refine ⟨15772562638767551753245253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42060167036713471341987341 15772562638767551753245253)
      ·
        refine ⟨2957355494768915953733485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15772562638767551753245253 2957355494768915953733485)
        ·
          refine ⟨1109008310538343482650057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2957355494768915953733485 1109008310538343482650057)
          ·
            refine ⟨831756232903757611987543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109008310538343482650057 831756232903757611987543)
            ·
              refine ⟨1247634349355636417981315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831756232903757611987543 1247634349355636417981315)
              ·
                refine ⟨1871451524033454626971973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247634349355636417981315 1871451524033454626971973)
                ·
                  refine ⟨350897160756272742557245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1871451524033454626971973 350897160756272742557245)
                  ·
                    rfl

theorem cell20_768791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 4].length) (baseStart_768791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768791 prefixEnd_768791 := by exact prefixLift 768791
  have htrace : WordTrace (prefixWord ++ tailWord_768791) baseStart_768791 baseEnd_768791 := by
    simpa [prefixWord, tailWord_768791, baseEnd_768791] using wordTrace_append hprefix tailTrace_768791
  have hstable : (prefixWord ++ tailWord_768791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768791).length < 2 ^ (prefixWord ++ tailWord_768791).sum := by decide
  have hdescent : baseEnd_768791 < baseStart_768791 := by decide
  rcases family_descends (prefixWord ++ tailWord_768791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768836 : List Nat := [2, 3, 4, 2, 1, 8]
def baseStart_768836 : Nat := 118140960795 + 768836 * 2 ^ 59
def prefixEnd_768836 : Nat := 4983230072969 + 3 ^ 40 * 768836 * 2
def baseEnd_768836 : Nat := 12996951851201947631743

theorem tailTrace_768836 : CollatzResearch.WordTrace tailWord_768836 prefixEnd_768836 12996951851201947631743 := by
  unfold tailWord_768836
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020876321322976790023181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18694501761763969053364241 14020876321322976790023181)
  ·
    refine ⟨5257828620496116296258693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14020876321322976790023181 5257828620496116296258693)
    ·
      refine ⟨985842866343021805548505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5257828620496116296258693 985842866343021805548505)
      ·
        refine ⟨739382149757266354161379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 985842866343021805548505 739382149757266354161379)
        ·
          refine ⟨1109073224635899531242069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739382149757266354161379 1109073224635899531242069)
          ·
            refine ⟨12996951851201947631743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1109073224635899531242069 12996951851201947631743)
            ·
              rfl

theorem cell20_768836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 8].length) (baseStart_768836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768836 prefixEnd_768836 := by exact prefixLift 768836
  have htrace : WordTrace (prefixWord ++ tailWord_768836) baseStart_768836 baseEnd_768836 := by
    simpa [prefixWord, tailWord_768836, baseEnd_768836] using wordTrace_append hprefix tailTrace_768836
  have hstable : (prefixWord ++ tailWord_768836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768836).length < 2 ^ (prefixWord ++ tailWord_768836).sum := by decide
  have hdescent : baseEnd_768836 < baseStart_768836 := by decide
  rcases family_descends (prefixWord ++ tailWord_768836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768857 : List Nat := [1, 2, 1, 2, 2, 6, 1, 5]
def baseStart_768857 : Nat := 118140960795 + 768857 * 2 ^ 59
def prefixEnd_768857 : Nat := 4983230072969 + 3 ^ 40 * 768857 * 2
def baseEnd_768857 : Nat := 116975761651556615452325

theorem tailTrace_768857 : CollatzResearch.WordTrace tailWord_768857 prefixEnd_768857 116975761651556615452325 := by
  unfold tailWord_768857
  simp only [CollatzResearch.WordTrace]
  refine ⟨28042518575569874166560825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18695012383713249444373883 28042518575569874166560825)
  ·
    refine ⟨21031888931677405624920619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28042518575569874166560825 21031888931677405624920619)
    ·
      refine ⟨31547833397516108437380929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21031888931677405624920619 31547833397516108437380929)
      ·
        refine ⟨23660875048137081328035697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31547833397516108437380929 23660875048137081328035697)
        ·
          refine ⟨17745656286102810996026773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23660875048137081328035697 17745656286102810996026773)
          ·
            refine ⟨831827638411069265438755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17745656286102810996026773 831827638411069265438755)
            ·
              refine ⟨1247741457616603898158133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831827638411069265438755 1247741457616603898158133)
              ·
                refine ⟨116975761651556615452325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1247741457616603898158133 116975761651556615452325)
                ·
                  rfl

theorem cell20_768857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_768857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768857 prefixEnd_768857 := by exact prefixLift 768857
  have htrace : WordTrace (prefixWord ++ tailWord_768857) baseStart_768857 baseEnd_768857 := by
    simpa [prefixWord, tailWord_768857, baseEnd_768857] using wordTrace_append hprefix tailTrace_768857
  have hstable : (prefixWord ++ tailWord_768857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768857).length < 2 ^ (prefixWord ++ tailWord_768857).sum := by decide
  have hdescent : baseEnd_768857 < baseStart_768857 := by decide
  rcases family_descends (prefixWord ++ tailWord_768857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768864 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_768864 : Nat := 118140960795 + 768864 * 2 ^ 59
def prefixEnd_768864 : Nat := 4983230072969 + 3 ^ 40 * 768864 * 2
def baseEnd_768864 : Nat := 350930479945408933123613

theorem tailTrace_768864 : CollatzResearch.WordTrace tailWord_768864 prefixEnd_768864 350930479945408933123613 := by
  unfold tailWord_768864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14021386943272257181032823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18695182591029676241377097 14021386943272257181032823)
  ·
    refine ⟨21032080414908385771549235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14021386943272257181032823 21032080414908385771549235)
    ·
      refine ⟨31548120622362578657323853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21032080414908385771549235 31548120622362578657323853)
      ·
        refine ⟨11830545233385966996496445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31548120622362578657323853 11830545233385966996496445)
        ·
          refine ⟨4436454462519737623686167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11830545233385966996496445 4436454462519737623686167)
          ·
            refine ⟨6654681693779606435529251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436454462519737623686167 6654681693779606435529251)
            ·
              refine ⟨9982022540669409653293877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654681693779606435529251 9982022540669409653293877)
              ·
                refine ⟨935814613187757154996301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9982022540669409653293877 935814613187757154996301)
                ·
                  refine ⟨350930479945408933123613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935814613187757154996301 350930479945408933123613)
                  ·
                    rfl

theorem cell20_768864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_768864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768864 prefixEnd_768864 := by exact prefixLift 768864
  have htrace : WordTrace (prefixWord ++ tailWord_768864) baseStart_768864 baseEnd_768864 := by
    simpa [prefixWord, tailWord_768864, baseEnd_768864] using wordTrace_append hprefix tailTrace_768864
  have hstable : (prefixWord ++ tailWord_768864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768864).length < 2 ^ (prefixWord ++ tailWord_768864).sum := by decide
  have hdescent : baseEnd_768864 < baseStart_768864 := by decide
  rcases family_descends (prefixWord ++ tailWord_768864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768871 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_768871 : Nat := 118140960795 + 768871 * 2 ^ 59
def prefixEnd_768871 : Nat := 4983230072969 + 3 ^ 40 * 768871 * 2
def baseEnd_768871 : Nat := 350933674936148019890251

theorem tailTrace_768871 : CollatzResearch.WordTrace tailWord_768871 prefixEnd_768871 350933674936148019890251 := by
  unfold tailWord_768871
  simp only [CollatzResearch.WordTrace]
  refine ⟨28043029197519154557570467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18695352798346103038380311 28043029197519154557570467)
  ·
    refine ⟨42064543796278731836355701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28043029197519154557570467 42064543796278731836355701)
    ·
      refine ⟨3943550980901131109658347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42064543796278731836355701 3943550980901131109658347)
      ·
        refine ⟨5915326471351696664487521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3943550980901131109658347 5915326471351696664487521)
        ·
          refine ⟨4436494853513772498365641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5915326471351696664487521 4436494853513772498365641)
          ·
            refine ⟨3327371140135329373774231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4436494853513772498365641 3327371140135329373774231)
            ·
              refine ⟨4991056710202994060661347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327371140135329373774231 4991056710202994060661347)
              ·
                refine ⟨7486585065304491090992021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991056710202994060661347 7486585065304491090992021)
                ·
                  refine ⟨350933674936148019890251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7486585065304491090992021 350933674936148019890251)
                  ·
                    rfl

theorem cell20_768871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_768871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768871 prefixEnd_768871 := by exact prefixLift 768871
  have htrace : WordTrace (prefixWord ++ tailWord_768871) baseStart_768871 baseEnd_768871 := by
    simpa [prefixWord, tailWord_768871, baseEnd_768871] using wordTrace_append hprefix tailTrace_768871
  have hstable : (prefixWord ++ tailWord_768871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768871).length < 2 ^ (prefixWord ++ tailWord_768871).sum := by decide
  have hdescent : baseEnd_768871 < baseStart_768871 := by decide
  rcases family_descends (prefixWord ++ tailWord_768871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768894 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_768894 : Nat := 118140960795 + 768894 * 2 ^ 59
def prefixEnd_768894 : Nat := 4983230072969 + 3 ^ 40 * 768894 * 2
def baseEnd_768894 : Nat := 350944172762862162123491

theorem tailTrace_768894 : CollatzResearch.WordTrace tailWord_768894 prefixEnd_768894 350944172762862162123491 := by
  unfold tailWord_768894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505483509554478685707217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18695912050957219657105157 3505483509554478685707217)
  ·
    refine ⟨2629112632165859014280413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3505483509554478685707217 2629112632165859014280413)
    ·
      refine ⟨985917237062197130355155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2629112632165859014280413 985917237062197130355155)
      ·
        refine ⟨1478875855593295695532733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985917237062197130355155 1478875855593295695532733)
        ·
          refine ⟨554578445847485885824775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1478875855593295695532733 554578445847485885824775)
          ·
            refine ⟨831867668771228828737163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554578445847485885824775 831867668771228828737163)
            ·
              refine ⟨1247801503156843243105745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831867668771228828737163 1247801503156843243105745)
              ·
                refine ⟨935851127367632432329309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247801503156843243105745 935851127367632432329309)
                ·
                  refine ⟨350944172762862162123491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935851127367632432329309 350944172762862162123491)
                  ·
                    rfl

theorem cell20_768894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_768894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768894 prefixEnd_768894 := by exact prefixLift 768894
  have htrace : WordTrace (prefixWord ++ tailWord_768894) baseStart_768894 baseEnd_768894 := by
    simpa [prefixWord, tailWord_768894, baseEnd_768894] using wordTrace_append hprefix tailTrace_768894
  have hstable : (prefixWord ++ tailWord_768894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768894).length < 2 ^ (prefixWord ++ tailWord_768894).sum := by decide
  have hdescent : baseEnd_768894 < baseStart_768894 := by decide
  rcases family_descends (prefixWord ++ tailWord_768894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768919 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 3]
def baseStart_768919 : Nat := 118140960795 + 768919 * 2 ^ 59
def prefixEnd_768919 : Nat := 4983230072969 + 3 ^ 40 * 768919 * 2
def baseEnd_768919 : Nat := 350955583444073186290055

theorem tailTrace_768919 : CollatzResearch.WordTrace tailWord_768919 prefixEnd_768919 350955583444073186290055 := by
  unfold tailWord_768919
  simp only [CollatzResearch.WordTrace]
  refine ⟨28044779901345258755317811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18696519934230172503545207 28044779901345258755317811)
  ·
    refine ⟨42067169852017888132976717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28044779901345258755317811 42067169852017888132976717)
    ·
      refine ⟨15775188694506708049866269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42067169852017888132976717 15775188694506708049866269)
      ·
        refine ⟨5915695760440015518699851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15775188694506708049866269 5915695760440015518699851)
        ·
          refine ⟨8873543640660023278049777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915695760440015518699851 8873543640660023278049777)
          ·
            refine ⟨6655157730495017458537333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8873543640660023278049777 6655157730495017458537333)
            ·
              refine ⟨623921037233907886737875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6655157730495017458537333 623921037233907886737875)
              ·
                refine ⟨935881555850861830106813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623921037233907886737875 935881555850861830106813)
                ·
                  refine ⟨350955583444073186290055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935881555850861830106813 350955583444073186290055)
                  ·
                    rfl

theorem cell20_768919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 3].length) (baseStart_768919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768919 prefixEnd_768919 := by exact prefixLift 768919
  have htrace : WordTrace (prefixWord ++ tailWord_768919) baseStart_768919 baseEnd_768919 := by
    simpa [prefixWord, tailWord_768919, baseEnd_768919] using wordTrace_append hprefix tailTrace_768919
  have hstable : (prefixWord ++ tailWord_768919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768919).length < 2 ^ (prefixWord ++ tailWord_768919).sum := by decide
  have hdescent : baseEnd_768919 < baseStart_768919 := by decide
  rcases family_descends (prefixWord ++ tailWord_768919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768966 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_768966 : Nat := 118140960795 + 768966 * 2 ^ 59
def prefixEnd_768966 : Nat := 4983230072969 + 3 ^ 40 * 768966 * 2
def baseEnd_768966 : Nat := 350977035524749911723197

theorem tailTrace_768966 : CollatzResearch.WordTrace tailWord_768966 prefixEnd_768966 350977035524749911723197 := by
  unfold tailWord_768966
  simp only [CollatzResearch.WordTrace]
  refine ⟨876452941630468305696211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18697662754783323854852501 876452941630468305696211)
  ·
    refine ⟨1314679412445702458544317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 876452941630468305696211 1314679412445702458544317)
    ·
      refine ⟨493004779667138421954119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1314679412445702458544317 493004779667138421954119)
      ·
        refine ⟨739507169500707632931179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493004779667138421954119 739507169500707632931179)
        ·
          refine ⟨1109260754251061449396769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739507169500707632931179 1109260754251061449396769)
          ·
            refine ⟨831945565688296087047577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109260754251061449396769 831945565688296087047577)
            ·
              refine ⟨623959174266222065285683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831945565688296087047577 623959174266222065285683)
              ·
                refine ⟨935938761399333097928525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623959174266222065285683 935938761399333097928525)
                ·
                  refine ⟨350977035524749911723197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935938761399333097928525 350977035524749911723197)
                  ·
                    rfl

theorem cell20_768966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_768966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768966 prefixEnd_768966 := by exact prefixLift 768966
  have htrace : WordTrace (prefixWord ++ tailWord_768966) baseStart_768966 baseEnd_768966 := by
    simpa [prefixWord, tailWord_768966, baseEnd_768966] using wordTrace_append hprefix tailTrace_768966
  have hstable : (prefixWord ++ tailWord_768966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768966).length < 2 ^ (prefixWord ++ tailWord_768966).sum := by decide
  have hdescent : baseEnd_768966 < baseStart_768966 := by decide
  rcases family_descends (prefixWord ++ tailWord_768966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_768974 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_768974 : Nat := 118140960795 + 768974 * 2 ^ 59
def prefixEnd_768974 : Nat := 4983230072969 + 3 ^ 40 * 768974 * 2
def baseEnd_768974 : Nat := 350980686942737439456497

theorem tailTrace_768974 : CollatzResearch.WordTrace tailWord_768974 prefixEnd_768974 350980686942737439456497 := by
  unfold tailWord_768974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505848239518250393571247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18697857277430668765713317 3505848239518250393571247)
  ·
    refine ⟨5258772359277375590356871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3505848239518250393571247 5258772359277375590356871)
    ·
      refine ⟨7888158538916063385535307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5258772359277375590356871 7888158538916063385535307)
      ·
        refine ⟨11832237808374095078302961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888158538916063385535307 11832237808374095078302961)
        ·
          refine ⟨8874178356280571308727221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11832237808374095078302961 8874178356280571308727221)
          ·
            refine ⟨831954220901303560193177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8874178356280571308727221 831954220901303560193177)
            ·
              refine ⟨623965665675977670144883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831954220901303560193177 623965665675977670144883)
              ·
                refine ⟨935948498513966505217325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623965665675977670144883 935948498513966505217325)
                ·
                  refine ⟨350980686942737439456497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935948498513966505217325 350980686942737439456497)
                  ·
                    rfl

theorem cell20_768974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_768974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_768974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_768974 prefixEnd_768974 := by exact prefixLift 768974
  have htrace : WordTrace (prefixWord ++ tailWord_768974) baseStart_768974 baseEnd_768974 := by
    simpa [prefixWord, tailWord_768974, baseEnd_768974] using wordTrace_append hprefix tailTrace_768974
  have hstable : (prefixWord ++ tailWord_768974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_768974).length < 2 ^ (prefixWord ++ tailWord_768974).sum := by decide
  have hdescent : baseEnd_768974 < baseStart_768974 := by decide
  rcases family_descends (prefixWord ++ tailWord_768974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769057 : List Nat := [1, 2, 3, 2, 3, 2, 2, 3, 2]
def baseStart_769057 : Nat := 118140960795 + 769057 * 2 ^ 59
def prefixEnd_769057 : Nat := 4983230072969 + 3 ^ 40 * 769057 * 2
def baseEnd_769057 : Nat := 351018570404358039689491

theorem tailTrace_769057 : CollatzResearch.WordTrace tailWord_769057 prefixEnd_769057 351018570404358039689491 := by
  unfold tailWord_769057
  simp only [CollatzResearch.WordTrace]
  refine ⟨28049813174845308323841425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18699875449896872215894283 28049813174845308323841425)
  ·
    refine ⟨21037359881133981242881069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28049813174845308323841425 21037359881133981242881069)
    ·
      refine ⟨7889009955425242966080401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21037359881133981242881069 7889009955425242966080401)
      ·
        refine ⟨5916757466568932224560301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7889009955425242966080401 5916757466568932224560301)
        ·
          refine ⟨2218784049963349584210113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5916757466568932224560301 2218784049963349584210113)
          ·
            refine ⟨1664088037472512188157585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2218784049963349584210113 1664088037472512188157585)
            ·
              refine ⟨1248066028104384141118189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1664088037472512188157585 1248066028104384141118189)
              ·
                refine ⟨468024760539144052919321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1248066028104384141118189 468024760539144052919321)
                ·
                  refine ⟨351018570404358039689491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468024760539144052919321 351018570404358039689491)
                  ·
                    rfl

theorem cell20_769057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_769057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769057 prefixEnd_769057 := by exact prefixLift 769057
  have htrace : WordTrace (prefixWord ++ tailWord_769057) baseStart_769057 baseEnd_769057 := by
    simpa [prefixWord, tailWord_769057, baseEnd_769057] using wordTrace_append hprefix tailTrace_769057
  have hstable : (prefixWord ++ tailWord_769057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769057).length < 2 ^ (prefixWord ++ tailWord_769057).sum := by decide
  have hdescent : baseEnd_769057 < baseStart_769057 := by decide
  rcases family_descends (prefixWord ++ tailWord_769057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769078 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_769078 : Nat := 118140960795 + 769078 * 2 ^ 59
def prefixEnd_769078 : Nat := 4983230072969 + 3 ^ 40 * 769078 * 2
def baseEnd_769078 : Nat := 351028155376575299989405

theorem tailTrace_769078 : CollatzResearch.WordTrace tailWord_769078 prefixEnd_769078 351028155376575299989405 := by
  unfold tailWord_769078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753161194235576806897243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18700386071846152606903925 1753161194235576806897243)
  ·
    refine ⟨2629741791353365210345865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1753161194235576806897243 2629741791353365210345865)
    ·
      refine ⟨1972306343515023907759399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2629741791353365210345865 1972306343515023907759399)
      ·
        refine ⟨2958459515272535861639099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972306343515023907759399 2958459515272535861639099)
        ·
          refine ⟨4437689272908803792458649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958459515272535861639099 4437689272908803792458649)
          ·
            refine ⟨3328266954681602844343987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4437689272908803792458649 3328266954681602844343987)
            ·
              refine ⟨4992400432022404266515981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328266954681602844343987 4992400432022404266515981)
              ·
                refine ⟨1872150162008401599943493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992400432022404266515981 1872150162008401599943493)
                ·
                  refine ⟨351028155376575299989405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1872150162008401599943493 351028155376575299989405)
                  ·
                    rfl

theorem cell20_769078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_769078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769078 prefixEnd_769078 := by exact prefixLift 769078
  have htrace : WordTrace (prefixWord ++ tailWord_769078) baseStart_769078 baseEnd_769078 := by
    simpa [prefixWord, tailWord_769078, baseEnd_769078] using wordTrace_append hprefix tailTrace_769078
  have hstable : (prefixWord ++ tailWord_769078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769078).length < 2 ^ (prefixWord ++ tailWord_769078).sum := by decide
  have hdescent : baseEnd_769078 < baseStart_769078 := by decide
  rcases family_descends (prefixWord ++ tailWord_769078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769130 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_769130 : Nat := 118140960795 + 769130 * 2 ^ 59
def prefixEnd_769130 : Nat := 4983230072969 + 3 ^ 40 * 769130 * 2
def baseEnd_769130 : Nat := 351051889593494230255859

theorem tailTrace_769130 : CollatzResearch.WordTrace tailWord_769130 prefixEnd_769130 351051889593494230255859 := by
  unfold tailWord_769130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7013118925895210447812211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18701650469053894527499229 7013118925895210447812211)
  ·
    refine ⟨10519678388842815671718317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7013118925895210447812211 10519678388842815671718317)
    ·
      refine ⟨3944879395816055876894369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10519678388842815671718317 3944879395816055876894369)
      ·
        refine ⟨2958659546862041907670777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3944879395816055876894369 2958659546862041907670777)
        ·
          refine ⟨2218994660146531430753083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958659546862041907670777 2218994660146531430753083)
          ·
            refine ⟨3328491990219797146129625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218994660146531430753083 3328491990219797146129625)
            ·
              refine ⟨2496368992664847859597219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3328491990219797146129625 2496368992664847859597219)
              ·
                refine ⟨3744553488997271789395829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496368992664847859597219 3744553488997271789395829)
                ·
                  refine ⟨351051889593494230255859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3744553488997271789395829 351051889593494230255859)
                  ·
                    rfl

theorem cell20_769130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_769130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769130 prefixEnd_769130 := by exact prefixLift 769130
  have htrace : WordTrace (prefixWord ++ tailWord_769130) baseStart_769130 baseEnd_769130 := by
    simpa [prefixWord, tailWord_769130, baseEnd_769130] using wordTrace_append hprefix tailTrace_769130
  have hstable : (prefixWord ++ tailWord_769130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769130).length < 2 ^ (prefixWord ++ tailWord_769130).sum := by decide
  have hdescent : baseEnd_769130 < baseStart_769130 := by decide
  rcases family_descends (prefixWord ++ tailWord_769130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769188 : List Nat := [2, 3, 1, 2, 3, 3, 2, 2, 2]
def baseStart_769188 : Nat := 118140960795 + 769188 * 2 ^ 59
def prefixEnd_769188 : Nat := 4983230072969 + 3 ^ 40 * 769188 * 2
def baseEnd_769188 : Nat := 351078362373903806322289

theorem tailTrace_769188 : CollatzResearch.WordTrace tailWord_769188 prefixEnd_769188 351078362373903806322289 := by
  unfold tailWord_769188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14027295568685358848430109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18703060758247145131240145 14027295568685358848430109)
  ·
    refine ⟨5260235838257009568161291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14027295568685358848430109 5260235838257009568161291)
    ·
      refine ⟨7890353757385514352241937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5260235838257009568161291 7890353757385514352241937)
      ·
        refine ⟨5917765318039135764181453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7890353757385514352241937 5917765318039135764181453)
        ·
          refine ⟨2219161994264675911568045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5917765318039135764181453 2219161994264675911568045)
          ·
            refine ⟨832185747849253466838017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2219161994264675911568045 832185747849253466838017)
            ·
              refine ⟨624139310886940100128513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832185747849253466838017 624139310886940100128513)
              ·
                refine ⟨468104483165205075096385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624139310886940100128513 468104483165205075096385)
                ·
                  refine ⟨351078362373903806322289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468104483165205075096385 351078362373903806322289)
                  ·
                    rfl

theorem cell20_769188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_769188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769188 prefixEnd_769188 := by exact prefixLift 769188
  have htrace : WordTrace (prefixWord ++ tailWord_769188) baseStart_769188 baseEnd_769188 := by
    simpa [prefixWord, tailWord_769188, baseEnd_769188] using wordTrace_append hprefix tailTrace_769188
  have hstable : (prefixWord ++ tailWord_769188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769188).length < 2 ^ (prefixWord ++ tailWord_769188).sum := by decide
  have hdescent : baseEnd_769188 < baseStart_769188 := by decide
  rcases family_descends (prefixWord ++ tailWord_769188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769222 : List Nat := [6, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_769222 : Nat := 118140960795 + 769222 * 2 ^ 59
def prefixEnd_769222 : Nat := 4983230072969 + 3 ^ 40 * 769222 * 2
def baseEnd_769222 : Nat := 351093880900350799188817

theorem tailTrace_769222 : CollatzResearch.WordTrace tailWord_769222 prefixEnd_769222 351093880900350799188817 := by
  unfold tailWord_769222
  simp only [CollatzResearch.WordTrace]
  refine ⟨876744725601485671987435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18703887479498361002398613 876744725601485671987435)
  ·
    refine ⟨1315117088402228507981153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 876744725601485671987435 1315117088402228507981153)
    ·
      refine ⟨986337816301671380985865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1315117088402228507981153 986337816301671380985865)
      ·
        refine ⟨739753362226253535739399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 986337816301671380985865 739753362226253535739399)
        ·
          refine ⟨1109630043339380303609099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739753362226253535739399 1109630043339380303609099)
          ·
            refine ⟨1664445065009070455413649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109630043339380303609099 1664445065009070455413649)
            ·
              refine ⟨1248333798756802841560237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1664445065009070455413649 1248333798756802841560237)
              ·
                refine ⟨468125174533801065585089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1248333798756802841560237 468125174533801065585089)
                ·
                  refine ⟨351093880900350799188817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468125174533801065585089 351093880900350799188817)
                  ·
                    rfl

theorem cell20_769222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_769222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769222 prefixEnd_769222 := by exact prefixLift 769222
  have htrace : WordTrace (prefixWord ++ tailWord_769222) baseStart_769222 baseEnd_769222 := by
    simpa [prefixWord, tailWord_769222, baseEnd_769222] using wordTrace_append hprefix tailTrace_769222
  have hstable : (prefixWord ++ tailWord_769222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769222).length < 2 ^ (prefixWord ++ tailWord_769222).sum := by decide
  have hdescent : baseEnd_769222 < baseStart_769222 := by decide
  rcases family_descends (prefixWord ++ tailWord_769222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769240 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 3]
def baseStart_769240 : Nat := 118140960795 + 769240 * 2 ^ 59
def prefixEnd_769240 : Nat := 4983230072969 + 3 ^ 40 * 769240 * 2
def baseEnd_769240 : Nat := 351102096590822736588743

theorem tailTrace_769240 : CollatzResearch.WordTrace tailWord_769240 prefixEnd_769240 351102096590822736588743 := by
  unfold tailWord_769240
  simp only [CollatzResearch.WordTrace]
  refine ⟨14028243866591165288876587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18704325155454887051835449 14028243866591165288876587)
  ·
    refine ⟨21042365799886747933314881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14028243866591165288876587 21042365799886747933314881)
    ·
      refine ⟨15781774349915060949986161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21042365799886747933314881 15781774349915060949986161)
      ·
        refine ⟨11836330762436295712489621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15781774349915060949986161 11836330762436295712489621)
        ·
          refine ⟨554828004489201361522951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11836330762436295712489621 554828004489201361522951)
          ·
            refine ⟨832242006733802042284427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554828004489201361522951 832242006733802042284427)
            ·
              refine ⟨1248363010100703063426641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832242006733802042284427 1248363010100703063426641)
              ·
                refine ⟨936272257575527297569981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1248363010100703063426641 936272257575527297569981)
                ·
                  refine ⟨351102096590822736588743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936272257575527297569981 351102096590822736588743)
                  ·
                    rfl

theorem cell20_769240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_769240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769240 prefixEnd_769240 := by exact prefixLift 769240
  have htrace : WordTrace (prefixWord ++ tailWord_769240) baseStart_769240 baseEnd_769240 := by
    simpa [prefixWord, tailWord_769240, baseEnd_769240] using wordTrace_append hprefix tailTrace_769240
  have hstable : (prefixWord ++ tailWord_769240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769240).length < 2 ^ (prefixWord ++ tailWord_769240).sum := by decide
  have hdescent : baseEnd_769240 < baseStart_769240 := by decide
  rcases family_descends (prefixWord ++ tailWord_769240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769303 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_769303 : Nat := 118140960795 + 769303 * 2 ^ 59
def prefixEnd_769303 : Nat := 4983230072969 + 3 ^ 40 * 769303 * 2
def baseEnd_769303 : Nat := 351130851507474517488485

theorem tailTrace_769303 : CollatzResearch.WordTrace tailWord_769303 prefixEnd_769303 351130851507474517488485 := by
  unfold tailWord_769303
  simp only [CollatzResearch.WordTrace]
  refine ⟨28058785531954092337296563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18705857021302728224864375 28058785531954092337296563)
  ·
    refine ⟨42088178297931138505944845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28058785531954092337296563 42088178297931138505944845)
    ·
      refine ⟨15783066861724176939729317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42088178297931138505944845 15783066861724176939729317)
      ·
        refine ⟨2959325036573283176199247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15783066861724176939729317 2959325036573283176199247)
        ·
          refine ⟨4438987554859924764298871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959325036573283176199247 4438987554859924764298871)
          ·
            refine ⟨6658481332289887146448307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438987554859924764298871 6658481332289887146448307)
            ·
              refine ⟨9987721998434830719672461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6658481332289887146448307 9987721998434830719672461)
              ·
                refine ⟨3745395749413061519877173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9987721998434830719672461 3745395749413061519877173)
                ·
                  refine ⟨351130851507474517488485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3745395749413061519877173 351130851507474517488485)
                  ·
                    rfl

theorem cell20_769303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_769303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769303 prefixEnd_769303 := by exact prefixLift 769303
  have htrace : WordTrace (prefixWord ++ tailWord_769303) baseStart_769303 baseEnd_769303 := by
    simpa [prefixWord, tailWord_769303, baseEnd_769303] using wordTrace_append hprefix tailTrace_769303
  have hstable : (prefixWord ++ tailWord_769303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769303).length < 2 ^ (prefixWord ++ tailWord_769303).sum := by decide
  have hdescent : baseEnd_769303 < baseStart_769303 := by decide
  rcases family_descends (prefixWord ++ tailWord_769303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769306 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_769306 : Nat := 118140960795 + 769306 * 2 ^ 59
def prefixEnd_769306 : Nat := 4983230072969 + 3 ^ 40 * 769306 * 2
def baseEnd_769306 : Nat := 351132220789219840388473

theorem tailTrace_769306 : CollatzResearch.WordTrace tailWord_769306 prefixEnd_769306 351132220789219840388473 := by
  unfold tailWord_769306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014723737735805962413943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18705929967295482566437181 7014723737735805962413943)
  ·
    refine ⟨10522085606603708943620915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7014723737735805962413943 10522085606603708943620915)
    ·
      refine ⟨15783128409905563415431373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10522085606603708943620915 15783128409905563415431373)
      ·
        refine ⟨5918673153714586280786765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15783128409905563415431373 5918673153714586280786765)
        ·
          refine ⟨2219502432642969855295037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5918673153714586280786765 2219502432642969855295037)
          ·
            refine ⟨832313412241113695735639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2219502432642969855295037 832313412241113695735639)
            ·
              refine ⟨1248470118361670543603459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832313412241113695735639 1248470118361670543603459)
              ·
                refine ⟨1872705177542505815405189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1248470118361670543603459 1872705177542505815405189)
                ·
                  refine ⟨351132220789219840388473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1872705177542505815405189 351132220789219840388473)
                  ·
                    rfl

theorem cell20_769306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_769306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769306 prefixEnd_769306 := by exact prefixLift 769306
  have htrace : WordTrace (prefixWord ++ tailWord_769306) baseStart_769306 baseEnd_769306 := by
    simpa [prefixWord, tailWord_769306, baseEnd_769306] using wordTrace_append hprefix tailTrace_769306
  have hstable : (prefixWord ++ tailWord_769306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769306).length < 2 ^ (prefixWord ++ tailWord_769306).sum := by decide
  have hdescent : baseEnd_769306 < baseStart_769306 := by decide
  rcases family_descends (prefixWord ++ tailWord_769306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769358 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_769358 : Nat := 118140960795 + 769358 * 2 ^ 59
def prefixEnd_769358 : Nat := 4983230072969 + 3 ^ 40 * 769358 * 2
def baseEnd_769358 : Nat := 351155955006138770654927

theorem tailTrace_769358 : CollatzResearch.WordTrace tailWord_769358 prefixEnd_769358 351155955006138770654927 := by
  unfold tailWord_769358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3507598943344354591318591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18707194364503224487032485 3507598943344354591318591)
  ·
    refine ⟨5261398415016531886977887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3507598943344354591318591 5261398415016531886977887)
    ·
      refine ⟨7892097622524797830466831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5261398415016531886977887 7892097622524797830466831)
      ·
        refine ⟨11838146433787196745700247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7892097622524797830466831 11838146433787196745700247)
        ·
          refine ⟨17757219650680795118550371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11838146433787196745700247 17757219650680795118550371)
          ·
            refine ⟨26635829476021192677825557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17757219650680795118550371 26635829476021192677825557)
            ·
              refine ⟨1248554506688493406773073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26635829476021192677825557 1248554506688493406773073)
              ·
                refine ⟨936415880016370055079805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1248554506688493406773073 936415880016370055079805)
                ·
                  refine ⟨351155955006138770654927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936415880016370055079805 351155955006138770654927)
                  ·
                    rfl

theorem cell20_769358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_769358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769358 prefixEnd_769358 := by exact prefixLift 769358
  have htrace : WordTrace (prefixWord ++ tailWord_769358) baseStart_769358 baseEnd_769358 := by
    simpa [prefixWord, tailWord_769358, baseEnd_769358] using wordTrace_append hprefix tailTrace_769358
  have hstable : (prefixWord ++ tailWord_769358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769358).length < 2 ^ (prefixWord ++ tailWord_769358).sum := by decide
  have hdescent : baseEnd_769358 < baseStart_769358 := by decide
  rcases family_descends (prefixWord ++ tailWord_769358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769389 : List Nat := [1, 5, 1, 1, 1, 4, 3, 4]
def baseStart_769389 : Nat := 118140960795 + 769389 * 2 ^ 59
def prefixEnd_769389 : Nat := 4983230072969 + 3 ^ 40 * 769389 * 2
def baseEnd_769389 : Nat := 117056701416946813540489

theorem tailTrace_769389 : CollatzResearch.WordTrace tailWord_769389 prefixEnd_769389 117056701416946813540489 := by
  unfold tailWord_769389
  simp only [CollatzResearch.WordTrace]
  refine ⟨28061922209642529024927221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18707948139761686016618147 28061922209642529024927221)
  ·
    refine ⟨2630805207153987096086927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28061922209642529024927221 2630805207153987096086927)
    ·
      refine ⟨3946207810730980644130391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630805207153987096086927 3946207810730980644130391)
      ·
        refine ⟨5919311716096470966195587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3946207810730980644130391 5919311716096470966195587)
        ·
          refine ⟨8878967574144706449293381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919311716096470966195587 8878967574144706449293381)
          ·
            refine ⟨1664806420152132459242509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8878967574144706449293381 1664806420152132459242509)
            ·
              refine ⟨624302407557049672215941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1664806420152132459242509 624302407557049672215941)
              ·
                refine ⟨117056701416946813540489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 624302407557049672215941 117056701416946813540489)
                ·
                  rfl

theorem cell20_769389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 4].length) (baseStart_769389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769389 prefixEnd_769389 := by exact prefixLift 769389
  have htrace : WordTrace (prefixWord ++ tailWord_769389) baseStart_769389 baseEnd_769389 := by
    simpa [prefixWord, tailWord_769389, baseEnd_769389] using wordTrace_append hprefix tailTrace_769389
  have hstable : (prefixWord ++ tailWord_769389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769389).length < 2 ^ (prefixWord ++ tailWord_769389).sum := by decide
  have hdescent : baseEnd_769389 < baseStart_769389 := by decide
  rcases family_descends (prefixWord ++ tailWord_769389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769393 : List Nat := [1, 2, 2, 2, 1, 2, 2, 8]
def baseStart_769393 : Nat := 118140960795 + 769393 * 2 ^ 59
def prefixEnd_769393 : Nat := 4983230072969 + 3 ^ 40 * 769393 * 2
def baseEnd_769393 : Nat := 117057309986611401496039

theorem tailTrace_769393 : CollatzResearch.WordTrace tailWord_769393 prefixEnd_769393 117057309986611401496039 := by
  unfold tailWord_769393
  simp only [CollatzResearch.WordTrace]
  refine ⟨28062068101628037708072833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18708045401085358472048555 28062068101628037708072833)
  ·
    refine ⟨21046551076221028281054625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28062068101628037708072833 21046551076221028281054625)
    ·
      refine ⟨15784913307165771210790969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21046551076221028281054625 15784913307165771210790969)
      ·
        refine ⟨11838684980374328408093227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15784913307165771210790969 11838684980374328408093227)
        ·
          refine ⟨17758027470561492612139841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11838684980374328408093227 17758027470561492612139841)
          ·
            refine ⟨13318520602921119459104881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17758027470561492612139841 13318520602921119459104881)
            ·
              refine ⟨9988890452190839594328661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13318520602921119459104881 9988890452190839594328661)
              ·
                refine ⟨117057309986611401496039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9988890452190839594328661 117057309986611401496039)
                ·
                  rfl

theorem cell20_769393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_769393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769393 prefixEnd_769393 := by exact prefixLift 769393
  have htrace : WordTrace (prefixWord ++ tailWord_769393) baseStart_769393 baseEnd_769393 := by
    simpa [prefixWord, tailWord_769393, baseEnd_769393] using wordTrace_append hprefix tailTrace_769393
  have hstable : (prefixWord ++ tailWord_769393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769393).length < 2 ^ (prefixWord ++ tailWord_769393).sum := by decide
  have hdescent : baseEnd_769393 < baseStart_769393 := by decide
  rcases family_descends (prefixWord ++ tailWord_769393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769406 : List Nat := [4, 2, 3, 2, 1, 1, 7]
def baseStart_769406 : Nat := 118140960795 + 769406 * 2 ^ 59
def prefixEnd_769406 : Nat := 4983230072969 + 3 ^ 40 * 769406 * 2
def baseEnd_769406 : Nat := 39019762612673770783859

theorem tailTrace_769406 : CollatzResearch.WordTrace tailWord_769406 prefixEnd_769406 39019762612673770783859 := by
  unfold tailWord_769406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3507817781322617616037009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18708361500387293952197381 3507817781322617616037009)
  ·
    refine ⟨2630863335991963212027757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3507817781322617616037009 2630863335991963212027757)
    ·
      refine ⟨986573750996986204510409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2630863335991963212027757 986573750996986204510409)
      ·
        refine ⟨739930313247739653382807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 986573750996986204510409 739930313247739653382807)
        ·
          refine ⟨1109895469871609480074211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739930313247739653382807 1109895469871609480074211)
          ·
            refine ⟨1664843204807414220111317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109895469871609480074211 1664843204807414220111317)
            ·
              refine ⟨39019762612673770783859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1664843204807414220111317 39019762612673770783859)
              ·
                rfl

theorem cell20_769406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 7].length) (baseStart_769406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769406 prefixEnd_769406 := by exact prefixLift 769406
  have htrace : WordTrace (prefixWord ++ tailWord_769406) baseStart_769406 baseEnd_769406 := by
    simpa [prefixWord, tailWord_769406, baseEnd_769406] using wordTrace_append hprefix tailTrace_769406
  have hstable : (prefixWord ++ tailWord_769406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769406).length < 2 ^ (prefixWord ++ tailWord_769406).sum := by decide
  have hdescent : baseEnd_769406 < baseStart_769406 := by decide
  rcases family_descends (prefixWord ++ tailWord_769406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769431 : List Nat := [1, 1, 3, 3, 1, 1, 1, 9]
def baseStart_769431 : Nat := 118140960795 + 769431 * 2 ^ 59
def prefixEnd_769431 : Nat := 4983230072969 + 3 ^ 40 * 769431 * 2
def baseEnd_769431 : Nat := 117063091398424987073765

theorem tailTrace_769431 : CollatzResearch.WordTrace tailWord_769431 prefixEnd_769431 117063091398424987073765 := by
  unfold tailWord_769431
  simp only [CollatzResearch.WordTrace]
  refine ⟨28063454075490370197956147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18708969383660246798637431 28063454075490370197956147)
  ·
    refine ⟨42095181113235555296934221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28063454075490370197956147 42095181113235555296934221)
    ·
      refine ⟨15785692917463333236350333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42095181113235555296934221 15785692917463333236350333)
      ·
        refine ⟨5919634844048749963631375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15785692917463333236350333 5919634844048749963631375)
        ·
          refine ⟨8879452266073124945447063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5919634844048749963631375 8879452266073124945447063)
          ·
            refine ⟨13319178399109687418170595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8879452266073124945447063 13319178399109687418170595)
            ·
              refine ⟨19978767598664531127255893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13319178399109687418170595 19978767598664531127255893)
              ·
                refine ⟨117063091398424987073765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19978767598664531127255893 117063091398424987073765)
                ·
                  rfl

theorem cell20_769431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_769431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769431 prefixEnd_769431 := by exact prefixLift 769431
  have htrace : WordTrace (prefixWord ++ tailWord_769431) baseStart_769431 baseEnd_769431 := by
    simpa [prefixWord, tailWord_769431, baseEnd_769431] using wordTrace_append hprefix tailTrace_769431
  have hstable : (prefixWord ++ tailWord_769431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769431).length < 2 ^ (prefixWord ++ tailWord_769431).sum := by decide
  have hdescent : baseEnd_769431 < baseStart_769431 := by decide
  rcases family_descends (prefixWord ++ tailWord_769431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769465 : List Nat := [1, 2, 1, 4, 5, 1, 6]
def baseStart_769465 : Nat := 118140960795 + 769465 * 2 ^ 59
def prefixEnd_769465 : Nat := 4983230072969 + 3 ^ 40 * 769465 * 2
def baseEnd_769465 : Nat := 39022754746857994898647

theorem tailTrace_769465 : CollatzResearch.WordTrace tailWord_769465 prefixEnd_769465 39022754746857994898647 := by
  unfold tailWord_769465
  simp only [CollatzResearch.WordTrace]
  refine ⟨28064694157367194004693849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18709796104911462669795899 28064694157367194004693849)
  ·
    refine ⟨21048520618025395503520387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28064694157367194004693849 21048520618025395503520387)
    ·
      refine ⟨31572780927038093255280581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21048520618025395503520387 31572780927038093255280581)
      ·
        refine ⟨5919896423819642485365109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31572780927038093255280581 5919896423819642485365109)
        ·
          refine ⟨554990289733091483002979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5919896423819642485365109 554990289733091483002979)
          ·
            refine ⟨832485434599637224504469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554990289733091483002979 832485434599637224504469)
            ·
              refine ⟨39022754746857994898647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 832485434599637224504469 39022754746857994898647)
              ·
                rfl

theorem cell20_769465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 6].length) (baseStart_769465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769465 prefixEnd_769465 := by exact prefixLift 769465
  have htrace : WordTrace (prefixWord ++ tailWord_769465) baseStart_769465 baseEnd_769465 := by
    simpa [prefixWord, tailWord_769465, baseEnd_769465] using wordTrace_append hprefix tailTrace_769465
  have hstable : (prefixWord ++ tailWord_769465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769465).length < 2 ^ (prefixWord ++ tailWord_769465).sum := by decide
  have hdescent : baseEnd_769465 < baseStart_769465 := by decide
  rcases family_descends (prefixWord ++ tailWord_769465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769593 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_769593 : Nat := 118140960795 + 769593 * 2 ^ 59
def prefixEnd_769593 : Nat := 4983230072969 + 3 ^ 40 * 769593 * 2
def baseEnd_769593 : Nat := 351263215409522397820633

theorem tailTrace_769593 : CollatzResearch.WordTrace tailWord_769593 prefixEnd_769593 351263215409522397820633 := by
  unfold tailWord_769593
  simp only [CollatzResearch.WordTrace]
  refine ⟨28069362700903471865353433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18712908467268981243568955 28069362700903471865353433)
  ·
    refine ⟨21052022025677603899015075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28069362700903471865353433 21052022025677603899015075)
    ·
      refine ⟨31578033038516405848522613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21052022025677603899015075 31578033038516405848522613)
      ·
        refine ⟨2960440597360913048298995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31578033038516405848522613 2960440597360913048298995)
        ·
          refine ⟨4440660896041369572448493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960440597360913048298995 4440660896041369572448493)
          ·
            refine ⟨1665247836015513589668185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4440660896041369572448493 1665247836015513589668185)
            ·
              refine ⟨1248935877011635192251139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665247836015513589668185 1248935877011635192251139)
              ·
                refine ⟨1873403815517452788376709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1248935877011635192251139 1873403815517452788376709)
                ·
                  refine ⟨351263215409522397820633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1873403815517452788376709 351263215409522397820633)
                  ·
                    rfl

theorem cell20_769593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_769593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769593 prefixEnd_769593 := by exact prefixLift 769593
  have htrace : WordTrace (prefixWord ++ tailWord_769593) baseStart_769593 baseEnd_769593 := by
    simpa [prefixWord, tailWord_769593, baseEnd_769593] using wordTrace_append hprefix tailTrace_769593
  have hstable : (prefixWord ++ tailWord_769593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769593).length < 2 ^ (prefixWord ++ tailWord_769593).sum := by decide
  have hdescent : baseEnd_769593 < baseStart_769593 := by decide
  rcases family_descends (prefixWord ++ tailWord_769593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769613 : List Nat := [1, 6, 1, 1, 4, 1, 2, 4]
def baseStart_769613 : Nat := 118140960795 + 769613 * 2 ^ 59
def prefixEnd_769613 : Nat := 4983230072969 + 3 ^ 40 * 769613 * 2
def baseEnd_769613 : Nat := 117090781318163739051295

theorem tailTrace_769613 : CollatzResearch.WordTrace tailWord_769613 prefixEnd_769613 117090781318163739051295 := by
  unfold tailWord_769613
  simp only [CollatzResearch.WordTrace]
  refine ⟨28070092160831015281081493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18713394773887343520720995 28070092160831015281081493)
  ·
    refine ⟨1315785570038953841300695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28070092160831015281081493 1315785570038953841300695)
    ·
      refine ⟨1973678355058430761951043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315785570038953841300695 1973678355058430761951043)
      ·
        refine ⟨2960517532587646142926565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973678355058430761951043 2960517532587646142926565)
        ·
          refine ⟨555097037360183651798731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2960517532587646142926565 555097037360183651798731)
          ·
            refine ⟨832645556040275477698097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555097037360183651798731 832645556040275477698097)
            ·
              refine ⟨624484167030206608273573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 832645556040275477698097 624484167030206608273573)
              ·
                refine ⟨117090781318163739051295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 624484167030206608273573 117090781318163739051295)
                ·
                  rfl

theorem cell20_769613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 4].length) (baseStart_769613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769613 prefixEnd_769613 := by exact prefixLift 769613
  have htrace : WordTrace (prefixWord ++ tailWord_769613) baseStart_769613 baseEnd_769613 := by
    simpa [prefixWord, tailWord_769613, baseEnd_769613] using wordTrace_append hprefix tailTrace_769613
  have hstable : (prefixWord ++ tailWord_769613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769613).length < 2 ^ (prefixWord ++ tailWord_769613).sum := by decide
  have hdescent : baseEnd_769613 < baseStart_769613 := by decide
  rcases family_descends (prefixWord ++ tailWord_769613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769659 : List Nat := [1, 1, 1, 1, 1, 4, 6, 5]
def baseStart_769659 : Nat := 118140960795 + 769659 * 2 ^ 59
def prefixEnd_769659 : Nat := 4983230072969 + 3 ^ 40 * 769659 * 2
def baseEnd_769659 : Nat := 117097779869306500540121

theorem tailTrace_769659 : CollatzResearch.WordTrace tailWord_769659 prefixEnd_769659 117097779869306500540121 := by
  unfold tailWord_769659
  simp only [CollatzResearch.WordTrace]
  refine ⟨28071769918664365137256031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18714513279109576758170687 28071769918664365137256031)
  ·
    refine ⟨42107654877996547705884047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28071769918664365137256031 42107654877996547705884047)
    ·
      refine ⟨63161482316994821558826071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42107654877996547705884047 63161482316994821558826071)
      ·
        refine ⟨94742223475492232338239107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63161482316994821558826071 94742223475492232338239107)
        ·
          refine ⟨142113335213238348507358661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94742223475492232338239107 142113335213238348507358661)
          ·
            refine ⟨26646250352482190345129749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142113335213238348507358661 26646250352482190345129749)
            ·
              refine ⟨1249042985272602672427957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26646250352482190345129749 1249042985272602672427957)
              ·
                refine ⟨117097779869306500540121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1249042985272602672427957 117097779869306500540121)
                ·
                  rfl

theorem cell20_769659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_769659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769659 prefixEnd_769659 := by exact prefixLift 769659
  have htrace : WordTrace (prefixWord ++ tailWord_769659) baseStart_769659 baseEnd_769659 := by
    simpa [prefixWord, tailWord_769659, baseEnd_769659] using wordTrace_append hprefix tailTrace_769659
  have hstable : (prefixWord ++ tailWord_769659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769659).length < 2 ^ (prefixWord ++ tailWord_769659).sum := by decide
  have hdescent : baseEnd_769659 < baseStart_769659 := by decide
  rcases family_descends (prefixWord ++ tailWord_769659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769697 : List Nat := [1, 2, 3, 3, 2, 9]
def baseStart_769697 : Nat := 118140960795 + 769697 * 2 ^ 59
def prefixEnd_769697 : Nat := 4983230072969 + 3 ^ 40 * 769697 * 2
def baseEnd_769697 : Nat := 13011506809013342901983

theorem tailTrace_769697 : CollatzResearch.WordTrace tailWord_769697 prefixEnd_769697 13011506809013342901983 := by
  unfold tailWord_769697
  simp only [CollatzResearch.WordTrace]
  refine ⟨28073155892526697627139345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18715437261684465084759563 28073155892526697627139345)
  ·
    refine ⟨21054866919395023220354509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28073155892526697627139345 21054866919395023220354509)
    ·
      refine ⟨7895575094773133707632941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21054866919395023220354509 7895575094773133707632941)
      ·
        refine ⟨2960840660539925140362353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7895575094773133707632941 2960840660539925140362353)
        ·
          refine ⟨2220630495404943855271765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2960840660539925140362353 2220630495404943855271765)
          ·
            refine ⟨13011506809013342901983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2220630495404943855271765 13011506809013342901983)
            ·
              rfl

theorem cell20_769697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 9].length) (baseStart_769697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769697 prefixEnd_769697 := by exact prefixLift 769697
  have htrace : WordTrace (prefixWord ++ tailWord_769697) baseStart_769697 baseEnd_769697 := by
    simpa [prefixWord, tailWord_769697, baseEnd_769697] using wordTrace_append hprefix tailTrace_769697
  have hstable : (prefixWord ++ tailWord_769697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769697).length < 2 ^ (prefixWord ++ tailWord_769697).sum := by decide
  have hdescent : baseEnd_769697 < baseStart_769697 := by decide
  rcases family_descends (prefixWord ++ tailWord_769697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769700 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_769700 : Nat := 118140960795 + 769700 * 2 ^ 59
def prefixEnd_769700 : Nat := 4983230072969 + 3 ^ 40 * 769700 * 2
def baseEnd_769700 : Nat := 351312053125105581253529

theorem tailTrace_769700 : CollatzResearch.WordTrace tailWord_769700 prefixEnd_769700 351312053125105581253529 := by
  unfold tailWord_769700
  simp only [CollatzResearch.WordTrace]
  refine ⟨14036632655757914569749277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18715510207677219426332369 14036632655757914569749277)
  ·
    refine ⟨5263737245909217963655979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14036632655757914569749277 5263737245909217963655979)
    ·
      refine ⟨7895605868863826945483969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5263737245909217963655979 7895605868863826945483969)
      ·
        refine ⟨5921704401647870209112977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7895605868863826945483969 5921704401647870209112977)
        ·
          refine ⟨4441278301235902656834733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5921704401647870209112977 4441278301235902656834733)
          ·
            refine ⟨1665479362963463496313025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4441278301235902656834733 1665479362963463496313025)
            ·
              refine ⟨1249109522222597622234769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665479362963463496313025 1249109522222597622234769)
              ·
                refine ⟨936832141666948216676077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249109522222597622234769 936832141666948216676077)
                ·
                  refine ⟨351312053125105581253529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936832141666948216676077 351312053125105581253529)
                  ·
                    rfl

theorem cell20_769700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_769700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769700 prefixEnd_769700 := by exact prefixLift 769700
  have htrace : WordTrace (prefixWord ++ tailWord_769700) baseStart_769700 baseEnd_769700 := by
    simpa [prefixWord, tailWord_769700, baseEnd_769700] using wordTrace_append hprefix tailTrace_769700
  have hstable : (prefixWord ++ tailWord_769700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769700).length < 2 ^ (prefixWord ++ tailWord_769700).sum := by decide
  have hdescent : baseEnd_769700 < baseStart_769700 := by decide
  rcases family_descends (prefixWord ++ tailWord_769700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769710 : List Nat := [4, 1, 4, 1, 2, 2, 1, 5]
def baseStart_769710 : Nat := 118140960795 + 769710 * 2 ^ 59
def prefixEnd_769710 : Nat := 4983230072969 + 3 ^ 40 * 769710 * 2
def baseEnd_769710 : Nat := 117105539132529996973385

theorem tailTrace_769710 : CollatzResearch.WordTrace tailWord_769710 prefixEnd_769710 117105539132529996973385 := by
  unfold tailWord_769710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509203755184950105920323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18715753360986400564908389 3509203755184950105920323)
  ·
    refine ⟨5263805632777425158880485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509203755184950105920323 5263805632777425158880485)
    ·
      refine ⟨986963556145767217290091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5263805632777425158880485 986963556145767217290091)
      ·
        refine ⟨1480445334218650825935137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986963556145767217290091 1480445334218650825935137)
        ·
          refine ⟨1110334000663988119451353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480445334218650825935137 1110334000663988119451353)
          ·
            refine ⟨832750500497991089588515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110334000663988119451353 832750500497991089588515)
            ·
              refine ⟨1249125750746986634382773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832750500497991089588515 1249125750746986634382773)
              ·
                refine ⟨117105539132529996973385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1249125750746986634382773 117105539132529996973385)
                ·
                  rfl

theorem cell20_769710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_769710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769710 prefixEnd_769710 := by exact prefixLift 769710
  have htrace : WordTrace (prefixWord ++ tailWord_769710) baseStart_769710 baseEnd_769710 := by
    simpa [prefixWord, tailWord_769710, baseEnd_769710] using wordTrace_append hprefix tailTrace_769710
  have hstable : (prefixWord ++ tailWord_769710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769710).length < 2 ^ (prefixWord ++ tailWord_769710).sum := by decide
  have hdescent : baseEnd_769710 < baseStart_769710 := by decide
  rcases family_descends (prefixWord ++ tailWord_769710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769721 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 3]
def baseStart_769721 : Nat := 118140960795 + 769721 * 2 ^ 59
def prefixEnd_769721 : Nat := 4983230072969 + 3 ^ 40 * 769721 * 2
def baseEnd_769721 : Nat := 351321638097322841553443

theorem tailTrace_769721 : CollatzResearch.WordTrace tailWord_769721 prefixEnd_769721 351321638097322841553443 := by
  unfold tailWord_769721
  simp only [CollatzResearch.WordTrace]
  refine ⟨28074031244439749726013017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18716020829626499817342011 28074031244439749726013017)
  ·
    refine ⟨21055523433329812294509763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28074031244439749726013017 21055523433329812294509763)
    ·
      refine ⟨31583285149994718441764645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21055523433329812294509763 31583285149994718441764645)
      ·
        refine ⟨5921865965624009707830871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31583285149994718441764645 5921865965624009707830871)
        ·
          refine ⟨8882798948436014561746307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921865965624009707830871 8882798948436014561746307)
          ·
            refine ⟨13324198422654021842619461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8882798948436014561746307 13324198422654021842619461)
            ·
              refine ⟨2498287204247629095491149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13324198422654021842619461 2498287204247629095491149)
              ·
                refine ⟨936857701592860910809181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2498287204247629095491149 936857701592860910809181)
                ·
                  refine ⟨351321638097322841553443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936857701592860910809181 351321638097322841553443)
                  ·
                    rfl

theorem cell20_769721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_769721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769721 prefixEnd_769721 := by exact prefixLift 769721
  have htrace : WordTrace (prefixWord ++ tailWord_769721) baseStart_769721 baseEnd_769721 := by
    simpa [prefixWord, tailWord_769721, baseEnd_769721] using wordTrace_append hprefix tailTrace_769721
  have hstable : (prefixWord ++ tailWord_769721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769721).length < 2 ^ (prefixWord ++ tailWord_769721).sum := by decide
  have hdescent : baseEnd_769721 < baseStart_769721 := by decide
  rcases family_descends (prefixWord ++ tailWord_769721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769728 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_769728 : Nat := 118140960795 + 769728 * 2 ^ 59
def prefixEnd_769728 : Nat := 4983230072969 + 3 ^ 40 * 769728 * 2
def baseEnd_769728 : Nat := 351324833088061928320081

theorem tailTrace_769728 : CollatzResearch.WordTrace tailWord_769728 prefixEnd_769728 351324833088061928320081 := by
  unfold tailWord_769728
  simp only [CollatzResearch.WordTrace]
  refine ⟨14037143277707194960758919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18716191036942926614345225 14037143277707194960758919)
  ·
    refine ⟨21055714916560792441138379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14037143277707194960758919 21055714916560792441138379)
    ·
      refine ⟨31583572374841188661707569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21055714916560792441138379 31583572374841188661707569)
      ·
        refine ⟨23687679281130891496280677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31583572374841188661707569 23687679281130891496280677)
        ·
          refine ⟨4441439865212042155552627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23687679281130891496280677 4441439865212042155552627)
          ·
            refine ⟨6662159797818063233328941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441439865212042155552627 6662159797818063233328941)
            ·
              refine ⟨2498309924181773712498353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6662159797818063233328941 2498309924181773712498353)
              ·
                refine ⟨1873732443136330284373765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2498309924181773712498353 1873732443136330284373765)
                ·
                  refine ⟨351324833088061928320081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1873732443136330284373765 351324833088061928320081)
                  ·
                    rfl

theorem cell20_769728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_769728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769728 prefixEnd_769728 := by exact prefixLift 769728
  have htrace : WordTrace (prefixWord ++ tailWord_769728) baseStart_769728 baseEnd_769728 := by
    simpa [prefixWord, tailWord_769728, baseEnd_769728] using wordTrace_append hprefix tailTrace_769728
  have hstable : (prefixWord ++ tailWord_769728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769728).length < 2 ^ (prefixWord ++ tailWord_769728).sum := by decide
  have hdescent : baseEnd_769728 < baseStart_769728 := by decide
  rcases family_descends (prefixWord ++ tailWord_769728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769741 : List Nat := [1, 6, 2, 1, 1, 1, 1, 5, 2]
def baseStart_769741 : Nat := 118140960795 + 769741 * 2 ^ 59
def prefixEnd_769741 : Nat := 4983230072969 + 3 ^ 40 * 769741 * 2
def baseEnd_769741 : Nat := 351330766642291660886695

theorem tailTrace_769741 : CollatzResearch.WordTrace tailWord_769741 prefixEnd_769741 351330766642291660886695 := by
  unfold tailWord_769741
  simp only [CollatzResearch.WordTrace]
  refine ⟨28074760704367293141741077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18716507136244862094494051 28074760704367293141741077)
  ·
    refine ⟨1316004408017216866019113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28074760704367293141741077 1316004408017216866019113)
    ·
      refine ⟨987003306012912649514335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1316004408017216866019113 987003306012912649514335)
      ·
        refine ⟨1480504959019368974271503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987003306012912649514335 1480504959019368974271503)
        ·
          refine ⟨2220757438529053461407255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480504959019368974271503 2220757438529053461407255)
          ·
            refine ⟨3331136157793580192110883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2220757438529053461407255 3331136157793580192110883)
            ·
              refine ⟨4996704236690370288166325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331136157793580192110883 4996704236690370288166325)
              ·
                refine ⟨468441022189722214515593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4996704236690370288166325 468441022189722214515593)
                ·
                  refine ⟨351330766642291660886695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468441022189722214515593 351330766642291660886695)
                  ·
                    rfl

theorem cell20_769741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_769741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769741 prefixEnd_769741 := by exact prefixLift 769741
  have htrace : WordTrace (prefixWord ++ tailWord_769741) baseStart_769741 baseEnd_769741 := by
    simpa [prefixWord, tailWord_769741, baseEnd_769741] using wordTrace_append hprefix tailTrace_769741
  have hstable : (prefixWord ++ tailWord_769741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769741).length < 2 ^ (prefixWord ++ tailWord_769741).sum := by decide
  have hdescent : baseEnd_769741 < baseStart_769741 := by decide
  rcases family_descends (prefixWord ++ tailWord_769741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769745 : List Nat := [1, 2, 2, 1, 2, 4, 1, 5, 2]
def baseStart_769745 : Nat := 118140960795 + 769745 * 2 ^ 59
def prefixEnd_769745 : Nat := 4983230072969 + 3 ^ 40 * 769745 * 2
def baseEnd_769745 : Nat := 351332592351285424753345

theorem tailTrace_769745 : CollatzResearch.WordTrace tailWord_769745 prefixEnd_769745 351332592351285424753345 := by
  unfold tailWord_769745
  simp only [CollatzResearch.WordTrace]
  refine ⟨28074906596352801824886689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18716604397568534549924459 28074906596352801824886689)
  ·
    refine ⟨21056179947264601368665017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28074906596352801824886689 21056179947264601368665017)
    ·
      refine ⟨15792134960448451026498763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21056179947264601368665017 15792134960448451026498763)
      ·
        refine ⟨23688202440672676539748145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15792134960448451026498763 23688202440672676539748145)
        ·
          refine ⟨17766151830504507404811109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23688202440672676539748145 17766151830504507404811109)
          ·
            refine ⟨3331153468219595138402083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17766151830504507404811109 3331153468219595138402083)
            ·
              refine ⟨4996730202329392707603125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331153468219595138402083 4996730202329392707603125)
              ·
                refine ⟨468443456468380566337793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4996730202329392707603125 468443456468380566337793)
                ·
                  refine ⟨351332592351285424753345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468443456468380566337793 351332592351285424753345)
                  ·
                    rfl

theorem cell20_769745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_769745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769745 prefixEnd_769745 := by exact prefixLift 769745
  have htrace : WordTrace (prefixWord ++ tailWord_769745) baseStart_769745 baseEnd_769745 := by
    simpa [prefixWord, tailWord_769745, baseEnd_769745] using wordTrace_append hprefix tailTrace_769745
  have hstable : (prefixWord ++ tailWord_769745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769745).length < 2 ^ (prefixWord ++ tailWord_769745).sum := by decide
  have hdescent : baseEnd_769745 < baseStart_769745 := by decide
  rcases family_descends (prefixWord ++ tailWord_769745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769787 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_769787 : Nat := 118140960795 + 769787 * 2 ^ 59
def prefixEnd_769787 : Nat := 4983230072969 + 3 ^ 40 * 769787 * 2
def baseEnd_769787 : Nat := 351351762295719945353173

theorem tailTrace_769787 : CollatzResearch.WordTrace tailWord_769787 prefixEnd_769787 351351762295719945353173 := by
  unfold tailWord_769787
  simp only [CollatzResearch.WordTrace]
  refine ⟨28076438462200642997915615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18717625641467095331943743 28076438462200642997915615)
  ·
    refine ⟨42114657693300964496873423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28076438462200642997915615 42114657693300964496873423)
    ·
      refine ⟨63171986539951446745310135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42114657693300964496873423 63171986539951446745310135)
      ·
        refine ⟨94757979809927170117965203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63171986539951446745310135 94757979809927170117965203)
        ·
          refine ⟨142136969714890755176947805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94757979809927170117965203 142136969714890755176947805)
          ·
            refine ⟨53301363643084033191355427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142136969714890755176947805 53301363643084033191355427)
            ·
              refine ⟨79952045464626049787033141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53301363643084033191355427 79952045464626049787033141)
              ·
                refine ⟨7495504262308692167534357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79952045464626049787033141 7495504262308692167534357)
                ·
                  refine ⟨351351762295719945353173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7495504262308692167534357 351351762295719945353173)
                  ·
                    rfl

theorem cell20_769787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_769787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769787 prefixEnd_769787 := by exact prefixLift 769787
  have htrace : WordTrace (prefixWord ++ tailWord_769787) baseStart_769787 baseEnd_769787 := by
    simpa [prefixWord, tailWord_769787, baseEnd_769787] using wordTrace_append hprefix tailTrace_769787
  have hstable : (prefixWord ++ tailWord_769787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769787).length < 2 ^ (prefixWord ++ tailWord_769787).sum := by decide
  have hdescent : baseEnd_769787 < baseStart_769787 := by decide
  rcases family_descends (prefixWord ++ tailWord_769787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769828 : List Nat := [2, 3, 1, 3, 2, 2, 2, 5]
def baseStart_769828 : Nat := 118140960795 + 769828 * 2 ^ 59
def prefixEnd_769828 : Nat := 4983230072969 + 3 ^ 40 * 769828 * 2
def baseEnd_769828 : Nat := 117123491937635341662113

theorem tailTrace_769828 : CollatzResearch.WordTrace tailWord_769828 prefixEnd_769828 117123491937635341662113 := by
  unfold tailWord_769828
  simp only [CollatzResearch.WordTrace]
  refine ⟨14038966927526053500079069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18718622570034738000105425 14038966927526053500079069)
  ·
    refine ⟨5264612597822270062529651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14038966927526053500079069 5264612597822270062529651)
    ·
      refine ⟨7896918896733405093794477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264612597822270062529651 7896918896733405093794477)
      ·
        refine ⟨2961344586275026910172929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7896918896733405093794477 2961344586275026910172929)
        ·
          refine ⟨2221008439706270182629697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2961344586275026910172929 2221008439706270182629697)
          ·
            refine ⟨1665756329779702636972273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221008439706270182629697 1665756329779702636972273)
            ·
              refine ⟨1249317247334776977729205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665756329779702636972273 1249317247334776977729205)
              ·
                refine ⟨117123491937635341662113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1249317247334776977729205 117123491937635341662113)
                ·
                  rfl

theorem cell20_769828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_769828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769828 prefixEnd_769828 := by exact prefixLift 769828
  have htrace : WordTrace (prefixWord ++ tailWord_769828) baseStart_769828 baseEnd_769828 := by
    simpa [prefixWord, tailWord_769828, baseEnd_769828] using wordTrace_append hprefix tailTrace_769828
  have hstable : (prefixWord ++ tailWord_769828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769828).length < 2 ^ (prefixWord ++ tailWord_769828).sum := by decide
  have hdescent : baseEnd_769828 < baseStart_769828 := by decide
  rcases family_descends (prefixWord ++ tailWord_769828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769869 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 3]
def baseStart_769869 : Nat := 118140960795 + 769869 * 2 ^ 59
def prefixEnd_769869 : Nat := 4983230072969 + 3 ^ 40 * 769869 * 2
def baseEnd_769869 : Nat := 351389189330092104619505

theorem tailTrace_769869 : CollatzResearch.WordTrace tailWord_769869 prefixEnd_769869 351389189330092104619505 := by
  unfold tailWord_769869
  simp only [CollatzResearch.WordTrace]
  refine ⟨28079429247903571002400661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18719619498602380668267107 28079429247903571002400661)
  ·
    refine ⟨1316223245995479890737531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28079429247903571002400661 1316223245995479890737531)
    ·
      refine ⟨1974334868993219836106297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1316223245995479890737531 1974334868993219836106297)
      ·
        refine ⟨1480751151744914877079723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1974334868993219836106297 1480751151744914877079723)
        ·
          refine ⟨2221126727617372315619585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480751151744914877079723 2221126727617372315619585)
          ·
            refine ⟨1665845045713029236714689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221126727617372315619585 1665845045713029236714689)
            ·
              refine ⟨1249383784284771927536017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665845045713029236714689 1249383784284771927536017)
              ·
                refine ⟨937037838213578945652013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249383784284771927536017 937037838213578945652013)
                ·
                  refine ⟨351389189330092104619505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937037838213578945652013 351389189330092104619505)
                  ·
                    rfl

theorem cell20_769869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_769869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769869 prefixEnd_769869 := by exact prefixLift 769869
  have htrace : WordTrace (prefixWord ++ tailWord_769869) baseStart_769869 baseEnd_769869 := by
    simpa [prefixWord, tailWord_769869, baseEnd_769869] using wordTrace_append hprefix tailTrace_769869
  have hstable : (prefixWord ++ tailWord_769869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769869).length < 2 ^ (prefixWord ++ tailWord_769869).sum := by decide
  have hdescent : baseEnd_769869 < baseStart_769869 := by decide
  rcases family_descends (prefixWord ++ tailWord_769869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769873 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 3]
def baseStart_769873 : Nat := 118140960795 + 769873 * 2 ^ 59
def prefixEnd_769873 : Nat := 4983230072969 + 3 ^ 40 * 769873 * 2
def baseEnd_769873 : Nat := 351391015039085868486155

theorem tailTrace_769873 : CollatzResearch.WordTrace tailWord_769873 prefixEnd_769873 351391015039085868486155 := by
  unfold tailWord_769873
  simp only [CollatzResearch.WordTrace]
  refine ⟨28079575139889079685546273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18719716759926053123697515 28079575139889079685546273)
  ·
    refine ⟨21059681354916809764159705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28079575139889079685546273 21059681354916809764159705)
    ·
      refine ⟨15794761016187607323119779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21059681354916809764159705 15794761016187607323119779)
      ·
        refine ⟨23692141524281410984679669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15794761016187607323119779 23692141524281410984679669)
        ·
          refine ⟨2221138267901382279813719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23692141524281410984679669 2221138267901382279813719)
          ·
            refine ⟨3331707401852073419720579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221138267901382279813719 3331707401852073419720579)
            ·
              refine ⟨4997561102778110129580869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331707401852073419720579 4997561102778110129580869)
              ·
                refine ⟨937042706770895649296413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4997561102778110129580869 937042706770895649296413)
                ·
                  refine ⟨351391015039085868486155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937042706770895649296413 351391015039085868486155)
                  ·
                    rfl

theorem cell20_769873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_769873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769873 prefixEnd_769873 := by exact prefixLift 769873
  have htrace : WordTrace (prefixWord ++ tailWord_769873) baseStart_769873 baseEnd_769873 := by
    simpa [prefixWord, tailWord_769873, baseEnd_769873] using wordTrace_append hprefix tailTrace_769873
  have hstable : (prefixWord ++ tailWord_769873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769873).length < 2 ^ (prefixWord ++ tailWord_769873).sum := by decide
  have hdescent : baseEnd_769873 < baseStart_769873 := by decide
  rcases family_descends (prefixWord ++ tailWord_769873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769876 : List Nat := [2, 4, 1, 1, 3, 2, 1, 4, 2]
def baseStart_769876 : Nat := 118140960795 + 769876 * 2 ^ 59
def prefixEnd_769876 : Nat := 4983230072969 + 3 ^ 40 * 769876 * 2
def baseEnd_769876 : Nat := 351392384320831191386143

theorem tailTrace_769876 : CollatzResearch.WordTrace tailWord_769876 prefixEnd_769876 351392384320831191386143 := by
  unfold tailWord_769876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14039842279439105598952741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18719789705918807465270321 14039842279439105598952741)
  ·
    refine ⟨2632470427394832299803639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14039842279439105598952741 2632470427394832299803639)
    ·
      refine ⟨3948705641092248449705459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2632470427394832299803639 3948705641092248449705459)
      ·
        refine ⟨5923058461638372674558189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3948705641092248449705459 5923058461638372674558189)
        ·
          refine ⟨2221146923114389752959321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5923058461638372674558189 2221146923114389752959321)
          ·
            refine ⟨1665860192335792314719491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221146923114389752959321 1665860192335792314719491)
            ·
              refine ⟨2498790288503688472079237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665860192335792314719491 2498790288503688472079237)
              ·
                refine ⟨468523179094441588514857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2498790288503688472079237 468523179094441588514857)
                ·
                  refine ⟨351392384320831191386143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468523179094441588514857 351392384320831191386143)
                  ·
                    rfl

theorem cell20_769876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_769876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769876 prefixEnd_769876 := by exact prefixLift 769876
  have htrace : WordTrace (prefixWord ++ tailWord_769876) baseStart_769876 baseEnd_769876 := by
    simpa [prefixWord, tailWord_769876, baseEnd_769876] using wordTrace_append hprefix tailTrace_769876
  have hstable : (prefixWord ++ tailWord_769876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769876).length < 2 ^ (prefixWord ++ tailWord_769876).sum := by decide
  have hdescent : baseEnd_769876 < baseStart_769876 := by decide
  rcases family_descends (prefixWord ++ tailWord_769876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769887 : List Nat := [1, 1, 2, 3, 1, 4, 3, 5]
def baseStart_769887 : Nat := 118140960795 + 769887 * 2 ^ 59
def prefixEnd_769887 : Nat := 4983230072969 + 3 ^ 40 * 769887 * 2
def baseEnd_769887 : Nat := 117132468340188014006477

theorem tailTrace_769887 : CollatzResearch.WordTrace tailWord_769887 prefixEnd_769887 117132468340188014006477 := by
  unfold tailWord_769887
  simp only [CollatzResearch.WordTrace]
  refine ⟨28080085761838360076555915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18720057174558906717703943 28080085761838360076555915)
  ·
    refine ⟨42120128642757540114833873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28080085761838360076555915 42120128642757540114833873)
    ·
      refine ⟨31590096482068155086125405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42120128642757540114833873 31590096482068155086125405)
      ·
        refine ⟨11846286180775558157297027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31590096482068155086125405 11846286180775558157297027)
        ·
          refine ⟨17769429271163337235945541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11846286180775558157297027 17769429271163337235945541)
          ·
            refine ⟨3331767988343125731739789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17769429271163337235945541 3331767988343125731739789)
            ·
              refine ⟨1249412995628672149402421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3331767988343125731739789 1249412995628672149402421)
              ·
                refine ⟨117132468340188014006477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1249412995628672149402421 117132468340188014006477)
                ·
                  rfl

theorem cell20_769887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_769887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769887 prefixEnd_769887 := by exact prefixLift 769887
  have htrace : WordTrace (prefixWord ++ tailWord_769887) baseStart_769887 baseEnd_769887 := by
    simpa [prefixWord, tailWord_769887, baseEnd_769887] using wordTrace_append hprefix tailTrace_769887
  have hstable : (prefixWord ++ tailWord_769887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769887).length < 2 ^ (prefixWord ++ tailWord_769887).sum := by decide
  have hdescent : baseEnd_769887 < baseStart_769887 := by decide
  rcases family_descends (prefixWord ++ tailWord_769887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769890 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_769890 : Nat := 118140960795 + 769890 * 2 ^ 59
def prefixEnd_769890 : Nat := 4983230072969 + 3 ^ 40 * 769890 * 2
def baseEnd_769890 : Nat := 351398774302309364919419

theorem tailTrace_769890 : CollatzResearch.WordTrace tailWord_769890 prefixEnd_769890 351398774302309364919419 := by
  unfold tailWord_769890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7020048795206872897228781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18720130120551661059276749 7020048795206872897228781)
  ·
    refine ⟨2632518298202577336460793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7020048795206872897228781 2632518298202577336460793)
    ·
      refine ⟨1974388723651933002345595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2632518298202577336460793 1974388723651933002345595)
      ·
        refine ⟨2961583085477899503518393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974388723651933002345595 2961583085477899503518393)
        ·
          refine ⟨2221187314108424627638795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2961583085477899503518393 2221187314108424627638795)
          ·
            refine ⟨3331780971162636941458193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221187314108424627638795 3331780971162636941458193)
            ·
              refine ⟨2498835728371977706093645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3331780971162636941458193 2498835728371977706093645)
              ·
                refine ⟨937063398139491639785117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2498835728371977706093645 937063398139491639785117)
                ·
                  refine ⟨351398774302309364919419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937063398139491639785117 351398774302309364919419)
                  ·
                    rfl

theorem cell20_769890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_769890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769890 prefixEnd_769890 := by exact prefixLift 769890
  have htrace : WordTrace (prefixWord ++ tailWord_769890) baseStart_769890 baseEnd_769890 := by
    simpa [prefixWord, tailWord_769890, baseEnd_769890] using wordTrace_append hprefix tailTrace_769890
  have hstable : (prefixWord ++ tailWord_769890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769890).length < 2 ^ (prefixWord ++ tailWord_769890).sum := by decide
  have hdescent : baseEnd_769890 < baseStart_769890 := by decide
  rcases family_descends (prefixWord ++ tailWord_769890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769956 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_769956 : Nat := 118140960795 + 769956 * 2 ^ 59
def prefixEnd_769956 : Nat := 4983230072969 + 3 ^ 40 * 769956 * 2
def baseEnd_769956 : Nat := 351428898500706468719149

theorem tailTrace_769956 : CollatzResearch.WordTrace tailWord_769956 prefixEnd_769956 351428898500706468719149 := by
  unfold tailWord_769956
  simp only [CollatzResearch.WordTrace]
  refine ⟨14041301199294192430408861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18721734932392256573878481 14041301199294192430408861)
  ·
    refine ⟨5265487949735322161403323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14041301199294192430408861 5265487949735322161403323)
    ·
      refine ⟨7898231924602983242104985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5265487949735322161403323 7898231924602983242104985)
      ·
        refine ⟨5923673943452237431578739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7898231924602983242104985 5923673943452237431578739)
        ·
          refine ⟨8885510915178356147368109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5923673943452237431578739 8885510915178356147368109)
          ·
            refine ⟨3332066593191883555263041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8885510915178356147368109 3332066593191883555263041)
            ·
              refine ⟨2499049944893912666447281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3332066593191883555263041 2499049944893912666447281)
              ·
                refine ⟨1874287458670434499835461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499049944893912666447281 1874287458670434499835461)
                ·
                  refine ⟨351428898500706468719149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874287458670434499835461 351428898500706468719149)
                  ·
                    rfl

theorem cell20_769956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_769956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769956 prefixEnd_769956 := by exact prefixLift 769956
  have htrace : WordTrace (prefixWord ++ tailWord_769956) baseStart_769956 baseEnd_769956 := by
    simpa [prefixWord, tailWord_769956, baseEnd_769956] using wordTrace_append hprefix tailTrace_769956
  have hstable : (prefixWord ++ tailWord_769956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769956).length < 2 ^ (prefixWord ++ tailWord_769956).sum := by decide
  have hdescent : baseEnd_769956 < baseStart_769956 := by decide
  rcases family_descends (prefixWord ++ tailWord_769956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769959 : List Nat := [1, 1, 6, 1, 2, 3, 2, 4]
def baseStart_769959 : Nat := 118140960795 + 769959 * 2 ^ 59
def prefixEnd_769959 : Nat := 4983230072969 + 3 ^ 40 * 769959 * 2
def baseEnd_769959 : Nat := 117143422594150597206379

theorem tailTrace_769959 : CollatzResearch.WordTrace tailWord_769959 prefixEnd_769959 117143422594150597206379 := by
  unfold tailWord_769959
  simp only [CollatzResearch.WordTrace]
  refine ⟨28082711817577516373176931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18721807878385010915451287 28082711817577516373176931)
  ·
    refine ⟨42124067726366274559765397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28082711817577516373176931 42124067726366274559765397)
    ·
      refine ⟨1974565674673419119989003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42124067726366274559765397 1974565674673419119989003)
      ·
        refine ⟨2961848512010128679983505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974565674673419119989003 2961848512010128679983505)
        ·
          refine ⟨2221386384007596509987629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2961848512010128679983505 2221386384007596509987629)
          ·
            refine ⟨833019894002848691245361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2221386384007596509987629 833019894002848691245361)
            ·
              refine ⟨624764920502136518434021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833019894002848691245361 624764920502136518434021)
              ·
                refine ⟨117143422594150597206379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 624764920502136518434021 117143422594150597206379)
                ·
                  rfl

theorem cell20_769959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 4].length) (baseStart_769959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769959 prefixEnd_769959 := by exact prefixLift 769959
  have htrace : WordTrace (prefixWord ++ tailWord_769959) baseStart_769959 baseEnd_769959 := by
    simpa [prefixWord, tailWord_769959, baseEnd_769959] using wordTrace_append hprefix tailTrace_769959
  have hstable : (prefixWord ++ tailWord_769959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769959).length < 2 ^ (prefixWord ++ tailWord_769959).sum := by decide
  have hdescent : baseEnd_769959 < baseStart_769959 := by decide
  rcases family_descends (prefixWord ++ tailWord_769959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769994 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_769994 : Nat := 118140960795 + 769994 * 2 ^ 59
def prefixEnd_769994 : Nat := 4983230072969 + 3 ^ 40 * 769994 * 2
def baseEnd_769994 : Nat := 351446242736147225452327

theorem tailTrace_769994 : CollatzResearch.WordTrace tailWord_769994 prefixEnd_769994 351446242736147225452327 := by
  unfold tailWord_769994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7020997093112679337675259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18722658914967144900467357 7020997093112679337675259)
  ·
    refine ⟨10531495639669019006512889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7020997093112679337675259 10531495639669019006512889)
    ·
      refine ⟨7898621729751764254884667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10531495639669019006512889 7898621729751764254884667)
      ·
        refine ⟨11847932594627646382327001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7898621729751764254884667 11847932594627646382327001)
        ·
          refine ⟨8885949445970734786745251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11847932594627646382327001 8885949445970734786745251)
          ·
            refine ⟨13328924168956102180117877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8885949445970734786745251 13328924168956102180117877)
            ·
              refine ⟨1249586640839634579386051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13328924168956102180117877 1249586640839634579386051)
              ·
                refine ⟨1874379961259451869079077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249586640839634579386051 1874379961259451869079077)
                ·
                  refine ⟨351446242736147225452327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874379961259451869079077 351446242736147225452327)
                  ·
                    rfl

theorem cell20_769994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_769994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_769994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_769994 prefixEnd_769994 := by exact prefixLift 769994
  have htrace : WordTrace (prefixWord ++ tailWord_769994) baseStart_769994 baseEnd_769994 := by
    simpa [prefixWord, tailWord_769994, baseEnd_769994] using wordTrace_append hprefix tailTrace_769994
  have hstable : (prefixWord ++ tailWord_769994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769994).length < 2 ^ (prefixWord ++ tailWord_769994).sum := by decide
  have hdescent : baseEnd_769994 < baseStart_769994 := by decide
  rcases family_descends (prefixWord ++ tailWord_769994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770049 : List Nat := [1, 2, 4, 1, 2, 1, 3, 4, 2]
def baseStart_770049 : Nat := 118140960795 + 770049 * 2 ^ 59
def prefixEnd_770049 : Nat := 4983230072969 + 3 ^ 40 * 770049 * 2
def baseEnd_770049 : Nat := 351471346234811478618769

theorem tailTrace_770049 : CollatzResearch.WordTrace tailWord_770049 prefixEnd_770049 351471346234811478618769 := by
  unfold tailWord_770049
  simp only [CollatzResearch.WordTrace]
  refine ⟨28085994387251461743953201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18723996258167641162635467 28085994387251461743953201)
  ·
    refine ⟨21064495790438596307964901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28085994387251461743953201 21064495790438596307964901)
    ·
      refine ⟨3949592960707236807743419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21064495790438596307964901 3949592960707236807743419)
      ·
        refine ⟨5924389441060855211615129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3949592960707236807743419 5924389441060855211615129)
        ·
          refine ⟨4443292080795641408711347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5924389441060855211615129 4443292080795641408711347)
          ·
            refine ⟨6664938121193462113067021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443292080795641408711347 6664938121193462113067021)
            ·
              refine ⟨2499351795447548292400133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6664938121193462113067021 2499351795447548292400133)
              ·
                refine ⟨468628461646415304825025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2499351795447548292400133 468628461646415304825025)
                ·
                  refine ⟨351471346234811478618769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468628461646415304825025 351471346234811478618769)
                  ·
                    rfl

theorem cell20_770049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_770049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770049 prefixEnd_770049 := by exact prefixLift 770049
  have htrace : WordTrace (prefixWord ++ tailWord_770049) baseStart_770049 baseEnd_770049 := by
    simpa [prefixWord, tailWord_770049, baseEnd_770049] using wordTrace_append hprefix tailTrace_770049
  have hstable : (prefixWord ++ tailWord_770049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770049).length < 2 ^ (prefixWord ++ tailWord_770049).sum := by decide
  have hdescent : baseEnd_770049 < baseStart_770049 := by decide
  rcases family_descends (prefixWord ++ tailWord_770049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770052 : List Nat := [2, 3, 2, 4, 2, 1, 1, 5]
def baseStart_770052 : Nat := 118140960795 + 770052 * 2 ^ 59
def prefixEnd_770052 : Nat := 4983230072969 + 3 ^ 40 * 770052 * 2
def baseEnd_770052 : Nat := 117157571838852267172919

theorem tailTrace_770052 : CollatzResearch.WordTrace tailWord_770052 prefixEnd_770052 117157571838852267172919 := by
  unfold tailWord_770052
  simp only [CollatzResearch.WordTrace]
  refine ⟨14043051903120296628156205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18724069204160395504208273 14043051903120296628156205)
  ·
    refine ⟨5266144463670111235558577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14043051903120296628156205 5266144463670111235558577)
    ·
      refine ⟨3949608347752583426668933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5266144463670111235558577 3949608347752583426668933)
      ·
        refine ⟨740551565203609392500425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3949608347752583426668933 740551565203609392500425)
        ·
          refine ⟨555413673902707044375319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 740551565203609392500425 555413673902707044375319)
          ·
            refine ⟨833120510854060566562979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555413673902707044375319 833120510854060566562979)
            ·
              refine ⟨1249680766281090849844469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833120510854060566562979 1249680766281090849844469)
              ·
                refine ⟨117157571838852267172919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1249680766281090849844469 117157571838852267172919)
                ·
                  rfl

theorem cell20_770052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_770052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770052 prefixEnd_770052 := by exact prefixLift 770052
  have htrace : WordTrace (prefixWord ++ tailWord_770052) baseStart_770052 baseEnd_770052 := by
    simpa [prefixWord, tailWord_770052, baseEnd_770052] using wordTrace_append hprefix tailTrace_770052
  have hstable : (prefixWord ++ tailWord_770052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770052).length < 2 ^ (prefixWord ++ tailWord_770052).sum := by decide
  have hdescent : baseEnd_770052 < baseStart_770052 := by decide
  rcases family_descends (prefixWord ++ tailWord_770052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770101 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 3]
def baseStart_770101 : Nat := 118140960795 + 770101 * 2 ^ 59
def prefixEnd_770101 : Nat := 4983230072969 + 3 ^ 40 * 770101 * 2
def baseEnd_770101 : Nat := 351495080451730408885223

theorem tailTrace_770101 : CollatzResearch.WordTrace tailWord_770101 prefixEnd_770101 351495080451730408885223 := by
  unfold tailWord_770101
  simp only [CollatzResearch.WordTrace]
  refine ⟨28087890983063074624846157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18725260655375383083230771 28087890983063074624846157)
  ·
    refine ⟨10532959118648652984317309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28087890983063074624846157 10532959118648652984317309)
    ·
      refine ⟨3949859669493244869118991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10532959118648652984317309 3949859669493244869118991)
      ·
        refine ⟨5924789504239867303678487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3949859669493244869118991 5924789504239867303678487)
        ·
          refine ⟨8887184256359800955517731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5924789504239867303678487 8887184256359800955517731)
          ·
            refine ⟨13330776384539701433276597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8887184256359800955517731 13330776384539701433276597)
            ·
              refine ⟨1249760286050597009369681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13330776384539701433276597 1249760286050597009369681)
              ·
                refine ⟨937320214537947757027261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249760286050597009369681 937320214537947757027261)
                ·
                  refine ⟨351495080451730408885223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937320214537947757027261 351495080451730408885223)
                  ·
                    rfl

theorem cell20_770101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_770101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770101 prefixEnd_770101 := by exact prefixLift 770101
  have htrace : WordTrace (prefixWord ++ tailWord_770101) baseStart_770101 baseEnd_770101 := by
    simpa [prefixWord, tailWord_770101, baseEnd_770101] using wordTrace_append hprefix tailTrace_770101
  have hstable : (prefixWord ++ tailWord_770101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770101).length < 2 ^ (prefixWord ++ tailWord_770101).sum := by decide
  have hdescent : baseEnd_770101 < baseStart_770101 := by decide
  rcases family_descends (prefixWord ++ tailWord_770101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770108 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_770108 : Nat := 118140960795 + 770108 * 2 ^ 59
def prefixEnd_770108 : Nat := 4983230072969 + 3 ^ 40 * 770108 * 2
def baseEnd_770108 : Nat := 351498275442469495651861

theorem tailTrace_770108 : CollatzResearch.WordTrace tailWord_770108 prefixEnd_770108 351498275442469495651861 := by
  unfold tailWord_770108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044073147018857410175489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18725430862691809880233985 14044073147018857410175489)
  ·
    refine ⟨10533054860264143057631617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14044073147018857410175489 10533054860264143057631617)
    ·
      refine ⟨7899791145198107293223713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10533054860264143057631617 7899791145198107293223713)
      ·
        refine ⟨5924843358898580469917785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7899791145198107293223713 5924843358898580469917785)
        ·
          refine ⟨4443632519173935352438339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5924843358898580469917785 4443632519173935352438339)
          ·
            refine ⟨6665448778760903028657509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443632519173935352438339 6665448778760903028657509)
            ·
              refine ⟨1249771646017669317873283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6665448778760903028657509 1249771646017669317873283)
              ·
                refine ⟨1874657469026503976809925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249771646017669317873283 1874657469026503976809925)
                ·
                  refine ⟨351498275442469495651861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1874657469026503976809925 351498275442469495651861)
                  ·
                    rfl

theorem cell20_770108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_770108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770108 prefixEnd_770108 := by exact prefixLift 770108
  have htrace : WordTrace (prefixWord ++ tailWord_770108) baseStart_770108 baseEnd_770108 := by
    simpa [prefixWord, tailWord_770108, baseEnd_770108] using wordTrace_append hprefix tailTrace_770108
  have hstable : (prefixWord ++ tailWord_770108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770108).length < 2 ^ (prefixWord ++ tailWord_770108).sum := by decide
  have hdescent : baseEnd_770108 < baseStart_770108 := by decide
  rcases family_descends (prefixWord ++ tailWord_770108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770160 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_770160 : Nat := 118140960795 + 770160 * 2 ^ 59
def prefixEnd_770160 : Nat := 4983230072969 + 3 ^ 40 * 770160 * 2
def baseEnd_770160 : Nat := 351522009659388425918315

theorem tailTrace_770160 : CollatzResearch.WordTrace tailWord_770160 prefixEnd_770160 351522009659388425918315 := by
  unfold tailWord_770160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045021444924663850621967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18726695259899551800829289 14045021444924663850621967)
  ·
    refine ⟨21067532167386995775932951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14045021444924663850621967 21067532167386995775932951)
    ·
      refine ⟨31601298251080493663899427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21067532167386995775932951 31601298251080493663899427)
      ·
        refine ⟨47401947376620740495849141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31601298251080493663899427 47401947376620740495849141)
        ·
          refine ⟨4443932566558194421485857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47401947376620740495849141 4443932566558194421485857)
          ·
            refine ⟨3332949424918645816114393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4443932566558194421485857 3332949424918645816114393)
            ·
              refine ⟨2499712068688984362085795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3332949424918645816114393 2499712068688984362085795)
              ·
                refine ⟨3749568103033476543128693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2499712068688984362085795 3749568103033476543128693)
                ·
                  refine ⟨351522009659388425918315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3749568103033476543128693 351522009659388425918315)
                  ·
                    rfl

theorem cell20_770160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_770160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770160 prefixEnd_770160 := by exact prefixLift 770160
  have htrace : WordTrace (prefixWord ++ tailWord_770160) baseStart_770160 baseEnd_770160 := by
    simpa [prefixWord, tailWord_770160, baseEnd_770160] using wordTrace_append hprefix tailTrace_770160
  have hstable : (prefixWord ++ tailWord_770160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770160).length < 2 ^ (prefixWord ++ tailWord_770160).sum := by decide
  have hdescent : baseEnd_770160 < baseStart_770160 := by decide
  rcases family_descends (prefixWord ++ tailWord_770160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770212 : List Nat := [2, 3, 1, 2, 12]
def baseStart_770212 : Nat := 118140960795 + 770212 * 2 ^ 59
def prefixEnd_770212 : Nat := 4983230072969 + 3 ^ 40 * 770212 * 2
def baseEnd_770212 : Nat := 4340070912053177236849

theorem tailTrace_770212 : CollatzResearch.WordTrace tailWord_770212 prefixEnd_770212 4340070912053177236849 := by
  unfold tailWord_770212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14045969742830470291068445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18727959657107293721424593 14045969742830470291068445)
  ·
    refine ⟨5267238653561426359150667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14045969742830470291068445 5267238653561426359150667)
    ·
      refine ⟨7900857980342139538726001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5267238653561426359150667 7900857980342139538726001)
      ·
        refine ⟨5925643485256604654044501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7900857980342139538726001 5925643485256604654044501)
        ·
          refine ⟨4340070912053177236849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5925643485256604654044501 4340070912053177236849)
          ·
            rfl

theorem cell20_770212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 12].length) (baseStart_770212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770212 prefixEnd_770212 := by exact prefixLift 770212
  have htrace : WordTrace (prefixWord ++ tailWord_770212) baseStart_770212 baseEnd_770212 := by
    simpa [prefixWord, tailWord_770212, baseEnd_770212] using wordTrace_append hprefix tailTrace_770212
  have hstable : (prefixWord ++ tailWord_770212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770212).length < 2 ^ (prefixWord ++ tailWord_770212).sum := by decide
  have hdescent : baseEnd_770212 < baseStart_770212 := by decide
  rcases family_descends (prefixWord ++ tailWord_770212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770219 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_770219 : Nat := 118140960795 + 770219 * 2 ^ 59
def prefixEnd_770219 : Nat := 4983230072969 + 3 ^ 40 * 770219 * 2
def baseEnd_770219 : Nat := 351548938867046442951407

theorem tailTrace_770219 : CollatzResearch.WordTrace tailWord_770219 prefixEnd_770219 351548938867046442951407 := by
  unfold tailWord_770219
  simp only [CollatzResearch.WordTrace]
  refine ⟨28092194796635580777641711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18728129864423720518427807 28092194796635580777641711)
  ·
    refine ⟨42138292194953371166462567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28092194796635580777641711 42138292194953371166462567)
    ·
      refine ⟨63207438292430056749693851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42138292194953371166462567 63207438292430056749693851)
      ·
        refine ⟨94811157438645085124540777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63207438292430056749693851 94811157438645085124540777)
        ·
          refine ⟨71108368078983813843405583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94811157438645085124540777 71108368078983813843405583)
          ·
            refine ⟨106662552118475720765108375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71108368078983813843405583 106662552118475720765108375)
            ·
              refine ⟨159993828177713581147662563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106662552118475720765108375 159993828177713581147662563)
              ·
                refine ⟨239990742266570371721493845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159993828177713581147662563 239990742266570371721493845)
                ·
                  refine ⟨351548938867046442951407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 239990742266570371721493845 351548938867046442951407)
                  ·
                    rfl

theorem cell20_770219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_770219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770219 prefixEnd_770219 := by exact prefixLift 770219
  have htrace : WordTrace (prefixWord ++ tailWord_770219) baseStart_770219 baseEnd_770219 := by
    simpa [prefixWord, tailWord_770219, baseEnd_770219] using wordTrace_append hprefix tailTrace_770219
  have hstable : (prefixWord ++ tailWord_770219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770219).length < 2 ^ (prefixWord ++ tailWord_770219).sum := by decide
  have hdescent : baseEnd_770219 < baseStart_770219 := by decide
  rcases family_descends (prefixWord ++ tailWord_770219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770225 : List Nat := [1, 2, 2, 5, 3, 1, 1, 5]
def baseStart_770225 : Nat := 118140960795 + 770225 * 2 ^ 59
def prefixEnd_770225 : Nat := 4983230072969 + 3 ^ 40 * 770225 * 2
def baseEnd_770225 : Nat := 117183892476845696250461

theorem tailTrace_770225 : CollatzResearch.WordTrace tailWord_770225 prefixEnd_770225 117183892476845696250461 := by
  unfold tailWord_770225
  simp only [CollatzResearch.WordTrace]
  refine ⟨28092413634613843802360129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18728275756409229201573419 28092413634613843802360129)
  ·
    refine ⟨21069310225960382851770097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28092413634613843802360129 21069310225960382851770097)
    ·
      refine ⟨15801982669470287138827573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21069310225960382851770097 15801982669470287138827573)
      ·
        refine ⟨1481435875262839419265085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15801982669470287138827573 1481435875262839419265085)
        ·
          refine ⟨555538453223564782224407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1481435875262839419265085 555538453223564782224407)
          ·
            refine ⟨833307679835347173336611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555538453223564782224407 833307679835347173336611)
            ·
              refine ⟨1249961519753020760004917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833307679835347173336611 1249961519753020760004917)
              ·
                refine ⟨117183892476845696250461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1249961519753020760004917 117183892476845696250461)
                ·
                  rfl

theorem cell20_770225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 5].length) (baseStart_770225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770225 prefixEnd_770225 := by exact prefixLift 770225
  have htrace : WordTrace (prefixWord ++ tailWord_770225) baseStart_770225 baseEnd_770225 := by
    simpa [prefixWord, tailWord_770225, baseEnd_770225] using wordTrace_append hprefix tailTrace_770225
  have hstable : (prefixWord ++ tailWord_770225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770225).length < 2 ^ (prefixWord ++ tailWord_770225).sum := by decide
  have hdescent : baseEnd_770225 < baseStart_770225 := by decide
  rcases family_descends (prefixWord ++ tailWord_770225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770242 : List Nat := [3, 5, 1, 1, 1, 2, 3, 4]
def baseStart_770242 : Nat := 118140960795 + 770242 * 2 ^ 59
def prefixEnd_770242 : Nat := 4983230072969 + 3 ^ 40 * 770242 * 2
def baseEnd_770242 : Nat := 117186478897920195061549

theorem tailTrace_770242 : CollatzResearch.WordTrace tailWord_770242 prefixEnd_770242 117186478897920195061549 := by
  unfold tailWord_770242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7023258418888063926432245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18728689117034837137152653 7023258418888063926432245)
  ·
    refine ⟨658430476770755993103023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7023258418888063926432245 658430476770755993103023)
    ·
      refine ⟨987645715156133989654535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 658430476770755993103023 987645715156133989654535)
      ·
        refine ⟨1481468572734200984481803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987645715156133989654535 1481468572734200984481803)
        ·
          refine ⟨2222202859101301476722705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481468572734200984481803 2222202859101301476722705)
          ·
            refine ⟨1666652144325976107542029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222202859101301476722705 1666652144325976107542029)
            ·
              refine ⟨624994554122241040328261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1666652144325976107542029 624994554122241040328261)
              ·
                refine ⟨117186478897920195061549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 624994554122241040328261 117186478897920195061549)
                ·
                  rfl

theorem cell20_770242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_770242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770242 prefixEnd_770242 := by exact prefixLift 770242
  have htrace : WordTrace (prefixWord ++ tailWord_770242) baseStart_770242 baseEnd_770242 := by
    simpa [prefixWord, tailWord_770242, baseEnd_770242] using wordTrace_append hprefix tailTrace_770242
  have hstable : (prefixWord ++ tailWord_770242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770242).length < 2 ^ (prefixWord ++ tailWord_770242).sum := by decide
  have hdescent : baseEnd_770242 < baseStart_770242 := by decide
  rcases family_descends (prefixWord ++ tailWord_770242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770277 : List Nat := [1, 3, 1, 4, 2, 1, 2, 4, 2]
def baseStart_770277 : Nat := 118140960795 + 770277 * 2 ^ 59
def prefixEnd_770277 : Nat := 4983230072969 + 3 ^ 40 * 770277 * 2
def baseEnd_770277 : Nat := 351575411647456019017837

theorem tailTrace_770277 : CollatzResearch.WordTrace tailWord_770277 prefixEnd_770277 351575411647456019017837 := by
  unfold tailWord_770277
  simp only [CollatzResearch.WordTrace]
  refine ⟨28094310230425456683253085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18729540153616971122168723 28094310230425456683253085)
  ·
    refine ⟨10535366336409546256219907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28094310230425456683253085 10535366336409546256219907)
    ·
      refine ⟨15803049504614319384329861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10535366336409546256219907 15803049504614319384329861)
      ·
        refine ⟨2963071782115184884561849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15803049504614319384329861 2963071782115184884561849)
        ·
          refine ⟨2222303836586388663421387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2963071782115184884561849 2222303836586388663421387)
          ·
            refine ⟨3333455754879582995132081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222303836586388663421387 3333455754879582995132081)
            ·
              refine ⟨2500091816159687246349061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3333455754879582995132081 2500091816159687246349061)
              ·
                refine ⟨468767215529941358690449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2500091816159687246349061 468767215529941358690449)
                ·
                  refine ⟨351575411647456019017837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468767215529941358690449 351575411647456019017837)
                  ·
                    rfl

theorem cell20_770277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_770277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770277 prefixEnd_770277 := by exact prefixLift 770277
  have htrace : WordTrace (prefixWord ++ tailWord_770277) baseStart_770277 baseEnd_770277 := by
    simpa [prefixWord, tailWord_770277, baseEnd_770277] using wordTrace_append hprefix tailTrace_770277
  have hstable : (prefixWord ++ tailWord_770277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770277).length < 2 ^ (prefixWord ++ tailWord_770277).sum := by decide
  have hdescent : baseEnd_770277 < baseStart_770277 := by decide
  rcases family_descends (prefixWord ++ tailWord_770277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770291 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 3]
def baseStart_770291 : Nat := 118140960795 + 770291 * 2 ^ 59
def prefixEnd_770291 : Nat := 4983230072969 + 3 ^ 40 * 770291 * 2
def baseEnd_770291 : Nat := 351581801628934192551113

theorem tailTrace_770291 : CollatzResearch.WordTrace tailWord_770291 prefixEnd_770291 351581801628934192551113 := by
  unfold tailWord_770291
  simp only [CollatzResearch.WordTrace]
  refine ⟨28094820852374737074262727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18729880568249824716175151 28094820852374737074262727)
  ·
    refine ⟨42142231278562105611394091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28094820852374737074262727 42142231278562105611394091)
    ·
      refine ⟨63213346917843158417091137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42142231278562105611394091 63213346917843158417091137)
      ·
        refine ⟨47410010188382368812818353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63213346917843158417091137 47410010188382368812818353)
        ·
          refine ⟨35557507641286776609613765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47410010188382368812818353 35557507641286776609613765)
          ·
            refine ⟨6667032682741270614302581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35557507641286776609613765 6667032682741270614302581)
            ·
              refine ⟨625034314006994120090867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6667032682741270614302581 625034314006994120090867)
              ·
                refine ⟨937551471010491180136301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625034314006994120090867 937551471010491180136301)
                ·
                  refine ⟨351581801628934192551113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937551471010491180136301 351581801628934192551113)
                  ·
                    rfl

theorem cell20_770291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 3].length) (baseStart_770291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770291 prefixEnd_770291 := by exact prefixLift 770291
  have htrace : WordTrace (prefixWord ++ tailWord_770291) baseStart_770291 baseEnd_770291 := by
    simpa [prefixWord, tailWord_770291, baseEnd_770291] using wordTrace_append hprefix tailTrace_770291
  have hstable : (prefixWord ++ tailWord_770291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770291).length < 2 ^ (prefixWord ++ tailWord_770291).sum := by decide
  have hdescent : baseEnd_770291 < baseStart_770291 := by decide
  rcases family_descends (prefixWord ++ tailWord_770291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770295 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_770295 : Nat := 118140960795 + 770295 * 2 ^ 59
def prefixEnd_770295 : Nat := 4983230072969 + 3 ^ 40 * 770295 * 2
def baseEnd_770295 : Nat := 351583627337927956417763

theorem tailTrace_770295 : CollatzResearch.WordTrace tailWord_770295 prefixEnd_770295 351583627337927956417763 := by
  unfold tailWord_770295
  simp only [CollatzResearch.WordTrace]
  refine ⟨28094966744360245757408339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18729977829573497171605559 28094966744360245757408339)
  ·
    refine ⟨42142450116540368636112509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28094966744360245757408339 42142450116540368636112509)
    ·
      refine ⟨15803418793702638238542191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42142450116540368636112509 15803418793702638238542191)
      ·
        refine ⟨23705128190553957357813287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15803418793702638238542191 23705128190553957357813287)
        ·
          refine ⟨35557692285830936036719931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23705128190553957357813287 35557692285830936036719931)
          ·
            refine ⟨53336538428746404055079897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35557692285830936036719931 53336538428746404055079897)
            ·
              refine ⟨40002403821559803041309923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53336538428746404055079897 40002403821559803041309923)
              ·
                refine ⟨60003605732339704561964885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40002403821559803041309923 60003605732339704561964885)
                ·
                  refine ⟨351583627337927956417763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60003605732339704561964885 351583627337927956417763)
                  ·
                    rfl

theorem cell20_770295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_770295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770295 prefixEnd_770295 := by exact prefixLift 770295
  have htrace : WordTrace (prefixWord ++ tailWord_770295) baseStart_770295 baseEnd_770295 := by
    simpa [prefixWord, tailWord_770295, baseEnd_770295] using wordTrace_append hprefix tailTrace_770295
  have hstable : (prefixWord ++ tailWord_770295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770295).length < 2 ^ (prefixWord ++ tailWord_770295).sum := by decide
  have hdescent : baseEnd_770295 < baseStart_770295 := by decide
  rcases family_descends (prefixWord ++ tailWord_770295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770311 : List Nat := [1, 1, 4, 5, 1, 2, 1, 3, 2]
def baseStart_770311 : Nat := 118140960795 + 770311 * 2 ^ 59
def prefixEnd_770311 : Nat := 4983230072969 + 3 ^ 40 * 770311 * 2
def baseEnd_770311 : Nat := 351590930173903011884365

theorem tailTrace_770311 : CollatzResearch.WordTrace tailWord_770311 prefixEnd_770311 351590930173903011884365 := by
  unfold tailWord_770311
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095550312302280489990787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18730366874868186993327191 28095550312302280489990787)
  ·
    refine ⟨42143325468453420734986181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28095550312302280489990787 42143325468453420734986181)
    ·
      refine ⟨7901873525335016387809909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42143325468453420734986181 7901873525335016387809909)
      ·
        refine ⟨740800643000157786357179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7901873525335016387809909 740800643000157786357179)
        ·
          refine ⟨1111200964500236679535769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740800643000157786357179 1111200964500236679535769)
          ·
            refine ⟨833400723375177509651827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1111200964500236679535769 833400723375177509651827)
            ·
              refine ⟨1250101085062766264477741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833400723375177509651827 1250101085062766264477741)
              ·
                refine ⟨468787906898537349179153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1250101085062766264477741 468787906898537349179153)
                ·
                  refine ⟨351590930173903011884365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468787906898537349179153 351590930173903011884365)
                  ·
                    rfl

theorem cell20_770311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 2].length) (baseStart_770311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770311 prefixEnd_770311 := by exact prefixLift 770311
  have htrace : WordTrace (prefixWord ++ tailWord_770311) baseStart_770311 baseEnd_770311 := by
    simpa [prefixWord, tailWord_770311, baseEnd_770311] using wordTrace_append hprefix tailTrace_770311
  have hstable : (prefixWord ++ tailWord_770311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770311).length < 2 ^ (prefixWord ++ tailWord_770311).sum := by decide
  have hdescent : baseEnd_770311 < baseStart_770311 := by decide
  rcases family_descends (prefixWord ++ tailWord_770311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770312 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_770312 : Nat := 118140960795 + 770312 * 2 ^ 59
def prefixEnd_770312 : Nat := 4983230072969 + 3 ^ 40 * 770312 * 2
def baseEnd_770312 : Nat := 351591386601151452851027

theorem tailTrace_770312 : CollatzResearch.WordTrace tailWord_770312 prefixEnd_770312 351591386601151452851027 := by
  unfold tailWord_770312
  simp only [CollatzResearch.WordTrace]
  refine ⟨14047793392649328830388595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18730391190199105107184793 14047793392649328830388595)
  ·
    refine ⟨21071690088973993245582893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14047793392649328830388595 21071690088973993245582893)
    ·
      refine ⟨7901883783365247467093585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21071690088973993245582893 7901883783365247467093585)
      ·
        refine ⟨5926412837523935600320189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7901883783365247467093585 5926412837523935600320189)
        ·
          refine ⟨2222404814071475850120071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5926412837523935600320189 2222404814071475850120071)
          ·
            refine ⟨3333607221107213775180107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222404814071475850120071 3333607221107213775180107)
            ·
              refine ⟨5000410831660820662770161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333607221107213775180107 5000410831660820662770161)
              ·
                refine ⟨3750308123745615497077621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5000410831660820662770161 3750308123745615497077621)
                ·
                  refine ⟨351591386601151452851027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3750308123745615497077621 351591386601151452851027)
                  ·
                    rfl

theorem cell20_770312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_770312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770312 prefixEnd_770312 := by exact prefixLift 770312
  have htrace : WordTrace (prefixWord ++ tailWord_770312) baseStart_770312 baseEnd_770312 := by
    simpa [prefixWord, tailWord_770312, baseEnd_770312] using wordTrace_append hprefix tailTrace_770312
  have hstable : (prefixWord ++ tailWord_770312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770312).length < 2 ^ (prefixWord ++ tailWord_770312).sum := by decide
  have hdescent : baseEnd_770312 < baseStart_770312 := by decide
  rcases family_descends (prefixWord ++ tailWord_770312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770336 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_770336 : Nat := 118140960795 + 770336 * 2 ^ 59
def prefixEnd_770336 : Nat := 4983230072969 + 3 ^ 40 * 770336 * 2
def baseEnd_770336 : Nat := 351602340855114036050929

theorem tailTrace_770336 : CollatzResearch.WordTrace tailWord_770336 prefixEnd_770336 351602340855114036050929 := by
  unfold tailWord_770336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14048231068605854879825431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18730974758141139839767241 14048231068605854879825431)
  ·
    refine ⟨21072346602908782319738147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14048231068605854879825431 21072346602908782319738147)
    ·
      refine ⟨31608519904363173479607221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21072346602908782319738147 31608519904363173479607221)
      ·
        refine ⟨2963298741034047513713177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31608519904363173479607221 2963298741034047513713177)
        ·
          refine ⟨2222474055775535635284883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2963298741034047513713177 2222474055775535635284883)
          ·
            refine ⟨3333711083663303452927325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2222474055775535635284883 3333711083663303452927325)
            ·
              refine ⟨1250141656373738794847747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3333711083663303452927325 1250141656373738794847747)
              ·
                refine ⟨1875212484560608192271621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250141656373738794847747 1875212484560608192271621)
                ·
                  refine ⟨351602340855114036050929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875212484560608192271621 351602340855114036050929)
                  ·
                    rfl

theorem cell20_770336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_770336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770336 prefixEnd_770336 := by exact prefixLift 770336
  have htrace : WordTrace (prefixWord ++ tailWord_770336) baseStart_770336 baseEnd_770336 := by
    simpa [prefixWord, tailWord_770336, baseEnd_770336] using wordTrace_append hprefix tailTrace_770336
  have hstable : (prefixWord ++ tailWord_770336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770336).length < 2 ^ (prefixWord ++ tailWord_770336).sum := by decide
  have hdescent : baseEnd_770336 < baseStart_770336 := by decide
  rcases family_descends (prefixWord ++ tailWord_770336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770346 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_770346 : Nat := 118140960795 + 770346 * 2 ^ 59
def prefixEnd_770346 : Nat := 4983230072969 + 3 ^ 40 * 770346 * 2
def baseEnd_770346 : Nat := 351606905127598445717555

theorem tailTrace_770346 : CollatzResearch.WordTrace tailWord_770346 prefixEnd_770346 351606905127598445717555 := by
  unfold tailWord_770346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7024206716793870366878723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18731217911450320978343261 7024206716793870366878723)
  ·
    refine ⟨10536310075190805550318085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7024206716793870366878723 10536310075190805550318085)
    ·
      refine ⟨1975558139098276040684641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10536310075190805550318085 1975558139098276040684641)
      ·
        refine ⟨1481668604323707030513481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1975558139098276040684641 1481668604323707030513481)
        ·
          refine ⟨1111251453242780272885111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1481668604323707030513481 1111251453242780272885111)
          ·
            refine ⟨1666877179864170409327667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111251453242780272885111 1666877179864170409327667)
            ·
              refine ⟨2500315769796255613991501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666877179864170409327667 2500315769796255613991501)
              ·
                refine ⟨937618413673595855246813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2500315769796255613991501 937618413673595855246813)
                ·
                  refine ⟨351606905127598445717555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937618413673595855246813 351606905127598445717555)
                  ·
                    rfl

theorem cell20_770346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_770346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770346 prefixEnd_770346 := by exact prefixLift 770346
  have htrace : WordTrace (prefixWord ++ tailWord_770346) baseStart_770346 baseEnd_770346 := by
    simpa [prefixWord, tailWord_770346, baseEnd_770346] using wordTrace_append hprefix tailTrace_770346
  have hstable : (prefixWord ++ tailWord_770346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770346).length < 2 ^ (prefixWord ++ tailWord_770346).sum := by decide
  have hdescent : baseEnd_770346 < baseStart_770346 := by decide
  rcases family_descends (prefixWord ++ tailWord_770346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770357 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_770357 : Nat := 118140960795 + 770357 * 2 ^ 59
def prefixEnd_770357 : Nat := 4983230072969 + 3 ^ 40 * 770357 * 2
def baseEnd_770357 : Nat := 351611925827331296350843

theorem tailTrace_770357 : CollatzResearch.WordTrace tailWord_770357 prefixEnd_770357 351611925827331296350843 := by
  unfold tailWord_770357
  simp only [CollatzResearch.WordTrace]
  refine ⟨28097228070135630346165325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18731485380090420230776883 28097228070135630346165325)
  ·
    refine ⟨10536460526300861379811997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28097228070135630346165325 10536460526300861379811997)
    ·
      refine ⟨3951172697362823017429499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10536460526300861379811997 3951172697362823017429499)
      ·
        refine ⟨5926759046044234526144249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951172697362823017429499 5926759046044234526144249)
        ·
          refine ⟨4445069284533175894608187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5926759046044234526144249 4445069284533175894608187)
          ·
            refine ⟨6667603926799763841912281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445069284533175894608187 6667603926799763841912281)
            ·
              refine ⟨5000702945099822881434211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667603926799763841912281 5000702945099822881434211)
              ·
                refine ⟨7501054417649734322151317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5000702945099822881434211 7501054417649734322151317)
                ·
                  refine ⟨351611925827331296350843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7501054417649734322151317 351611925827331296350843)
                  ·
                    rfl

theorem cell20_770357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_770357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770357 prefixEnd_770357 := by exact prefixLift 770357
  have htrace : WordTrace (prefixWord ++ tailWord_770357) baseStart_770357 baseEnd_770357 := by
    simpa [prefixWord, tailWord_770357, baseEnd_770357] using wordTrace_append hprefix tailTrace_770357
  have hstable : (prefixWord ++ tailWord_770357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770357).length < 2 ^ (prefixWord ++ tailWord_770357).sum := by decide
  have hdescent : baseEnd_770357 < baseStart_770357 := by decide
  rcases family_descends (prefixWord ++ tailWord_770357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770364 : List Nat := [2, 2, 2, 2, 1, 2, 1, 8]
def baseStart_770364 : Nat := 118140960795 + 770364 * 2 ^ 59
def prefixEnd_770364 : Nat := 4983230072969 + 3 ^ 40 * 770364 * 2
def baseEnd_770364 : Nat := 117205040272690127705827

theorem tailTrace_770364 : CollatzResearch.WordTrace tailWord_770364 prefixEnd_770364 117205040272690127705827 := by
  unfold tailWord_770364
  simp only [CollatzResearch.WordTrace]
  refine ⟨14048741690555135270835073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18731655587406847027780097 14048741690555135270835073)
  ·
    refine ⟨10536556267916351453126305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14048741690555135270835073 10536556267916351453126305)
    ·
      refine ⟨7902417200937263589844729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10536556267916351453126305 7902417200937263589844729)
      ·
        refine ⟨5926812900702947692383547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7902417200937263589844729 5926812900702947692383547)
        ·
          refine ⟨8890219351054421538575321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5926812900702947692383547 8890219351054421538575321)
          ·
            refine ⟨6667664513290816153931491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8890219351054421538575321 6667664513290816153931491)
            ·
              refine ⟨10001496769936224230897237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667664513290816153931491 10001496769936224230897237)
              ·
                refine ⟨117205040272690127705827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10001496769936224230897237 117205040272690127705827)
                ·
                  rfl

theorem cell20_770364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_770364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770364 prefixEnd_770364 := by exact prefixLift 770364
  have htrace : WordTrace (prefixWord ++ tailWord_770364) baseStart_770364 baseEnd_770364 := by
    simpa [prefixWord, tailWord_770364, baseEnd_770364] using wordTrace_append hprefix tailTrace_770364
  have hstable : (prefixWord ++ tailWord_770364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770364).length < 2 ^ (prefixWord ++ tailWord_770364).sum := by decide
  have hdescent : baseEnd_770364 < baseStart_770364 := by decide
  rcases family_descends (prefixWord ++ tailWord_770364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770371 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_770371 : Nat := 118140960795 + 770371 * 2 ^ 59
def prefixEnd_770371 : Nat := 4983230072969 + 3 ^ 40 * 770371 * 2
def baseEnd_770371 : Nat := 351618315808809469884119

theorem tailTrace_770371 : CollatzResearch.WordTrace tailWord_770371 prefixEnd_770371 351618315808809469884119 := by
  unfold tailWord_770371
  simp only [CollatzResearch.WordTrace]
  refine ⟨28097738692084910737174967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18731825794723273824783311 28097738692084910737174967)
  ·
    refine ⟨42146608038127366105762451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28097738692084910737174967 42146608038127366105762451)
    ·
      refine ⟨63219912057191049158643677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42146608038127366105762451 63219912057191049158643677)
      ·
        refine ⟨23707467021446643434491379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63219912057191049158643677 23707467021446643434491379)
        ·
          refine ⟨35561200532169965151737069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23707467021446643434491379 35561200532169965151737069)
          ·
            refine ⟨13335450199563736931901401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35561200532169965151737069 13335450199563736931901401)
            ·
              refine ⟨10001587649672802698926051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13335450199563736931901401 10001587649672802698926051)
              ·
                refine ⟨15002381474509204048389077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001587649672802698926051 15002381474509204048389077)
                ·
                  refine ⟨351618315808809469884119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15002381474509204048389077 351618315808809469884119)
                  ·
                    rfl

theorem cell20_770371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_770371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770371 prefixEnd_770371 := by exact prefixLift 770371
  have htrace : WordTrace (prefixWord ++ tailWord_770371) baseStart_770371 baseEnd_770371 := by
    simpa [prefixWord, tailWord_770371, baseEnd_770371] using wordTrace_append hprefix tailTrace_770371
  have hstable : (prefixWord ++ tailWord_770371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770371).length < 2 ^ (prefixWord ++ tailWord_770371).sum := by decide
  have hdescent : baseEnd_770371 < baseStart_770371 := by decide
  rcases family_descends (prefixWord ++ tailWord_770371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770412 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_770412 : Nat := 118140960795 + 770412 * 2 ^ 59
def prefixEnd_770412 : Nat := 4983230072969 + 3 ^ 40 * 770412 * 2
def baseEnd_770412 : Nat := 351637029325995549517285

theorem tailTrace_770412 : CollatzResearch.WordTrace tailWord_770412 prefixEnd_770412 351637029325995549517285 := by
  unfold tailWord_770412
  simp only [CollatzResearch.WordTrace]
  refine ⟨14049617042468187369708745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18732822723290916492944993 14049617042468187369708745)
  ·
    refine ⟨10537212781851140527281559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14049617042468187369708745 10537212781851140527281559)
    ·
      refine ⟨15805819172776710790922339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10537212781851140527281559 15805819172776710790922339)
      ·
        refine ⟨23708728759165066186383509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15805819172776710790922339 23708728759165066186383509)
        ·
          refine ⟨1111346660585862477486727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23708728759165066186383509 1111346660585862477486727)
          ·
            refine ⟨1667019990878793716230091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111346660585862477486727 1667019990878793716230091)
            ·
              refine ⟨2500529986318190574345137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667019990878793716230091 2500529986318190574345137)
              ·
                refine ⟨1875397489738642930758853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2500529986318190574345137 1875397489738642930758853)
                ·
                  refine ⟨351637029325995549517285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875397489738642930758853 351637029325995549517285)
                  ·
                    rfl

theorem cell20_770412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_770412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770412 prefixEnd_770412 := by exact prefixLift 770412
  have htrace : WordTrace (prefixWord ++ tailWord_770412) baseStart_770412 baseEnd_770412 := by
    simpa [prefixWord, tailWord_770412, baseEnd_770412] using wordTrace_append hprefix tailTrace_770412
  have hstable : (prefixWord ++ tailWord_770412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770412).length < 2 ^ (prefixWord ++ tailWord_770412).sum := by decide
  have hdescent : baseEnd_770412 < baseStart_770412 := by decide
  rcases family_descends (prefixWord ++ tailWord_770412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770429 : List Nat := [1, 4, 1, 1, 2, 4, 2, 3, 2]
def baseStart_770429 : Nat := 118140960795 + 770429 * 2 ^ 59
def prefixEnd_770429 : Nat := 4983230072969 + 3 ^ 40 * 770429 * 2
def baseEnd_770429 : Nat := 351644788589219045950549

theorem tailTrace_770429 : CollatzResearch.WordTrace tailWord_770429 prefixEnd_770429 351644788589219045950549 := by
  unfold tailWord_770429
  simp only [CollatzResearch.WordTrace]
  refine ⟨28099854125874786642786341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18733236083916524428524227 28099854125874786642786341)
  ·
    refine ⟨5268722648601522495522439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28099854125874786642786341 5268722648601522495522439)
    ·
      refine ⟨7903083972902283743283659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5268722648601522495522439 7903083972902283743283659)
      ·
        refine ⟨11854625959353425614925489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7903083972902283743283659 11854625959353425614925489)
        ·
          refine ⟨8890969469515069211194117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11854625959353425614925489 8890969469515069211194117)
          ·
            refine ⟨1667056775534075477098897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8890969469515069211194117 1667056775534075477098897)
            ·
              refine ⟨1250292581650556607824173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667056775534075477098897 1250292581650556607824173)
              ·
                refine ⟨468859718118958727934065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1250292581650556607824173 468859718118958727934065)
                ·
                  refine ⟨351644788589219045950549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468859718118958727934065 351644788589219045950549)
                  ·
                    rfl

theorem cell20_770429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_770429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770429 prefixEnd_770429 := by exact prefixLift 770429
  have htrace : WordTrace (prefixWord ++ tailWord_770429) baseStart_770429 baseEnd_770429 := by
    simpa [prefixWord, tailWord_770429, baseEnd_770429] using wordTrace_append hprefix tailTrace_770429
  have hstable : (prefixWord ++ tailWord_770429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770429).length < 2 ^ (prefixWord ++ tailWord_770429).sum := by decide
  have hdescent : baseEnd_770429 < baseStart_770429 := by decide
  rcases family_descends (prefixWord ++ tailWord_770429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770440 : List Nat := [2, 1, 3, 3, 1, 1, 9]
def baseStart_770440 : Nat := 118140960795 + 770440 * 2 ^ 59
def prefixEnd_770440 : Nat := 4983230072969 + 3 ^ 40 * 770440 * 2
def baseEnd_770440 : Nat := 39072201032105766287093

theorem tailTrace_770440 : CollatzResearch.WordTrace tailWord_770440 prefixEnd_770440 39072201032105766287093 := by
  unfold tailWord_770440
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050127664417467760718387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18733503552556623680957849 14050127664417467760718387)
  ·
    refine ⟨21075191496626201641077581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14050127664417467760718387 21075191496626201641077581)
    ·
      refine ⟨7903196811234825615404093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21075191496626201641077581 7903196811234825615404093)
      ·
        refine ⟨2963698804213059605776535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7903196811234825615404093 2963698804213059605776535)
        ·
          refine ⟨4445548206319589408664803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963698804213059605776535 4445548206319589408664803)
          ·
            refine ⟨6668322309479384112997205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445548206319589408664803 6668322309479384112997205)
            ·
              refine ⟨39072201032105766287093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6668322309479384112997205 39072201032105766287093)
              ·
                rfl

theorem cell20_770440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 9].length) (baseStart_770440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770440 prefixEnd_770440 := by exact prefixLift 770440
  have htrace : WordTrace (prefixWord ++ tailWord_770440) baseStart_770440 baseEnd_770440 := by
    simpa [prefixWord, tailWord_770440, baseEnd_770440] using wordTrace_append hprefix tailTrace_770440
  have hstable : (prefixWord ++ tailWord_770440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770440).length < 2 ^ (prefixWord ++ tailWord_770440).sum := by decide
  have hdescent : baseEnd_770440 < baseStart_770440 := by decide
  rcases family_descends (prefixWord ++ tailWord_770440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770443 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 3]
def baseStart_770443 : Nat := 118140960795 + 770443 * 2 ^ 59
def prefixEnd_770443 : Nat := 4983230072969 + 3 ^ 40 * 770443 * 2
def baseEnd_770443 : Nat := 351651178570697219483825

theorem tailTrace_770443 : CollatzResearch.WordTrace tailWord_770443 prefixEnd_770443 351651178570697219483825 := by
  unfold tailWord_770443
  simp only [CollatzResearch.WordTrace]
  refine ⟨28100364747824067033795983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18733576498549378022530655 28100364747824067033795983)
  ·
    refine ⟨42150547121736100550693975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28100364747824067033795983 42150547121736100550693975)
    ·
      refine ⟨63225820682604150826040963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42150547121736100550693975 63225820682604150826040963)
      ·
        refine ⟨94838731023906226239061445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63225820682604150826040963 94838731023906226239061445)
        ·
          refine ⟨17782262066982417419824021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94838731023906226239061445 17782262066982417419824021)
          ·
            refine ⟨833543534389800816554251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17782262066982417419824021 833543534389800816554251)
            ·
              refine ⟨1250315301584701224831377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833543534389800816554251 1250315301584701224831377)
              ·
                refine ⟨937736476188525918623533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250315301584701224831377 937736476188525918623533)
                ·
                  refine ⟨351651178570697219483825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937736476188525918623533 351651178570697219483825)
                  ·
                    rfl

theorem cell20_770443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 3].length) (baseStart_770443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770443 prefixEnd_770443 := by exact prefixLift 770443
  have htrace : WordTrace (prefixWord ++ tailWord_770443) baseStart_770443 baseEnd_770443 := by
    simpa [prefixWord, tailWord_770443, baseEnd_770443] using wordTrace_append hprefix tailTrace_770443
  have hstable : (prefixWord ++ tailWord_770443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770443).length < 2 ^ (prefixWord ++ tailWord_770443).sum := by decide
  have hdescent : baseEnd_770443 < baseStart_770443 := by decide
  rcases family_descends (prefixWord ++ tailWord_770443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770571 : List Nat := [1, 1, 1, 1, 7, 3, 1, 5]
def baseStart_770571 : Nat := 118140960795 + 770571 * 2 ^ 59
def prefixEnd_770571 : Nat := 4983230072969 + 3 ^ 40 * 770571 * 2
def baseEnd_770571 : Nat := 117236533752832554405545

theorem tailTrace_770571 : CollatzResearch.WordTrace tailWord_770571 prefixEnd_770571 117236533752832554405545 := by
  unfold tailWord_770571
  simp only [CollatzResearch.WordTrace]
  refine ⟨28105033291360344894455567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18736688860906896596303711 28105033291360344894455567)
  ·
    refine ⟨42157549937040517341683351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28105033291360344894455567 42157549937040517341683351)
    ·
      refine ⟨63236324905560776012525027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42157549937040517341683351 63236324905560776012525027)
      ·
        refine ⟨94854487358341164018787541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63236324905560776012525027 94854487358341164018787541)
        ·
          refine ⟨2223152047461121031690333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 94854487358341164018787541 2223152047461121031690333)
          ·
            refine ⟨833682017797920386883875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2223152047461121031690333 833682017797920386883875)
            ·
              refine ⟨1250523026696880580325813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833682017797920386883875 1250523026696880580325813)
              ·
                refine ⟨117236533752832554405545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1250523026696880580325813 117236533752832554405545)
                ·
                  rfl

theorem cell20_770571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_770571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770571 prefixEnd_770571 := by exact prefixLift 770571
  have htrace : WordTrace (prefixWord ++ tailWord_770571) baseStart_770571 baseEnd_770571 := by
    simpa [prefixWord, tailWord_770571, baseEnd_770571] using wordTrace_append hprefix tailTrace_770571
  have hstable : (prefixWord ++ tailWord_770571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770571).length < 2 ^ (prefixWord ++ tailWord_770571).sum := by decide
  have hdescent : baseEnd_770571 < baseStart_770571 := by decide
  rcases family_descends (prefixWord ++ tailWord_770571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770605 : List Nat := [1, 5, 4, 1, 1, 1, 7]
def baseStart_770605 : Nat := 118140960795 + 770605 * 2 ^ 59
def prefixEnd_770605 : Nat := 4983230072969 + 3 ^ 40 * 770605 * 2
def baseEnd_770605 : Nat := 39080568864993850675907

theorem tailTrace_770605 : CollatzResearch.WordTrace tailWord_770605 prefixEnd_770605 39080568864993850675907 := by
  unfold tailWord_770605
  simp only [CollatzResearch.WordTrace]
  refine ⟨28106273373237168701193269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18737515582158112467462179 28106273373237168701193269)
  ·
    refine ⟨2634963128740984565736869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28106273373237168701193269 2634963128740984565736869)
    ·
      refine ⟨494055586638934606075663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2634963128740984565736869 494055586638934606075663)
      ·
        refine ⟨741083379958401909113495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494055586638934606075663 741083379958401909113495)
        ·
          refine ⟨1111625069937602863670243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741083379958401909113495 1111625069937602863670243)
          ·
            refine ⟨1667437604906404295505365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111625069937602863670243 1667437604906404295505365)
            ·
              refine ⟨39080568864993850675907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1667437604906404295505365 39080568864993850675907)
              ·
                rfl

theorem cell20_770605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 7].length) (baseStart_770605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770605 prefixEnd_770605 := by exact prefixLift 770605
  have htrace : WordTrace (prefixWord ++ tailWord_770605) baseStart_770605 baseEnd_770605 := by
    simpa [prefixWord, tailWord_770605, baseEnd_770605] using wordTrace_append hprefix tailTrace_770605
  have hstable : (prefixWord ++ tailWord_770605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770605).length < 2 ^ (prefixWord ++ tailWord_770605).sum := by decide
  have hdescent : baseEnd_770605 < baseStart_770605 := by decide
  rcases family_descends (prefixWord ++ tailWord_770605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770612 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_770612 : Nat := 118140960795 + 770612 * 2 ^ 59
def prefixEnd_770612 : Nat := 4983230072969 + 3 ^ 40 * 770612 * 2
def baseEnd_770612 : Nat := 351728314775683742849801

theorem tailTrace_770612 : CollatzResearch.WordTrace tailWord_770612 prefixEnd_770612 351728314775683742849801 := by
  unfold tailWord_770612
  simp only [CollatzResearch.WordTrace]
  refine ⟨14053264342105904448349045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18737685789474539264465393 14053264342105904448349045)
  ·
    refine ⟨1317493532072428542032723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14053264342105904448349045 1317493532072428542032723)
    ·
      refine ⟨1976240298108642813049085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317493532072428542032723 1976240298108642813049085)
      ·
        refine ⟨741090111790741054893407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1976240298108642813049085 741090111790741054893407)
        ·
          refine ⟨1111635167686111582340111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741090111790741054893407 1111635167686111582340111)
          ·
            refine ⟨1667452751529167373510167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111635167686111582340111 1667452751529167373510167)
            ·
              refine ⟨2501179127293751060265251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667452751529167373510167 2501179127293751060265251)
              ·
                refine ⟨3751768690940626590397877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501179127293751060265251 3751768690940626590397877)
                ·
                  refine ⟨351728314775683742849801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3751768690940626590397877 351728314775683742849801)
                  ·
                    rfl

theorem cell20_770612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_770612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770612 prefixEnd_770612 := by exact prefixLift 770612
  have htrace : WordTrace (prefixWord ++ tailWord_770612) baseStart_770612 baseEnd_770612 := by
    simpa [prefixWord, tailWord_770612, baseEnd_770612] using wordTrace_append hprefix tailTrace_770612
  have hstable : (prefixWord ++ tailWord_770612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770612).length < 2 ^ (prefixWord ++ tailWord_770612).sum := by decide
  have hdescent : baseEnd_770612 < baseStart_770612 := by decide
  rcases family_descends (prefixWord ++ tailWord_770612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770623 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_770623 : Nat := 118140960795 + 770623 * 2 ^ 59
def prefixEnd_770623 : Nat := 4983230072969 + 3 ^ 40 * 770623 * 2
def baseEnd_770623 : Nat := 351733335475416593483089

theorem tailTrace_770623 : CollatzResearch.WordTrace tailWord_770623 prefixEnd_770623 351733335475416593483089 := by
  unfold tailWord_770623
  simp only [CollatzResearch.WordTrace]
  refine ⟨28106929887171957775348523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18737953258114638516899015 28106929887171957775348523)
  ·
    refine ⟨42160394830757936663022785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28106929887171957775348523 42160394830757936663022785)
    ·
      refine ⟨31620296123068452497267089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42160394830757936663022785 31620296123068452497267089)
      ·
        refine ⟨23715222092301339372950317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31620296123068452497267089 23715222092301339372950317)
        ·
          refine ⟨8893208284613002264856369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23715222092301339372950317 8893208284613002264856369)
          ·
            refine ⟨6669906213459751698642277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8893208284613002264856369 6669906213459751698642277)
            ·
              refine ⟨1250607415023703443495427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6669906213459751698642277 1250607415023703443495427)
              ·
                refine ⟨1875911122535555165243141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250607415023703443495427 1875911122535555165243141)
                ·
                  refine ⟨351733335475416593483089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1875911122535555165243141 351733335475416593483089)
                  ·
                    rfl

theorem cell20_770623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_770623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770623 prefixEnd_770623 := by exact prefixLift 770623
  have htrace : WordTrace (prefixWord ++ tailWord_770623) baseStart_770623 baseEnd_770623 := by
    simpa [prefixWord, tailWord_770623, baseEnd_770623] using wordTrace_append hprefix tailTrace_770623
  have hstable : (prefixWord ++ tailWord_770623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770623).length < 2 ^ (prefixWord ++ tailWord_770623).sum := by decide
  have hdescent : baseEnd_770623 < baseStart_770623 := by decide
  rcases family_descends (prefixWord ++ tailWord_770623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770657 : List Nat := [1, 2, 3, 1, 1, 6, 1, 3, 2]
def baseStart_770657 : Nat := 118140960795 + 770657 * 2 ^ 59
def prefixEnd_770657 : Nat := 4983230072969 + 3 ^ 40 * 770657 * 2
def baseEnd_770657 : Nat := 351748854001863586349617

theorem tailTrace_770657 : CollatzResearch.WordTrace tailWord_770657 prefixEnd_770657 351748854001863586349617 := by
  unfold tailWord_770657
  simp only [CollatzResearch.WordTrace]
  refine ⟨28108169969048781582086225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18738779979365854388057483 28108169969048781582086225)
  ·
    refine ⟨21081127476786586186564669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28108169969048781582086225 21081127476786586186564669)
    ·
      refine ⟨7905422803794969819961751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21081127476786586186564669 7905422803794969819961751)
      ·
        refine ⟨11858134205692454729942627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7905422803794969819961751 11858134205692454729942627)
        ·
          refine ⟨17787201308538682094913941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11858134205692454729942627 17787201308538682094913941)
          ·
            refine ⟨833775061337750723199091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17787201308538682094913941 833775061337750723199091)
            ·
              refine ⟨1250662592006626084798637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833775061337750723199091 1250662592006626084798637)
              ·
                refine ⟨468998472002484781799489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1250662592006626084798637 468998472002484781799489)
                ·
                  refine ⟨351748854001863586349617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468998472002484781799489 351748854001863586349617)
                  ·
                    rfl

theorem cell20_770657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_770657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770657 prefixEnd_770657 := by exact prefixLift 770657
  have htrace : WordTrace (prefixWord ++ tailWord_770657) baseStart_770657 baseEnd_770657 := by
    simpa [prefixWord, tailWord_770657, baseEnd_770657] using wordTrace_append hprefix tailTrace_770657
  have hstable : (prefixWord ++ tailWord_770657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770657).length < 2 ^ (prefixWord ++ tailWord_770657).sum := by decide
  have hdescent : baseEnd_770657 < baseStart_770657 := by decide
  rcases family_descends (prefixWord ++ tailWord_770657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770664 : List Nat := [2, 1, 4, 3, 3, 1, 6]
def baseStart_770664 : Nat := 118140960795 + 770664 * 2 ^ 59
def prefixEnd_770664 : Nat := 4983230072969 + 3 ^ 40 * 770664 * 2
def baseEnd_770664 : Nat := 39083560999178074790695

theorem tailTrace_770664 : CollatzResearch.WordTrace tailWord_770664 prefixEnd_770664 39083560999178074790695 := by
  unfold tailWord_770664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14054212640011710888795523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18738950186682281185060697 14054212640011710888795523)
  ·
    refine ⟨21081318960017566333193285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14054212640011710888795523 21081318960017566333193285)
    ·
      refine ⟨3952747305003293687473741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21081318960017566333193285 3952747305003293687473741)
      ·
        refine ⟨1482280239376235132802653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3952747305003293687473741 1482280239376235132802653)
        ·
          refine ⟨555855089766088174800995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1482280239376235132802653 555855089766088174800995)
          ·
            refine ⟨833782634649132262201493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555855089766088174800995 833782634649132262201493)
            ·
              refine ⟨39083560999178074790695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 833782634649132262201493 39083560999178074790695)
              ·
                rfl

theorem cell20_770664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 6].length) (baseStart_770664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770664 prefixEnd_770664 := by exact prefixLift 770664
  have htrace : WordTrace (prefixWord ++ tailWord_770664) baseStart_770664 baseEnd_770664 := by
    simpa [prefixWord, tailWord_770664, baseEnd_770664] using wordTrace_append hprefix tailTrace_770664
  have hstable : (prefixWord ++ tailWord_770664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770664).length < 2 ^ (prefixWord ++ tailWord_770664).sum := by decide
  have hdescent : baseEnd_770664 < baseStart_770664 := by decide
  rcases family_descends (prefixWord ++ tailWord_770664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770674 : List Nat := [3, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_770674 : Nat := 118140960795 + 770674 * 2 ^ 59
def prefixEnd_770674 : Nat := 4983230072969 + 3 ^ 40 * 770674 * 2
def baseEnd_770674 : Nat := 351756613265087082782881

theorem tailTrace_770674 : CollatzResearch.WordTrace tailWord_770674 prefixEnd_770674 351756613265087082782881 := by
  unfold tailWord_770674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7027197502496798371363769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18739193339991462323636717 7027197502496798371363769)
  ·
    refine ⟨5270398126872598778522827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7027197502496798371363769 5270398126872598778522827)
    ·
      refine ⟨7905597190308898167784241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5270398126872598778522827 7905597190308898167784241)
      ·
        refine ⟨5929197892731673625838181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7905597190308898167784241 5929197892731673625838181)
        ·
          refine ⟨1111724604887188804844659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5929197892731673625838181 1111724604887188804844659)
          ·
            refine ⟨1667586907330783207266989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111724604887188804844659 1667586907330783207266989)
            ·
              refine ⟨625345090249043702725121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1667586907330783207266989 625345090249043702725121)
              ·
                refine ⟨469008817686782777043841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625345090249043702725121 469008817686782777043841)
                ·
                  refine ⟨351756613265087082782881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469008817686782777043841 351756613265087082782881)
                  ·
                    rfl

theorem cell20_770674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_770674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770674 prefixEnd_770674 := by exact prefixLift 770674
  have htrace : WordTrace (prefixWord ++ tailWord_770674) baseStart_770674 baseEnd_770674 := by
    simpa [prefixWord, tailWord_770674, baseEnd_770674] using wordTrace_append hprefix tailTrace_770674
  have hstable : (prefixWord ++ tailWord_770674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770674).length < 2 ^ (prefixWord ++ tailWord_770674).sum := by decide
  have hdescent : baseEnd_770674 < baseStart_770674 := by decide
  rcases family_descends (prefixWord ++ tailWord_770674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770685 : List Nat := [1, 4, 1, 1, 5, 1, 2, 5]
def baseStart_770685 : Nat := 118140960795 + 770685 * 2 ^ 59
def prefixEnd_770685 : Nat := 4983230072969 + 3 ^ 40 * 770685 * 2
def baseEnd_770685 : Nat := 117253877988273311138723

theorem tailTrace_770685 : CollatzResearch.WordTrace tailWord_770685 prefixEnd_770685 117253877988273311138723 := by
  unfold tailWord_770685
  simp only [CollatzResearch.WordTrace]
  refine ⟨28109191212947342364105509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18739460808631561576070339 28109191212947342364105509)
  ·
    refine ⟨5270473352427626693269783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28109191212947342364105509 5270473352427626693269783)
    ·
      refine ⟨7905710028641440039904675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5270473352427626693269783 7905710028641440039904675)
      ·
        refine ⟨11858565042962160059857013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7905710028641440039904675 11858565042962160059857013)
        ·
          refine ⟨1111740472777702505611595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11858565042962160059857013 1111740472777702505611595)
          ·
            refine ⟨1667610709166553758417393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111740472777702505611595 1667610709166553758417393)
            ·
              refine ⟨1250708031874915318813045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667610709166553758417393 1250708031874915318813045)
              ·
                refine ⟨117253877988273311138723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1250708031874915318813045 117253877988273311138723)
                ·
                  rfl

theorem cell20_770685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_770685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770685 prefixEnd_770685 := by exact prefixLift 770685
  have htrace : WordTrace (prefixWord ++ tailWord_770685) baseStart_770685 baseEnd_770685 := by
    simpa [prefixWord, tailWord_770685, baseEnd_770685] using wordTrace_append hprefix tailTrace_770685
  have hstable : (prefixWord ++ tailWord_770685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770685).length < 2 ^ (prefixWord ++ tailWord_770685).sum := by decide
  have hdescent : baseEnd_770685 < baseStart_770685 := by decide
  rcases family_descends (prefixWord ++ tailWord_770685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770733 : List Nat := [1, 5, 2, 1, 1, 3, 1, 4, 2]
def baseStart_770733 : Nat := 118140960795 + 770733 * 2 ^ 59
def prefixEnd_770733 : Nat := 4983230072969 + 3 ^ 40 * 770733 * 2
def baseEnd_770733 : Nat := 351783542472745099815973

theorem tailTrace_770733 : CollatzResearch.WordTrace tailWord_770733 prefixEnd_770733 351783542472745099815973 := by
  unfold tailWord_770733
  simp only [CollatzResearch.WordTrace]
  refine ⟨28110941916773446561852853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18740627944515631041235235 28110941916773446561852853)
  ·
    refine ⟨2635400804697510615173705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28110941916773446561852853 2635400804697510615173705)
    ·
      refine ⟨1976550603523132961380279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2635400804697510615173705 1976550603523132961380279)
      ·
        refine ⟨2964825905284699442070419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976550603523132961380279 2964825905284699442070419)
        ·
          refine ⟨4447238857927049163105629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964825905284699442070419 4447238857927049163105629)
          ·
            refine ⟨1667714571722643436164611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4447238857927049163105629 1667714571722643436164611)
            ·
              refine ⟨2501571857583965154246917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667714571722643436164611 2501571857583965154246917)
              ·
                refine ⟨469044723296993466421297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2501571857583965154246917 469044723296993466421297)
                ·
                  refine ⟨351783542472745099815973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469044723296993466421297 351783542472745099815973)
                  ·
                    rfl

theorem cell20_770733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_770733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770733 prefixEnd_770733 := by exact prefixLift 770733
  have htrace : WordTrace (prefixWord ++ tailWord_770733) baseStart_770733 baseEnd_770733 := by
    simpa [prefixWord, tailWord_770733, baseEnd_770733] using wordTrace_append hprefix tailTrace_770733
  have hstable : (prefixWord ++ tailWord_770733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770733).length < 2 ^ (prefixWord ++ tailWord_770733).sum := by decide
  have hdescent : baseEnd_770733 < baseStart_770733 := by decide
  rcases family_descends (prefixWord ++ tailWord_770733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770785 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 3]
def baseStart_770785 : Nat := 118140960795 + 770785 * 2 ^ 59
def prefixEnd_770785 : Nat := 4983230072969 + 3 ^ 40 * 770785 * 2
def baseEnd_770785 : Nat := 351807276689664030082427

theorem tailTrace_770785 : CollatzResearch.WordTrace tailWord_770785 prefixEnd_770785 351807276689664030082427 := by
  unfold tailWord_770785
  simp only [CollatzResearch.WordTrace]
  refine ⟨28112838512585059442745809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18741892341723372961830539 28112838512585059442745809)
  ·
    refine ⟨21084628884438794582059357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28112838512585059442745809 21084628884438794582059357)
    ·
      refine ⟨7906735831664547968272259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21084628884438794582059357 7906735831664547968272259)
      ·
        refine ⟨11860103747496821952408389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7906735831664547968272259 11860103747496821952408389)
        ·
          refine ⟨2223769452655654116076573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11860103747496821952408389 2223769452655654116076573)
          ·
            refine ⟨833913544745870293528715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2223769452655654116076573 833913544745870293528715)
            ·
              refine ⟨1250870317118805440293073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833913544745870293528715 1250870317118805440293073)
              ·
                refine ⟨938152737839104080219805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250870317118805440293073 938152737839104080219805)
                ·
                  refine ⟨351807276689664030082427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938152737839104080219805 351807276689664030082427)
                  ·
                    rfl

theorem cell20_770785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_770785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770785 prefixEnd_770785 := by exact prefixLift 770785
  have htrace : WordTrace (prefixWord ++ tailWord_770785) baseStart_770785 baseEnd_770785 := by
    simpa [prefixWord, tailWord_770785, baseEnd_770785] using wordTrace_append hprefix tailTrace_770785
  have hstable : (prefixWord ++ tailWord_770785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770785).length < 2 ^ (prefixWord ++ tailWord_770785).sum := by decide
  have hdescent : baseEnd_770785 < baseStart_770785 := by decide
  rcases family_descends (prefixWord ++ tailWord_770785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770792 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_770792 : Nat := 118140960795 + 770792 * 2 ^ 59
def prefixEnd_770792 : Nat := 4983230072969 + 3 ^ 40 * 770792 * 2
def baseEnd_770792 : Nat := 351810471680403116849065

theorem tailTrace_770792 : CollatzResearch.WordTrace tailWord_770792 prefixEnd_770792 351810471680403116849065 := by
  unfold tailWord_770792
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056546911779849819125315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18742062549039799758833753 14056546911779849819125315)
  ·
    refine ⟨21084820367669774728687973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14056546911779849819125315 21084820367669774728687973)
    ·
      refine ⟨3953403818938082761628995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21084820367669774728687973 3953403818938082761628995)
      ·
        refine ⟨5930105728407124142443493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3953403818938082761628995 5930105728407124142443493)
        ·
          refine ⟨1111894824076335776708155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5930105728407124142443493 1111894824076335776708155)
          ·
            refine ⟨1667842236114503665062233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111894824076335776708155 1667842236114503665062233)
            ·
              refine ⟨1250881677085877748796675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667842236114503665062233 1250881677085877748796675)
              ·
                refine ⟨1876322515628816623195013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250881677085877748796675 1876322515628816623195013)
                ·
                  refine ⟨351810471680403116849065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876322515628816623195013 351810471680403116849065)
                  ·
                    rfl

theorem cell20_770792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_770792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770792 prefixEnd_770792 := by exact prefixLift 770792
  have htrace : WordTrace (prefixWord ++ tailWord_770792) baseStart_770792 baseEnd_770792 := by
    simpa [prefixWord, tailWord_770792, baseEnd_770792] using wordTrace_append hprefix tailTrace_770792
  have hstable : (prefixWord ++ tailWord_770792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770792).length < 2 ^ (prefixWord ++ tailWord_770792).sum := by decide
  have hdescent : baseEnd_770792 < baseStart_770792 := by decide
  rcases family_descends (prefixWord ++ tailWord_770792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770803 : List Nat := [1, 1, 1, 2, 2, 3, 1, 9]
def baseStart_770803 : Nat := 118140960795 + 770803 * 2 ^ 59
def prefixEnd_770803 : Nat := 4983230072969 + 3 ^ 40 * 770803 * 2
def baseEnd_770803 : Nat := 117271830793378655827451

theorem tailTrace_770803 : CollatzResearch.WordTrace tailWord_770803 prefixEnd_770803 117271830793378655827451 := by
  unfold tailWord_770803
  simp only [CollatzResearch.WordTrace]
  refine ⟨28113495026519848516901063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18742330017679899011267375 28113495026519848516901063)
  ·
    refine ⟨42170242539779772775351595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28113495026519848516901063 42170242539779772775351595)
    ·
      refine ⟨63255363809669659163027393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42170242539779772775351595 63255363809669659163027393)
      ·
        refine ⟨47441522857252244372270545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63255363809669659163027393 47441522857252244372270545)
        ·
          refine ⟨35581142142939183279202909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47441522857252244372270545 35581142142939183279202909)
          ·
            refine ⟨13342928303602193729701091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35581142142939183279202909 13342928303602193729701091)
            ·
              refine ⟨20014392455403290594551637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13342928303602193729701091 20014392455403290594551637)
              ·
                refine ⟨117271830793378655827451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20014392455403290594551637 117271830793378655827451)
                ·
                  rfl

theorem cell20_770803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_770803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770803 prefixEnd_770803 := by exact prefixLift 770803
  have htrace : WordTrace (prefixWord ++ tailWord_770803) baseStart_770803 baseEnd_770803 := by
    simpa [prefixWord, tailWord_770803, baseEnd_770803] using wordTrace_append hprefix tailTrace_770803
  have hstable : (prefixWord ++ tailWord_770803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770803).length < 2 ^ (prefixWord ++ tailWord_770803).sum := by decide
  have hdescent : baseEnd_770803 < baseStart_770803 := by decide
  rcases family_descends (prefixWord ++ tailWord_770803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770820 : List Nat := [2, 3, 2, 2, 1, 1, 3, 6]
def baseStart_770820 : Nat := 118140960795 + 770820 * 2 ^ 59
def prefixEnd_770820 : Nat := 4983230072969 + 3 ^ 40 * 770820 * 2
def baseEnd_770820 : Nat := 117274417214453154638539

theorem tailTrace_770820 : CollatzResearch.WordTrace tailWord_770820 prefixEnd_770820 117274417214453154638539 := by
  unfold tailWord_770820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14057057533729130210134957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18742743378305506946846609 14057057533729130210134957)
  ·
    refine ⟨5271396575148423828800609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14057057533729130210134957 5271396575148423828800609)
    ·
      refine ⟨3953547431361317871600457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5271396575148423828800609 3953547431361317871600457)
      ·
        refine ⟨2965160573520988403700343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3953547431361317871600457 2965160573520988403700343)
        ·
          refine ⟨4447740860281482605550515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965160573520988403700343 4447740860281482605550515)
          ·
            refine ⟨6671611290422223908325773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4447740860281482605550515 6671611290422223908325773)
            ·
              refine ⟨2501854233908333965622165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6671611290422223908325773 2501854233908333965622165)
              ·
                refine ⟨117274417214453154638539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2501854233908333965622165 117274417214453154638539)
                ·
                  rfl

theorem cell20_770820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_770820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770820 prefixEnd_770820 := by exact prefixLift 770820
  have htrace : WordTrace (prefixWord ++ tailWord_770820) baseStart_770820 baseEnd_770820 := by
    simpa [prefixWord, tailWord_770820, baseEnd_770820] using wordTrace_append hprefix tailTrace_770820
  have hstable : (prefixWord ++ tailWord_770820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770820).length < 2 ^ (prefixWord ++ tailWord_770820).sum := by decide
  have hdescent : baseEnd_770820 < baseStart_770820 := by decide
  rcases family_descends (prefixWord ++ tailWord_770820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770847 : List Nat := [1, 1, 2, 4, 2, 3, 3, 2, 2]
def baseStart_770847 : Nat := 118140960795 + 770847 * 2 ^ 59
def prefixEnd_770847 : Nat := 4983230072969 + 3 ^ 40 * 770847 * 2
def baseEnd_770847 : Nat := 351835575179067370015507

theorem tailTrace_770847 : CollatzResearch.WordTrace tailWord_770847 prefixEnd_770847 351835575179067370015507 := by
  unfold tailWord_770847
  simp only [CollatzResearch.WordTrace]
  refine ⟨28115099838360444031502795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18743399892240296021001863 28115099838360444031502795)
  ·
    refine ⟨42172649757540666047254193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28115099838360444031502795 42172649757540666047254193)
    ·
      refine ⟨31629487318155499535440645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42172649757540666047254193 31629487318155499535440645)
      ·
        refine ⟨5930528872154156162895121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31629487318155499535440645 5930528872154156162895121)
        ·
          refine ⟨4447896654115617122171341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5930528872154156162895121 4447896654115617122171341)
          ·
            refine ⟨1667961245293356420814253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4447896654115617122171341 1667961245293356420814253)
            ·
              refine ⟨625485466985008657805345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1667961245293356420814253 625485466985008657805345)
              ·
                refine ⟨469114100238756493354009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625485466985008657805345 469114100238756493354009)
                ·
                  refine ⟨351835575179067370015507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469114100238756493354009 351835575179067370015507)
                  ·
                    rfl

theorem cell20_770847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 2].length) (baseStart_770847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770847 prefixEnd_770847 := by exact prefixLift 770847
  have htrace : WordTrace (prefixWord ++ tailWord_770847) baseStart_770847 baseEnd_770847 := by
    simpa [prefixWord, tailWord_770847, baseEnd_770847] using wordTrace_append hprefix tailTrace_770847
  have hstable : (prefixWord ++ tailWord_770847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770847).length < 2 ^ (prefixWord ++ tailWord_770847).sum := by decide
  have hdescent : baseEnd_770847 < baseStart_770847 := by decide
  rcases family_descends (prefixWord ++ tailWord_770847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770872 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_770872 : Nat := 118140960795 + 770872 * 2 ^ 59
def prefixEnd_770872 : Nat := 4983230072969 + 3 ^ 40 * 770872 * 2
def baseEnd_770872 : Nat := 351846985860278394182071

theorem tailTrace_770872 : CollatzResearch.WordTrace tailWord_770872 prefixEnd_770872 351846985860278394182071 := by
  unfold tailWord_770872
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058005831634936650581435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18744007775513248867441913 14058005831634936650581435)
  ·
    refine ⟨21087008747452404975872153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14058005831634936650581435 21087008747452404975872153)
    ·
      refine ⟨15815256560589303731904115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21087008747452404975872153 15815256560589303731904115)
      ·
        refine ⟨23722884840883955597856173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15815256560589303731904115 23722884840883955597856173)
        ·
          refine ⟨8896081815331483349196065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23722884840883955597856173 8896081815331483349196065)
          ·
            refine ⟨6672061361498612511897049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8896081815331483349196065 6672061361498612511897049)
            ·
              refine ⟨5004046021123959383922787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6672061361498612511897049 5004046021123959383922787)
              ·
                refine ⟨7506069031685939075884181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004046021123959383922787 7506069031685939075884181)
                ·
                  refine ⟨351846985860278394182071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7506069031685939075884181 351846985860278394182071)
                  ·
                    rfl

theorem cell20_770872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_770872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770872 prefixEnd_770872 := by exact prefixLift 770872
  have htrace : WordTrace (prefixWord ++ tailWord_770872) baseStart_770872 baseEnd_770872 := by
    simpa [prefixWord, tailWord_770872, baseEnd_770872] using wordTrace_append hprefix tailTrace_770872
  have hstable : (prefixWord ++ tailWord_770872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770872).length < 2 ^ (prefixWord ++ tailWord_770872).sum := by decide
  have hdescent : baseEnd_770872 < baseStart_770872 := by decide
  rcases family_descends (prefixWord ++ tailWord_770872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770906 : List Nat := [3, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_770906 : Nat := 118140960795 + 770906 * 2 ^ 59
def prefixEnd_770906 : Nat := 4983230072969 + 3 ^ 40 * 770906 * 2
def baseEnd_770906 : Nat := 351862504386725387048599

theorem tailTrace_770906 : CollatzResearch.WordTrace tailWord_770906 prefixEnd_770906 351862504386725387048599 := by
  unfold tailWord_770906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029312936286674276975143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18744834496764464738600381 7029312936286674276975143)
  ·
    refine ⟨10543969404430011415462715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7029312936286674276975143 10543969404430011415462715)
    ·
      refine ⟨15815954106645017123194073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10543969404430011415462715 15815954106645017123194073)
      ·
        refine ⟨11861965579983762842395555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15815954106645017123194073 11861965579983762842395555)
        ·
          refine ⟨17792948369975644263593333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11861965579983762842395555 17792948369975644263593333)
          ·
            refine ⟨1668088909685216649711875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17792948369975644263593333 1668088909685216649711875)
            ·
              refine ⟨2502133364527824974567813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668088909685216649711875 2502133364527824974567813)
              ·
                refine ⟨469150005848967182731465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2502133364527824974567813 469150005848967182731465)
                ·
                  refine ⟨351862504386725387048599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469150005848967182731465 351862504386725387048599)
                  ·
                    rfl

theorem cell20_770906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_770906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770906 prefixEnd_770906 := by exact prefixLift 770906
  have htrace : WordTrace (prefixWord ++ tailWord_770906) baseStart_770906 baseEnd_770906 := by
    simpa [prefixWord, tailWord_770906, baseEnd_770906] using wordTrace_append hprefix tailTrace_770906
  have hstable : (prefixWord ++ tailWord_770906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770906).length < 2 ^ (prefixWord ++ tailWord_770906).sum := by decide
  have hdescent : baseEnd_770906 < baseStart_770906 := by decide
  rcases family_descends (prefixWord ++ tailWord_770906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770920 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_770920 : Nat := 118140960795 + 770920 * 2 ^ 59
def prefixEnd_770920 : Nat := 4983230072969 + 3 ^ 40 * 770920 * 2
def baseEnd_770920 : Nat := 351868894368203560581875

theorem tailTrace_770920 : CollatzResearch.WordTrace tailWord_770920 prefixEnd_770920 351868894368203560581875 := by
  unfold tailWord_770920
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058881183547988749455107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18745174911397318332606809 14058881183547988749455107)
  ·
    refine ⟨21088321775321983124182661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14058881183547988749455107 21088321775321983124182661)
    ·
      refine ⟨3954060332872871835784249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21088321775321983124182661 3954060332872871835784249)
      ·
        refine ⟨2965545249654653876838187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3954060332872871835784249 2965545249654653876838187)
        ·
          refine ⟨4448317874481980815257281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965545249654653876838187 4448317874481980815257281)
          ·
            refine ⟨3336238405861485611442961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448317874481980815257281 3336238405861485611442961)
            ·
              refine ⟨2502178804396114208582221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3336238405861485611442961 2502178804396114208582221)
              ·
                refine ⟨938317051648542828218333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2502178804396114208582221 938317051648542828218333)
                ·
                  refine ⟨351868894368203560581875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938317051648542828218333 351868894368203560581875)
                  ·
                    rfl

theorem cell20_770920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_770920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770920 prefixEnd_770920 := by exact prefixLift 770920
  have htrace : WordTrace (prefixWord ++ tailWord_770920) baseStart_770920 baseEnd_770920 := by
    simpa [prefixWord, tailWord_770920, baseEnd_770920] using wordTrace_append hprefix tailTrace_770920
  have hstable : (prefixWord ++ tailWord_770920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770920).length < 2 ^ (prefixWord ++ tailWord_770920).sum := by decide
  have hdescent : baseEnd_770920 < baseStart_770920 := by decide
  rcases family_descends (prefixWord ++ tailWord_770920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770948 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_770948 : Nat := 118140960795 + 770948 * 2 ^ 59
def prefixEnd_770948 : Nat := 4983230072969 + 3 ^ 40 * 770948 * 2
def baseEnd_770948 : Nat := 351881674331159907648427

theorem tailTrace_770948 : CollatzResearch.WordTrace tailWord_770948 prefixEnd_770948 351881674331159907648427 := by
  unfold tailWord_770948
  simp only [CollatzResearch.WordTrace]
  refine ⟨14059391805497269140464749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18745855740663025520619665 14059391805497269140464749)
  ·
    refine ⟨5272271927061475927674281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14059391805497269140464749 5272271927061475927674281)
    ·
      refine ⟨3954203945296106945755711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5272271927061475927674281 3954203945296106945755711)
      ·
        refine ⟨5931305917944160418633567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3954203945296106945755711 5931305917944160418633567)
        ·
          refine ⟨8896958876916240627950351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5931305917944160418633567 8896958876916240627950351)
          ·
            refine ⟨13345438315374360941925527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8896958876916240627950351 13345438315374360941925527)
            ·
              refine ⟨20018157473061541412888291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13345438315374360941925527 20018157473061541412888291)
              ·
                refine ⟨30027236209592312119332437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20018157473061541412888291 30027236209592312119332437)
                ·
                  refine ⟨351881674331159907648427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30027236209592312119332437 351881674331159907648427)
                  ·
                    rfl

theorem cell20_770948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_770948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770948 prefixEnd_770948 := by exact prefixLift 770948
  have htrace : WordTrace (prefixWord ++ tailWord_770948) baseStart_770948 baseEnd_770948 := by
    simpa [prefixWord, tailWord_770948, baseEnd_770948] using wordTrace_append hprefix tailTrace_770948
  have hstable : (prefixWord ++ tailWord_770948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770948).length < 2 ^ (prefixWord ++ tailWord_770948).sum := by decide
  have hdescent : baseEnd_770948 < baseStart_770948 := by decide
  rcases family_descends (prefixWord ++ tailWord_770948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770965 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_770965 : Nat := 118140960795 + 770965 * 2 ^ 59
def prefixEnd_770965 : Nat := 4983230072969 + 3 ^ 40 * 770965 * 2
def baseEnd_770965 : Nat := 351889433594383404081691

theorem tailTrace_770965 : CollatzResearch.WordTrace tailWord_770965 prefixEnd_770965 351889433594383404081691 := by
  unfold tailWord_770965
  simp only [CollatzResearch.WordTrace]
  refine ⟨28119403651932950184298349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18746269101288633456198899 28119403651932950184298349)
  ·
    refine ⟨10544776369474856319111881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28119403651932950184298349 10544776369474856319111881)
    ·
      refine ⟨7908582277106142239333911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10544776369474856319111881 7908582277106142239333911)
      ·
        refine ⟨11862873415659213359000867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7908582277106142239333911 11862873415659213359000867)
        ·
          refine ⟨17794310123488820038501301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11862873415659213359000867 17794310123488820038501301)
          ·
            refine ⟨1668216574077076878609497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17794310123488820038501301 1668216574077076878609497)
            ·
              refine ⟨1251162430557807658957123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668216574077076878609497 1251162430557807658957123)
              ·
                refine ⟨1876743645836711488435685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251162430557807658957123 1876743645836711488435685)
                ·
                  refine ⟨351889433594383404081691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1876743645836711488435685 351889433594383404081691)
                  ·
                    rfl

theorem cell20_770965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_770965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770965 prefixEnd_770965 := by exact prefixLift 770965
  have htrace : WordTrace (prefixWord ++ tailWord_770965) baseStart_770965 baseEnd_770965 := by
    simpa [prefixWord, tailWord_770965, baseEnd_770965] using wordTrace_append hprefix tailTrace_770965
  have hstable : (prefixWord ++ tailWord_770965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770965).length < 2 ^ (prefixWord ++ tailWord_770965).sum := by decide
  have hdescent : baseEnd_770965 < baseStart_770965 := by decide
  rcases family_descends (prefixWord ++ tailWord_770965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770975 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 3]
def baseStart_770975 : Nat := 118140960795 + 770975 * 2 ^ 59
def prefixEnd_770975 : Nat := 4983230072969 + 3 ^ 40 * 770975 * 2
def baseEnd_770975 : Nat := 351893997866867813748317

theorem tailTrace_770975 : CollatzResearch.WordTrace tailWord_770975 prefixEnd_770975 351893997866867813748317 := by
  unfold tailWord_770975
  simp only [CollatzResearch.WordTrace]
  refine ⟨28119768381896721892162379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18746512254597814594774919 28119768381896721892162379)
  ·
    refine ⟨42179652572845082838243569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28119768381896721892162379 42179652572845082838243569)
    ·
      refine ⟨31634739429633812128682677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42179652572845082838243569 31634739429633812128682677)
      ·
        refine ⟨2965756821528169887064001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31634739429633812128682677 2965756821528169887064001)
        ·
          refine ⟨2224317616146127415298001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2965756821528169887064001 2224317616146127415298001)
          ·
            refine ⟨1668238212109595561473501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224317616146127415298001 1668238212109595561473501)
            ·
              refine ⟨625589329541098335552563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1668238212109595561473501 625589329541098335552563)
              ·
                refine ⟨938383994311647503328845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625589329541098335552563 938383994311647503328845)
                ·
                  refine ⟨351893997866867813748317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938383994311647503328845 351893997866867813748317)
                  ·
                    rfl

theorem cell20_770975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 3].length) (baseStart_770975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770975 prefixEnd_770975 := by exact prefixLift 770975
  have htrace : WordTrace (prefixWord ++ tailWord_770975) baseStart_770975 baseEnd_770975 := by
    simpa [prefixWord, tailWord_770975, baseEnd_770975] using wordTrace_append hprefix tailTrace_770975
  have hstable : (prefixWord ++ tailWord_770975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770975).length < 2 ^ (prefixWord ++ tailWord_770975).sum := by decide
  have hdescent : baseEnd_770975 < baseStart_770975 := by decide
  rcases family_descends (prefixWord ++ tailWord_770975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770979 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 3]
def baseStart_770979 : Nat := 118140960795 + 770979 * 2 ^ 59
def prefixEnd_770979 : Nat := 4983230072969 + 3 ^ 40 * 770979 * 2
def baseEnd_770979 : Nat := 351895823575861577614967

theorem tailTrace_770979 : CollatzResearch.WordTrace tailWord_770979 prefixEnd_770979 351895823575861577614967 := by
  unfold tailWord_770979
  simp only [CollatzResearch.WordTrace]
  refine ⟨28119914273882230575307991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18746609515921487050205327 28119914273882230575307991)
  ·
    refine ⟨42179871410823345862961987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28119914273882230575307991 42179871410823345862961987)
    ·
      refine ⟨63269807116235018794442981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42179871410823345862961987 63269807116235018794442981)
      ·
        refine ⟨11863088834294066023958059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63269807116235018794442981 11863088834294066023958059)
        ·
          refine ⟨17794633251441099035937089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11863088834294066023958059 17794633251441099035937089)
          ·
            refine ⟨13345974938580824276952817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17794633251441099035937089 13345974938580824276952817)
            ·
              refine ⟨10009481203935618207714613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13345974938580824276952817 10009481203935618207714613)
              ·
                refine ⟨938388862868964206973245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10009481203935618207714613 938388862868964206973245)
                ·
                  refine ⟨351895823575861577614967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938388862868964206973245 351895823575861577614967)
                  ·
                    rfl

theorem cell20_770979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_770979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_770979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_770979 prefixEnd_770979 := by exact prefixLift 770979
  have htrace : WordTrace (prefixWord ++ tailWord_770979) baseStart_770979 baseEnd_770979 := by
    simpa [prefixWord, tailWord_770979, baseEnd_770979] using wordTrace_append hprefix tailTrace_770979
  have hstable : (prefixWord ++ tailWord_770979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770979).length < 2 ^ (prefixWord ++ tailWord_770979).sum := by decide
  have hdescent : baseEnd_770979 < baseStart_770979 := by decide
  rcases family_descends (prefixWord ++ tailWord_770979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771030 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_771030 : Nat := 118140960795 + 771030 * 2 ^ 59
def prefixEnd_771030 : Nat := 4983230072969 + 3 ^ 40 * 771030 * 2
def baseEnd_771030 : Nat := 351919101365532066914759

theorem tailTrace_771030 : CollatzResearch.WordTrace tailWord_771030 prefixEnd_771030 351919101365532066914759 := by
  unfold tailWord_771030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757610899793591642838409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18747849597798310856943029 1757610899793591642838409)
  ·
    refine ⟨1318208174845193732128807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1757610899793591642838409 1318208174845193732128807)
    ·
      refine ⟨1977312262267790598193211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318208174845193732128807 1977312262267790598193211)
      ·
        refine ⟨2965968393401685897289817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977312262267790598193211 2965968393401685897289817)
        ·
          refine ⟨2224476295051264422967363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2965968393401685897289817 2224476295051264422967363)
          ·
            refine ⟨3336714442576896634451045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224476295051264422967363 3336714442576896634451045)
            ·
              refine ⟨625633957983168118959571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3336714442576896634451045 625633957983168118959571)
              ·
                refine ⟨938450936974752178439357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625633957983168118959571 938450936974752178439357)
                ·
                  refine ⟨351919101365532066914759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938450936974752178439357 351919101365532066914759)
                  ·
                    rfl

theorem cell20_771030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_771030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771030 prefixEnd_771030 := by exact prefixLift 771030
  have htrace : WordTrace (prefixWord ++ tailWord_771030) baseStart_771030 baseEnd_771030 := by
    simpa [prefixWord, tailWord_771030, baseEnd_771030] using wordTrace_append hprefix tailTrace_771030
  have hstable : (prefixWord ++ tailWord_771030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771030).length < 2 ^ (prefixWord ++ tailWord_771030).sum := by decide
  have hdescent : baseEnd_771030 < baseStart_771030 := by decide
  rcases family_descends (prefixWord ++ tailWord_771030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771034 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_771034 : Nat := 118140960795 + 771034 * 2 ^ 59
def prefixEnd_771034 : Nat := 4983230072969 + 3 ^ 40 * 771034 * 2
def baseEnd_771034 : Nat := 351920927074525830781409

theorem tailTrace_771034 : CollatzResearch.WordTrace tailWord_771034 prefixEnd_771034 351920927074525830781409 := by
  unfold tailWord_771034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7030480072170743742140039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18747946859121983312373437 7030480072170743742140039)
  ·
    refine ⟨10545720108256115613210059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7030480072170743742140039 10545720108256115613210059)
    ·
      refine ⟨15818580162384173419815089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10545720108256115613210059 15818580162384173419815089)
      ·
        refine ⟨11863935121788130064861317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15818580162384173419815089 11863935121788130064861317)
        ·
          refine ⟨2224487835335274387161497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11863935121788130064861317 2224487835335274387161497)
          ·
            refine ⟨1668365876501455790371123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224487835335274387161497 1668365876501455790371123)
            ·
              refine ⟨2502548814752183685556685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668365876501455790371123 2502548814752183685556685)
              ·
                refine ⟨938455805532068882083757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2502548814752183685556685 938455805532068882083757)
                ·
                  refine ⟨351920927074525830781409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938455805532068882083757 351920927074525830781409)
                  ·
                    rfl

theorem cell20_771034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_771034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771034 prefixEnd_771034 := by exact prefixLift 771034
  have htrace : WordTrace (prefixWord ++ tailWord_771034) baseStart_771034 baseEnd_771034 := by
    simpa [prefixWord, tailWord_771034, baseEnd_771034] using wordTrace_append hprefix tailTrace_771034
  have hstable : (prefixWord ++ tailWord_771034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771034).length < 2 ^ (prefixWord ++ tailWord_771034).sum := by decide
  have hdescent : baseEnd_771034 < baseStart_771034 := by decide
  rcases family_descends (prefixWord ++ tailWord_771034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771086 : List Nat := [4, 1, 1, 2, 2, 2, 3, 5]
def baseStart_771086 : Nat := 118140960795 + 771086 * 2 ^ 59
def prefixEnd_771086 : Nat := 4983230072969 + 3 ^ 40 * 771086 * 2
def baseEnd_771086 : Nat := 117314887097148253682621

theorem tailTrace_771086 : CollatzResearch.WordTrace tailWord_771086 prefixEnd_771086 117314887097148253682621 := by
  unfold tailWord_771086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515477110561823481181639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18749211256329725232968741 3515477110561823481181639)
  ·
    refine ⟨5273215665842735221772459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3515477110561823481181639 5273215665842735221772459)
    ·
      refine ⟨7909823498764102832658689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5273215665842735221772459 7909823498764102832658689)
      ·
        refine ⟨5932367624073077124494017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7909823498764102832658689 5932367624073077124494017)
        ·
          refine ⟨4449275718054807843370513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5932367624073077124494017 4449275718054807843370513)
          ·
            refine ⟨3336956788541105882527885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4449275718054807843370513 3336956788541105882527885)
            ·
              refine ⟨1251358795702914705947957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3336956788541105882527885 1251358795702914705947957)
              ·
                refine ⟨117314887097148253682621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1251358795702914705947957 117314887097148253682621)
                ·
                  rfl

theorem cell20_771086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_771086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771086 prefixEnd_771086 := by exact prefixLift 771086
  have htrace : WordTrace (prefixWord ++ tailWord_771086) baseStart_771086 baseEnd_771086 := by
    simpa [prefixWord, tailWord_771086, baseEnd_771086] using wordTrace_append hprefix tailTrace_771086
  have hstable : (prefixWord ++ tailWord_771086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771086).length < 2 ^ (prefixWord ++ tailWord_771086).sum := by decide
  have hdescent : baseEnd_771086 < baseStart_771086 := by decide
  rcases family_descends (prefixWord ++ tailWord_771086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771134 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_771134 : Nat := 118140960795 + 771134 * 2 ^ 59
def prefixEnd_771134 : Nat := 4983230072969 + 3 ^ 40 * 771134 * 2
def baseEnd_771134 : Nat := 351966569799369927447667

theorem tailTrace_771134 : CollatzResearch.WordTrace tailWord_771134 prefixEnd_771134 351966569799369927447667 := by
  unfold tailWord_771134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515695948540086505900057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18750378392213794698133637 3515695948540086505900057)
  ·
    refine ⟨2636771961405064879425043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3515695948540086505900057 2636771961405064879425043)
    ·
      refine ⟨3955157942107597319137565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636771961405064879425043 3955157942107597319137565)
      ·
        refine ⟨1483184228290348994676587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3955157942107597319137565 1483184228290348994676587)
        ·
          refine ⟨2224776342435523492014881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483184228290348994676587 2224776342435523492014881)
          ·
            refine ⟨1668582256826642619011161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224776342435523492014881 1668582256826642619011161)
            ·
              refine ⟨1251436692619981964258371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668582256826642619011161 1251436692619981964258371)
              ·
                refine ⟨1877155038929972946387557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251436692619981964258371 1877155038929972946387557)
                ·
                  refine ⟨351966569799369927447667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877155038929972946387557 351966569799369927447667)
                  ·
                    rfl

theorem cell20_771134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_771134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771134 prefixEnd_771134 := by exact prefixLift 771134
  have htrace : WordTrace (prefixWord ++ tailWord_771134) baseStart_771134 baseEnd_771134 := by
    simpa [prefixWord, tailWord_771134, baseEnd_771134] using wordTrace_append hprefix tailTrace_771134
  have hstable : (prefixWord ++ tailWord_771134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771134).length < 2 ^ (prefixWord ++ tailWord_771134).sum := by decide
  have hdescent : baseEnd_771134 < baseStart_771134 := by decide
  rcases family_descends (prefixWord ++ tailWord_771134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771158 : List Nat := [5, 2, 2, 1, 2, 1, 1, 6]
def baseStart_771158 : Nat := 118140960795 + 771158 * 2 ^ 59
def prefixEnd_771158 : Nat := 4983230072969 + 3 ^ 40 * 771158 * 2
def baseEnd_771158 : Nat := 117325841351110836882523

theorem tailTrace_771158 : CollatzResearch.WordTrace tailWord_771158 prefixEnd_771158 117325841351110836882523 := by
  unfold tailWord_771158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757902683764609009129633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18750961960155829430716085 1757902683764609009129633)
  ·
    refine ⟨1318427012823456756847225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1757902683764609009129633 1318427012823456756847225)
    ·
      refine ⟨988820259617592567635419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1318427012823456756847225 988820259617592567635419)
      ·
        refine ⟨1483230389426388851453129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988820259617592567635419 1483230389426388851453129)
        ·
          refine ⟨1112422792069791638589847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1483230389426388851453129 1112422792069791638589847)
          ·
            refine ⟨1668634188104687457884771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112422792069791638589847 1668634188104687457884771)
            ·
              refine ⟨2502951282157031186827157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668634188104687457884771 2502951282157031186827157)
              ·
                refine ⟨117325841351110836882523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2502951282157031186827157 117325841351110836882523)
                ·
                  rfl

theorem cell20_771158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_771158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771158 prefixEnd_771158 := by exact prefixLift 771158
  have htrace : WordTrace (prefixWord ++ tailWord_771158) baseStart_771158 baseEnd_771158 := by
    simpa [prefixWord, tailWord_771158, baseEnd_771158] using wordTrace_append hprefix tailTrace_771158
  have hstable : (prefixWord ++ tailWord_771158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771158).length < 2 ^ (prefixWord ++ tailWord_771158).sum := by decide
  have hdescent : baseEnd_771158 < baseStart_771158 := by decide
  rcases family_descends (prefixWord ++ tailWord_771158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771189 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 4]
def baseStart_771189 : Nat := 118140960795 + 771189 * 2 ^ 59
def prefixEnd_771189 : Nat := 4983230072969 + 3 ^ 40 * 771189 * 2
def baseEnd_771189 : Nat := 351991673298034180614109

theorem tailTrace_771189 : CollatzResearch.WordTrace tailWord_771189 prefixEnd_771189 351991673298034180614109 := by
  unfold tailWord_771189
  simp only [CollatzResearch.WordTrace]
  refine ⟨28127573603121436440452621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18751715735414290960301747 28127573603121436440452621)
  ·
    refine ⟨10547840101170538665169733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28127573603121436440452621 10547840101170538665169733)
    ·
      refine ⟨1977720018969475999719325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10547840101170538665169733 1977720018969475999719325)
      ·
        refine ⟨741645007113553499894747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1977720018969475999719325 741645007113553499894747)
        ·
          refine ⟨1112467510670330249842121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741645007113553499894747 1112467510670330249842121)
          ·
            refine ⟨834350633002747687381591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112467510670330249842121 834350633002747687381591)
            ·
              refine ⟨1251525949504121531072387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834350633002747687381591 1251525949504121531072387)
              ·
                refine ⟨1877288924256182296608581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251525949504121531072387 1877288924256182296608581)
                ·
                  refine ⟨351991673298034180614109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877288924256182296608581 351991673298034180614109)
                  ·
                    rfl

theorem cell20_771189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_771189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771189 prefixEnd_771189 := by exact prefixLift 771189
  have htrace : WordTrace (prefixWord ++ tailWord_771189) baseStart_771189 baseEnd_771189 := by
    simpa [prefixWord, tailWord_771189, baseEnd_771189] using wordTrace_append hprefix tailTrace_771189
  have hstable : (prefixWord ++ tailWord_771189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771189).length < 2 ^ (prefixWord ++ tailWord_771189).sum := by decide
  have hdescent : baseEnd_771189 < baseStart_771189 := by decide
  rcases family_descends (prefixWord ++ tailWord_771189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771262 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_771262 : Nat := 118140960795 + 771262 * 2 ^ 59
def prefixEnd_771262 : Nat := 4983230072969 + 3 ^ 40 * 771262 * 2
def baseEnd_771262 : Nat := 352024992487170371180477

theorem tailTrace_771262 : CollatzResearch.WordTrace tailWord_771262 prefixEnd_771262 352024992487170371180477 := by
  unfold tailWord_771262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516279516482121238482505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18753490754571313271906693 3516279516482121238482505)
  ·
    refine ⟨2637209637361590928861879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3516279516482121238482505 2637209637361590928861879)
    ·
      refine ⟨3955814456042386393292819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2637209637361590928861879 3955814456042386393292819)
      ·
        refine ⟨5933721684063579589939229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3955814456042386393292819 5933721684063579589939229)
        ·
          refine ⟨2225145631523842346227211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5933721684063579589939229 2225145631523842346227211)
          ·
            refine ⟨3337718447285763519340817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225145631523842346227211 3337718447285763519340817)
            ·
              refine ⟨2503288835464322639505613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337718447285763519340817 2503288835464322639505613)
              ·
                refine ⟨938733313299120989814605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2503288835464322639505613 938733313299120989814605)
                ·
                  refine ⟨352024992487170371180477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938733313299120989814605 352024992487170371180477)
                  ·
                    rfl

theorem cell20_771262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_771262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771262 prefixEnd_771262 := by exact prefixLift 771262
  have htrace : WordTrace (prefixWord ++ tailWord_771262) baseStart_771262 baseEnd_771262 := by
    simpa [prefixWord, tailWord_771262, baseEnd_771262] using wordTrace_append hprefix tailTrace_771262
  have hstable : (prefixWord ++ tailWord_771262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771262).length < 2 ^ (prefixWord ++ tailWord_771262).sum := by decide
  have hdescent : baseEnd_771262 < baseStart_771262 := by decide
  rcases family_descends (prefixWord ++ tailWord_771262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771297 : List Nat := [1, 2, 3, 1, 3, 3, 7]
def baseStart_771297 : Nat := 118140960795 + 771297 * 2 ^ 59
def prefixEnd_771297 : Nat := 4983230072969 + 3 ^ 40 * 771297 * 2
def baseEnd_771297 : Nat := 39115663048985089445963

theorem tailTrace_771297 : CollatzResearch.WordTrace tailWord_771297 prefixEnd_771297 39115663048985089445963 := by
  unfold tailWord_771297
  simp only [CollatzResearch.WordTrace]
  refine ⟨28131512686730170885384145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18754341791153447256922763 28131512686730170885384145)
  ·
    refine ⟨21098634515047628164038109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28131512686730170885384145 21098634515047628164038109)
    ·
      refine ⟨7911987943142860561514291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21098634515047628164038109 7911987943142860561514291)
      ·
        refine ⟨11867981914714290842271437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7911987943142860561514291 11867981914714290842271437)
        ·
          refine ⟨4450493218017859065851789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11867981914714290842271437 4450493218017859065851789)
          ·
            refine ⟨1668934956756697149694421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4450493218017859065851789 1668934956756697149694421)
            ·
              refine ⟨39115663048985089445963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1668934956756697149694421 39115663048985089445963)
              ·
                rfl

theorem cell20_771297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 7].length) (baseStart_771297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771297 prefixEnd_771297 := by exact prefixLift 771297
  have htrace : WordTrace (prefixWord ++ tailWord_771297) baseStart_771297 baseEnd_771297 := by
    simpa [prefixWord, tailWord_771297, baseEnd_771297] using wordTrace_append hprefix tailTrace_771297
  have hstable : (prefixWord ++ tailWord_771297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771297).length < 2 ^ (prefixWord ++ tailWord_771297).sum := by decide
  have hdescent : baseEnd_771297 < baseStart_771297 := by decide
  rcases family_descends (prefixWord ++ tailWord_771297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771307 : List Nat := [1, 1, 1, 1, 2, 6, 2, 4, 2]
def baseStart_771307 : Nat := 118140960795 + 771307 * 2 ^ 59
def prefixEnd_771307 : Nat := 4983230072969 + 3 ^ 40 * 771307 * 2
def baseEnd_771307 : Nat := 352045531713350214680293

theorem tailTrace_771307 : CollatzResearch.WordTrace tailWord_771307 prefixEnd_771307 352045531713350214680293 := by
  unfold tailWord_771307
  simp only [CollatzResearch.WordTrace]
  refine ⟨28131877416693942593248175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18754584944462628395498783 28131877416693942593248175)
  ·
    refine ⟨42197816125040913889872263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28131877416693942593248175 42197816125040913889872263)
    ·
      refine ⟨63296724187561370834808395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42197816125040913889872263 63296724187561370834808395)
      ·
        refine ⟨94945086281342056252212593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63296724187561370834808395 94945086281342056252212593)
        ·
          refine ⟨71208814711006542189159445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94945086281342056252212593 71208814711006542189159445)
          ·
            refine ⟨3337913189578431665116849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71208814711006542189159445 3337913189578431665116849)
            ·
              refine ⟨2503434892183823748837637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337913189578431665116849 2503434892183823748837637)
              ·
                refine ⟨469394042284466952907057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2503434892183823748837637 469394042284466952907057)
                ·
                  refine ⟨352045531713350214680293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469394042284466952907057 352045531713350214680293)
                  ·
                    rfl

theorem cell20_771307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 4, 2].length) (baseStart_771307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771307 prefixEnd_771307 := by exact prefixLift 771307
  have htrace : WordTrace (prefixWord ++ tailWord_771307) baseStart_771307 baseEnd_771307 := by
    simpa [prefixWord, tailWord_771307, baseEnd_771307] using wordTrace_append hprefix tailTrace_771307
  have hstable : (prefixWord ++ tailWord_771307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771307).length < 2 ^ (prefixWord ++ tailWord_771307).sum := by decide
  have hdescent : baseEnd_771307 < baseStart_771307 := by decide
  rcases family_descends (prefixWord ++ tailWord_771307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771358 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_771358 : Nat := 118140960795 + 771358 * 2 ^ 59
def prefixEnd_771358 : Nat := 4983230072969 + 3 ^ 40 * 771358 * 2
def baseEnd_771358 : Nat := 352068809503020703980085

theorem tailTrace_771358 : CollatzResearch.WordTrace tailWord_771358 prefixEnd_771358 352068809503020703980085 := by
  unfold tailWord_771358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3516717192438647287919341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18755825026339452202236485 3516717192438647287919341)
  ·
    refine ⟨1318768947164492732969753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3516717192438647287919341 1318768947164492732969753)
    ·
      refine ⟨989076710373369549727315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1318768947164492732969753 989076710373369549727315)
      ·
        refine ⟨1483615065560054324590973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989076710373369549727315 1483615065560054324590973)
        ·
          refine ⟨556355649585020371721615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1483615065560054324590973 556355649585020371721615)
          ·
            refine ⟨834533474377530557582423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556355649585020371721615 834533474377530557582423)
            ·
              refine ⟨1251800211566295836373635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834533474377530557582423 1251800211566295836373635)
              ·
                refine ⟨1877700317349443754560453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251800211566295836373635 1877700317349443754560453)
                ·
                  refine ⟨352068809503020703980085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877700317349443754560453 352068809503020703980085)
                  ·
                    rfl

theorem cell20_771358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_771358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771358 prefixEnd_771358 := by exact prefixLift 771358
  have htrace : WordTrace (prefixWord ++ tailWord_771358) baseStart_771358 baseEnd_771358 := by
    simpa [prefixWord, tailWord_771358, baseEnd_771358] using wordTrace_append hprefix tailTrace_771358
  have hstable : (prefixWord ++ tailWord_771358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771358).length < 2 ^ (prefixWord ++ tailWord_771358).sum := by decide
  have hdescent : baseEnd_771358 < baseStart_771358 := by decide
  rcases family_descends (prefixWord ++ tailWord_771358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771362 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_771362 : Nat := 118140960795 + 771362 * 2 ^ 59
def prefixEnd_771362 : Nat := 4983230072969 + 3 ^ 40 * 771362 * 2
def baseEnd_771362 : Nat := 352070635212014467846735

theorem tailTrace_771362 : CollatzResearch.WordTrace tailWord_771362 prefixEnd_771362 352070635212014467846735 := by
  unfold tailWord_771362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7033470857873671746625085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18755922287663124657666893 7033470857873671746625085)
  ·
    refine ⟨2637551571702626904984407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7033470857873671746625085 2637551571702626904984407)
    ·
      refine ⟨3956327357553940357476611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2637551571702626904984407 3956327357553940357476611)
      ·
        refine ⟨5934491036330910536214917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956327357553940357476611 5934491036330910536214917)
        ·
          refine ⟨1112717069312045725540297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5934491036330910536214917 1112717069312045725540297)
          ·
            refine ⟨834537801984034294155223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112717069312045725540297 834537801984034294155223)
            ·
              refine ⟨1251806702976051441232835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834537801984034294155223 1251806702976051441232835)
              ·
                refine ⟨1877710054464077161849253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251806702976051441232835 1877710054464077161849253)
                ·
                  refine ⟨352070635212014467846735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877710054464077161849253 352070635212014467846735)
                  ·
                    rfl

theorem cell20_771362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_771362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771362 prefixEnd_771362 := by exact prefixLift 771362
  have htrace : WordTrace (prefixWord ++ tailWord_771362) baseStart_771362 baseEnd_771362 := by
    simpa [prefixWord, tailWord_771362, baseEnd_771362] using wordTrace_append hprefix tailTrace_771362
  have hstable : (prefixWord ++ tailWord_771362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771362).length < 2 ^ (prefixWord ++ tailWord_771362).sum := by decide
  have hdescent : baseEnd_771362 < baseStart_771362 := by decide
  rcases family_descends (prefixWord ++ tailWord_771362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771418 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_771418 : Nat := 118140960795 + 771418 * 2 ^ 59
def prefixEnd_771418 : Nat := 4983230072969 + 3 ^ 40 * 771418 * 2
def baseEnd_771418 : Nat := 352096195137927161979839

theorem tailTrace_771418 : CollatzResearch.WordTrace tailWord_771418 prefixEnd_771418 352096195137927161979839 := by
  unfold tailWord_771418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7033981479822952137634727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18757283946194539033692605 7033981479822952137634727)
  ·
    refine ⟨10550972219734428206452091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7033981479822952137634727 10550972219734428206452091)
    ·
      refine ⟨15826458329601642309678137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10550972219734428206452091 15826458329601642309678137)
      ·
        refine ⟨11869843747201231732258603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15826458329601642309678137 11869843747201231732258603)
        ·
          refine ⟨17804765620801847598387905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11869843747201231732258603 17804765620801847598387905)
          ·
            refine ⟨13353574215601385698790929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17804765620801847598387905 13353574215601385698790929)
            ·
              refine ⟨10015180661701039274093197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13353574215601385698790929 10015180661701039274093197)
              ·
                refine ⟨3755692748137889727784949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10015180661701039274093197 3755692748137889727784949)
                ·
                  refine ⟨352096195137927161979839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3755692748137889727784949 352096195137927161979839)
                  ·
                    rfl

theorem cell20_771418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_771418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771418 prefixEnd_771418 := by exact prefixLift 771418
  have htrace : WordTrace (prefixWord ++ tailWord_771418) baseStart_771418 baseEnd_771418 := by
    simpa [prefixWord, tailWord_771418, baseEnd_771418] using wordTrace_append hprefix tailTrace_771418
  have hstable : (prefixWord ++ tailWord_771418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771418).length < 2 ^ (prefixWord ++ tailWord_771418).sum := by decide
  have hdescent : baseEnd_771418 < baseStart_771418 := by decide
  rcases family_descends (prefixWord ++ tailWord_771418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771425 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_771425 : Nat := 118140960795 + 771425 * 2 ^ 59
def prefixEnd_771425 : Nat := 4983230072969 + 3 ^ 40 * 771425 * 2
def baseEnd_771425 : Nat := 352099390128666248746477

theorem tailTrace_771425 : CollatzResearch.WordTrace tailWord_771425 prefixEnd_771425 352099390128666248746477 := by
  unfold tailWord_771425
  simp only [CollatzResearch.WordTrace]
  refine ⟨28136181230266448746043729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18757454153510965830695819 28136181230266448746043729)
  ·
    refine ⟨21102135922699836559532797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28136181230266448746043729 21102135922699836559532797)
    ·
      refine ⟨7913300971012438709824799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21102135922699836559532797 7913300971012438709824799)
      ·
        refine ⟨11869951456518658064737199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7913300971012438709824799 11869951456518658064737199)
        ·
          refine ⟨17804927184777987097105799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11869951456518658064737199 17804927184777987097105799)
          ·
            refine ⟨26707390777166980645658699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17804927184777987097105799 26707390777166980645658699)
            ·
              refine ⟨40061086165750470968488049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26707390777166980645658699 40061086165750470968488049)
              ·
                refine ⟨30045814624312853226366037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40061086165750470968488049 30045814624312853226366037)
                ·
                  refine ⟨352099390128666248746477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30045814624312853226366037 352099390128666248746477)
                  ·
                    rfl

theorem cell20_771425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_771425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771425 prefixEnd_771425 := by exact prefixLift 771425
  have htrace : WordTrace (prefixWord ++ tailWord_771425) baseStart_771425 baseEnd_771425 := by
    simpa [prefixWord, tailWord_771425, baseEnd_771425] using wordTrace_append hprefix tailTrace_771425
  have hstable : (prefixWord ++ tailWord_771425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771425).length < 2 ^ (prefixWord ++ tailWord_771425).sum := by decide
  have hdescent : baseEnd_771425 < baseStart_771425 := by decide
  rcases family_descends (prefixWord ++ tailWord_771425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771428 : List Nat := [2, 3, 1, 1, 3, 4, 1, 5]
def baseStart_771428 : Nat := 118140960795 + 771428 * 2 ^ 59
def prefixEnd_771428 : Nat := 4983230072969 + 3 ^ 40 * 771428 * 2
def baseEnd_771428 : Nat := 117366919803470523882155

theorem tailTrace_771428 : CollatzResearch.WordTrace tailWord_771428 prefixEnd_771428 117366919803470523882155 := by
  unfold tailWord_771428
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068145324627790129201469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18757527099503720172268625 14068145324627790129201469)
  ·
    refine ⟨5275554496735421298450551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14068145324627790129201469 5275554496735421298450551)
    ·
      refine ⟨7913331745103131947675827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5275554496735421298450551 7913331745103131947675827)
      ·
        refine ⟨11869997617654697921513741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7913331745103131947675827 11869997617654697921513741)
        ·
          refine ⟨4451249106620511720567653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11869997617654697921513741 4451249106620511720567653)
          ·
            refine ⟨834609207491345947606435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4451249106620511720567653 834609207491345947606435)
            ·
              refine ⟨1251913811237018921409653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834609207491345947606435 1251913811237018921409653)
              ·
                refine ⟨117366919803470523882155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1251913811237018921409653 117366919803470523882155)
                ·
                  rfl

theorem cell20_771428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_771428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771428 prefixEnd_771428 := by exact prefixLift 771428
  have htrace : WordTrace (prefixWord ++ tailWord_771428) baseStart_771428 baseEnd_771428 := by
    simpa [prefixWord, tailWord_771428, baseEnd_771428] using wordTrace_append hprefix tailTrace_771428
  have hstable : (prefixWord ++ tailWord_771428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771428).length < 2 ^ (prefixWord ++ tailWord_771428).sum := by decide
  have hdescent : baseEnd_771428 < baseStart_771428 := by decide
  rcases family_descends (prefixWord ++ tailWord_771428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771438 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_771438 : Nat := 118140960795 + 771438 * 2 ^ 59
def prefixEnd_771438 : Nat := 4983230072969 + 3 ^ 40 * 771438 * 2
def baseEnd_771438 : Nat := 352105323682895981313091

theorem tailTrace_771438 : CollatzResearch.WordTrace tailWord_771438 prefixEnd_771438 352105323682895981313091 := by
  unfold tailWord_771438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517081922402418995783371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18757770252812901310844645 3517081922402418995783371)
  ·
    refine ⟨5275622883603628493675057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3517081922402418995783371 5275622883603628493675057)
    ·
      refine ⟨3956717162702721370256293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5275622883603628493675057 3956717162702721370256293)
      ·
        refine ⟨741884468006760256923055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3956717162702721370256293 741884468006760256923055)
        ·
          refine ⟨1112826702010140385384583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741884468006760256923055 1112826702010140385384583)
          ·
            refine ⟨1669240053015210578076875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112826702010140385384583 1669240053015210578076875)
            ·
              refine ⟨2503860079522815867115313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669240053015210578076875 2503860079522815867115313)
              ·
                refine ⟨1877895059642111900336485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503860079522815867115313 1877895059642111900336485)
                ·
                  refine ⟨352105323682895981313091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877895059642111900336485 352105323682895981313091)
                  ·
                    rfl

theorem cell20_771438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_771438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771438 prefixEnd_771438 := by exact prefixLift 771438
  have htrace : WordTrace (prefixWord ++ tailWord_771438) baseStart_771438 baseEnd_771438 := by
    simpa [prefixWord, tailWord_771438, baseEnd_771438] using wordTrace_append hprefix tailTrace_771438
  have hstable : (prefixWord ++ tailWord_771438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771438).length < 2 ^ (prefixWord ++ tailWord_771438).sum := by decide
  have hdescent : baseEnd_771438 < baseStart_771438 := by decide
  rcases family_descends (prefixWord ++ tailWord_771438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771442 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_771442 : Nat := 118140960795 + 771442 * 2 ^ 59
def prefixEnd_771442 : Nat := 4983230072969 + 3 ^ 40 * 771442 * 2
def baseEnd_771442 : Nat := 352107149391889745179741

theorem tailTrace_771442 : CollatzResearch.WordTrace tailWord_771442 prefixEnd_771442 352107149391889745179741 := by
  unfold tailWord_771442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7034200317801215162353145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18757867514136573766275053 7034200317801215162353145)
  ·
    refine ⟨5275650238350911371764859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7034200317801215162353145 5275650238350911371764859)
    ·
      refine ⟨7913475357526367057647289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5275650238350911371764859 7913475357526367057647289)
      ·
        refine ⟨5935106518144775293235467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7913475357526367057647289 5935106518144775293235467)
        ·
          refine ⟨8902659777217162939853201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5935106518144775293235467 8902659777217162939853201)
          ·
            refine ⟨6676994832912872204889901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8902659777217162939853201 6676994832912872204889901)
            ·
              refine ⟨2503873062342327076833713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6676994832912872204889901 2503873062342327076833713)
              ·
                refine ⟨1877904796756745307625285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2503873062342327076833713 1877904796756745307625285)
                ·
                  refine ⟨352107149391889745179741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1877904796756745307625285 352107149391889745179741)
                  ·
                    rfl

theorem cell20_771442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_771442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771442 prefixEnd_771442 := by exact prefixLift 771442
  have htrace : WordTrace (prefixWord ++ tailWord_771442) baseStart_771442 baseEnd_771442 := by
    simpa [prefixWord, tailWord_771442, baseEnd_771442] using wordTrace_append hprefix tailTrace_771442
  have hstable : (prefixWord ++ tailWord_771442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771442).length < 2 ^ (prefixWord ++ tailWord_771442).sum := by decide
  have hdescent : baseEnd_771442 < baseStart_771442 := by decide
  rcases family_descends (prefixWord ++ tailWord_771442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771445 : List Nat := [1, 3, 4, 1, 3, 1, 3, 4]
def baseStart_771445 : Nat := 118140960795 + 771445 * 2 ^ 59
def prefixEnd_771445 : Nat := 4983230072969 + 3 ^ 40 * 771445 * 2
def baseEnd_771445 : Nat := 117369506224545022693243

theorem tailTrace_771445 : CollatzResearch.WordTrace tailWord_771445 prefixEnd_771445 117369506224545022693243 := by
  unfold tailWord_771445
  simp only [CollatzResearch.WordTrace]
  refine ⟨28136910690193992161771789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18757940460129328107847859 28136910690193992161771789)
  ·
    refine ⟨10551341508822747060664421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28136910690193992161771789 10551341508822747060664421)
    ·
      refine ⟨1978376532904265073874579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10551341508822747060664421 1978376532904265073874579)
      ·
        refine ⟨2967564799356397610811869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978376532904265073874579 2967564799356397610811869)
        ·
          refine ⟨1112836799758649104054451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2967564799356397610811869 1112836799758649104054451)
          ·
            refine ⟨1669255199637973656081677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112836799758649104054451 1669255199637973656081677)
            ·
              refine ⟨625970699864240121030629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669255199637973656081677 625970699864240121030629)
              ·
                refine ⟨117369506224545022693243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 625970699864240121030629 117369506224545022693243)
                ·
                  rfl

theorem cell20_771445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 4].length) (baseStart_771445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771445 prefixEnd_771445 := by exact prefixLift 771445
  have htrace : WordTrace (prefixWord ++ tailWord_771445) baseStart_771445 baseEnd_771445 := by
    simpa [prefixWord, tailWord_771445, baseEnd_771445] using wordTrace_append hprefix tailTrace_771445
  have hstable : (prefixWord ++ tailWord_771445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771445).length < 2 ^ (prefixWord ++ tailWord_771445).sum := by decide
  have hdescent : baseEnd_771445 < baseStart_771445 := by decide
  rcases family_descends (prefixWord ++ tailWord_771445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771459 : List Nat := [1, 1, 1, 3, 5, 1, 1, 5, 2]
def baseStart_771459 : Nat := 118140960795 + 771459 * 2 ^ 59
def prefixEnd_771459 : Nat := 4983230072969 + 3 ^ 40 * 771459 * 2
def baseEnd_771459 : Nat := 352114908655113241613005

theorem tailTrace_771459 : CollatzResearch.WordTrace tailWord_771459 prefixEnd_771459 352114908655113241613005 := by
  unfold tailWord_771459
  simp only [CollatzResearch.WordTrace]
  refine ⟨28137421312143272552781431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18758280874762181701854287 28137421312143272552781431)
  ·
    refine ⟨42206131968214908829172147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28137421312143272552781431 42206131968214908829172147)
    ·
      refine ⟨63309197952322363243758221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42206131968214908829172147 63309197952322363243758221)
      ·
        refine ⟨23740949232120886216409333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63309197952322363243758221 23740949232120886216409333)
        ·
          refine ⟨2225713990511333082788375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23740949232120886216409333 2225713990511333082788375)
          ·
            refine ⟨3338570985766999624182563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225713990511333082788375 3338570985766999624182563)
            ·
              refine ⟨5007856478650499436273845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338570985766999624182563 5007856478650499436273845)
              ·
                refine ⟨469486544873484322150673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5007856478650499436273845 469486544873484322150673)
                ·
                  refine ⟨352114908655113241613005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469486544873484322150673 352114908655113241613005)
                  ·
                    rfl

theorem cell20_771459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 2].length) (baseStart_771459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771459 prefixEnd_771459 := by exact prefixLift 771459
  have htrace : WordTrace (prefixWord ++ tailWord_771459) baseStart_771459 baseEnd_771459 := by
    simpa [prefixWord, tailWord_771459, baseEnd_771459] using wordTrace_append hprefix tailTrace_771459
  have hstable : (prefixWord ++ tailWord_771459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771459).length < 2 ^ (prefixWord ++ tailWord_771459).sum := by decide
  have hdescent : baseEnd_771459 < baseStart_771459 := by decide
  rcases family_descends (prefixWord ++ tailWord_771459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771476 : List Nat := [2, 4, 2, 1, 2, 1, 2, 4, 2]
def baseStart_771476 : Nat := 118140960795 + 771476 * 2 ^ 59
def prefixEnd_771476 : Nat := 4983230072969 + 3 ^ 40 * 771476 * 2
def baseEnd_771476 : Nat := 352122667918336738046269

theorem tailTrace_771476 : CollatzResearch.WordTrace tailWord_771476 prefixEnd_771476 352122667918336738046269 := by
  unfold tailWord_771476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14069020676540842228075141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18758694235387789637433521 14069020676540842228075141)
  ·
    refine ⟨2637941376851407917764089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14069020676540842228075141 2637941376851407917764089)
    ·
      refine ⟨1978456032638555938323067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2637941376851407917764089 1978456032638555938323067)
      ·
        refine ⟨2967684048957833907484601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978456032638555938323067 2967684048957833907484601)
        ·
          refine ⟨2225763036718375430613451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2967684048957833907484601 2225763036718375430613451)
          ·
            refine ⟨3338644555077563145920177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225763036718375430613451 3338644555077563145920177)
            ·
              refine ⟨2503983416308172359440133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3338644555077563145920177 2503983416308172359440133)
              ·
                refine ⟨469496890557782317395025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2503983416308172359440133 469496890557782317395025)
                ·
                  refine ⟨352122667918336738046269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469496890557782317395025 352122667918336738046269)
                  ·
                    rfl

theorem cell20_771476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_771476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771476 prefixEnd_771476 := by exact prefixLift 771476
  have htrace : WordTrace (prefixWord ++ tailWord_771476) baseStart_771476 baseEnd_771476 := by
    simpa [prefixWord, tailWord_771476, baseEnd_771476] using wordTrace_append hprefix tailTrace_771476
  have hstable : (prefixWord ++ tailWord_771476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771476).length < 2 ^ (prefixWord ++ tailWord_771476).sum := by decide
  have hdescent : baseEnd_771476 < baseStart_771476 := by decide
  rcases family_descends (prefixWord ++ tailWord_771476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771486 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_771486 : Nat := 118140960795 + 771486 * 2 ^ 59
def prefixEnd_771486 : Nat := 4983230072969 + 3 ^ 40 * 771486 * 2
def baseEnd_771486 : Nat := 352127232190821147712895

theorem tailTrace_771486 : CollatzResearch.WordTrace tailWord_771486 prefixEnd_771486 352127232190821147712895 := by
  unfold tailWord_771486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517300760380682020501789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18758937388696970776009541 3517300760380682020501789)
  ·
    refine ⟨1318987785142755757688171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3517300760380682020501789 1318987785142755757688171)
    ·
      refine ⟨1978481677714133636532257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318987785142755757688171 1978481677714133636532257)
      ·
        refine ⟨1483861258285600227399193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978481677714133636532257 1483861258285600227399193)
        ·
          refine ⟨1112895943714200170549395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1483861258285600227399193 1112895943714200170549395)
          ·
            refine ⟨1669343915571300255824093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112895943714200170549395 1669343915571300255824093)
            ·
              refine ⟨626003968339237595934035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669343915571300255824093 626003968339237595934035)
              ·
                refine ⟨939005952508856393901053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626003968339237595934035 939005952508856393901053)
                ·
                  refine ⟨352127232190821147712895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939005952508856393901053 352127232190821147712895)
                  ·
                    rfl

theorem cell20_771486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_771486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771486 prefixEnd_771486 := by exact prefixLift 771486
  have htrace : WordTrace (prefixWord ++ tailWord_771486) baseStart_771486 baseEnd_771486 := by
    simpa [prefixWord, tailWord_771486, baseEnd_771486] using wordTrace_append hprefix tailTrace_771486
  have hstable : (prefixWord ++ tailWord_771486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771486).length < 2 ^ (prefixWord ++ tailWord_771486).sum := by decide
  have hdescent : baseEnd_771486 < baseStart_771486 := by decide
  rcases family_descends (prefixWord ++ tailWord_771486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771542 : List Nat := [5, 2, 1, 1, 1, 2, 1, 7]
def baseStart_771542 : Nat := 118140960795 + 771542 * 2 ^ 59
def prefixEnd_771542 : Nat := 4983230072969 + 3 ^ 40 * 771542 * 2
def baseEnd_771542 : Nat := 117384264038911280615333

theorem tailTrace_771542 : CollatzResearch.WordTrace tailWord_771542 prefixEnd_771542 117384264038911280615333 := by
  unfold tailWord_771542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758778035677661108003305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18760299047228385152035253 1758778035677661108003305)
  ·
    refine ⟨1319083526758245831002479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1758778035677661108003305 1319083526758245831002479)
    ·
      refine ⟨1978625290137368746503719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319083526758245831002479 1978625290137368746503719)
      ·
        refine ⟨2967937935206053119755579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978625290137368746503719 2967937935206053119755579)
        ·
          refine ⟨4451906902809079679633369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967937935206053119755579 4451906902809079679633369)
          ·
            refine ⟨3338930177106809759725027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4451906902809079679633369 3338930177106809759725027)
            ·
              refine ⟨5008395265660214639587541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338930177106809759725027 5008395265660214639587541)
              ·
                refine ⟨117384264038911280615333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5008395265660214639587541 117384264038911280615333)
                ·
                  rfl

theorem cell20_771542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_771542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771542 prefixEnd_771542 := by exact prefixLift 771542
  have htrace : WordTrace (prefixWord ++ tailWord_771542) baseStart_771542 baseEnd_771542 := by
    simpa [prefixWord, tailWord_771542, baseEnd_771542] using wordTrace_append hprefix tailTrace_771542
  have hstable : (prefixWord ++ tailWord_771542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771542).length < 2 ^ (prefixWord ++ tailWord_771542).sum := by decide
  have hdescent : baseEnd_771542 < baseStart_771542 := by decide
  rcases family_descends (prefixWord ++ tailWord_771542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771586 : List Nat := [3, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_771586 : Nat := 118140960795 + 771586 * 2 ^ 59
def prefixEnd_771586 : Nat := 4983230072969 + 3 ^ 40 * 771586 * 2
def baseEnd_771586 : Nat := 352172874915665244379153

theorem tailTrace_771586 : CollatzResearch.WordTrace tailWord_771586 prefixEnd_771586 352172874915665244379153 := by
  unfold tailWord_771586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7035513345670793310663653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18761368921788782161769741 7035513345670793310663653)
  ·
    refine ⟨1319158752313273745749435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7035513345670793310663653 1319158752313273745749435)
    ·
      refine ⟨1978738128469910618624153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319158752313273745749435 1978738128469910618624153)
      ·
        refine ⟨1484053596352432963968115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978738128469910618624153 1484053596352432963968115)
        ·
          refine ⟨2226080394528649445952173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484053596352432963968115 2226080394528649445952173)
          ·
            refine ⟨834780147948243542232065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2226080394528649445952173 834780147948243542232065)
            ·
              refine ⟨626085110961182656674049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834780147948243542232065 626085110961182656674049)
              ·
                refine ⟨469563833220886992505537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626085110961182656674049 469563833220886992505537)
                ·
                  refine ⟨352172874915665244379153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469563833220886992505537 352172874915665244379153)
                  ·
                    rfl

theorem cell20_771586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_771586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771586 prefixEnd_771586 := by exact prefixLift 771586
  have htrace : WordTrace (prefixWord ++ tailWord_771586) baseStart_771586 baseEnd_771586 := by
    simpa [prefixWord, tailWord_771586, baseEnd_771586] using wordTrace_append hprefix tailTrace_771586
  have hstable : (prefixWord ++ tailWord_771586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771586).length < 2 ^ (prefixWord ++ tailWord_771586).sum := by decide
  have hdescent : baseEnd_771586 < baseStart_771586 := by decide
  rcases family_descends (prefixWord ++ tailWord_771586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771615 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_771615 : Nat := 118140960795 + 771615 * 2 ^ 59
def prefixEnd_771615 : Nat := 4983230072969 + 3 ^ 40 * 771615 * 2
def baseEnd_771615 : Nat := 352186111305870032412367

theorem tailTrace_771615 : CollatzResearch.WordTrace tailWord_771615 prefixEnd_771615 352186111305870032412367 := by
  unfold tailWord_771615
  simp only [CollatzResearch.WordTrace]
  refine ⟨28143111099578111195460299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18762074066385407463640199 28143111099578111195460299)
  ·
    refine ⟨42214666649367166793190449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28143111099578111195460299 42214666649367166793190449)
    ·
      refine ⟨31660999987025375094892837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42214666649367166793190449 31660999987025375094892837)
      ·
        refine ⟨5936437497567257830292407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31660999987025375094892837 5936437497567257830292407)
        ·
          refine ⟨8904656246350886745438611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936437497567257830292407 8904656246350886745438611)
          ·
            refine ⟨13356984369526330118157917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8904656246350886745438611 13356984369526330118157917)
            ·
              refine ⟨5008869138572373794309219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13356984369526330118157917 5008869138572373794309219)
              ·
                refine ⟨7513303707858560691463829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008869138572373794309219 7513303707858560691463829)
                ·
                  refine ⟨352186111305870032412367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7513303707858560691463829 352186111305870032412367)
                  ·
                    rfl

theorem cell20_771615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_771615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771615 prefixEnd_771615 := by exact prefixLift 771615
  have htrace : WordTrace (prefixWord ++ tailWord_771615) baseStart_771615 baseEnd_771615 := by
    simpa [prefixWord, tailWord_771615, baseEnd_771615] using wordTrace_append hprefix tailTrace_771615
  have hstable : (prefixWord ++ tailWord_771615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771615).length < 2 ^ (prefixWord ++ tailWord_771615).sum := by decide
  have hdescent : baseEnd_771615 < baseStart_771615 := by decide
  rcases family_descends (prefixWord ++ tailWord_771615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771638 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_771638 : Nat := 118140960795 + 771638 * 2 ^ 59
def prefixEnd_771638 : Nat := 4983230072969 + 3 ^ 40 * 771638 * 2
def baseEnd_771638 : Nat := 352196609132584174645607

theorem tailTrace_771638 : CollatzResearch.WordTrace tailWord_771638 prefixEnd_771638 352196609132584174645607 := by
  unfold tailWord_771638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758996873655924132721723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18762633318996524082365045 1758996873655924132721723)
  ·
    refine ⟨2638495310483886199082585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1758996873655924132721723 2638495310483886199082585)
    ·
      refine ⟨1978871482862914649311939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2638495310483886199082585 1978871482862914649311939)
      ·
        refine ⟨2968307224294371973967909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978871482862914649311939 2968307224294371973967909)
        ·
          refine ⟨556557604555194745118983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2968307224294371973967909 556557604555194745118983)
          ·
            refine ⟨834836406832792117678475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556557604555194745118983 834836406832792117678475)
            ·
              refine ⟨1252254610249188176517713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834836406832792117678475 1252254610249188176517713)
              ·
                refine ⟨939190957686891132388285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252254610249188176517713 939190957686891132388285)
                ·
                  refine ⟨352196609132584174645607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939190957686891132388285 352196609132584174645607)
                  ·
                    rfl

theorem cell20_771638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_771638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771638 prefixEnd_771638 := by exact prefixLift 771638
  have htrace : WordTrace (prefixWord ++ tailWord_771638) baseStart_771638 baseEnd_771638 := by
    simpa [prefixWord, tailWord_771638, baseEnd_771638] using wordTrace_append hprefix tailTrace_771638
  have hstable : (prefixWord ++ tailWord_771638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771638).length < 2 ^ (prefixWord ++ tailWord_771638).sum := by decide
  have hdescent : baseEnd_771638 < baseStart_771638 := by decide
  rcases family_descends (prefixWord ++ tailWord_771638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771649 : List Nat := [1, 2, 5, 1, 1, 1, 1, 6, 2]
def baseStart_771649 : Nat := 118140960795 + 771649 * 2 ^ 59
def prefixEnd_771649 : Nat := 4983230072969 + 3 ^ 40 * 771649 * 2
def baseEnd_771649 : Nat := 352201629832317025278895

theorem tailTrace_771649 : CollatzResearch.WordTrace tailWord_771649 prefixEnd_771649 352201629832317025278895 := by
  unfold tailWord_771649
  simp only [CollatzResearch.WordTrace]
  refine ⟨28144351181454935002198001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18762900787636623334798667 28144351181454935002198001)
  ·
    refine ⟨21108263386091201251648501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28144351181454935002198001 21108263386091201251648501)
    ·
      refine ⟨1978899692446050117342047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21108263386091201251648501 1978899692446050117342047)
      ·
        refine ⟨2968349538669075176013071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1978899692446050117342047 2968349538669075176013071)
        ·
          refine ⟨4452524308003612764019607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968349538669075176013071 4452524308003612764019607)
          ·
            refine ⟨6678786462005419146029411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452524308003612764019607 6678786462005419146029411)
            ·
              refine ⟨10018179693008128719044117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678786462005419146029411 10018179693008128719044117)
              ·
                refine ⟨469602173109756033705193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10018179693008128719044117 469602173109756033705193)
                ·
                  refine ⟨352201629832317025278895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469602173109756033705193 352201629832317025278895)
                  ·
                    rfl

theorem cell20_771649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_771649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771649 prefixEnd_771649 := by exact prefixLift 771649
  have htrace : WordTrace (prefixWord ++ tailWord_771649) baseStart_771649 baseEnd_771649 := by
    simpa [prefixWord, tailWord_771649, baseEnd_771649] using wordTrace_append hprefix tailTrace_771649
  have hstable : (prefixWord ++ tailWord_771649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771649).length < 2 ^ (prefixWord ++ tailWord_771649).sum := by decide
  have hdescent : baseEnd_771649 < baseStart_771649 := by decide
  rcases family_descends (prefixWord ++ tailWord_771649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771684 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_771684 : Nat := 118140960795 + 771684 * 2 ^ 59
def prefixEnd_771684 : Nat := 4983230072969 + 3 ^ 40 * 771684 * 2
def baseEnd_771684 : Nat := 352217604786012459112085

theorem tailTrace_771684 : CollatzResearch.WordTrace tailWord_771684 prefixEnd_771684 352217604786012459112085 := by
  unfold tailWord_771684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072813868164067989861053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18763751824218757319814737 14072813868164067989861053)
  ·
    refine ⟨5277305200561525496197895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14072813868164067989861053 5277305200561525496197895)
    ·
      refine ⟨7915957800842288244296843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277305200561525496197895 7915957800842288244296843)
      ·
        refine ⟨11873936701263432366445265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915957800842288244296843 11873936701263432366445265)
        ·
          refine ⟨8905452525947574274833949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11873936701263432366445265 8905452525947574274833949)
          ·
            refine ⟨3339544697230340353062731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8905452525947574274833949 3339544697230340353062731)
            ·
              refine ⟨5009317045845510529594097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339544697230340353062731 5009317045845510529594097)
              ·
                refine ⟨3756987784384132897195573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5009317045845510529594097 3756987784384132897195573)
                ·
                  refine ⟨352217604786012459112085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3756987784384132897195573 352217604786012459112085)
                  ·
                    rfl

theorem cell20_771684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_771684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771684 prefixEnd_771684 := by exact prefixLift 771684
  have htrace : WordTrace (prefixWord ++ tailWord_771684) baseStart_771684 baseEnd_771684 := by
    simpa [prefixWord, tailWord_771684, baseEnd_771684] using wordTrace_append hprefix tailTrace_771684
  have hstable : (prefixWord ++ tailWord_771684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771684).length < 2 ^ (prefixWord ++ tailWord_771684).sum := by decide
  have hdescent : baseEnd_771684 < baseStart_771684 := by decide
  rcases family_descends (prefixWord ++ tailWord_771684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771687 : List Nat := [1, 1, 5, 1, 1, 1, 5, 3, 2]
def baseStart_771687 : Nat := 118140960795 + 771687 * 2 ^ 59
def prefixEnd_771687 : Nat := 4983230072969 + 3 ^ 40 * 771687 * 2
def baseEnd_771687 : Nat := 352218974067757782012073

theorem tailTrace_771687 : CollatzResearch.WordTrace tailWord_771687 prefixEnd_771687 352218974067757782012073 := by
  unfold tailWord_771687
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145737155317267492081315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18763824770211511661387543 28145737155317267492081315)
  ·
    refine ⟨42218605732975901238121973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28145737155317267492081315 42218605732975901238121973)
    ·
      refine ⟨3957994287466490741073935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42218605732975901238121973 3957994287466490741073935)
      ·
        refine ⟨5936991431199736111610903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957994287466490741073935 5936991431199736111610903)
        ·
          refine ⟨8905487146799604167416355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936991431199736111610903 8905487146799604167416355)
          ·
            refine ⟨13358230720199406251124533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8905487146799604167416355 13358230720199406251124533)
            ·
              refine ⟨1252334130018694336042925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13358230720199406251124533 1252334130018694336042925)
              ·
                refine ⟨469625298757010376016097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1252334130018694336042925 469625298757010376016097)
                ·
                  refine ⟨352218974067757782012073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469625298757010376016097 352218974067757782012073)
                  ·
                    rfl

theorem cell20_771687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 2].length) (baseStart_771687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771687 prefixEnd_771687 := by exact prefixLift 771687
  have htrace : WordTrace (prefixWord ++ tailWord_771687) baseStart_771687 baseEnd_771687 := by
    simpa [prefixWord, tailWord_771687, baseEnd_771687] using wordTrace_append hprefix tailTrace_771687
  have hstable : (prefixWord ++ tailWord_771687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771687).length < 2 ^ (prefixWord ++ tailWord_771687).sum := by decide
  have hdescent : baseEnd_771687 < baseStart_771687 := by decide
  rcases family_descends (prefixWord ++ tailWord_771687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771694 : List Nat := [4, 1, 2, 2, 3, 2, 6]
def baseStart_771694 : Nat := 118140960795 + 771694 * 2 ^ 59
def prefixEnd_771694 : Nat := 4983230072969 + 3 ^ 40 * 771694 * 2
def baseEnd_771694 : Nat := 39135796562055207642079

theorem tailTrace_771694 : CollatzResearch.WordTrace tailWord_771694 prefixEnd_771694 39135796562055207642079 := by
  unfold tailWord_771694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3518249058286488460948267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18763994977527938458390757 3518249058286488460948267)
  ·
    refine ⟨5277373587429732691422401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3518249058286488460948267 5277373587429732691422401)
    ·
      refine ⟨3958030190572299518566801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5277373587429732691422401 3958030190572299518566801)
      ·
        refine ⟨2968522642929224638925101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3958030190572299518566801 2968522642929224638925101)
        ·
          refine ⟨1113195991098459239596913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2968522642929224638925101 1113195991098459239596913)
          ·
            refine ⟨834896993323844429697685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113195991098459239596913 834896993323844429697685)
            ·
              refine ⟨39135796562055207642079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 834896993323844429697685 39135796562055207642079)
              ·
                rfl

theorem cell20_771694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 6].length) (baseStart_771694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771694 prefixEnd_771694 := by exact prefixLift 771694
  have htrace : WordTrace (prefixWord ++ tailWord_771694) baseStart_771694 baseEnd_771694 := by
    simpa [prefixWord, tailWord_771694, baseEnd_771694] using wordTrace_append hprefix tailTrace_771694
  have hstable : (prefixWord ++ tailWord_771694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771694).length < 2 ^ (prefixWord ++ tailWord_771694).sum := by decide
  have hdescent : baseEnd_771694 < baseStart_771694 := by decide
  rcases family_descends (prefixWord ++ tailWord_771694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771701 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_771701 : Nat := 118140960795 + 771701 * 2 ^ 59
def prefixEnd_771701 : Nat := 4983230072969 + 3 ^ 40 * 771701 * 2
def baseEnd_771701 : Nat := 352225364049235955545349

theorem tailTrace_771701 : CollatzResearch.WordTrace tailWord_771701 prefixEnd_771701 352225364049235955545349 := by
  unfold tailWord_771701
  simp only [CollatzResearch.WordTrace]
  refine ⟨28146247777266547883090957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18764165184844365255393971 28146247777266547883090957)
  ·
    refine ⟨10554842916474955456159109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28146247777266547883090957 10554842916474955456159109)
    ·
      refine ⟨1979033046839054148029833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10554842916474955456159109 1979033046839054148029833)
      ·
        refine ⟨1484274785129290611022375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1979033046839054148029833 1484274785129290611022375)
        ·
          refine ⟨2226412177693935916533563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484274785129290611022375 2226412177693935916533563)
          ·
            refine ⟨3339618266540903874800345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226412177693935916533563 3339618266540903874800345)
            ·
              refine ⟨2504713699905677906100259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3339618266540903874800345 2504713699905677906100259)
              ·
                refine ⟨3757070549858516859150389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504713699905677906100259 3757070549858516859150389)
                ·
                  refine ⟨352225364049235955545349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3757070549858516859150389 352225364049235955545349)
                  ·
                    rfl

theorem cell20_771701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_771701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771701 prefixEnd_771701 := by exact prefixLift 771701
  have htrace : WordTrace (prefixWord ++ tailWord_771701) baseStart_771701 baseEnd_771701 := by
    simpa [prefixWord, tailWord_771701, baseEnd_771701] using wordTrace_append hprefix tailTrace_771701
  have hstable : (prefixWord ++ tailWord_771701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771701).length < 2 ^ (prefixWord ++ tailWord_771701).sum := by decide
  have hdescent : baseEnd_771701 < baseStart_771701 := by decide
  rcases family_descends (prefixWord ++ tailWord_771701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771752 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 3]
def baseStart_771752 : Nat := 118140960795 + 771752 * 2 ^ 59
def prefixEnd_771752 : Nat := 4983230072969 + 3 ^ 40 * 771752 * 2
def baseEnd_771752 : Nat := 352248641838906444845141

theorem tailTrace_771752 : CollatzResearch.WordTrace tailWord_771752 prefixEnd_771752 352248641838906444845141 := by
  unfold tailWord_771752
  simp only [CollatzResearch.WordTrace]
  refine ⟨14074053950040891796598755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18765405266721189062131673 14074053950040891796598755)
  ·
    refine ⟨21111080925061337694898133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14074053950040891796598755 21111080925061337694898133)
    ·
      refine ⟨494790959181125102224175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 21111080925061337694898133 494790959181125102224175)
      ·
        refine ⟨742186438771687653336263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494790959181125102224175 742186438771687653336263)
        ·
          refine ⟨1113279658157531480004395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742186438771687653336263 1113279658157531480004395)
          ·
            refine ⟨1669919487236297220006593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113279658157531480004395 1669919487236297220006593)
            ·
              refine ⟨1252439615427222915004945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669919487236297220006593 1252439615427222915004945)
              ·
                refine ⟨939329711570417186253709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252439615427222915004945 939329711570417186253709)
                ·
                  refine ⟨352248641838906444845141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939329711570417186253709 352248641838906444845141)
                  ·
                    rfl

theorem cell20_771752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_771752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771752 prefixEnd_771752 := by exact prefixLift 771752
  have htrace : WordTrace (prefixWord ++ tailWord_771752) baseStart_771752 baseEnd_771752 := by
    simpa [prefixWord, tailWord_771752, baseEnd_771752] using wordTrace_append hprefix tailTrace_771752
  have hstable : (prefixWord ++ tailWord_771752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771752).length < 2 ^ (prefixWord ++ tailWord_771752).sum := by decide
  have hdescent : baseEnd_771752 < baseStart_771752 := by decide
  rcases family_descends (prefixWord ++ tailWord_771752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771760 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_771760 : Nat := 118140960795 + 771760 * 2 ^ 59
def prefixEnd_771760 : Nat := 4983230072969 + 3 ^ 40 * 771760 * 2
def baseEnd_771760 : Nat := 352252293256893972578441

theorem tailTrace_771760 : CollatzResearch.WordTrace tailWord_771760 prefixEnd_771760 352252293256893972578441 := by
  unfold tailWord_771760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14074199842026400479744367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18765599789368533972992489 14074199842026400479744367)
  ·
    refine ⟨21111299763039600719616551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14074199842026400479744367 21111299763039600719616551)
    ·
      refine ⟨31666949644559401079424827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21111299763039600719616551 31666949644559401079424827)
      ·
        refine ⟨47500424466839101619137241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31666949644559401079424827 47500424466839101619137241)
        ·
          refine ⟨35625318350129326214352931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47500424466839101619137241 35625318350129326214352931)
          ·
            refine ⟨53437977525193989321529397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35625318350129326214352931 53437977525193989321529397)
            ·
              refine ⟨5009810392986936498893381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53437977525193989321529397 5009810392986936498893381)
              ·
                refine ⟨939339448685050593542509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5009810392986936498893381 939339448685050593542509)
                ·
                  refine ⟨352252293256893972578441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939339448685050593542509 352252293256893972578441)
                  ·
                    rfl

theorem cell20_771760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_771760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771760 prefixEnd_771760 := by exact prefixLift 771760
  have htrace : WordTrace (prefixWord ++ tailWord_771760) baseStart_771760 baseEnd_771760 := by
    simpa [prefixWord, tailWord_771760, baseEnd_771760] using wordTrace_append hprefix tailTrace_771760
  have hstable : (prefixWord ++ tailWord_771760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771760).length < 2 ^ (prefixWord ++ tailWord_771760).sum := by decide
  have hdescent : baseEnd_771760 < baseStart_771760 := by decide
  rcases family_descends (prefixWord ++ tailWord_771760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771801 : List Nat := [1, 2, 1, 2, 3, 4, 2, 3, 2]
def baseStart_771801 : Nat := 118140960795 + 771801 * 2 ^ 59
def prefixEnd_771801 : Nat := 4983230072969 + 3 ^ 40 * 771801 * 2
def baseEnd_771801 : Nat := 352271006774080052211607

theorem tailTrace_771801 : CollatzResearch.WordTrace tailWord_771801 prefixEnd_771801 352271006774080052211607 := by
  unfold tailWord_771801
  simp only [CollatzResearch.WordTrace]
  refine ⟨28149895076904264961731257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18766596717936176641154171 28149895076904264961731257)
  ·
    refine ⟨21112421307678198721298443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28149895076904264961731257 21112421307678198721298443)
    ·
      refine ⟨31668631961517298081947665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21112421307678198721298443 31668631961517298081947665)
      ·
        refine ⟨23751473971137973561460749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31668631961517298081947665 23751473971137973561460749)
        ·
          refine ⟨8906802739176740085547781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23751473971137973561460749 8906802739176740085547781)
          ·
            refine ⟨1670025513595638766040209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8906802739176740085547781 1670025513595638766040209)
            ·
              refine ⟨1252519135196729074530157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1670025513595638766040209 1252519135196729074530157)
              ·
                refine ⟨469694675698773402948809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1252519135196729074530157 469694675698773402948809)
                ·
                  refine ⟨352271006774080052211607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469694675698773402948809 352271006774080052211607)
                  ·
                    rfl

theorem cell20_771801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_771801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771801 prefixEnd_771801 := by exact prefixLift 771801
  have htrace : WordTrace (prefixWord ++ tailWord_771801) baseStart_771801 baseEnd_771801 := by
    simpa [prefixWord, tailWord_771801, baseEnd_771801] using wordTrace_append hprefix tailTrace_771801
  have hstable : (prefixWord ++ tailWord_771801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771801).length < 2 ^ (prefixWord ++ tailWord_771801).sum := by decide
  have hdescent : baseEnd_771801 < baseStart_771801 := by decide
  rcases family_descends (prefixWord ++ tailWord_771801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771811 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 3]
def baseStart_771811 : Nat := 118140960795 + 771811 * 2 ^ 59
def prefixEnd_771811 : Nat := 4983230072969 + 3 ^ 40 * 771811 * 2
def baseEnd_771811 : Nat := 352275571046564461878233

theorem tailTrace_771811 : CollatzResearch.WordTrace tailWord_771811 prefixEnd_771811 352275571046564461878233 := by
  unfold tailWord_771811
  simp only [CollatzResearch.WordTrace]
  refine ⟨28150259806868036669595287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18766839871245357779730191 28150259806868036669595287)
  ·
    refine ⟨42225389710302055004392931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28150259806868036669595287 42225389710302055004392931)
    ·
      refine ⟨63338084565453082506589397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42225389710302055004392931 63338084565453082506589397)
      ·
        refine ⟨1484486357002806621248189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 63338084565453082506589397 1484486357002806621248189)
        ·
          refine ⟨556682383876052482968071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1484486357002806621248189 556682383876052482968071)
          ·
            refine ⟨835023575814078724452107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556682383876052482968071 835023575814078724452107)
            ·
              refine ⟨1252535363721118086678161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835023575814078724452107 1252535363721118086678161)
              ·
                refine ⟨939401522790838565008621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252535363721118086678161 939401522790838565008621)
                ·
                  refine ⟨352275571046564461878233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939401522790838565008621 352275571046564461878233)
                  ·
                    rfl

theorem cell20_771811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 3].length) (baseStart_771811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771811 prefixEnd_771811 := by exact prefixLift 771811
  have htrace : WordTrace (prefixWord ++ tailWord_771811) baseStart_771811 baseEnd_771811 := by
    simpa [prefixWord, tailWord_771811, baseEnd_771811] using wordTrace_append hprefix tailTrace_771811
  have hstable : (prefixWord ++ tailWord_771811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771811).length < 2 ^ (prefixWord ++ tailWord_771811).sum := by decide
  have hdescent : baseEnd_771811 < baseStart_771811 := by decide
  rcases family_descends (prefixWord ++ tailWord_771811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771812 : List Nat := [2, 3, 1, 1, 1, 3, 9]
def baseStart_771812 : Nat := 118140960795 + 771812 * 2 ^ 59
def prefixEnd_771812 : Nat := 4983230072969 + 3 ^ 40 * 771812 * 2
def baseEnd_771812 : Nat := 39141780830423655871655

theorem tailTrace_771812 : CollatzResearch.WordTrace tailWord_771812 prefixEnd_771812 39141780830423655871655 := by
  unfold tailWord_771812
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075148139932206920190845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18766864186576275893587793 14075148139932206920190845)
  ·
    refine ⟨5278180552474577595071567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14075148139932206920190845 5278180552474577595071567)
    ·
      refine ⟨7917270828711866392607351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5278180552474577595071567 7917270828711866392607351)
      ·
        refine ⟨11875906243067799588911027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7917270828711866392607351 11875906243067799588911027)
        ·
          refine ⟨17813859364601699383366541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11875906243067799588911027 17813859364601699383366541)
          ·
            refine ⟨6680197261725637268762453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17813859364601699383366541 6680197261725637268762453)
            ·
              refine ⟨39141780830423655871655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6680197261725637268762453 39141780830423655871655)
              ·
                rfl

theorem cell20_771812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 9].length) (baseStart_771812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771812 prefixEnd_771812 := by exact prefixLift 771812
  have htrace : WordTrace (prefixWord ++ tailWord_771812) baseStart_771812 baseEnd_771812 := by
    simpa [prefixWord, tailWord_771812, baseEnd_771812] using wordTrace_append hprefix tailTrace_771812
  have hstable : (prefixWord ++ tailWord_771812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771812).length < 2 ^ (prefixWord ++ tailWord_771812).sum := by decide
  have hdescent : baseEnd_771812 < baseStart_771812 := by decide
  rcases family_descends (prefixWord ++ tailWord_771812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771822 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_771822 : Nat := 118140960795 + 771822 * 2 ^ 59
def prefixEnd_771822 : Nat := 4983230072969 + 3 ^ 40 * 771822 * 2
def baseEnd_771822 : Nat := 352280591746297312511521

theorem tailTrace_771822 : CollatzResearch.WordTrace tailWord_771822 prefixEnd_771822 352280591746297312511521 := by
  unfold tailWord_771822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3518832626228523193530715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18767107339885457032163813 3518832626228523193530715)
  ·
    refine ⟨5278248939342784790296073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3518832626228523193530715 5278248939342784790296073)
    ·
      refine ⟨3958686704507088592722055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5278248939342784790296073 3958686704507088592722055)
      ·
        refine ⟨5938030056760632889083083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3958686704507088592722055 5938030056760632889083083)
        ·
          refine ⟨8907045085140949333624625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5938030056760632889083083 8907045085140949333624625)
          ·
            refine ⟨6680283813855712000218469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8907045085140949333624625 6680283813855712000218469)
            ·
              refine ⟨1252553215097946000040963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6680283813855712000218469 1252553215097946000040963)
              ·
                refine ⟨1878829822646919000061445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252553215097946000040963 1878829822646919000061445)
                ·
                  refine ⟨352280591746297312511521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1878829822646919000061445 352280591746297312511521)
                  ·
                    rfl

theorem cell20_771822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_771822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771822 prefixEnd_771822 := by exact prefixLift 771822
  have htrace : WordTrace (prefixWord ++ tailWord_771822) baseStart_771822 baseEnd_771822 := by
    simpa [prefixWord, tailWord_771822, baseEnd_771822] using wordTrace_append hprefix tailTrace_771822
  have hstable : (prefixWord ++ tailWord_771822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771822).length < 2 ^ (prefixWord ++ tailWord_771822).sum := by decide
  have hdescent : baseEnd_771822 < baseStart_771822 := by decide
  rcases family_descends (prefixWord ++ tailWord_771822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771828 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_771828 : Nat := 118140960795 + 771828 * 2 ^ 59
def prefixEnd_771828 : Nat := 4983230072969 + 3 ^ 40 * 771828 * 2
def baseEnd_771828 : Nat := 352283330309787958311497

theorem tailTrace_771828 : CollatzResearch.WordTrace tailWord_771828 prefixEnd_771828 352283330309787958311497 := by
  unfold tailWord_771828
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075439923903224286482069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18767253231870965715309425 14075439923903224286482069)
  ·
    refine ⟨659786246432963638428847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14075439923903224286482069 659786246432963638428847)
    ·
      refine ⟨989679369649445457643271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659786246432963638428847 989679369649445457643271)
      ·
        refine ⟨1484519054474168186464907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989679369649445457643271 1484519054474168186464907)
        ·
          refine ⟨2226778581711252279697361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484519054474168186464907 2226778581711252279697361)
          ·
            refine ⟨1670083936283439209773021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226778581711252279697361 1670083936283439209773021)
            ·
              refine ⟨626281476106289703664883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1670083936283439209773021 626281476106289703664883)
              ·
                refine ⟨939422214159434555497325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626281476106289703664883 939422214159434555497325)
                ·
                  refine ⟨352283330309787958311497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939422214159434555497325 352283330309787958311497)
                  ·
                    rfl

theorem cell20_771828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_771828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771828 prefixEnd_771828 := by exact prefixLift 771828
  have htrace : WordTrace (prefixWord ++ tailWord_771828) baseStart_771828 baseEnd_771828 := by
    simpa [prefixWord, tailWord_771828, baseEnd_771828] using wordTrace_append hprefix tailTrace_771828
  have hstable : (prefixWord ++ tailWord_771828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771828).length < 2 ^ (prefixWord ++ tailWord_771828).sum := by decide
  have hdescent : baseEnd_771828 < baseStart_771828 := by decide
  rcases family_descends (prefixWord ++ tailWord_771828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771843 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_771843 : Nat := 118140960795 + 771843 * 2 ^ 59
def prefixEnd_771843 : Nat := 4983230072969 + 3 ^ 40 * 771843 * 2
def baseEnd_771843 : Nat := 352290176718514572811435

theorem tailTrace_771843 : CollatzResearch.WordTrace tailWord_771843 prefixEnd_771843 352290176718514572811435 := by
  unfold tailWord_771843
  simp only [CollatzResearch.WordTrace]
  refine ⟨28151426942752106134760183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18767617961834737423173455 28151426942752106134760183)
  ·
    refine ⟨42227140414128159202140275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28151426942752106134760183 42227140414128159202140275)
    ·
      refine ⟨63340710621192238803210413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42227140414128159202140275 63340710621192238803210413)
      ·
        refine ⟨23752766482947089551203905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63340710621192238803210413 23752766482947089551203905)
        ·
          refine ⟨17814574862210317163402929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23752766482947089551203905 17814574862210317163402929)
          ·
            refine ⟨13360931146657737872552197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17814574862210317163402929 13360931146657737872552197)
            ·
              refine ⟨2505174589998325851103537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13360931146657737872552197 2505174589998325851103537)
              ·
                refine ⟨1878880942498744388327653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2505174589998325851103537 1878880942498744388327653)
                ·
                  refine ⟨352290176718514572811435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1878880942498744388327653 352290176718514572811435)
                  ·
                    rfl

theorem cell20_771843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_771843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771843 prefixEnd_771843 := by exact prefixLift 771843
  have htrace : WordTrace (prefixWord ++ tailWord_771843) baseStart_771843 baseEnd_771843 := by
    simpa [prefixWord, tailWord_771843, baseEnd_771843] using wordTrace_append hprefix tailTrace_771843
  have hstable : (prefixWord ++ tailWord_771843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771843).length < 2 ^ (prefixWord ++ tailWord_771843).sum := by decide
  have hdescent : baseEnd_771843 < baseStart_771843 := by decide
  rcases family_descends (prefixWord ++ tailWord_771843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771874 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_771874 : Nat := 118140960795 + 771874 * 2 ^ 59
def prefixEnd_771874 : Nat := 4983230072969 + 3 ^ 40 * 771874 * 2
def baseEnd_771874 : Nat := 352304325963216242777975

theorem tailTrace_771874 : CollatzResearch.WordTrace tailWord_771874 prefixEnd_771874 352304325963216242777975 := by
  unfold tailWord_771874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7038139401409949607284669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18768371737093198952759117 7038139401409949607284669)
  ·
    refine ⟨2639302275528731102731751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7038139401409949607284669 2639302275528731102731751)
    ·
      refine ⟨3958953413293096654097627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2639302275528731102731751 3958953413293096654097627)
      ·
        refine ⟨5938430119939644981146441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3958953413293096654097627 5938430119939644981146441)
        ·
          refine ⟨4453822589954733735859831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5938430119939644981146441 4453822589954733735859831)
          ·
            refine ⟨6680733884932100603789747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453822589954733735859831 6680733884932100603789747)
            ·
              refine ⟨10021100827398150905684621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680733884932100603789747 10021100827398150905684621)
              ·
                refine ⟨3757912810274306589631733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10021100827398150905684621 3757912810274306589631733)
                ·
                  refine ⟨352304325963216242777975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3757912810274306589631733 352304325963216242777975)
                  ·
                    rfl

theorem cell20_771874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_771874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771874 prefixEnd_771874 := by exact prefixLift 771874
  have htrace : WordTrace (prefixWord ++ tailWord_771874) baseStart_771874 baseEnd_771874 := by
    simpa [prefixWord, tailWord_771874, baseEnd_771874] using wordTrace_append hprefix tailTrace_771874
  have hstable : (prefixWord ++ tailWord_771874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771874).length < 2 ^ (prefixWord ++ tailWord_771874).sum := by decide
  have hdescent : baseEnd_771874 < baseStart_771874 := by decide
  rcases family_descends (prefixWord ++ tailWord_771874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771891 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 3]
def baseStart_771891 : Nat := 118140960795 + 771891 * 2 ^ 59
def prefixEnd_771891 : Nat := 4983230072969 + 3 ^ 40 * 771891 * 2
def baseEnd_771891 : Nat := 352312085226439739211239

theorem tailTrace_771891 : CollatzResearch.WordTrace tailWord_771891 prefixEnd_771891 352312085226439739211239 := by
  unfold tailWord_771891
  simp only [CollatzResearch.WordTrace]
  refine ⟨28153177646578210332507527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18768785097718806888338351 28153177646578210332507527)
  ·
    refine ⟨42229766469867315498761291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28153177646578210332507527 42229766469867315498761291)
    ·
      refine ⟨63344649704800973248141937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42229766469867315498761291 63344649704800973248141937)
      ·
        refine ⟨47508487278600729936106453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63344649704800973248141937 47508487278600729936106453)
        ·
          refine ⟨1113480170592204607877495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47508487278600729936106453 1113480170592204607877495)
          ·
            refine ⟨1670220255888306911816243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113480170592204607877495 1670220255888306911816243)
            ·
              refine ⟨2505330383832460367724365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670220255888306911816243 2505330383832460367724365)
              ·
                refine ⟨939498893937172637896637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2505330383832460367724365 939498893937172637896637)
                ·
                  refine ⟨352312085226439739211239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 939498893937172637896637 352312085226439739211239)
                  ·
                    rfl

theorem cell20_771891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_771891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771891 prefixEnd_771891 := by exact prefixLift 771891
  have htrace : WordTrace (prefixWord ++ tailWord_771891) baseStart_771891 baseEnd_771891 := by
    simpa [prefixWord, tailWord_771891, baseEnd_771891] using wordTrace_append hprefix tailTrace_771891
  have hstable : (prefixWord ++ tailWord_771891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771891).length < 2 ^ (prefixWord ++ tailWord_771891).sum := by decide
  have hdescent : baseEnd_771891 < baseStart_771891 := by decide
  rcases family_descends (prefixWord ++ tailWord_771891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771895 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_771895 : Nat := 118140960795 + 771895 * 2 ^ 59
def prefixEnd_771895 : Nat := 4983230072969 + 3 ^ 40 * 771895 * 2
def baseEnd_771895 : Nat := 352313910935433503077889

theorem tailTrace_771895 : CollatzResearch.WordTrace tailWord_771895 prefixEnd_771895 352313910935433503077889 := by
  unfold tailWord_771895
  simp only [CollatzResearch.WordTrace]
  refine ⟨28153323538563719015653139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18768882359042479343768759 28153323538563719015653139)
  ·
    refine ⟨42229985307845578523479709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28153323538563719015653139 42229985307845578523479709)
    ·
      refine ⟨15836244490442091946304891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42229985307845578523479709 15836244490442091946304891)
      ·
        refine ⟨23754366735663137919457337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15836244490442091946304891 23754366735663137919457337)
        ·
          refine ⟨17815775051747353439593003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23754366735663137919457337 17815775051747353439593003)
          ·
            refine ⟨26723662577621030159389505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17815775051747353439593003 26723662577621030159389505)
            ·
              refine ⟨20042746933215772619542129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26723662577621030159389505 20042746933215772619542129)
              ·
                refine ⟨15032060199911829464656597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20042746933215772619542129 15032060199911829464656597)
                ·
                  refine ⟨352313910935433503077889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15032060199911829464656597 352313910935433503077889)
                  ·
                    rfl

theorem cell20_771895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_771895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771895 prefixEnd_771895 := by exact prefixLift 771895
  have htrace : WordTrace (prefixWord ++ tailWord_771895) baseStart_771895 baseEnd_771895 := by
    simpa [prefixWord, tailWord_771895, baseEnd_771895] using wordTrace_append hprefix tailTrace_771895
  have hstable : (prefixWord ++ tailWord_771895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771895).length < 2 ^ (prefixWord ++ tailWord_771895).sum := by decide
  have hdescent : baseEnd_771895 < baseStart_771895 := by decide
  rcases family_descends (prefixWord ++ tailWord_771895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771932 : List Nat := [2, 2, 4, 2, 2, 1, 1, 4, 2]
def baseStart_771932 : Nat := 118140960795 + 771932 * 2 ^ 59
def prefixEnd_771932 : Nat := 4983230072969 + 3 ^ 40 * 771932 * 2
def baseEnd_771932 : Nat := 352330798743625818844405

theorem tailTrace_771932 : CollatzResearch.WordTrace tailWord_771932 prefixEnd_771932 352330798743625818844405 := by
  unfold tailWord_771932
  simp only [CollatzResearch.WordTrace]
  refine ⟨14077336519714837167375025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18769782026286449556500033 14077336519714837167375025)
  ·
    refine ⟨10558002389786127875531269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14077336519714837167375025 10558002389786127875531269)
    ·
      refine ⟨1979625448084898976662113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10558002389786127875531269 1979625448084898976662113)
      ·
        refine ⟨1484719086063674232496585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1979625448084898976662113 1484719086063674232496585)
        ·
          refine ⟨1113539314547755674372439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1484719086063674232496585 1113539314547755674372439)
          ·
            refine ⟨1670308971821633511558659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113539314547755674372439 1670308971821633511558659)
            ·
              refine ⟨2505463457732450267337989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670308971821633511558659 2505463457732450267337989)
              ·
                refine ⟨469774398324834425125873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2505463457732450267337989 469774398324834425125873)
                ·
                  refine ⟨352330798743625818844405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469774398324834425125873 352330798743625818844405)
                  ·
                    rfl

theorem cell20_771932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_771932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_771932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_771932 prefixEnd_771932 := by exact prefixLift 771932
  have htrace : WordTrace (prefixWord ++ tailWord_771932) baseStart_771932 baseEnd_771932 := by
    simpa [prefixWord, tailWord_771932, baseEnd_771932] using wordTrace_append hprefix tailTrace_771932
  have hstable : (prefixWord ++ tailWord_771932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771932).length < 2 ^ (prefixWord ++ tailWord_771932).sum := by decide
  have hdescent : baseEnd_771932 < baseStart_771932 := by decide
  rcases family_descends (prefixWord ++ tailWord_771932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772029 : List Nat := [1, 4, 1, 2, 3, 1, 3, 3, 2]
def baseStart_772029 : Nat := 118140960795 + 772029 * 2 ^ 59
def prefixEnd_772029 : Nat := 4983230072969 + 3 ^ 40 * 772029 * 2
def baseEnd_772029 : Nat := 352375072186724592610675

theorem tailTrace_772029 : CollatzResearch.WordTrace tailWord_772029 prefixEnd_772029 352375072186724592610675 := by
  unfold tailWord_772029
  simp only [CollatzResearch.WordTrace]
  refine ⟨28158210920078259901031141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18772140613385506600687427 28158210920078259901031141)
  ·
    refine ⟨5279664547514673731443339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28158210920078259901031141 5279664547514673731443339)
    ·
      refine ⟨7919496821272010597165009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5279664547514673731443339 7919496821272010597165009)
      ·
        refine ⟨5939622615954007947873757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7919496821272010597165009 5939622615954007947873757)
        ·
          refine ⟨2227358480982752980452659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5939622615954007947873757 2227358480982752980452659)
          ·
            refine ⟨3341037721474129470678989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227358480982752980452659 3341037721474129470678989)
            ·
              refine ⟨1252889145552798551504621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3341037721474129470678989 1252889145552798551504621)
              ·
                refine ⟨469833429582299456814233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1252889145552798551504621 469833429582299456814233)
                ·
                  refine ⟨352375072186724592610675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469833429582299456814233 352375072186724592610675)
                  ·
                    rfl

theorem cell20_772029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_772029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772029 prefixEnd_772029 := by exact prefixLift 772029
  have htrace : WordTrace (prefixWord ++ tailWord_772029) baseStart_772029 baseEnd_772029 := by
    simpa [prefixWord, tailWord_772029, baseEnd_772029] using wordTrace_append hprefix tailTrace_772029
  have hstable : (prefixWord ++ tailWord_772029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772029).length < 2 ^ (prefixWord ++ tailWord_772029).sum := by decide
  have hdescent : baseEnd_772029 < baseStart_772029 := by decide
  rcases family_descends (prefixWord ++ tailWord_772029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772040 : List Nat := [2, 1, 3, 1, 4, 1, 8]
def baseStart_772040 : Nat := 118140960795 + 772040 * 2 ^ 59
def prefixEnd_772040 : Nat := 4983230072969 + 3 ^ 40 * 772040 * 2
def baseEnd_772040 : Nat := 39153343654050827027107

theorem tailTrace_772040 : CollatzResearch.WordTrace tailWord_772040 prefixEnd_772040 39153343654050827027107 := by
  unfold tailWord_772040
  simp only [CollatzResearch.WordTrace]
  refine ⟨14079306061519204389840787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18772408082025605853121049 14079306061519204389840787)
  ·
    refine ⟨21118959092278806584761181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14079306061519204389840787 21118959092278806584761181)
    ·
      refine ⟨7919609659604552469285443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21118959092278806584761181 7919609659604552469285443)
      ·
        refine ⟨11879414489406828703928165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7919609659604552469285443 11879414489406828703928165)
        ·
          refine ⟨2227390216763780381986531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11879414489406828703928165 2227390216763780381986531)
          ·
            refine ⟨3341085325145670572979797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227390216763780381986531 3341085325145670572979797)
            ·
              refine ⟨39153343654050827027107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3341085325145670572979797 39153343654050827027107)
              ·
                rfl

theorem cell20_772040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 8].length) (baseStart_772040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772040 prefixEnd_772040 := by exact prefixLift 772040
  have htrace : WordTrace (prefixWord ++ tailWord_772040) baseStart_772040 baseEnd_772040 := by
    simpa [prefixWord, tailWord_772040, baseEnd_772040] using wordTrace_append hprefix tailTrace_772040
  have hstable : (prefixWord ++ tailWord_772040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772040).length < 2 ^ (prefixWord ++ tailWord_772040).sum := by decide
  have hdescent : baseEnd_772040 < baseStart_772040 := by decide
  rcases family_descends (prefixWord ++ tailWord_772040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772047 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_772047 : Nat := 118140960795 + 772047 * 2 ^ 59
def prefixEnd_772047 : Nat := 4983230072969 + 3 ^ 40 * 772047 * 2
def baseEnd_772047 : Nat := 352383287877196530010601

theorem tailTrace_772047 : CollatzResearch.WordTrace tailWord_772047 prefixEnd_772047 352383287877196530010601 := by
  unfold tailWord_772047
  simp only [CollatzResearch.WordTrace]
  refine ⟨28158867434013048975186395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18772578289342032650124263 28158867434013048975186395)
  ·
    refine ⟨42238301151019573462779593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28158867434013048975186395 42238301151019573462779593)
    ·
      refine ⟨31678725863264680097084695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42238301151019573462779593 31678725863264680097084695)
      ·
        refine ⟨47518088794897020145627043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31678725863264680097084695 47518088794897020145627043)
        ·
          refine ⟨71277133192345530218440565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47518088794897020145627043 71277133192345530218440565)
          ·
            refine ⟨6682231236782393457978803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71277133192345530218440565 6682231236782393457978803)
            ·
              refine ⟨10023346855173590186968205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682231236782393457978803 10023346855173590186968205)
              ·
                refine ⟨3758755070690096320113077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10023346855173590186968205 3758755070690096320113077)
                ·
                  refine ⟨352383287877196530010601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3758755070690096320113077 352383287877196530010601)
                  ·
                    rfl

theorem cell20_772047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_772047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772047 prefixEnd_772047 := by exact prefixLift 772047
  have htrace : WordTrace (prefixWord ++ tailWord_772047) baseStart_772047 baseEnd_772047 := by
    simpa [prefixWord, tailWord_772047, baseEnd_772047] using wordTrace_append hprefix tailTrace_772047
  have hstable : (prefixWord ++ tailWord_772047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772047).length < 2 ^ (prefixWord ++ tailWord_772047).sum := by decide
  have hdescent : baseEnd_772047 < baseStart_772047 := by decide
  rcases family_descends (prefixWord ++ tailWord_772047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772057 : List Nat := [1, 2, 1, 2, 6, 1, 2, 5]
def baseStart_772057 : Nat := 118140960795 + 772057 * 2 ^ 59
def prefixEnd_772057 : Nat := 4983230072969 + 3 ^ 40 * 772057 * 2
def baseEnd_772057 : Nat := 117462617383226979892409

theorem tailTrace_772057 : CollatzResearch.WordTrace tailWord_772057 prefixEnd_772057 117462617383226979892409 := by
  unfold tailWord_772057
  simp only [CollatzResearch.WordTrace]
  refine ⟨28159232163976820683050425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18772821442651213788700283 28159232163976820683050425)
  ·
    refine ⟨21119424122982615512287819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28159232163976820683050425 21119424122982615512287819)
    ·
      refine ⟨31679136184473923268431729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21119424122982615512287819 31679136184473923268431729)
      ·
        refine ⟨23759352138355442451323797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31679136184473923268431729 23759352138355442451323797)
        ·
          refine ⟨1113719631485411364905803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23759352138355442451323797 1113719631485411364905803)
          ·
            refine ⟨1670579447228117047358705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113719631485411364905803 1670579447228117047358705)
            ·
              refine ⟨1252934585421087785519029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1670579447228117047358705 1252934585421087785519029)
              ·
                refine ⟨117462617383226979892409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1252934585421087785519029 117462617383226979892409)
                ·
                  rfl

theorem cell20_772057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_772057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772057 prefixEnd_772057 := by exact prefixLift 772057
  have htrace : WordTrace (prefixWord ++ tailWord_772057) baseStart_772057 baseEnd_772057 := by
    simpa [prefixWord, tailWord_772057, baseEnd_772057] using wordTrace_append hprefix tailTrace_772057
  have hstable : (prefixWord ++ tailWord_772057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772057).length < 2 ^ (prefixWord ++ tailWord_772057).sum := by decide
  have hdescent : baseEnd_772057 < baseStart_772057 := by decide
  rcases family_descends (prefixWord ++ tailWord_772057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772133 : List Nat := [1, 3, 1, 2, 2, 4, 3, 4]
def baseStart_772133 : Nat := 118140960795 + 772133 * 2 ^ 59
def prefixEnd_772133 : Nat := 4983230072969 + 3 ^ 40 * 772133 * 2
def baseEnd_772133 : Nat := 117474180206854151047861

theorem tailTrace_772133 : CollatzResearch.WordTrace tailWord_772133 prefixEnd_772133 117474180206854151047861 := by
  unfold tailWord_772133
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162004111701485662817053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18774669407800990441878035 28162004111701485662817053)
  ·
    refine ⟨10560751541888057123556395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28162004111701485662817053 10560751541888057123556395)
    ·
      refine ⟨15841127312832085685334593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10560751541888057123556395 15841127312832085685334593)
      ·
        refine ⟨11880845484624064264000945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15841127312832085685334593 11880845484624064264000945)
        ·
          refine ⟨8910634113468048198000709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11880845484624064264000945 8910634113468048198000709)
          ·
            refine ⟨1670743896275259037125133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8910634113468048198000709 1670743896275259037125133)
            ·
              refine ⟨626528961103222138921925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1670743896275259037125133 626528961103222138921925)
              ·
                refine ⟨117474180206854151047861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 626528961103222138921925 117474180206854151047861)
                ·
                  rfl

theorem cell20_772133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 4].length) (baseStart_772133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772133 prefixEnd_772133 := by exact prefixLift 772133
  have htrace : WordTrace (prefixWord ++ tailWord_772133) baseStart_772133 baseEnd_772133 := by
    simpa [prefixWord, tailWord_772133, baseEnd_772133] using wordTrace_append hprefix tailTrace_772133
  have hstable : (prefixWord ++ tailWord_772133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772133).length < 2 ^ (prefixWord ++ tailWord_772133).sum := by decide
  have hdescent : baseEnd_772133 < baseStart_772133 := by decide
  rcases family_descends (prefixWord ++ tailWord_772133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772188 : List Nat := [2, 2, 4, 1, 1, 4, 2, 4]
def baseStart_772188 : Nat := 118140960795 + 772188 * 2 ^ 59
def prefixEnd_772188 : Nat := 4983230072969 + 3 ^ 40 * 772188 * 2
def baseEnd_772188 : Nat := 117482548039742235436675

theorem tailTrace_772188 : CollatzResearch.WordTrace tailWord_772188 prefixEnd_772188 117482548039742235436675 := by
  unfold tailWord_772188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14082005063251115028034609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18776006751001486704046145 14082005063251115028034609)
  ·
    refine ⟨10561503797438336271025957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14082005063251115028034609 10561503797438336271025957)
    ·
      refine ⟨1980281962019688050817367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10561503797438336271025957 1980281962019688050817367)
      ·
        refine ⟨2970422943029532076226051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980281962019688050817367 2970422943029532076226051)
        ·
          refine ⟨4455634414544298114339077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970422943029532076226051 4455634414544298114339077)
          ·
            refine ⟨835431452727055896438577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4455634414544298114339077 835431452727055896438577)
            ·
              refine ⟨626573589545291922328933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835431452727055896438577 626573589545291922328933)
              ·
                refine ⟨117482548039742235436675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 626573589545291922328933 117482548039742235436675)
                ·
                  rfl

theorem cell20_772188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_772188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772188 prefixEnd_772188 := by exact prefixLift 772188
  have htrace : WordTrace (prefixWord ++ tailWord_772188) baseStart_772188 baseEnd_772188 := by
    simpa [prefixWord, tailWord_772188, baseEnd_772188] using wordTrace_append hprefix tailTrace_772188
  have hstable : (prefixWord ++ tailWord_772188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772188).length < 2 ^ (prefixWord ++ tailWord_772188).sum := by decide
  have hdescent : baseEnd_772188 < baseStart_772188 := by decide
  rcases family_descends (prefixWord ++ tailWord_772188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772192 : List Nat := [2, 1, 1, 3, 2, 4, 1, 6]
def baseStart_772192 : Nat := 118140960795 + 772192 * 2 ^ 59
def prefixEnd_772192 : Nat := 4983230072969 + 3 ^ 40 * 772192 * 2
def baseEnd_772192 : Nat := 117483156609406823392225

theorem tailTrace_772192 : CollatzResearch.WordTrace tailWord_772192 prefixEnd_772192 117483156609406823392225 := by
  unfold tailWord_772192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14082078009243869369607415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18776104012325159159476553 14082078009243869369607415)
  ·
    refine ⟨21123117013865804054411123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14082078009243869369607415 21123117013865804054411123)
    ·
      refine ⟨31684675520798706081616685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21123117013865804054411123 31684675520798706081616685)
      ·
        refine ⟨11881753320299514780606257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31684675520798706081616685 11881753320299514780606257)
        ·
          refine ⟨8911314990224636085454693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11881753320299514780606257 8911314990224636085454693)
          ·
            refine ⟨1670871560667119266022755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8911314990224636085454693 1670871560667119266022755)
            ·
              refine ⟨2506307341000678899034133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670871560667119266022755 2506307341000678899034133)
              ·
                refine ⟨117483156609406823392225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2506307341000678899034133 117483156609406823392225)
                ·
                  rfl

theorem cell20_772192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_772192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772192 prefixEnd_772192 := by exact prefixLift 772192
  have htrace : WordTrace (prefixWord ++ tailWord_772192) baseStart_772192 baseEnd_772192 := by
    simpa [prefixWord, tailWord_772192, baseEnd_772192] using wordTrace_append hprefix tailTrace_772192
  have hstable : (prefixWord ++ tailWord_772192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772192).length < 2 ^ (prefixWord ++ tailWord_772192).sum := by decide
  have hdescent : baseEnd_772192 < baseStart_772192 := by decide
  rcases family_descends (prefixWord ++ tailWord_772192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772199 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_772199 : Nat := 118140960795 + 772199 * 2 ^ 59
def prefixEnd_772199 : Nat := 4983230072969 + 3 ^ 40 * 772199 * 2
def baseEnd_772199 : Nat := 352452664818959556943313

theorem tailTrace_772199 : CollatzResearch.WordTrace tailWord_772199 prefixEnd_772199 352452664818959556943313 := by
  unfold tailWord_772199
  simp only [CollatzResearch.WordTrace]
  refine ⟨28164411329462378934719651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18776274219641585956479767 28164411329462378934719651)
  ·
    refine ⟨42246616994193568402079477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28164411329462378934719651 42246616994193568402079477)
    ·
      refine ⟨3960620343205647037694951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42246616994193568402079477 3960620343205647037694951)
      ·
        refine ⟨5940930514808470556542427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960620343205647037694951 5940930514808470556542427)
        ·
          refine ⟨8911395772212705834813641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940930514808470556542427 8911395772212705834813641)
          ·
            refine ⟨6683546829159529376110231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8911395772212705834813641 6683546829159529376110231)
            ·
              refine ⟨10025320243739294064165347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683546829159529376110231 10025320243739294064165347)
              ·
                refine ⟨15037980365608941096248021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10025320243739294064165347 15037980365608941096248021)
                ·
                  refine ⟨352452664818959556943313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15037980365608941096248021 352452664818959556943313)
                  ·
                    rfl

theorem cell20_772199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_772199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772199 prefixEnd_772199 := by exact prefixLift 772199
  have htrace : WordTrace (prefixWord ++ tailWord_772199) baseStart_772199 baseEnd_772199 := by
    simpa [prefixWord, tailWord_772199, baseEnd_772199] using wordTrace_append hprefix tailTrace_772199
  have hstable : (prefixWord ++ tailWord_772199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772199).length < 2 ^ (prefixWord ++ tailWord_772199).sum := by decide
  have hdescent : baseEnd_772199 < baseStart_772199 := by decide
  rcases family_descends (prefixWord ++ tailWord_772199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772251 : List Nat := [1, 1, 1, 1, 1, 1, 2, 12]
def baseStart_772251 : Nat := 118140960795 + 772251 * 2 ^ 59
def prefixEnd_772251 : Nat := 4983230072969 + 3 ^ 40 * 772251 * 2
def baseEnd_772251 : Nat := 117492133011959495736589

theorem tailTrace_772251 : CollatzResearch.WordTrace tailWord_772251 prefixEnd_772251 117492133011959495736589 := by
  unfold tailWord_772251
  simp only [CollatzResearch.WordTrace]
  refine ⟨28166307925273991815612607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18777538616849327877075071 28166307925273991815612607)
  ·
    refine ⟨42249461887910987723418911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28166307925273991815612607 42249461887910987723418911)
    ·
      refine ⟨63374192831866481585128367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42249461887910987723418911 63374192831866481585128367)
      ·
        refine ⟨95061289247799722377692551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63374192831866481585128367 95061289247799722377692551)
        ·
          refine ⟨142591933871699583566538827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95061289247799722377692551 142591933871699583566538827)
          ·
            refine ⟨213887900807549375349808241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142591933871699583566538827 213887900807549375349808241)
            ·
              refine ⟨160415925605662031512356181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213887900807549375349808241 160415925605662031512356181)
              ·
                refine ⟨117492133011959495736589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 160415925605662031512356181 117492133011959495736589)
                ·
                  rfl

theorem cell20_772251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_772251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772251 prefixEnd_772251 := by exact prefixLift 772251
  have htrace : WordTrace (prefixWord ++ tailWord_772251) baseStart_772251 baseEnd_772251 := by
    simpa [prefixWord, tailWord_772251, baseEnd_772251] using wordTrace_append hprefix tailTrace_772251
  have hstable : (prefixWord ++ tailWord_772251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772251).length < 2 ^ (prefixWord ++ tailWord_772251).sum := by decide
  have hdescent : baseEnd_772251 < baseStart_772251 := by decide
  rcases family_descends (prefixWord ++ tailWord_772251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772270 : List Nat := [4, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_772270 : Nat := 118140960795 + 772270 * 2 ^ 59
def prefixEnd_772270 : Nat := 4983230072969 + 3 ^ 40 * 772270 * 2
def baseEnd_772270 : Nat := 352485071153598865576357

theorem tailTrace_772270 : CollatzResearch.WordTrace tailWord_772270 prefixEnd_772270 352485071153598865576357 := by
  unfold tailWord_772270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520875114025644757569283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18778000608136772040369509 3520875114025644757569283)
  ·
    refine ⟨5281312671038467136353925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3520875114025644757569283 5281312671038467136353925)
    ·
      refine ⟨990246125819712588066361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5281312671038467136353925 990246125819712588066361)
      ·
        refine ⟨742684594364784441049771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 990246125819712588066361 742684594364784441049771)
        ·
          refine ⟨1114026891547176661574657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742684594364784441049771 1114026891547176661574657)
          ·
            refine ⟨835520168660382496180993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114026891547176661574657 835520168660382496180993)
            ·
              refine ⟨626640126495286872135745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835520168660382496180993 626640126495286872135745)
              ·
                refine ⟨469980094871465154101809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626640126495286872135745 469980094871465154101809)
                ·
                  refine ⟨352485071153598865576357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469980094871465154101809 352485071153598865576357)
                  ·
                    rfl

theorem cell20_772270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_772270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772270 prefixEnd_772270 := by exact prefixLift 772270
  have htrace : WordTrace (prefixWord ++ tailWord_772270) baseStart_772270 baseEnd_772270 := by
    simpa [prefixWord, tailWord_772270, baseEnd_772270] using wordTrace_append hprefix tailTrace_772270
  have hstable : (prefixWord ++ tailWord_772270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772270).length < 2 ^ (prefixWord ++ tailWord_772270).sum := by decide
  have hdescent : baseEnd_772270 < baseStart_772270 := by decide
  rcases family_descends (prefixWord ++ tailWord_772270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772320 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_772320 : Nat := 118140960795 + 772320 * 2 ^ 59
def prefixEnd_772320 : Nat := 4983230072969 + 3 ^ 40 * 772320 * 2
def baseEnd_772320 : Nat := 352507892516020913909485

theorem tailTrace_772320 : CollatzResearch.WordTrace tailWord_772320 prefixEnd_772320 352507892516020913909485 := by
  unfold tailWord_772320
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084412281012008299937207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18779216374682677733249609 14084412281012008299937207)
  ·
    refine ⟨21126618421518012449905811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14084412281012008299937207 21126618421518012449905811)
    ·
      refine ⟨31689927632277018674858717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21126618421518012449905811 31689927632277018674858717)
      ·
        refine ⟨11883722862103882003072019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31689927632277018674858717 11883722862103882003072019)
        ·
          refine ⟨17825584293155823004608029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11883722862103882003072019 17825584293155823004608029)
          ·
            refine ⟨6684594109933433626728011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17825584293155823004608029 6684594109933433626728011)
            ·
              refine ⟨10026891164900150440092017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684594109933433626728011 10026891164900150440092017)
              ·
                refine ⟨7520168373675112830069013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10026891164900150440092017 7520168373675112830069013)
                ·
                  refine ⟨352507892516020913909485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7520168373675112830069013 352507892516020913909485)
                  ·
                    rfl

theorem cell20_772320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_772320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772320 prefixEnd_772320 := by exact prefixLift 772320
  have htrace : WordTrace (prefixWord ++ tailWord_772320) baseStart_772320 baseEnd_772320 := by
    simpa [prefixWord, tailWord_772320, baseEnd_772320] using wordTrace_append hprefix tailTrace_772320
  have hstable : (prefixWord ++ tailWord_772320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772320).length < 2 ^ (prefixWord ++ tailWord_772320).sum := by decide
  have hdescent : baseEnd_772320 < baseStart_772320 := by decide
  rcases family_descends (prefixWord ++ tailWord_772320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772322 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_772322 : Nat := 118140960795 + 772322 * 2 ^ 59
def prefixEnd_772322 : Nat := 4983230072969 + 3 ^ 40 * 772322 * 2
def baseEnd_772322 : Nat := 352508805370517795842811

theorem tailTrace_772322 : CollatzResearch.WordTrace tailWord_772322 prefixEnd_772322 352508805370517795842811 := by
  unfold tailWord_772322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7042224377004192735361805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18779265005344513960964813 7042224377004192735361805)
  ·
    refine ⟨2640834141376572275760677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7042224377004192735361805 2640834141376572275760677)
    ·
      refine ⟨495156401508107301705127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2640834141376572275760677 495156401508107301705127)
      ·
        refine ⟨742734602262160952557691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495156401508107301705127 742734602262160952557691)
        ·
          refine ⟨1114101903393241428836537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742734602262160952557691 1114101903393241428836537)
          ·
            refine ⟨835576427544931071627403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114101903393241428836537 835576427544931071627403)
            ·
              refine ⟨1253364641317396607441105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835576427544931071627403 1253364641317396607441105)
              ·
                refine ⟨940023480988047455580829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253364641317396607441105 940023480988047455580829)
                ·
                  refine ⟨352508805370517795842811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940023480988047455580829 352508805370517795842811)
                  ·
                    rfl

theorem cell20_772322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_772322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772322 prefixEnd_772322 := by exact prefixLift 772322
  have htrace : WordTrace (prefixWord ++ tailWord_772322) baseStart_772322 baseEnd_772322 := by
    simpa [prefixWord, tailWord_772322, baseEnd_772322] using wordTrace_append hprefix tailTrace_772322
  have hstable : (prefixWord ++ tailWord_772322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772322).length < 2 ^ (prefixWord ++ tailWord_772322).sum := by decide
  have hdescent : baseEnd_772322 < baseStart_772322 := by decide
  rcases family_descends (prefixWord ++ tailWord_772322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772323 : List Nat := [1, 1, 1, 8, 1, 1, 7]
def baseStart_772323 : Nat := 118140960795 + 772323 * 2 ^ 59
def prefixEnd_772323 : Nat := 4983230072969 + 3 ^ 40 * 772323 * 2
def baseEnd_772323 : Nat := 39167695755307359645497

theorem tailTrace_772323 : CollatzResearch.WordTrace tailWord_772323 prefixEnd_772323 39167695755307359645497 := by
  unfold tailWord_772323
  simp only [CollatzResearch.WordTrace]
  refine ⟨28168933981013148112233623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18779289320675432074822415 28168933981013148112233623)
  ·
    refine ⟨42253400971519722168350435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28168933981013148112233623 42253400971519722168350435)
    ·
      refine ⟨63380101457279583252525653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42253400971519722168350435 63380101457279583252525653)
      ·
        refine ⟨742735563952495116240535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 63380101457279583252525653 742735563952495116240535)
        ·
          refine ⟨1114103345928742674360803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742735563952495116240535 1114103345928742674360803)
          ·
            refine ⟨1671155018893114011541205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114103345928742674360803 1671155018893114011541205)
            ·
              refine ⟨39167695755307359645497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1671155018893114011541205 39167695755307359645497)
              ·
                rfl

theorem cell20_772323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 7].length) (baseStart_772323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772323 prefixEnd_772323 := by exact prefixLift 772323
  have htrace : WordTrace (prefixWord ++ tailWord_772323) baseStart_772323 baseEnd_772323 := by
    simpa [prefixWord, tailWord_772323, baseEnd_772323] using wordTrace_append hprefix tailTrace_772323
  have hstable : (prefixWord ++ tailWord_772323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772323).length < 2 ^ (prefixWord ++ tailWord_772323).sum := by decide
  have hdescent : baseEnd_772323 < baseStart_772323 := by decide
  rcases family_descends (prefixWord ++ tailWord_772323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772354 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_772354 : Nat := 118140960795 + 772354 * 2 ^ 59
def prefixEnd_772354 : Nat := 4983230072969 + 3 ^ 40 * 772354 * 2
def baseEnd_772354 : Nat := 352523411042467906776013

theorem tailTrace_772354 : CollatzResearch.WordTrace tailWord_772354 prefixEnd_772354 352523411042467906776013 := by
  unfold tailWord_772354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7042516160975210101653029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18780043095933893604408077 7042516160975210101653029)
  ·
    refine ⟨1320471780182851894059943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7042516160975210101653029 1320471780182851894059943)
    ·
      refine ⟨1980707670274277841089915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320471780182851894059943 1980707670274277841089915)
      ·
        refine ⟨2971061505411416761634873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980707670274277841089915 2971061505411416761634873)
        ·
          refine ⟨2228296129058562571226155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2971061505411416761634873 2228296129058562571226155)
          ·
            refine ⟨3342444193587843856839233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228296129058562571226155 3342444193587843856839233)
            ·
              refine ⟨2506833145190882892629425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3342444193587843856839233 2506833145190882892629425)
              ·
                refine ⟨1880124858893162169472069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2506833145190882892629425 1880124858893162169472069)
                ·
                  refine ⟨352523411042467906776013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1880124858893162169472069 352523411042467906776013)
                  ·
                    rfl

theorem cell20_772354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_772354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772354 prefixEnd_772354 := by exact prefixLift 772354
  have htrace : WordTrace (prefixWord ++ tailWord_772354) baseStart_772354 baseEnd_772354 := by
    simpa [prefixWord, tailWord_772354, baseEnd_772354] using wordTrace_append hprefix tailTrace_772354
  have hstable : (prefixWord ++ tailWord_772354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772354).length < 2 ^ (prefixWord ++ tailWord_772354).sum := by decide
  have hdescent : baseEnd_772354 < baseStart_772354 := by decide
  rcases family_descends (prefixWord ++ tailWord_772354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772361 : List Nat := [1, 2, 1, 1, 3, 6, 2, 4]
def baseStart_772361 : Nat := 118140960795 + 772361 * 2 ^ 59
def prefixEnd_772361 : Nat := 4983230072969 + 3 ^ 40 * 772361 * 2
def baseEnd_772361 : Nat := 117508868677735664514217

theorem tailTrace_772361 : CollatzResearch.WordTrace tailWord_772361 prefixEnd_772361 117508868677735664514217 := by
  unfold tailWord_772361
  simp only [CollatzResearch.WordTrace]
  refine ⟨28170319954875480602116937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18780213303250320401411291 28170319954875480602116937)
  ·
    refine ⟨21127739966156610451587703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28170319954875480602116937 21127739966156610451587703)
    ·
      refine ⟨31691609949234915677381555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21127739966156610451587703 31691609949234915677381555)
      ·
        refine ⟨47537414923852373516072333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31691609949234915677381555 47537414923852373516072333)
        ·
          refine ⟨17826530596444640068527125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47537414923852373516072333 17826530596444640068527125)
          ·
            refine ⟨835618621708342503212209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17826530596444640068527125 835618621708342503212209)
            ·
              refine ⟨626713966281256877409157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835618621708342503212209 626713966281256877409157)
              ·
                refine ⟨117508868677735664514217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 626713966281256877409157 117508868677735664514217)
                ·
                  rfl

theorem cell20_772361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 4].length) (baseStart_772361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772361 prefixEnd_772361 := by exact prefixLift 772361
  have htrace : WordTrace (prefixWord ++ tailWord_772361) baseStart_772361 baseEnd_772361 := by
    simpa [prefixWord, tailWord_772361, baseEnd_772361] using wordTrace_append hprefix tailTrace_772361
  have hstable : (prefixWord ++ tailWord_772361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772361).length < 2 ^ (prefixWord ++ tailWord_772361).sum := by decide
  have hdescent : baseEnd_772361 < baseStart_772361 := by decide
  rcases family_descends (prefixWord ++ tailWord_772361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772398 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_772398 : Nat := 118140960795 + 772398 * 2 ^ 59
def prefixEnd_772398 : Nat := 4983230072969 + 3 ^ 40 * 772398 * 2
def baseEnd_772398 : Nat := 352543493841399309309167

theorem tailTrace_772398 : CollatzResearch.WordTrace tailWord_772398 prefixEnd_772398 352543493841399309309167 := by
  unfold tailWord_772398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521458681967679490151731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18781112970494290614142565 3521458681967679490151731)
  ·
    refine ⟨5282188022951519235227597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3521458681967679490151731 5282188022951519235227597)
    ·
      refine ⟨1980820508606819713210349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5282188022951519235227597 1980820508606819713210349)
      ·
        refine ⟨742807690727557392453881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1980820508606819713210349 742807690727557392453881)
        ·
          refine ⟨557105768045668044340411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742807690727557392453881 557105768045668044340411)
          ·
            refine ⟨835658652068502066510617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557105768045668044340411 835658652068502066510617)
            ·
              refine ⟨626743989051376549882963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835658652068502066510617 626743989051376549882963)
              ·
                refine ⟨940115983577064824824445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626743989051376549882963 940115983577064824824445)
                ·
                  refine ⟨352543493841399309309167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940115983577064824824445 352543493841399309309167)
                  ·
                    rfl

theorem cell20_772398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_772398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772398 prefixEnd_772398 := by exact prefixLift 772398
  have htrace : WordTrace (prefixWord ++ tailWord_772398) baseStart_772398 baseEnd_772398 := by
    simpa [prefixWord, tailWord_772398, baseEnd_772398] using wordTrace_append hprefix tailTrace_772398
  have hstable : (prefixWord ++ tailWord_772398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772398).length < 2 ^ (prefixWord ++ tailWord_772398).sum := by decide
  have hdescent : baseEnd_772398 < baseStart_772398 := by decide
  rcases family_descends (prefixWord ++ tailWord_772398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772402 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_772402 : Nat := 118140960795 + 772402 * 2 ^ 59
def prefixEnd_772402 : Nat := 4983230072969 + 3 ^ 40 * 772402 * 2
def baseEnd_772402 : Nat := 352545319550393073175817

theorem tailTrace_772402 : CollatzResearch.WordTrace tailWord_772402 prefixEnd_772402 352545319550393073175817 := by
  unfold tailWord_772402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7042953836931736151089865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18781210231817963069572973 7042953836931736151089865)
  ·
    refine ⟨5282215377698802113317399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7042953836931736151089865 5282215377698802113317399)
    ·
      refine ⟨7923323066548203169976099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5282215377698802113317399 7923323066548203169976099)
      ·
        refine ⟨11884984599822304754964149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7923323066548203169976099 11884984599822304754964149)
        ·
          refine ⟨1114217306233341070777889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11884984599822304754964149 1114217306233341070777889)
          ·
            refine ⟨835662979675005803083417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114217306233341070777889 835662979675005803083417)
            ·
              refine ⟨626747234756254352312563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835662979675005803083417 626747234756254352312563)
              ·
                refine ⟨940120852134381528468845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626747234756254352312563 940120852134381528468845)
                ·
                  refine ⟨352545319550393073175817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940120852134381528468845 352545319550393073175817)
                  ·
                    rfl

theorem cell20_772402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_772402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772402 prefixEnd_772402 := by exact prefixLift 772402
  have htrace : WordTrace (prefixWord ++ tailWord_772402) baseStart_772402 baseEnd_772402 := by
    simpa [prefixWord, tailWord_772402, baseEnd_772402] using wordTrace_append hprefix tailTrace_772402
  have hstable : (prefixWord ++ tailWord_772402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772402).length < 2 ^ (prefixWord ++ tailWord_772402).sum := by decide
  have hdescent : baseEnd_772402 < baseStart_772402 := by decide
  rcases family_descends (prefixWord ++ tailWord_772402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772506 : List Nat := [3, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_772506 : Nat := 118140960795 + 772506 * 2 ^ 59
def prefixEnd_772506 : Nat := 4983230072969 + 3 ^ 40 * 772506 * 2
def baseEnd_772506 : Nat := 352592787984230933708725

theorem tailTrace_772506 : CollatzResearch.WordTrace tailWord_772506 prefixEnd_772506 352592787984230933708725 := by
  unfold tailWord_772506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7043902134837542591536343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18783739026233446910763581 7043902134837542591536343)
  ·
    refine ⟨10565853202256313887304515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7043902134837542591536343 10565853202256313887304515)
    ·
      refine ⟨15848779803384470830956773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10565853202256313887304515 15848779803384470830956773)
      ·
        refine ⟨2971646213134588280804395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15848779803384470830956773 2971646213134588280804395)
        ·
          refine ⟨4457469319701882421206593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971646213134588280804395 4457469319701882421206593)
          ·
            refine ⟨3343101989776411815904945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4457469319701882421206593 3343101989776411815904945)
            ·
              refine ⟨2507326492332308861928709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3343101989776411815904945 2507326492332308861928709)
              ·
                refine ⟨470123717312307911611633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2507326492332308861928709 470123717312307911611633)
                ·
                  refine ⟨352592787984230933708725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470123717312307911611633 352592787984230933708725)
                  ·
                    rfl

theorem cell20_772506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_772506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772506 prefixEnd_772506 := by exact prefixLift 772506
  have htrace : WordTrace (prefixWord ++ tailWord_772506) baseStart_772506 baseEnd_772506 := by
    simpa [prefixWord, tailWord_772506, baseEnd_772506] using wordTrace_append hprefix tailTrace_772506
  have hstable : (prefixWord ++ tailWord_772506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772506).length < 2 ^ (prefixWord ++ tailWord_772506).sum := by decide
  have hdescent : baseEnd_772506 < baseStart_772506 := by decide
  rcases family_descends (prefixWord ++ tailWord_772506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772517 : List Nat := [1, 3, 1, 2, 1, 1, 4, 7]
def baseStart_772517 : Nat := 118140960795 + 772517 * 2 ^ 59
def prefixEnd_772517 : Nat := 4983230072969 + 3 ^ 40 * 772517 * 2
def baseEnd_772517 : Nat := 117532602894654594780671

theorem tailTrace_772517 : CollatzResearch.WordTrace tailWord_772517 prefixEnd_772517 117532602894654594780671 := by
  unfold tailWord_772517
  simp only [CollatzResearch.WordTrace]
  refine ⟨28176009742310319244795805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18784006494873546163197203 28176009742310319244795805)
  ·
    refine ⟨10566003653366369716798427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28176009742310319244795805 10566003653366369716798427)
    ·
      refine ⟨15849005480049554575197641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10566003653366369716798427 15849005480049554575197641)
      ·
        refine ⟨11886754110037165931398231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15849005480049554575197641 11886754110037165931398231)
        ·
          refine ⟨17830131165055748897097347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11886754110037165931398231 17830131165055748897097347)
          ·
            refine ⟨26745196747583623345646021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17830131165055748897097347 26745196747583623345646021)
            ·
              refine ⟨5014724390171929377308629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26745196747583623345646021 5014724390171929377308629)
              ·
                refine ⟨117532602894654594780671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5014724390171929377308629 117532602894654594780671)
                ·
                  rfl

theorem cell20_772517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_772517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772517 prefixEnd_772517 := by exact prefixLift 772517
  have htrace : WordTrace (prefixWord ++ tailWord_772517) baseStart_772517 baseEnd_772517 := by
    simpa [prefixWord, tailWord_772517, baseEnd_772517] using wordTrace_append hprefix tailTrace_772517
  have hstable : (prefixWord ++ tailWord_772517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772517).length < 2 ^ (prefixWord ++ tailWord_772517).sum := by decide
  have hdescent : baseEnd_772517 < baseStart_772517 := by decide
  rcases family_descends (prefixWord ++ tailWord_772517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772541 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_772541 : Nat := 118140960795 + 772541 * 2 ^ 59
def prefixEnd_772541 : Nat := 4983230072969 + 3 ^ 40 * 772541 * 2
def baseEnd_772541 : Nat := 352608762937926367541915

theorem tailTrace_772541 : CollatzResearch.WordTrace tailWord_772541 prefixEnd_772541 352608762937926367541915 := by
  unfold tailWord_772541
  simp only [CollatzResearch.WordTrace]
  refine ⟨28176885094223371343669477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18784590062815580895779651 28176885094223371343669477)
  ·
    refine ⟨5283165955166882126938027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28176885094223371343669477 5283165955166882126938027)
    ·
      refine ⟨7924748932750323190407041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5283165955166882126938027 7924748932750323190407041)
      ·
        refine ⟨5943561699562742392805281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7924748932750323190407041 5943561699562742392805281)
        ·
          refine ⟨4457671274672056794603961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5943561699562742392805281 4457671274672056794603961)
          ·
            refine ⟨3343253456004042595952971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4457671274672056794603961 3343253456004042595952971)
            ·
              refine ⟨5014880184006063893929457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343253456004042595952971 5014880184006063893929457)
              ·
                refine ⟨3761160138004547920447093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5014880184006063893929457 3761160138004547920447093)
                ·
                  refine ⟨352608762937926367541915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3761160138004547920447093 352608762937926367541915)
                  ·
                    rfl

theorem cell20_772541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_772541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772541 prefixEnd_772541 := by exact prefixLift 772541
  have htrace : WordTrace (prefixWord ++ tailWord_772541) baseStart_772541 baseEnd_772541 := by
    simpa [prefixWord, tailWord_772541, baseEnd_772541] using wordTrace_append hprefix tailTrace_772541
  have hstable : (prefixWord ++ tailWord_772541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772541).length < 2 ^ (prefixWord ++ tailWord_772541).sum := by decide
  have hdescent : baseEnd_772541 < baseStart_772541 := by decide
  rcases family_descends (prefixWord ++ tailWord_772541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772565 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_772565 : Nat := 118140960795 + 772565 * 2 ^ 59
def prefixEnd_772565 : Nat := 4983230072969 + 3 ^ 40 * 772565 * 2
def baseEnd_772565 : Nat := 352619717191888950741817

theorem tailTrace_772565 : CollatzResearch.WordTrace tailWord_772565 prefixEnd_772565 352619717191888950741817 := by
  unfold tailWord_772565
  simp only [CollatzResearch.WordTrace]
  refine ⟨28177760446136423442543149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18785173630757615628362099 28177760446136423442543149)
  ·
    refine ⟨10566660167301158790953681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28177760446136423442543149 10566660167301158790953681)
    ·
      refine ⟨7924995125475869093215261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10566660167301158790953681 7924995125475869093215261)
      ·
        refine ⟨2971873172053450909955723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7924995125475869093215261 2971873172053450909955723)
        ·
          refine ⟨4457809758080176364933585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971873172053450909955723 4457809758080176364933585)
          ·
            refine ⟨3343357318560132273700189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4457809758080176364933585 3343357318560132273700189)
            ·
              refine ⟨1253758994460049602637571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3343357318560132273700189 1253758994460049602637571)
              ·
                refine ⟨1880638491690074403956357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253758994460049602637571 1880638491690074403956357)
                ·
                  refine ⟨352619717191888950741817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1880638491690074403956357 352619717191888950741817)
                  ·
                    rfl

theorem cell20_772565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_772565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772565 prefixEnd_772565 := by exact prefixLift 772565
  have htrace : WordTrace (prefixWord ++ tailWord_772565) baseStart_772565 baseEnd_772565 := by
    simpa [prefixWord, tailWord_772565, baseEnd_772565] using wordTrace_append hprefix tailTrace_772565
  have hstable : (prefixWord ++ tailWord_772565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772565).length < 2 ^ (prefixWord ++ tailWord_772565).sum := by decide
  have hdescent : baseEnd_772565 < baseStart_772565 := by decide
  rcases family_descends (prefixWord ++ tailWord_772565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772575 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 3]
def baseStart_772575 : Nat := 118140960795 + 772575 * 2 ^ 59
def prefixEnd_772575 : Nat := 4983230072969 + 3 ^ 40 * 772575 * 2
def baseEnd_772575 : Nat := 352624281464373360408443

theorem tailTrace_772575 : CollatzResearch.WordTrace tailWord_772575 prefixEnd_772575 352624281464373360408443 := by
  unfold tailWord_772575
  simp only [CollatzResearch.WordTrace]
  refine ⟨28178125176100195150407179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18785416784066796766938119 28178125176100195150407179)
  ·
    refine ⟨42267187764150292725610769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28178125176100195150407179 42267187764150292725610769)
    ·
      refine ⟨31700390823112719544208077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42267187764150292725610769 31700390823112719544208077)
      ·
        refine ⟨11887646558667269829078029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31700390823112719544208077 11887646558667269829078029)
        ·
          refine ⟨4457867459500226185904261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11887646558667269829078029 4457867459500226185904261)
          ·
            refine ⟨835850148656292409857049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4457867459500226185904261 835850148656292409857049)
            ·
              refine ⟨626887611492219307392787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835850148656292409857049 626887611492219307392787)
              ·
                refine ⟨940331417238328961089181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626887611492219307392787 940331417238328961089181)
                ·
                  refine ⟨352624281464373360408443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940331417238328961089181 352624281464373360408443)
                  ·
                    rfl

theorem cell20_772575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 3].length) (baseStart_772575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772575 prefixEnd_772575 := by exact prefixLift 772575
  have htrace : WordTrace (prefixWord ++ tailWord_772575) baseStart_772575 baseEnd_772575 := by
    simpa [prefixWord, tailWord_772575, baseEnd_772575] using wordTrace_append hprefix tailTrace_772575
  have hstable : (prefixWord ++ tailWord_772575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772575).length < 2 ^ (prefixWord ++ tailWord_772575).sum := by decide
  have hdescent : baseEnd_772575 < baseStart_772575 := by decide
  rcases family_descends (prefixWord ++ tailWord_772575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772593 : List Nat := [1, 2, 2, 2, 3, 1, 1, 8]
def baseStart_772593 : Nat := 118140960795 + 772593 * 2 ^ 59
def prefixEnd_772593 : Nat := 4983230072969 + 3 ^ 40 * 772593 * 2
def baseEnd_772593 : Nat := 117544165718281765936123

theorem tailTrace_772593 : CollatzResearch.WordTrace tailWord_772593 prefixEnd_772593 117544165718281765936123 := by
  unfold tailWord_772593
  simp only [CollatzResearch.WordTrace]
  refine ⟨28178781690034984224562433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18785854460023322816374955 28178781690034984224562433)
  ·
    refine ⟨21134086267526238168421825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28178781690034984224562433 21134086267526238168421825)
    ·
      refine ⟨15850564700644678626316369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21134086267526238168421825 15850564700644678626316369)
      ·
        refine ⟨11887923525483508969737277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15850564700644678626316369 11887923525483508969737277)
        ·
          refine ⟨4457971322056315863651479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11887923525483508969737277 4457971322056315863651479)
          ·
            refine ⟨6686956983084473795477219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457971322056315863651479 6686956983084473795477219)
            ·
              refine ⟨10030435474626710693215829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686956983084473795477219 10030435474626710693215829)
              ·
                refine ⟨117544165718281765936123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10030435474626710693215829 117544165718281765936123)
                ·
                  rfl

theorem cell20_772593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_772593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772593 prefixEnd_772593 := by exact prefixLift 772593
  have htrace : WordTrace (prefixWord ++ tailWord_772593) baseStart_772593 baseEnd_772593 := by
    simpa [prefixWord, tailWord_772593, baseEnd_772593] using wordTrace_append hprefix tailTrace_772593
  have hstable : (prefixWord ++ tailWord_772593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772593).length < 2 ^ (prefixWord ++ tailWord_772593).sum := by decide
  have hdescent : baseEnd_772593 < baseStart_772593 := by decide
  rcases family_descends (prefixWord ++ tailWord_772593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772610 : List Nat := [3, 4, 1, 2, 10]
def baseStart_772610 : Nat := 118140960795 + 772610 * 2 ^ 59
def prefixEnd_772610 : Nat := 4983230072969 + 3 ^ 40 * 772610 * 2
def baseEnd_772610 : Nat := 4353583412568750546193

theorem tailTrace_772610 : CollatzResearch.WordTrace tailWord_772610 prefixEnd_772610 4353583412568750546193 := by
  unfold tailWord_772610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7044850432743349031982821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18786267820648930751954189 7044850432743349031982821)
  ·
    refine ⟨1320909456139377943496779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7044850432743349031982821 1320909456139377943496779)
    ·
      refine ⟨1981364184209066915245169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320909456139377943496779 1981364184209066915245169)
      ·
        refine ⟨1486023138156800186433877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1981364184209066915245169 1486023138156800186433877)
        ·
          refine ⟨4353583412568750546193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1486023138156800186433877 4353583412568750546193)
          ·
            rfl

theorem cell20_772610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 10].length) (baseStart_772610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772610 prefixEnd_772610 := by exact prefixLift 772610
  have htrace : WordTrace (prefixWord ++ tailWord_772610) baseStart_772610 baseEnd_772610 := by
    simpa [prefixWord, tailWord_772610, baseEnd_772610] using wordTrace_append hprefix tailTrace_772610
  have hstable : (prefixWord ++ tailWord_772610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772610).length < 2 ^ (prefixWord ++ tailWord_772610).sum := by decide
  have hdescent : baseEnd_772610 < baseStart_772610 := by decide
  rcases family_descends (prefixWord ++ tailWord_772610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772620 : List Nat := [2, 2, 1, 2, 4, 2, 1, 4, 2]
def baseStart_772620 : Nat := 118140960795 + 772620 * 2 ^ 59
def prefixEnd_772620 : Nat := 4983230072969 + 3 ^ 40 * 772620 * 2
def baseEnd_772620 : Nat := 352644820690553203908259

theorem tailTrace_772620 : CollatzResearch.WordTrace tailWord_772620 prefixEnd_772620 352644820690553203908259 := by
  unfold tailWord_772620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14089883230468583917897657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18786510973958111890530209 14089883230468583917897657)
  ·
    refine ⟨10567412422851437938423243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14089883230468583917897657 10567412422851437938423243)
    ·
      refine ⟨15851118634277156907634865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10567412422851437938423243 15851118634277156907634865)
      ·
        refine ⟨11888338975707867680726149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15851118634277156907634865 11888338975707867680726149)
        ·
          refine ⟨2229063557945225190136153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11888338975707867680726149 2229063557945225190136153)
          ·
            refine ⟨1671797668458918892602115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229063557945225190136153 1671797668458918892602115)
            ·
              refine ⟨2507696502688378338903173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671797668458918892602115 2507696502688378338903173)
              ·
                refine ⟨470193094254070938544345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2507696502688378338903173 470193094254070938544345)
                ·
                  refine ⟨352644820690553203908259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470193094254070938544345 352644820690553203908259)
                  ·
                    rfl

theorem cell20_772620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_772620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772620 prefixEnd_772620 := by exact prefixLift 772620
  have htrace : WordTrace (prefixWord ++ tailWord_772620) baseStart_772620 baseEnd_772620 := by
    simpa [prefixWord, tailWord_772620, baseEnd_772620] using wordTrace_append hprefix tailTrace_772620
  have hstable : (prefixWord ++ tailWord_772620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772620).length < 2 ^ (prefixWord ++ tailWord_772620).sum := by decide
  have hdescent : baseEnd_772620 < baseStart_772620 := by decide
  rcases family_descends (prefixWord ++ tailWord_772620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772644 : List Nat := [2, 3, 1, 5, 1, 1, 3, 4]
def baseStart_772644 : Nat := 118140960795 + 772644 * 2 ^ 59
def prefixEnd_772644 : Nat := 4983230072969 + 3 ^ 40 * 772644 * 2
def baseEnd_772644 : Nat := 117551924981505262369387

theorem tailTrace_772644 : CollatzResearch.WordTrace tailWord_772644 prefixEnd_772644 117551924981505262369387 := by
  unfold tailWord_772644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090320906425109967334493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18787094541900146623112657 14090320906425109967334493)
  ·
    refine ⟨5283870339909416237750435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14090320906425109967334493 5283870339909416237750435)
    ·
      refine ⟨7925805509864124356625653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5283870339909416237750435 7925805509864124356625653)
      ·
        refine ⟨743044266549761658433655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7925805509864124356625653 743044266549761658433655)
        ·
          refine ⟨1114566399824642487650483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743044266549761658433655 1114566399824642487650483)
          ·
            refine ⟨1671849599736963731475725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114566399824642487650483 1671849599736963731475725)
            ·
              refine ⟨626943599901361399303397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1671849599736963731475725 626943599901361399303397)
              ·
                refine ⟨117551924981505262369387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 626943599901361399303397 117551924981505262369387)
                ·
                  rfl

theorem cell20_772644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_772644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772644 prefixEnd_772644 := by exact prefixLift 772644
  have htrace : WordTrace (prefixWord ++ tailWord_772644) baseStart_772644 baseEnd_772644 := by
    simpa [prefixWord, tailWord_772644, baseEnd_772644] using wordTrace_append hprefix tailTrace_772644
  have hstable : (prefixWord ++ tailWord_772644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772644).length < 2 ^ (prefixWord ++ tailWord_772644).sum := by decide
  have hdescent : baseEnd_772644 < baseStart_772644 := by decide
  rcases family_descends (prefixWord ++ tailWord_772644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772679 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_772679 : Nat := 118140960795 + 772679 * 2 ^ 59
def prefixEnd_772679 : Nat := 4983230072969 + 3 ^ 40 * 772679 * 2
def baseEnd_772679 : Nat := 352671749898211220941351

theorem tailTrace_772679 : CollatzResearch.WordTrace tailWord_772679 prefixEnd_772679 352671749898211220941351 := by
  unfold tailWord_772679
  simp only [CollatzResearch.WordTrace]
  refine ⟨28181918367723420912193091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18787945578482280608128727 28181918367723420912193091)
  ·
    refine ⟨42272877551585131368289637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28181918367723420912193091 42272877551585131368289637)
    ·
      refine ⟨7926164540922212131554307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42272877551585131368289637 7926164540922212131554307)
      ·
        refine ⟨11889246811383318197331461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926164540922212131554307 11889246811383318197331461)
        ·
          refine ⟨2229233777134372161999649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11889246811383318197331461 2229233777134372161999649)
          ·
            refine ⟨1671925332850779121499737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229233777134372161999649 1671925332850779121499737)
            ·
              refine ⟨1253943999638084341124803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671925332850779121499737 1253943999638084341124803)
              ·
                refine ⟨1880915999457126511687205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253943999638084341124803 1880915999457126511687205)
                ·
                  refine ⟨352671749898211220941351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1880915999457126511687205 352671749898211220941351)
                  ·
                    rfl

theorem cell20_772679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_772679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772679 prefixEnd_772679 := by exact prefixLift 772679
  have htrace : WordTrace (prefixWord ++ tailWord_772679) baseStart_772679 baseEnd_772679 := by
    simpa [prefixWord, tailWord_772679, baseEnd_772679] using wordTrace_append hprefix tailTrace_772679
  have hstable : (prefixWord ++ tailWord_772679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772679).length < 2 ^ (prefixWord ++ tailWord_772679).sum := by decide
  have hdescent : baseEnd_772679 < baseStart_772679 := by decide
  rcases family_descends (prefixWord ++ tailWord_772679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772693 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 3]
def baseStart_772693 : Nat := 118140960795 + 772693 * 2 ^ 59
def prefixEnd_772693 : Nat := 4983230072969 + 3 ^ 40 * 772693 * 2
def baseEnd_772693 : Nat := 352678139879689394474627

theorem tailTrace_772693 : CollatzResearch.WordTrace tailWord_772693 prefixEnd_772693 352678139879689394474627 := by
  unfold tailWord_772693
  simp only [CollatzResearch.WordTrace]
  refine ⟨28182428989672701303202733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18788285993115134202135155 28182428989672701303202733)
  ·
    refine ⟨10568410871127262988701025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28182428989672701303202733 10568410871127262988701025)
    ·
      refine ⟨7926308153345447241525769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10568410871127262988701025 7926308153345447241525769)
      ·
        refine ⟨5944731115009085431144327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7926308153345447241525769 5944731115009085431144327)
        ·
          refine ⟨8917096672513628146716491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5944731115009085431144327 8917096672513628146716491)
          ·
            refine ⟨13375645008770442220074737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917096672513628146716491 13375645008770442220074737)
            ·
              refine ⟨10031733756577831665056053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13375645008770442220074737 10031733756577831665056053)
              ·
                refine ⟨940475039679171718599005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10031733756577831665056053 940475039679171718599005)
                ·
                  refine ⟨352678139879689394474627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 940475039679171718599005 352678139879689394474627)
                  ·
                    rfl

theorem cell20_772693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_772693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772693 prefixEnd_772693 := by exact prefixLift 772693
  have htrace : WordTrace (prefixWord ++ tailWord_772693) baseStart_772693 baseEnd_772693 := by
    simpa [prefixWord, tailWord_772693, baseEnd_772693] using wordTrace_append hprefix tailTrace_772693
  have hstable : (prefixWord ++ tailWord_772693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772693).length < 2 ^ (prefixWord ++ tailWord_772693).sum := by decide
  have hdescent : baseEnd_772693 < baseStart_772693 := by decide
  rcases family_descends (prefixWord ++ tailWord_772693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772707 : List Nat := [1, 1, 1, 5, 1, 2, 3, 6]
def baseStart_772707 : Nat := 118140960795 + 772707 * 2 ^ 59
def prefixEnd_772707 : Nat := 4983230072969 + 3 ^ 40 * 772707 * 2
def baseEnd_772707 : Nat := 117561509953722522669301

theorem tailTrace_772707 : CollatzResearch.WordTrace tailWord_772707 prefixEnd_772707 117561509953722522669301 := by
  unfold tailWord_772707
  simp only [CollatzResearch.WordTrace]
  refine ⟨28182939611621981694212375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18788626407747987796141583 28182939611621981694212375)
  ·
    refine ⟨42274409417432972541318563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28182939611621981694212375 42274409417432972541318563)
    ·
      refine ⟨63411614126149458811977845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42274409417432972541318563 63411614126149458811977845)
      ·
        refine ⟨5944838824326511763622923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63411614126149458811977845 5944838824326511763622923)
        ·
          refine ⟨8917258236489767645434385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5944838824326511763622923 8917258236489767645434385)
          ·
            refine ⟨6687943677367325734075789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8917258236489767645434385 6687943677367325734075789)
            ·
              refine ⟨2507978879012747150278421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6687943677367325734075789 2507978879012747150278421)
              ·
                refine ⟨117561509953722522669301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2507978879012747150278421 117561509953722522669301)
                ·
                  rfl

theorem cell20_772707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_772707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772707 prefixEnd_772707 := by exact prefixLift 772707
  have htrace : WordTrace (prefixWord ++ tailWord_772707) baseStart_772707 baseEnd_772707 := by
    simpa [prefixWord, tailWord_772707, baseEnd_772707] using wordTrace_append hprefix tailTrace_772707
  have hstable : (prefixWord ++ tailWord_772707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772707).length < 2 ^ (prefixWord ++ tailWord_772707).sum := by decide
  have hdescent : baseEnd_772707 < baseStart_772707 := by decide
  rcases family_descends (prefixWord ++ tailWord_772707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772785 : List Nat := [1, 2, 2, 6, 2, 1, 2, 2, 2]
def baseStart_772785 : Nat := 118140960795 + 772785 * 2 ^ 59
def prefixEnd_772785 : Nat := 4983230072969 + 3 ^ 40 * 772785 * 2
def baseEnd_772785 : Nat := 352720131186545963407585

theorem tailTrace_772785 : CollatzResearch.WordTrace tailWord_772785 prefixEnd_772785 352720131186545963407585 := by
  unfold tailWord_772785
  simp only [CollatzResearch.WordTrace]
  refine ⟨28185784505339401015551809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18790523003559600677034539 28185784505339401015551809)
  ·
    refine ⟨21139338379004550761663857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28185784505339401015551809 21139338379004550761663857)
    ·
      refine ⟨15854503784253413071247893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21139338379004550761663857 15854503784253413071247893)
      ·
        refine ⟨743179864886878737714745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15854503784253413071247893 743179864886878737714745)
        ·
          refine ⟨557384898665159053286059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743179864886878737714745 557384898665159053286059)
          ·
            refine ⟨836077347997738579929089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557384898665159053286059 836077347997738579929089)
            ·
              refine ⟨627058010998303934946817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836077347997738579929089 627058010998303934946817)
              ·
                refine ⟨470293508248727951210113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627058010998303934946817 470293508248727951210113)
                ·
                  refine ⟨352720131186545963407585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470293508248727951210113 352720131186545963407585)
                  ·
                    rfl

theorem cell20_772785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_772785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772785 prefixEnd_772785 := by exact prefixLift 772785
  have htrace : WordTrace (prefixWord ++ tailWord_772785) baseStart_772785 baseEnd_772785 := by
    simpa [prefixWord, tailWord_772785, baseEnd_772785] using wordTrace_append hprefix tailTrace_772785
  have hstable : (prefixWord ++ tailWord_772785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772785).length < 2 ^ (prefixWord ++ tailWord_772785).sum := by decide
  have hdescent : baseEnd_772785 < baseStart_772785 := by decide
  rcases family_descends (prefixWord ++ tailWord_772785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772789 : List Nat := [1, 3, 3, 3, 1, 1, 4, 2, 2]
def baseStart_772789 : Nat := 118140960795 + 772789 * 2 ^ 59
def prefixEnd_772789 : Nat := 4983230072969 + 3 ^ 40 * 772789 * 2
def baseEnd_772789 : Nat := 352721956895539727274235

theorem tailTrace_772789 : CollatzResearch.WordTrace tailWord_772789 prefixEnd_772789 352721956895539727274235 := by
  unfold tailWord_772789
  simp only [CollatzResearch.WordTrace]
  refine ⟨28185930397324909698697421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18790620264883273132464947 28185930397324909698697421)
  ·
    refine ⟨10569723898996841137011533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28185930397324909698697421 10569723898996841137011533)
    ·
      refine ⟨3963646462123815426379325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10569723898996841137011533 3963646462123815426379325)
      ·
        refine ⟨1486367423296430784892247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3963646462123815426379325 1486367423296430784892247)
        ·
          refine ⟨2229551134944646177338371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486367423296430784892247 2229551134944646177338371)
          ·
            refine ⟨3344326702416969266007557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229551134944646177338371 3344326702416969266007557)
            ·
              refine ⟨627061256703181737376417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3344326702416969266007557 627061256703181737376417)
              ·
                refine ⟨470295942527386303032313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627061256703181737376417 470295942527386303032313)
                ·
                  refine ⟨352721956895539727274235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470295942527386303032313 352721956895539727274235)
                  ·
                    rfl

theorem cell20_772789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_772789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772789 prefixEnd_772789 := by exact prefixLift 772789
  have htrace : WordTrace (prefixWord ++ tailWord_772789) baseStart_772789 baseEnd_772789 := by
    simpa [prefixWord, tailWord_772789, baseEnd_772789] using wordTrace_append hprefix tailTrace_772789
  have hstable : (prefixWord ++ tailWord_772789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772789).length < 2 ^ (prefixWord ++ tailWord_772789).sum := by decide
  have hdescent : baseEnd_772789 < baseStart_772789 := by decide
  rcases family_descends (prefixWord ++ tailWord_772789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772800 : List Nat := [2, 1, 1, 2, 4, 4, 1, 5]
def baseStart_772800 : Nat := 118140960795 + 772800 * 2 ^ 59
def prefixEnd_772800 : Nat := 4983230072969 + 3 ^ 40 * 772800 * 2
def baseEnd_772800 : Nat := 117575659198424192635841

theorem tailTrace_772800 : CollatzResearch.WordTrace tailWord_772800 prefixEnd_772800 117575659198424192635841 := by
  unfold tailWord_772800
  simp only [CollatzResearch.WordTrace]
  refine ⟨14093165800142529288673927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18790887733523372384898569 14093165800142529288673927)
  ·
    refine ⟨21139748700213793933010891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14093165800142529288673927 21139748700213793933010891)
    ·
      refine ⟨31709623050320690899516337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21139748700213793933010891 31709623050320690899516337)
      ·
        refine ⟨23782217287740518174637253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31709623050320690899516337 23782217287740518174637253)
        ·
          refine ⟨4459165741451347157744485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23782217287740518174637253 4459165741451347157744485)
          ·
            refine ⟨836093576522127592077091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4459165741451347157744485 836093576522127592077091)
            ·
              refine ⟨1254140364783191388115637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836093576522127592077091 1254140364783191388115637)
              ·
                refine ⟨117575659198424192635841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1254140364783191388115637 117575659198424192635841)
                ·
                  rfl

theorem cell20_772800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_772800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772800 prefixEnd_772800 := by exact prefixLift 772800
  have htrace : WordTrace (prefixWord ++ tailWord_772800) baseStart_772800 baseEnd_772800 := by
    simpa [prefixWord, tailWord_772800, baseEnd_772800] using wordTrace_append hprefix tailTrace_772800
  have hstable : (prefixWord ++ tailWord_772800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772800).length < 2 ^ (prefixWord ++ tailWord_772800).sum := by decide
  have hdescent : baseEnd_772800 < baseStart_772800 := by decide
  rcases family_descends (prefixWord ++ tailWord_772800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772814 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_772814 : Nat := 118140960795 + 772814 * 2 ^ 59
def prefixEnd_772814 : Nat := 4983230072969 + 3 ^ 40 * 772814 * 2
def baseEnd_772814 : Nat := 352733367576750751440799

theorem tailTrace_772814 : CollatzResearch.WordTrace tailWord_772814 prefixEnd_772814 352733367576750751440799 := by
  unfold tailWord_772814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523355277779292371044687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18791228148156225978904997 3523355277779292371044687)
  ·
    refine ⟨5285032916668938556567031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3523355277779292371044687 5285032916668938556567031)
    ·
      refine ⟨7927549375003407834850547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5285032916668938556567031 7927549375003407834850547)
      ·
        refine ⟨11891324062505111752275821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7927549375003407834850547 11891324062505111752275821)
        ·
          refine ⟨4459246523439416907103433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11891324062505111752275821 4459246523439416907103433)
          ·
            refine ⟨3344434892579562680327575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4459246523439416907103433 3344434892579562680327575)
            ·
              refine ⟨5016652338869344020491363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344434892579562680327575 5016652338869344020491363)
              ·
                refine ⟨7524978508304016030737045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5016652338869344020491363 7524978508304016030737045)
                ·
                  refine ⟨352733367576750751440799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7524978508304016030737045 352733367576750751440799)
                  ·
                    rfl

theorem cell20_772814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_772814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772814 prefixEnd_772814 := by exact prefixLift 772814
  have htrace : WordTrace (prefixWord ++ tailWord_772814) baseStart_772814 baseEnd_772814 := by
    simpa [prefixWord, tailWord_772814, baseEnd_772814] using wordTrace_append hprefix tailTrace_772814
  have hstable : (prefixWord ++ tailWord_772814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772814).length < 2 ^ (prefixWord ++ tailWord_772814).sum := by decide
  have hdescent : baseEnd_772814 < baseStart_772814 := by decide
  rcases family_descends (prefixWord ++ tailWord_772814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772831 : List Nat := [1, 1, 2, 3, 2, 3, 1, 5, 2]
def baseStart_772831 : Nat := 118140960795 + 772831 * 2 ^ 59
def prefixEnd_772831 : Nat := 4983230072969 + 3 ^ 40 * 772831 * 2
def baseEnd_772831 : Nat := 352741126839974247874063

theorem tailTrace_772831 : CollatzResearch.WordTrace tailWord_772831 prefixEnd_772831 352741126839974247874063 := by
  unfold tailWord_772831
  simp only [CollatzResearch.WordTrace]
  refine ⟨28187462263172750871726347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18791641508781833914484231 28187462263172750871726347)
  ·
    refine ⟨42281193394759126307589521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28187462263172750871726347 42281193394759126307589521)
    ·
      refine ⟨31710895046069344730692141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42281193394759126307589521 31710895046069344730692141)
      ·
        refine ⟨11891585642276004274009553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31710895046069344730692141 11891585642276004274009553)
        ·
          refine ⟨8918689231707003205507165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11891585642276004274009553 8918689231707003205507165)
          ·
            refine ⟨3344508461890126202065187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8918689231707003205507165 3344508461890126202065187)
            ·
              refine ⟨5016762692835189303097781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344508461890126202065187 5016762692835189303097781)
              ·
                refine ⟨470321502453298997165417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5016762692835189303097781 470321502453298997165417)
                ·
                  refine ⟨352741126839974247874063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470321502453298997165417 352741126839974247874063)
                  ·
                    rfl

theorem cell20_772831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 2].length) (baseStart_772831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772831 prefixEnd_772831 := by exact prefixLift 772831
  have htrace : WordTrace (prefixWord ++ tailWord_772831) baseStart_772831 baseEnd_772831 := by
    simpa [prefixWord, tailWord_772831, baseEnd_772831] using wordTrace_append hprefix tailTrace_772831
  have hstable : (prefixWord ++ tailWord_772831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772831).length < 2 ^ (prefixWord ++ tailWord_772831).sum := by decide
  have hdescent : baseEnd_772831 < baseStart_772831 := by decide
  rcases family_descends (prefixWord ++ tailWord_772831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772845 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_772845 : Nat := 118140960795 + 772845 * 2 ^ 59
def prefixEnd_772845 : Nat := 4983230072969 + 3 ^ 40 * 772845 * 2
def baseEnd_772845 : Nat := 352747516821452421407339

theorem tailTrace_772845 : CollatzResearch.WordTrace tailWord_772845 prefixEnd_772845 352747516821452421407339 := by
  unfold tailWord_772845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28187972885122031262735989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18791981923414687508490659 28187972885122031262735989)
  ·
    refine ⟨2642622457980190430881499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28187972885122031262735989 2642622457980190430881499)
    ·
      refine ⟨3963933686970285646322249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642622457980190430881499 3963933686970285646322249)
      ·
        refine ⟨2972950265227714234741687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3963933686970285646322249 2972950265227714234741687)
        ·
          refine ⟨4459425397841571352112531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972950265227714234741687 4459425397841571352112531)
          ·
            refine ⟨6689138096762357028168797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459425397841571352112531 6689138096762357028168797)
            ·
              refine ⟨2508426786285883885563299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6689138096762357028168797 2508426786285883885563299)
              ·
                refine ⟨3762640179428825828344949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508426786285883885563299 3762640179428825828344949)
                ·
                  refine ⟨352747516821452421407339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3762640179428825828344949 352747516821452421407339)
                  ·
                    rfl

theorem cell20_772845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_772845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_772845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_772845 prefixEnd_772845 := by exact prefixLift 772845
  have htrace : WordTrace (prefixWord ++ tailWord_772845) baseStart_772845 baseEnd_772845 := by
    simpa [prefixWord, tailWord_772845, baseEnd_772845] using wordTrace_append hprefix tailTrace_772845
  have hstable : (prefixWord ++ tailWord_772845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772845).length < 2 ^ (prefixWord ++ tailWord_772845).sum := by decide
  have hdescent : baseEnd_772845 < baseStart_772845 := by decide
  rcases family_descends (prefixWord ++ tailWord_772845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
