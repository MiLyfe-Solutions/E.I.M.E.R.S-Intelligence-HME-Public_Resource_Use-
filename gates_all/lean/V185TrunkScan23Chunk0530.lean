import V185TrunkScan23Chunk0529

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3133672 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_3133672 : Nat := 118140960795 + 3133672 * 2 ^ 59
def prefixEnd_3133672 : Nat := 4983230072969 + 3 ^ 40 * 3133672 * 2
def baseEnd_3133672 : Nat := 1609079949536168727588511

theorem tailTrace_3133672 : CollatzResearch.WordTrace tailWord_3133672 prefixEnd_3133672 1609079949536168727588511 := by
  unfold tailWord_3133672
  simp only [CollatzResearch.WordTrace]
  refine ⟨57147203751624503707085635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76196271668832671609447513 57147203751624503707085635)
  ·
    refine ⟨85720805627436755560628453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57147203751624503707085635 85720805627436755560628453)
    ·
      refine ⟨16072651055144391667617835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85720805627436755560628453 16072651055144391667617835)
      ·
        refine ⟨24108976582716587501426753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16072651055144391667617835 24108976582716587501426753)
        ·
          refine ⟨18081732437037440626070065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24108976582716587501426753 18081732437037440626070065)
          ·
            refine ⟨13561299327778080469552549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18081732437037440626070065 13561299327778080469552549)
            ·
              refine ⟨2542743623958390088041103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13561299327778080469552549 2542743623958390088041103)
              ·
                refine ⟨3814115435937585132061655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542743623958390088041103 3814115435937585132061655)
                ·
                  refine ⟨5721173153906377698092483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814115435937585132061655 5721173153906377698092483)
                  ·
                    refine ⟨8581759730859566547138725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5721173153906377698092483 8581759730859566547138725)
                    ·
                      refine ⟨1609079949536168727588511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8581759730859566547138725 1609079949536168727588511)
                      ·
                        rfl

theorem cell23_3133672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_3133672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133672 prefixEnd_3133672 := by exact prefixLift 3133672
  have htrace : WordTrace (prefixWord ++ tailWord_3133672) baseStart_3133672 baseEnd_3133672 := by
    simpa [prefixWord, tailWord_3133672, baseEnd_3133672] using wordTrace_append hprefix tailTrace_3133672
  have hstable : (prefixWord ++ tailWord_3133672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133672).length < 2 ^ (prefixWord ++ tailWord_3133672).sum := by decide
  have hdescent : baseEnd_3133672 < baseStart_3133672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133675 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 3]
def baseStart_3133675 : Nat := 118140960795 + 3133675 * 2 ^ 59
def prefixEnd_3133675 : Nat := 4983230072969 + 3 ^ 40 * 3133675 * 2
def baseEnd_3133675 : Nat := 1609081489978132215850997

theorem tailTrace_3133675 : CollatzResearch.WordTrace tailWord_3133675 prefixEnd_3133675 1609081489978132215850997 := by
  unfold tailWord_3133675
  simp only [CollatzResearch.WordTrace]
  refine ⟨114294516922238138926530479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76196344614825425951020319 114294516922238138926530479)
  ·
    refine ⟨171441775383357208389795719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114294516922238138926530479 171441775383357208389795719)
    ·
      refine ⟨257162663075035812584693579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171441775383357208389795719 257162663075035812584693579)
      ·
        refine ⟨385743994612553718877040369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257162663075035812584693579 385743994612553718877040369)
        ·
          refine ⟨289307995959415289157780277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385743994612553718877040369 289307995959415289157780277)
          ·
            refine ⟨27122624621195183358541901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 289307995959415289157780277 27122624621195183358541901)
            ·
              refine ⟨10170984232948193759453213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27122624621195183358541901 10170984232948193759453213)
              ·
                refine ⟨3814119087355572659794955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10170984232948193759453213 3814119087355572659794955)
                ·
                  refine ⟨5721178631033358989692433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814119087355572659794955 5721178631033358989692433)
                  ·
                    refine ⟨4290883973275019242269325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5721178631033358989692433 4290883973275019242269325)
                    ·
                      refine ⟨1609081489978132215850997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4290883973275019242269325 1609081489978132215850997)
                      ·
                        rfl

theorem cell23_3133675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 3].length) (baseStart_3133675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133675 prefixEnd_3133675 := by exact prefixLift 3133675
  have htrace : WordTrace (prefixWord ++ tailWord_3133675) baseStart_3133675 baseEnd_3133675 := by
    simpa [prefixWord, tailWord_3133675, baseEnd_3133675] using wordTrace_append hprefix tailTrace_3133675
  have hstable : (prefixWord ++ tailWord_3133675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133675).length < 2 ^ (prefixWord ++ tailWord_3133675).sum := by decide
  have hdescent : baseEnd_3133675 < baseStart_3133675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133682 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_3133682 : Nat := 118140960795 + 3133682 * 2 ^ 59
def prefixEnd_3133682 : Nat := 4983230072969 + 3 ^ 40 * 3133682 * 2
def baseEnd_3133682 : Nat := 536361694780904562821155

theorem tailTrace_3133682 : CollatzResearch.WordTrace tailWord_3133682 prefixEnd_3133682 536361694780904562821155 := by
  unfold tailWord_3133682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28573693058303194780508825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76196514822141852748023533 28573693058303194780508825)
  ·
    refine ⟨21430269793727396085381619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28573693058303194780508825 21430269793727396085381619)
    ·
      refine ⟨32145404690591094128072429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21430269793727396085381619 32145404690591094128072429)
      ·
        refine ⟨12054526758971660298027161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32145404690591094128072429 12054526758971660298027161)
        ·
          refine ⟨9040895069228745223520371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12054526758971660298027161 9040895069228745223520371)
          ·
            refine ⟨13561342603843117835280557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9040895069228745223520371 13561342603843117835280557)
            ·
              refine ⟨5085503476441169188230209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13561342603843117835280557 5085503476441169188230209)
              ·
                refine ⟨3814127607330876891172657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5085503476441169188230209 3814127607330876891172657)
                ·
                  refine ⟨2860595705498157668379493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814127607330876891172657 2860595705498157668379493)
                  ·
                    refine ⟨536361694780904562821155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2860595705498157668379493 536361694780904562821155)
                    ·
                      rfl

theorem cell23_3133682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_3133682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133682 prefixEnd_3133682 := by exact prefixLift 3133682
  have htrace : WordTrace (prefixWord ++ tailWord_3133682) baseStart_3133682 baseEnd_3133682 := by
    simpa [prefixWord, tailWord_3133682, baseEnd_3133682] using wordTrace_append hprefix tailTrace_3133682
  have hstable : (prefixWord ++ tailWord_3133682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133682).length < 2 ^ (prefixWord ++ tailWord_3133682).sum := by decide
  have hdescent : baseEnd_3133682 < baseStart_3133682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133688 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_3133688 : Nat := 118140960795 + 3133688 * 2 ^ 59
def prefixEnd_3133688 : Nat := 4983230072969 + 3 ^ 40 * 3133688 * 2
def baseEnd_3133688 : Nat := 1609088165226640664988437

theorem tailTrace_3133688 : CollatzResearch.WordTrace tailWord_3133688 prefixEnd_3133688 1609088165226640664988437 := by
  unfold tailWord_3133688
  simp only [CollatzResearch.WordTrace]
  refine ⟨57147495535595521073376859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76196660714127361431169145 57147495535595521073376859)
  ·
    refine ⟨85721243303393281610065289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57147495535595521073376859 85721243303393281610065289)
    ·
      refine ⟨64290932477544961207548967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85721243303393281610065289 64290932477544961207548967)
      ·
        refine ⟨96436398716317441811323451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64290932477544961207548967 96436398716317441811323451)
        ·
          refine ⟨144654598074476162716985177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96436398716317441811323451 144654598074476162716985177)
          ·
            refine ⟨108490948555857122037738883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144654598074476162716985177 108490948555857122037738883)
            ·
              refine ⟨162736422833785683056608325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108490948555857122037738883 162736422833785683056608325)
              ·
                refine ⟨30513079281334815573114061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162736422833785683056608325 30513079281334815573114061)
                ·
                  refine ⟨11442404730500555839917773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30513079281334815573114061 11442404730500555839917773)
                  ·
                    refine ⟨4290901773937708439969165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11442404730500555839917773 4290901773937708439969165)
                    ·
                      refine ⟨1609088165226640664988437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4290901773937708439969165 1609088165226640664988437)
                      ·
                        rfl

theorem cell23_3133688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_3133688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133688 prefixEnd_3133688 := by exact prefixLift 3133688
  have htrace : WordTrace (prefixWord ++ tailWord_3133688) baseStart_3133688 baseEnd_3133688 := by
    simpa [prefixWord, tailWord_3133688, baseEnd_3133688] using wordTrace_append hprefix tailTrace_3133688
  have hstable : (prefixWord ++ tailWord_3133688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133688).length < 2 ^ (prefixWord ++ tailWord_3133688).sum := by decide
  have hdescent : baseEnd_3133688 < baseStart_3133688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133705 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 3]
def baseStart_3133705 : Nat := 118140960795 + 3133705 * 2 ^ 59
def prefixEnd_3133705 : Nat := 4983230072969 + 3 ^ 40 * 3133705 * 2
def baseEnd_3133705 : Nat := 1609096894397767098475859

theorem tailTrace_3133705 : CollatzResearch.WordTrace tailWord_3133705 prefixEnd_3133705 1609096894397767098475859 := by
  unfold tailWord_3133705
  simp only [CollatzResearch.WordTrace]
  refine ⟨114295611112129454050122569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76197074074752969366748379 114295611112129454050122569)
  ·
    refine ⟨85721708334097090537591927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114295611112129454050122569 85721708334097090537591927)
    ·
      refine ⟨128582562501145635806387891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85721708334097090537591927 128582562501145635806387891)
      ·
        refine ⟨192873843751718453709581837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128582562501145635806387891 192873843751718453709581837)
        ·
          refine ⟨72327691406894420141093189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192873843751718453709581837 72327691406894420141093189)
          ·
            refine ⟨13561442138792703776454973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72327691406894420141093189 13561442138792703776454973)
            ·
              refine ⟨5085540802047263916170615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13561442138792703776454973 5085540802047263916170615)
              ·
                refine ⟨7628311203070895874255923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085540802047263916170615 7628311203070895874255923)
                ·
                  refine ⟨11442466804606343811383885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7628311203070895874255923 11442466804606343811383885)
                  ·
                    refine ⟨4290925051727378929268957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11442466804606343811383885 4290925051727378929268957)
                    ·
                      refine ⟨1609096894397767098475859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4290925051727378929268957 1609096894397767098475859)
                      ·
                        rfl

theorem cell23_3133705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_3133705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133705 prefixEnd_3133705 := by exact prefixLift 3133705
  have htrace : WordTrace (prefixWord ++ tailWord_3133705) baseStart_3133705 baseEnd_3133705 := by
    simpa [prefixWord, tailWord_3133705, baseEnd_3133705] using wordTrace_append hprefix tailTrace_3133705
  have hstable : (prefixWord ++ tailWord_3133705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133705).length < 2 ^ (prefixWord ++ tailWord_3133705).sum := by decide
  have hdescent : baseEnd_3133705 < baseStart_3133705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133715 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 3, 3, 2]
def baseStart_3133715 : Nat := 118140960795 + 3133715 * 2 ^ 59
def prefixEnd_3133715 : Nat := 4983230072969 + 3 ^ 40 * 3133715 * 2
def baseEnd_3133715 : Nat := 1609102029204312059350813

theorem tailTrace_3133715 : CollatzResearch.WordTrace tailWord_3133715 prefixEnd_3133715 1609102029204312059350813 := by
  unfold tailWord_3133715
  simp only [CollatzResearch.WordTrace]
  refine ⟨114295975842093225757986599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76197317228062150505324399 114295975842093225757986599)
  ·
    refine ⟨171443963763139838636979899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114295975842093225757986599 171443963763139838636979899)
    ·
      refine ⟨257165945644709757955469849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171443963763139838636979899 257165945644709757955469849)
      ·
        refine ⟨192874459233532318466602387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257165945644709757955469849 192874459233532318466602387)
        ·
          refine ⟨289311688850298477699903581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192874459233532318466602387 289311688850298477699903581)
          ·
            refine ⟨108491883318861929137463843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289311688850298477699903581 108491883318861929137463843)
            ·
              refine ⟨162737824978292893706195765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108491883318861929137463843 162737824978292893706195765)
              ·
                refine ⟨15256671091714958784955853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162737824978292893706195765 15256671091714958784955853)
                ·
                  refine ⟨5721251659393109544358445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15256671091714958784955853 5721251659393109544358445)
                  ·
                    refine ⟨2145469372272416079134417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5721251659393109544358445 2145469372272416079134417)
                    ·
                      refine ⟨1609102029204312059350813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145469372272416079134417 1609102029204312059350813)
                      ·
                        rfl

theorem cell23_3133715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 3, 2].length) (baseStart_3133715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133715 prefixEnd_3133715 := by exact prefixLift 3133715
  have htrace : WordTrace (prefixWord ++ tailWord_3133715) baseStart_3133715 baseEnd_3133715 := by
    simpa [prefixWord, tailWord_3133715, baseEnd_3133715] using wordTrace_append hprefix tailTrace_3133715
  have hstable : (prefixWord ++ tailWord_3133715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133715).length < 2 ^ (prefixWord ++ tailWord_3133715).sum := by decide
  have hdescent : baseEnd_3133715 < baseStart_3133715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133768 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 7]
def baseStart_3133768 : Nat := 118140960795 + 3133768 * 2 ^ 59
def prefixEnd_3133768 : Nat := 4983230072969 + 3 ^ 40 * 3133768 * 2
def baseEnd_3133768 : Nat := 178792138186555594665341

theorem tailTrace_3133768 : CollatzResearch.WordTrace tailWord_3133768 prefixEnd_3133768 178792138186555594665341 := by
  unfold tailWord_3133768
  simp only [CollatzResearch.WordTrace]
  refine ⟨57148954455450607904832979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76198605940600810539777305 57148954455450607904832979)
  ·
    refine ⟨85723431683175911857249469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57148954455450607904832979 85723431683175911857249469)
    ·
      refine ⟨32146286881190966946468551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85723431683175911857249469 32146286881190966946468551)
      ·
        refine ⟨48219430321786450419702827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32146286881190966946468551 48219430321786450419702827)
        ·
          refine ⟨72329145482679675629554241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48219430321786450419702827 72329145482679675629554241)
          ·
            refine ⟨54246859112009756722165681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72329145482679675629554241 54246859112009756722165681)
            ·
              refine ⟨40685144334007317541624261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54246859112009756722165681 40685144334007317541624261)
              ·
                refine ⟨7628464562626372039054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40685144334007317541624261 7628464562626372039054549)
                ·
                  refine ⟨178792138186555594665341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7628464562626372039054549 178792138186555594665341)
                  ·
                    rfl

theorem cell23_3133768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 7].length) (baseStart_3133768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133768 prefixEnd_3133768 := by exact prefixLift 3133768
  have htrace : WordTrace (prefixWord ++ tailWord_3133768) baseStart_3133768 baseEnd_3133768 := by
    simpa [prefixWord, tailWord_3133768, baseEnd_3133768] using wordTrace_append hprefix tailTrace_3133768
  have hstable : (prefixWord ++ tailWord_3133768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133768).length < 2 ^ (prefixWord ++ tailWord_3133768).sum := by decide
  have hdescent : baseEnd_3133768 < baseStart_3133768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133785 : List Nat := [1, 2, 1, 2, 2, 2, 1, 7, 5]
def baseStart_3133785 : Nat := 118140960795 + 3133785 * 2 ^ 59
def prefixEnd_3133785 : Nat := 4983230072969 + 3 ^ 40 * 3133785 * 2
def baseEnd_3133785 : Nat := 178793108094458531719499

theorem tailTrace_3133785 : CollatzResearch.WordTrace tailWord_3133785 prefixEnd_3133785 178793108094458531719499 := by
  unfold tailWord_3133785
  simp only [CollatzResearch.WordTrace]
  refine ⟨114298528951839627713034809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76199019301226418475356539 114298528951839627713034809)
  ·
    refine ⟨85723896713879720784776107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114298528951839627713034809 85723896713879720784776107)
    ·
      refine ⟨128585845070819581177164161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85723896713879720784776107 128585845070819581177164161)
      ·
        refine ⟨96439383803114685882873121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128585845070819581177164161 96439383803114685882873121)
        ·
          refine ⟨72329537852336014412154841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96439383803114685882873121 72329537852336014412154841)
          ·
            refine ⟨54247153389252010809116131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72329537852336014412154841 54247153389252010809116131)
            ·
              refine ⟨81370730083878016213674197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54247153389252010809116131 81370730083878016213674197)
              ·
                refine ⟨1907126486340891005007989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81370730083878016213674197 1907126486340891005007989)
                ·
                  refine ⟨178793108094458531719499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1907126486340891005007989 178793108094458531719499)
                  ·
                    rfl

theorem cell23_3133785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 5].length) (baseStart_3133785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133785 prefixEnd_3133785 := by exact prefixLift 3133785
  have htrace : WordTrace (prefixWord ++ tailWord_3133785) baseStart_3133785 baseEnd_3133785 := by
    simpa [prefixWord, tailWord_3133785, baseEnd_3133785] using wordTrace_append hprefix tailTrace_3133785
  have hstable : (prefixWord ++ tailWord_3133785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133785).length < 2 ^ (prefixWord ++ tailWord_3133785).sum := by decide
  have hdescent : baseEnd_3133785 < baseStart_3133785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133795 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 3]
def baseStart_3133795 : Nat := 118140960795 + 3133795 * 2 ^ 59
def prefixEnd_3133795 : Nat := 4983230072969 + 3 ^ 40 * 3133795 * 2
def baseEnd_3133795 : Nat := 1609143107656671746350445

theorem tailTrace_3133795 : CollatzResearch.WordTrace tailWord_3133795 prefixEnd_3133795 1609143107656671746350445 := by
  unfold tailWord_3133795
  simp only [CollatzResearch.WordTrace]
  refine ⟨114298893681803399420898839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76199262454535599613932559 114298893681803399420898839)
  ·
    refine ⟨171448340522705099131348259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114298893681803399420898839 171448340522705099131348259)
    ·
      refine ⟨257172510784057648697022389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171448340522705099131348259 257172510784057648697022389)
      ·
        refine ⟨24109922886005404565345849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257172510784057648697022389 24109922886005404565345849)
        ·
          refine ⟨18082442164504053424009387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24109922886005404565345849 18082442164504053424009387)
          ·
            refine ⟨27123663246756080136014081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18082442164504053424009387 27123663246756080136014081)
            ·
              refine ⟨20342747435067060102010561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27123663246756080136014081 20342747435067060102010561)
              ·
                refine ⟨15257060576300295076507921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20342747435067060102010561 15257060576300295076507921)
                ·
                  refine ⟨11442795432225221307380941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15257060576300295076507921 11442795432225221307380941)
                  ·
                    refine ⟨4291048287084457990267853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11442795432225221307380941 4291048287084457990267853)
                    ·
                      refine ⟨1609143107656671746350445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291048287084457990267853 1609143107656671746350445)
                      ·
                        rfl

theorem cell23_3133795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_3133795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133795 prefixEnd_3133795 := by exact prefixLift 3133795
  have htrace : WordTrace (prefixWord ++ tailWord_3133795) baseStart_3133795 baseEnd_3133795 := by
    simpa [prefixWord, tailWord_3133795, baseEnd_3133795] using wordTrace_append hprefix tailTrace_3133795
  have hstable : (prefixWord ++ tailWord_3133795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133795).length < 2 ^ (prefixWord ++ tailWord_3133795).sum := by decide
  have hdescent : baseEnd_3133795 < baseStart_3133795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133835 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 4]
def baseStart_3133835 : Nat := 118140960795 + 3133835 * 2 ^ 59
def prefixEnd_3133835 : Nat := 4983230072969 + 3 ^ 40 * 3133835 * 2
def baseEnd_3133835 : Nat := 1609163646882851589850261

theorem tailTrace_3133835 : CollatzResearch.WordTrace tailWord_3133835 prefixEnd_3133835 1609163646882851589850261 := by
  unfold tailWord_3133835
  simp only [CollatzResearch.WordTrace]
  refine ⟨114300352601658486252354959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76200235067772324168236639 114300352601658486252354959)
  ·
    refine ⟨171450528902487729378532439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114300352601658486252354959 171450528902487729378532439)
    ·
      refine ⟨257175793353731594067798659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171450528902487729378532439 257175793353731594067798659)
      ·
        refine ⟨385763690030597391101697989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257175793353731594067798659 385763690030597391101697989)
        ·
          refine ⟨72330691880737010831568373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385763690030597391101697989 72330691880737010831568373)
          ·
            refine ⟨6781002363819094765459535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72330691880737010831568373 6781002363819094765459535)
            ·
              refine ⟨10171503545728642148189303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781002363819094765459535 10171503545728642148189303)
              ·
                refine ⟨15257255318592963222283955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10171503545728642148189303 15257255318592963222283955)
                ·
                  refine ⟨22885882977889444833425933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15257255318592963222283955 22885882977889444833425933)
                  ·
                    refine ⟨8582206116708541812534725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22885882977889444833425933 8582206116708541812534725)
                    ·
                      refine ⟨1609163646882851589850261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8582206116708541812534725 1609163646882851589850261)
                      ·
                        rfl

theorem cell23_3133835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 4].length) (baseStart_3133835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133835 prefixEnd_3133835 := by exact prefixLift 3133835
  have htrace : WordTrace (prefixWord ++ tailWord_3133835) baseStart_3133835 baseEnd_3133835 := by
    simpa [prefixWord, tailWord_3133835, baseEnd_3133835] using wordTrace_append hprefix tailTrace_3133835
  have hstable : (prefixWord ++ tailWord_3133835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133835).length < 2 ^ (prefixWord ++ tailWord_3133835).sum := by decide
  have hdescent : baseEnd_3133835 < baseStart_3133835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133845 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_3133845 : Nat := 118140960795 + 3133845 * 2 ^ 59
def prefixEnd_3133845 : Nat := 4983230072969 + 3 ^ 40 * 3133845 * 2
def baseEnd_3133845 : Nat := 536389593896465516908405

theorem tailTrace_3133845 : CollatzResearch.WordTrace tailWord_3133845 prefixEnd_3133845 536389593896465516908405 := by
  unfold tailWord_3133845
  simp only [CollatzResearch.WordTrace]
  refine ⟨114300717331622257960218989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76200478221081505306812659 114300717331622257960218989)
  ·
    refine ⟨42862768999358346735082121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114300717331622257960218989 42862768999358346735082121)
    ·
      refine ⟨32147076749518760051311591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42862768999358346735082121 32147076749518760051311591)
      ·
        refine ⟨48220615124278140076967387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32147076749518760051311591 48220615124278140076967387)
        ·
          refine ⟨72330922686417210115451081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48220615124278140076967387 72330922686417210115451081)
          ·
            refine ⟨54248192014812907586588311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72330922686417210115451081 54248192014812907586588311)
            ·
              refine ⟨81372288022219361379882467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54248192014812907586588311 81372288022219361379882467)
              ·
                refine ⟨122058432033329042069823701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81372288022219361379882467 122058432033329042069823701)
                ·
                  refine ⟨2860744500781149423511493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 122058432033329042069823701 2860744500781149423511493)
                  ·
                    refine ⟨536389593896465516908405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2860744500781149423511493 536389593896465516908405)
                    ·
                      rfl

theorem cell23_3133845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_3133845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133845 prefixEnd_3133845 := by exact prefixLift 3133845
  have htrace : WordTrace (prefixWord ++ tailWord_3133845) baseStart_3133845 baseEnd_3133845 := by
    simpa [prefixWord, tailWord_3133845, baseEnd_3133845] using wordTrace_append hprefix tailTrace_3133845
  have hstable : (prefixWord ++ tailWord_3133845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133845).length < 2 ^ (prefixWord ++ tailWord_3133845).sum := by decide
  have hdescent : baseEnd_3133845 < baseStart_3133845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133896 : List Nat := [2, 1, 3, 1, 3, 4, 1, 3, 1, 4]
def baseStart_3133896 : Nat := 118140960795 + 3133896 * 2 ^ 59
def prefixEnd_3133896 : Nat := 4983230072969 + 3 ^ 40 * 3133896 * 2
def baseEnd_3133896 : Nat := 536398323067591950395827

theorem tailTrace_3133896 : CollatzResearch.WordTrace tailWord_3133896 prefixEnd_3133896 536398323067591950395827 := by
  unfold tailWord_3133896
  simp only [CollatzResearch.WordTrace]
  refine ⟨57151288727218746835162771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76201718302958329113550361 57151288727218746835162771)
  ·
    refine ⟨85726933090828120252744157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57151288727218746835162771 85726933090828120252744157)
    ·
      refine ⟨32147599909060545094779059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85726933090828120252744157 32147599909060545094779059)
      ·
        refine ⟨48221399863590817642168589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32147599909060545094779059 48221399863590817642168589)
        ·
          refine ⟨18083024948846556615813221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48221399863590817642168589 18083024948846556615813221)
          ·
            refine ⟨3390567177908729365464979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18083024948846556615813221 3390567177908729365464979)
            ·
              refine ⟨5085850766863094048197469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390567177908729365464979 5085850766863094048197469)
              ·
                refine ⟨1907194037573660268074051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5085850766863094048197469 1907194037573660268074051)
                ·
                  refine ⟨2860791056360490402111077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907194037573660268074051 2860791056360490402111077)
                  ·
                    refine ⟨536398323067591950395827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2860791056360490402111077 536398323067591950395827)
                    ·
                      rfl

theorem cell23_3133896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_3133896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133896 prefixEnd_3133896 := by exact prefixLift 3133896
  have htrace : WordTrace (prefixWord ++ tailWord_3133896) baseStart_3133896 baseEnd_3133896 := by
    simpa [prefixWord, tailWord_3133896, baseEnd_3133896] using wordTrace_append hprefix tailTrace_3133896
  have hstable : (prefixWord ++ tailWord_3133896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133896).length < 2 ^ (prefixWord ++ tailWord_3133896).sum := by decide
  have hdescent : baseEnd_3133896 < baseStart_3133896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133906 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3133906 : Nat := 118140960795 + 3133906 * 2 ^ 59
def prefixEnd_3133906 : Nat := 4983230072969 + 3 ^ 40 * 3133906 * 2
def baseEnd_3133906 : Nat := 1609200104009320812062435

theorem tailTrace_3133906 : CollatzResearch.WordTrace tailWord_3133906 prefixEnd_3133906 1609200104009320812062435 := by
  unfold tailWord_3133906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28575735546100316344547393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76201961456267510252126381 28575735546100316344547393)
  ·
    refine ⟨21431801659575237258410545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28575735546100316344547393 21431801659575237258410545)
    ·
      refine ⟨16073851244681427943807909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21431801659575237258410545 16073851244681427943807909)
      ·
        refine ⟨3013847108377767739463983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16073851244681427943807909 3013847108377767739463983)
        ·
          refine ⟨4520770662566651609195975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013847108377767739463983 4520770662566651609195975)
          ·
            refine ⟨6781155993849977413793963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4520770662566651609195975 6781155993849977413793963)
            ·
              refine ⟨10171733990774966120690945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781155993849977413793963 10171733990774966120690945)
              ·
                refine ⟨7628800493081224590518209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10171733990774966120690945 7628800493081224590518209)
                ·
                  refine ⟨5721600369810918442888657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7628800493081224590518209 5721600369810918442888657)
                  ·
                    refine ⟨4291200277358188832166493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5721600369810918442888657 4291200277358188832166493)
                    ·
                      refine ⟨1609200104009320812062435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291200277358188832166493 1609200104009320812062435)
                      ·
                        rfl

theorem cell23_3133906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3133906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133906 prefixEnd_3133906 := by exact prefixLift 3133906
  have htrace : WordTrace (prefixWord ++ tailWord_3133906) baseStart_3133906 baseEnd_3133906 := by
    simpa [prefixWord, tailWord_3133906, baseEnd_3133906] using wordTrace_append hprefix tailTrace_3133906
  have hstable : (prefixWord ++ tailWord_3133906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133906).length < 2 ^ (prefixWord ++ tailWord_3133906).sum := by decide
  have hdescent : baseEnd_3133906 < baseStart_3133906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133919 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 3]
def baseStart_3133919 : Nat := 118140960795 + 3133919 * 2 ^ 59
def prefixEnd_3133919 : Nat := 4983230072969 + 3 ^ 40 * 3133919 * 2
def baseEnd_3133919 : Nat := 1609206779257829261199875

theorem tailTrace_3133919 : CollatzResearch.WordTrace tailWord_3133919 prefixEnd_3133919 1609206779257829261199875 := by
  unfold tailWord_3133919
  simp only [CollatzResearch.WordTrace]
  refine ⟨114303416333354168598412811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76202277555569445732275207 114303416333354168598412811)
  ·
    refine ⟨171455124500031252897619217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114303416333354168598412811 171455124500031252897619217)
    ·
      refine ⟨128591343375023439673214413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171455124500031252897619217 128591343375023439673214413)
      ·
        refine ⟨48221753765633789877455405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128591343375023439673214413 48221753765633789877455405)
        ·
          refine ⟨18083157662112671204045777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48221753765633789877455405 18083157662112671204045777)
          ·
            refine ⟨13562368246584503403034333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18083157662112671204045777 13562368246584503403034333)
            ·
              refine ⟨5085888092469188776137875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13562368246584503403034333 5085888092469188776137875)
              ·
                refine ⟨7628832138703783164206813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085888092469188776137875 7628832138703783164206813)
                ·
                  refine ⟨2860812052013918686577555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7628832138703783164206813 2860812052013918686577555)
                  ·
                    refine ⟨4291218078020878029866333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2860812052013918686577555 4291218078020878029866333)
                    ·
                      refine ⟨1609206779257829261199875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291218078020878029866333 1609206779257829261199875)
                      ·
                        rfl

theorem cell23_3133919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_3133919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133919 prefixEnd_3133919 := by exact prefixLift 3133919
  have htrace : WordTrace (prefixWord ++ tailWord_3133919) baseStart_3133919 baseEnd_3133919 := by
    simpa [prefixWord, tailWord_3133919, baseEnd_3133919] using wordTrace_append hprefix tailTrace_3133919
  have hstable : (prefixWord ++ tailWord_3133919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133919).length < 2 ^ (prefixWord ++ tailWord_3133919).sum := by decide
  have hdescent : baseEnd_3133919 < baseStart_3133919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133935 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 1, 6]
def baseStart_3133935 : Nat := 118140960795 + 3133935 * 2 ^ 59
def prefixEnd_3133935 : Nat := 4983230072969 + 3 ^ 40 * 3133935 * 2
def baseEnd_3133935 : Nat := 536404998316100399533267

theorem tailTrace_3133935 : CollatzResearch.WordTrace tailWord_3133935 prefixEnd_3133935 536404998316100399533267 := by
  unfold tailWord_3133935
  simp only [CollatzResearch.WordTrace]
  refine ⟨114303999901296203330995259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76202666600864135553996839 114303999901296203330995259)
  ·
    refine ⟨171455999851944304996492889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114303999901296203330995259 171455999851944304996492889)
    ·
      refine ⟨128591999888958228747369667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171455999851944304996492889 128591999888958228747369667)
      ·
        refine ⟨192887999833437343121054501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128591999888958228747369667 192887999833437343121054501)
        ·
          refine ⟨36166499968769501835197719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192887999833437343121054501 36166499968769501835197719)
          ·
            refine ⟨54249749953154252752796579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36166499968769501835197719 54249749953154252752796579)
            ·
              refine ⟨81374624929731379129194869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54249749953154252752796579 81374624929731379129194869)
              ·
                refine ⟨7628871087162316793362019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81374624929731379129194869 7628871087162316793362019)
                ·
                  refine ⟨11443306630743475190043029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7628871087162316793362019 11443306630743475190043029)
                  ·
                    refine ⟨536404998316100399533267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11443306630743475190043029 536404998316100399533267)
                    ·
                      rfl

theorem cell23_3133935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_3133935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133935 prefixEnd_3133935 := by exact prefixLift 3133935
  have htrace : WordTrace (prefixWord ++ tailWord_3133935) baseStart_3133935 baseEnd_3133935 := by
    simpa [prefixWord, tailWord_3133935, baseEnd_3133935] using wordTrace_append hprefix tailTrace_3133935
  have hstable : (prefixWord ++ tailWord_3133935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133935).length < 2 ^ (prefixWord ++ tailWord_3133935).sum := by decide
  have hdescent : baseEnd_3133935 < baseStart_3133935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133945 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3133945 : Nat := 118140960795 + 3133945 * 2 ^ 59
def prefixEnd_3133945 : Nat := 4983230072969 + 3 ^ 40 * 3133945 * 2
def baseEnd_3133945 : Nat := 1609220129754846159474755

theorem tailTrace_3133945 : CollatzResearch.WordTrace tailWord_3133945 prefixEnd_3133945 1609220129754846159474755 := by
  unfold tailWord_3133945
  simp only [CollatzResearch.WordTrace]
  refine ⟨114304364631259975038859289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76202909754173316692572859 114304364631259975038859289)
  ·
    refine ⟨85728273473444981279144467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114304364631259975038859289 85728273473444981279144467)
    ·
      refine ⟨128592410210167471918716701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85728273473444981279144467 128592410210167471918716701)
      ·
        refine ⟨48222153828812801969518763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128592410210167471918716701 48222153828812801969518763)
        ·
          refine ⟨72333230743219202954278145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48222153828812801969518763 72333230743219202954278145)
          ·
            refine ⟨54249923057414402215708609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72333230743219202954278145 54249923057414402215708609)
            ·
              refine ⟨40687442293060801661781457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54249923057414402215708609 40687442293060801661781457)
              ·
                refine ⟨30515581719795601246336093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40687442293060801661781457 30515581719795601246336093)
                ·
                  refine ⟨11443343144923350467376035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30515581719795601246336093 11443343144923350467376035)
                  ·
                    refine ⟨17165014717385025701064053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11443343144923350467376035 17165014717385025701064053)
                    ·
                      refine ⟨1609220129754846159474755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17165014717385025701064053 1609220129754846159474755)
                      ·
                        rfl

theorem cell23_3133945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3133945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133945 prefixEnd_3133945 := by exact prefixLift 3133945
  have htrace : WordTrace (prefixWord ++ tailWord_3133945) baseStart_3133945 baseEnd_3133945 := by
    simpa [prefixWord, tailWord_3133945, baseEnd_3133945] using wordTrace_append hprefix tailTrace_3133945
  have hstable : (prefixWord ++ tailWord_3133945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133945).length < 2 ^ (prefixWord ++ tailWord_3133945).sum := by decide
  have hdescent : baseEnd_3133945 < baseStart_3133945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133956 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_3133956 : Nat := 118140960795 + 3133956 * 2 ^ 59
def prefixEnd_3133956 : Nat := 4983230072969 + 3 ^ 40 * 3133956 * 2
def baseEnd_3133956 : Nat := 536408592680681872145735

theorem tailTrace_3133956 : CollatzResearch.WordTrace tailWord_3133956 prefixEnd_3133956 536408592680681872145735 := by
  unfold tailWord_3133956
  simp only [CollatzResearch.WordTrace]
  refine ⟨57152382917110061958754861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76203177222813415945006481 57152382917110061958754861)
  ·
    refine ⟨21432143593916273234533073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57152382917110061958754861 21432143593916273234533073)
    ·
      refine ⟨16074107695437204925899805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21432143593916273234533073 16074107695437204925899805)
      ·
        refine ⟨6027790385788951847212427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16074107695437204925899805 6027790385788951847212427)
        ·
          refine ⟨9041685578683427770818641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027790385788951847212427 9041685578683427770818641)
          ·
            refine ⟨6781264184012570828113981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9041685578683427770818641 6781264184012570828113981)
            ·
              refine ⟨2542974069004714060542743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6781264184012570828113981 2542974069004714060542743)
              ·
                refine ⟨3814461103507071090814115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2542974069004714060542743 3814461103507071090814115)
                ·
                  refine ⟨5721691655260606636221173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814461103507071090814115 5721691655260606636221173)
                  ·
                    refine ⟨536408592680681872145735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5721691655260606636221173 536408592680681872145735)
                    ·
                      rfl

theorem cell23_3133956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_3133956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133956 prefixEnd_3133956 := by exact prefixLift 3133956
  have htrace : WordTrace (prefixWord ++ tailWord_3133956) baseStart_3133956 baseEnd_3133956 := by
    simpa [prefixWord, tailWord_3133956, baseEnd_3133956] using wordTrace_append hprefix tailTrace_3133956
  have hstable : (prefixWord ++ tailWord_3133956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133956).length < 2 ^ (prefixWord ++ tailWord_3133956).sum := by decide
  have hdescent : baseEnd_3133956 < baseStart_3133956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3133997 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3133997 : Nat := 118140960795 + 3133997 * 2 ^ 59
def prefixEnd_3133997 : Nat := 4983230072969 + 3 ^ 40 * 3133997 * 2
def baseEnd_3133997 : Nat := 1609246830748879956024517

theorem tailTrace_3133997 : CollatzResearch.WordTrace tailWord_3133997 prefixEnd_3133997 1609246830748879956024517 := by
  unfold tailWord_3133997
  simp only [CollatzResearch.WordTrace]
  refine ⟨114306261227071587919752245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76204174151381058613168163 114306261227071587919752245)
  ·
    refine ⟨10716211990037961367476773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114306261227071587919752245 10716211990037961367476773)
    ·
      refine ⟨2009289748132117756401895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10716211990037961367476773 2009289748132117756401895)
      ·
        refine ⟨3013934622198176634602843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009289748132117756401895 3013934622198176634602843)
        ·
          refine ⟨4520901933297264951904265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013934622198176634602843 4520901933297264951904265)
          ·
            refine ⟨3390676449972948713928199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520901933297264951904265 3390676449972948713928199)
            ·
              refine ⟨5086014674959423070892299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390676449972948713928199 5086014674959423070892299)
              ·
                refine ⟨7629022012439134606338449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086014674959423070892299 7629022012439134606338449)
                ·
                  refine ⟨5721766509329350954753837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7629022012439134606338449 5721766509329350954753837)
                  ·
                    refine ⟨2145662440998506608032689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5721766509329350954753837 2145662440998506608032689)
                    ·
                      refine ⟨1609246830748879956024517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145662440998506608032689 1609246830748879956024517)
                      ·
                        rfl

theorem cell23_3133997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3133997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3133997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3133997 prefixEnd_3133997 := by exact prefixLift 3133997
  have htrace : WordTrace (prefixWord ++ tailWord_3133997) baseStart_3133997 baseEnd_3133997 := by
    simpa [prefixWord, tailWord_3133997, baseEnd_3133997] using wordTrace_append hprefix tailTrace_3133997
  have hstable : (prefixWord ++ tailWord_3133997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3133997).length < 2 ^ (prefixWord ++ tailWord_3133997).sum := by decide
  have hdescent : baseEnd_3133997 < baseStart_3133997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3133997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134009 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3134009 : Nat := 118140960795 + 3134009 * 2 ^ 59
def prefixEnd_3134009 : Nat := 4983230072969 + 3 ^ 40 * 3134009 * 2
def baseEnd_3134009 : Nat := 1609252992516733909074461

theorem tailTrace_3134009 : CollatzResearch.WordTrace tailWord_3134009 prefixEnd_3134009 1609252992516733909074461 := by
  unfold tailWord_3134009
  simp only [CollatzResearch.WordTrace]
  refine ⟨114306698903028113969189081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76204465935352075979459387 114306698903028113969189081)
  ·
    refine ⟨85730024177271085476891811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114306698903028113969189081 85730024177271085476891811)
    ·
      refine ⟨128595036265906628215337717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85730024177271085476891811 128595036265906628215337717)
      ·
        refine ⟨12055784649928746395187911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128595036265906628215337717 12055784649928746395187911)
        ·
          refine ⟨18083676974893119592781867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12055784649928746395187911 18083676974893119592781867)
          ·
            refine ⟨27125515462339679389172801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18083676974893119592781867 27125515462339679389172801)
            ·
              refine ⟨20344136596754759541879601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27125515462339679389172801 20344136596754759541879601)
              ·
                refine ⟨15258102447566069656409701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20344136596754759541879601 15258102447566069656409701)
                ·
                  refine ⟨2860894208918638060576819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15258102447566069656409701 2860894208918638060576819)
                  ·
                    refine ⟨4291341313377957090865229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2860894208918638060576819 4291341313377957090865229)
                    ·
                      refine ⟨1609252992516733909074461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291341313377957090865229 1609252992516733909074461)
                      ·
                        rfl

theorem cell23_3134009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3134009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134009 prefixEnd_3134009 := by exact prefixLift 3134009
  have htrace : WordTrace (prefixWord ++ tailWord_3134009) baseStart_3134009 baseEnd_3134009 := by
    simpa [prefixWord, tailWord_3134009, baseEnd_3134009] using wordTrace_append hprefix tailTrace_3134009
  have hstable : (prefixWord ++ tailWord_3134009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134009).length < 2 ^ (prefixWord ++ tailWord_3134009).sum := by decide
  have hdescent : baseEnd_3134009 < baseStart_3134009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134013 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_3134013 : Nat := 118140960795 + 3134013 * 2 ^ 59
def prefixEnd_3134013 : Nat := 4983230072969 + 3 ^ 40 * 3134013 * 2
def baseEnd_3134013 : Nat := 1609255046439351893424443

theorem tailTrace_3134013 : CollatzResearch.WordTrace tailWord_3134013 prefixEnd_3134013 1609255046439351893424443 := by
  unfold tailWord_3134013
  simp only [CollatzResearch.WordTrace]
  refine ⟨114306844795013622652334693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76204563196675748434889795 114306844795013622652334693)
  ·
    refine ⟨21432533399065054247312755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114306844795013622652334693 21432533399065054247312755)
    ·
      refine ⟨32148800098597581370969133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21432533399065054247312755 32148800098597581370969133)
      ·
        refine ⟨12055800036974093014113425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32148800098597581370969133 12055800036974093014113425)
        ·
          refine ⟨9041850027730569760585069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12055800036974093014113425 9041850027730569760585069)
          ·
            refine ⟨3390693760398963660219401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9041850027730569760585069 3390693760398963660219401)
            ·
              refine ⟨2543020320299222745164551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390693760398963660219401 2543020320299222745164551)
              ·
                refine ⟨3814530480448834117746827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543020320299222745164551 3814530480448834117746827)
                ·
                  refine ⟨5721795720673251176620241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814530480448834117746827 5721795720673251176620241)
                  ·
                    refine ⟨4291346790504938382465181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5721795720673251176620241 4291346790504938382465181)
                    ·
                      refine ⟨1609255046439351893424443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291346790504938382465181 1609255046439351893424443)
                      ·
                        rfl

theorem cell23_3134013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_3134013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134013 prefixEnd_3134013 := by exact prefixLift 3134013
  have htrace : WordTrace (prefixWord ++ tailWord_3134013) baseStart_3134013 baseEnd_3134013 := by
    simpa [prefixWord, tailWord_3134013, baseEnd_3134013] using wordTrace_append hprefix tailTrace_3134013
  have hstable : (prefixWord ++ tailWord_3134013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134013).length < 2 ^ (prefixWord ++ tailWord_3134013).sum := by decide
  have hdescent : baseEnd_3134013 < baseStart_3134013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134026 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_3134026 : Nat := 118140960795 + 3134026 * 2 ^ 59
def prefixEnd_3134026 : Nat := 4983230072969 + 3 ^ 40 * 3134026 * 2
def baseEnd_3134026 : Nat := 1609261721687860342561883

theorem tailTrace_3134026 : CollatzResearch.WordTrace tailWord_3134026 prefixEnd_3134026 1609261721687860342561883 := by
  unfold tailWord_3134026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28576829735991631468139483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76204879295977683915038621 28576829735991631468139483)
  ·
    refine ⟨42865244603987447202209225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28576829735991631468139483 42865244603987447202209225)
    ·
      refine ⟨32148933452990585401656919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42865244603987447202209225 32148933452990585401656919)
      ·
        refine ⟨48223400179485878102485379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32148933452990585401656919 48223400179485878102485379)
        ·
          refine ⟨72335100269228817153728069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48223400179485878102485379 72335100269228817153728069)
          ·
            refine ⟨13562831300480403216324013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72335100269228817153728069 13562831300480403216324013)
            ·
              refine ⟨5086061737680151206121505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13562831300480403216324013 5086061737680151206121505)
              ·
                refine ⟨3814546303260113404591129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5086061737680151206121505 3814546303260113404591129)
                ·
                  refine ⟨2860909727445085053443347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814546303260113404591129 2860909727445085053443347)
                  ·
                    refine ⟨4291364591167627580165021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2860909727445085053443347 4291364591167627580165021)
                    ·
                      refine ⟨1609261721687860342561883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291364591167627580165021 1609261721687860342561883)
                      ·
                        rfl

theorem cell23_3134026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_3134026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134026 prefixEnd_3134026 := by exact prefixLift 3134026
  have htrace : WordTrace (prefixWord ++ tailWord_3134026) baseStart_3134026 baseEnd_3134026 := by
    simpa [prefixWord, tailWord_3134026, baseEnd_3134026] using wordTrace_append hprefix tailTrace_3134026
  have hstable : (prefixWord ++ tailWord_3134026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134026).length < 2 ^ (prefixWord ++ tailWord_3134026).sum := by decide
  have hdescent : baseEnd_3134026 < baseStart_3134026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134052 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_3134052 : Nat := 118140960795 + 3134052 * 2 ^ 59
def prefixEnd_3134052 : Nat := 4983230072969 + 3 ^ 40 * 3134052 * 2
def baseEnd_3134052 : Nat := 1609275072184877240836763

theorem tailTrace_3134052 : CollatzResearch.WordTrace tailWord_3134052 prefixEnd_3134052 1609275072184877240836763 := by
  unfold tailWord_3134052
  simp only [CollatzResearch.WordTrace]
  refine ⟨57154133620936166156502205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76205511494581554875336273 57154133620936166156502205)
  ·
    refine ⟨21432800107851062308688327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57154133620936166156502205 21432800107851062308688327)
    ·
      refine ⟨32149200161776593463032491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21432800107851062308688327 32149200161776593463032491)
      ·
        refine ⟨48223800242664890194548737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32149200161776593463032491 48223800242664890194548737)
        ·
          refine ⟨36167850181998667645911553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48223800242664890194548737 36167850181998667645911553)
          ·
            refine ⟨27125887636499000734433665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36167850181998667645911553 27125887636499000734433665)
            ·
              refine ⟨20344415727374250550825249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27125887636499000734433665 20344415727374250550825249)
              ·
                refine ⟨15258311795530687913118937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20344415727374250550825249 15258311795530687913118937)
                ·
                  refine ⟨11443733846648015934839203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15258311795530687913118937 11443733846648015934839203)
                  ·
                    refine ⟨17165600769972023902258805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11443733846648015934839203 17165600769972023902258805)
                    ·
                      refine ⟨1609275072184877240836763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17165600769972023902258805 1609275072184877240836763)
                      ·
                        rfl

theorem cell23_3134052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_3134052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134052 prefixEnd_3134052 := by exact prefixLift 3134052
  have htrace : WordTrace (prefixWord ++ tailWord_3134052) baseStart_3134052 baseEnd_3134052 := by
    simpa [prefixWord, tailWord_3134052, baseEnd_3134052] using wordTrace_append hprefix tailTrace_3134052
  have hstable : (prefixWord ++ tailWord_3134052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134052).length < 2 ^ (prefixWord ++ tailWord_3134052).sum := by decide
  have hdescent : baseEnd_3134052 < baseStart_3134052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134053 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 1, 3, 2]
def baseStart_3134053 : Nat := 118140960795 + 3134053 * 2 ^ 59
def prefixEnd_3134053 : Nat := 4983230072969 + 3 ^ 40 * 3134053 * 2
def baseEnd_3134053 : Nat := 1609275585665531736924259

theorem tailTrace_3134053 : CollatzResearch.WordTrace tailWord_3134053 prefixEnd_3134053 1609275585665531736924259 := by
  unfold tailWord_3134053
  simp only [CollatzResearch.WordTrace]
  refine ⟨114308303714868709483790813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76205535809912472989193875 114308303714868709483790813)
  ·
    refine ⟨42865613893075766056421555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114308303714868709483790813 42865613893075766056421555)
    ·
      refine ⟨64298420839613649084632333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42865613893075766056421555 64298420839613649084632333)
      ·
        refine ⟨24111907814855118406737125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64298420839613649084632333 24111907814855118406737125)
        ·
          refine ⟨4520982715285334701263211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24111907814855118406737125 4520982715285334701263211)
          ·
            refine ⟨6781474072928002051894817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4520982715285334701263211 6781474072928002051894817)
            ·
              refine ⟨5086105554696001538921113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6781474072928002051894817 5086105554696001538921113)
              ·
                refine ⟨3814579166022001154190835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5086105554696001538921113 3814579166022001154190835)
                ·
                  refine ⟨5721868749033001731286253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814579166022001154190835 5721868749033001731286253)
                  ·
                    refine ⟨2145700780887375649232345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5721868749033001731286253 2145700780887375649232345)
                    ·
                      refine ⟨1609275585665531736924259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145700780887375649232345 1609275585665531736924259)
                      ·
                        rfl

theorem cell23_3134053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_3134053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134053 prefixEnd_3134053 := by exact prefixLift 3134053
  have htrace : WordTrace (prefixWord ++ tailWord_3134053) baseStart_3134053 baseEnd_3134053 := by
    simpa [prefixWord, tailWord_3134053, baseEnd_3134053] using wordTrace_append hprefix tailTrace_3134053
  have hstable : (prefixWord ++ tailWord_3134053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134053).length < 2 ^ (prefixWord ++ tailWord_3134053).sum := by decide
  have hdescent : baseEnd_3134053 < baseStart_3134053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134100 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_3134100 : Nat := 118140960795 + 3134100 * 2 ^ 59
def prefixEnd_3134100 : Nat := 4983230072969 + 3 ^ 40 * 3134100 * 2
def baseEnd_3134100 : Nat := 1609299719256293053036543

theorem tailTrace_3134100 : CollatzResearch.WordTrace tailWord_3134100 prefixEnd_3134100 1609299719256293053036543 := by
  unfold tailWord_3134100
  simp only [CollatzResearch.WordTrace]
  refine ⟨57155008972849218255375877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76206678630465624340501169 57155008972849218255375877)
  ·
    refine ⟨10716564182409228422882977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57155008972849218255375877 10716564182409228422882977)
    ·
      refine ⟨8037423136806921317162233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10716564182409228422882977 8037423136806921317162233)
      ·
        refine ⟨6028067352605190987871675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8037423136806921317162233 6028067352605190987871675)
        ·
          refine ⟨9042101028907786481807513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028067352605190987871675 9042101028907786481807513)
          ·
            refine ⟨6781575771680839861355635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9042101028907786481807513 6781575771680839861355635)
            ·
              refine ⟨10172363657521259792033453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781575771680839861355635 10172363657521259792033453)
              ·
                refine ⟨3814636371570472422012545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10172363657521259792033453 3814636371570472422012545)
                ·
                  refine ⟨2860977278677854316509409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814636371570472422012545 2860977278677854316509409)
                  ·
                    refine ⟨2145732959008390737382057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2860977278677854316509409 2145732959008390737382057)
                    ·
                      refine ⟨1609299719256293053036543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145732959008390737382057 1609299719256293053036543)
                      ·
                        rfl

theorem cell23_3134100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_3134100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134100 prefixEnd_3134100 := by exact prefixLift 3134100
  have htrace : WordTrace (prefixWord ++ tailWord_3134100) baseStart_3134100 baseEnd_3134100 := by
    simpa [prefixWord, tailWord_3134100, baseEnd_3134100] using wordTrace_append hprefix tailTrace_3134100
  have hstable : (prefixWord ++ tailWord_3134100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134100).length < 2 ^ (prefixWord ++ tailWord_3134100).sum := by decide
  have hdescent : baseEnd_3134100 < baseStart_3134100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134150 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3134150 : Nat := 118140960795 + 3134150 * 2 ^ 59
def prefixEnd_3134150 : Nat := 4983230072969 + 3 ^ 40 * 3134150 * 2
def baseEnd_3134150 : Nat := 1609325393289017857411313

theorem tailTrace_3134150 : CollatzResearch.WordTrace tailWord_3134150 prefixEnd_3134150 1609325393289017857411313 := by
  unfold tailWord_3134150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3572245049859915470314747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76207894397011530033381269 3572245049859915470314747)
  ·
    refine ⟨5358367574789873205472121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3572245049859915470314747 5358367574789873205472121)
    ·
      refine ⟨4018775681092404904104091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5358367574789873205472121 4018775681092404904104091)
      ·
        refine ⟨6028163521638607356156137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4018775681092404904104091 6028163521638607356156137)
        ·
          refine ⟨4521122641228955517117103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6028163521638607356156137 4521122641228955517117103)
          ·
            refine ⟨6781683961843433275675655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521122641228955517117103 6781683961843433275675655)
            ·
              refine ⟨10172525942765149913513483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781683961843433275675655 10172525942765149913513483)
              ·
                refine ⟨15258788914147724870270225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10172525942765149913513483 15258788914147724870270225)
                ·
                  refine ⟨11444091685610793652702669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15258788914147724870270225 11444091685610793652702669)
                  ·
                    refine ⟨4291534382104047619763501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11444091685610793652702669 4291534382104047619763501)
                    ·
                      refine ⟨1609325393289017857411313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291534382104047619763501 1609325393289017857411313)
                      ·
                        rfl

theorem cell23_3134150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3134150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134150 prefixEnd_3134150 := by exact prefixLift 3134150
  have htrace : WordTrace (prefixWord ++ tailWord_3134150) baseStart_3134150 baseEnd_3134150 := by
    simpa [prefixWord, tailWord_3134150, baseEnd_3134150] using wordTrace_append hprefix tailTrace_3134150
  have hstable : (prefixWord ++ tailWord_3134150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134150).length < 2 ^ (prefixWord ++ tailWord_3134150).sum := by decide
  have hdescent : baseEnd_3134150 < baseStart_3134150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134156 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3134156 : Nat := 118140960795 + 3134156 * 2 ^ 59
def prefixEnd_3134156 : Nat := 4983230072969 + 3 ^ 40 * 3134156 * 2
def baseEnd_3134156 : Nat := 1609328474172944833936285

theorem tailTrace_3134156 : CollatzResearch.WordTrace tailWord_3134156 prefixEnd_3134156 1609328474172944833936285 := by
  unfold tailWord_3134156
  simp only [CollatzResearch.WordTrace]
  refine ⟨57156030216747779037395161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76208040288997038716526881 57156030216747779037395161)
  ·
    refine ⟨42867022662560834278046371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57156030216747779037395161 42867022662560834278046371)
    ·
      refine ⟨64300533993841251417069557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42867022662560834278046371 64300533993841251417069557)
      ·
        refine ⟨6028175061922617320350271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64300533993841251417069557 6028175061922617320350271)
        ·
          refine ⟨9042262592883925980525407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028175061922617320350271 9042262592883925980525407)
          ·
            refine ⟨13563393889325888970788111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9042262592883925980525407 13563393889325888970788111)
            ·
              refine ⟨20345090833988833456182167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13563393889325888970788111 20345090833988833456182167)
              ·
                refine ⟨30517636250983250184273251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20345090833988833456182167 30517636250983250184273251)
                ·
                  refine ⟨45776454376474875276409877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30517636250983250184273251 45776454376474875276409877)
                  ·
                    refine ⟨2145771298897259778581713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45776454376474875276409877 2145771298897259778581713)
                    ·
                      refine ⟨1609328474172944833936285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145771298897259778581713 1609328474172944833936285)
                      ·
                        rfl

theorem cell23_3134156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3134156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134156 prefixEnd_3134156 := by exact prefixLift 3134156
  have htrace : WordTrace (prefixWord ++ tailWord_3134156) baseStart_3134156 baseEnd_3134156 := by
    simpa [prefixWord, tailWord_3134156, baseEnd_3134156] using wordTrace_append hprefix tailTrace_3134156
  have hstable : (prefixWord ++ tailWord_3134156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134156).length < 2 ^ (prefixWord ++ tailWord_3134156).sum := by decide
  have hdescent : baseEnd_3134156 < baseStart_3134156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134216 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_3134216 : Nat := 118140960795 + 3134216 * 2 ^ 59
def prefixEnd_3134216 : Nat := 4983230072969 + 3 ^ 40 * 3134216 * 2
def baseEnd_3134216 : Nat := 1609359283012214599186009

theorem tailTrace_3134216 : CollatzResearch.WordTrace tailWord_3134216 prefixEnd_3134216 1609359283012214599186009 := by
  unfold tailWord_3134216
  simp only [CollatzResearch.WordTrace]
  refine ⟨57157124406639094160987251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76209499208852125547983001 57157124406639094160987251)
  ·
    refine ⟨85735686609958641241480877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57157124406639094160987251 85735686609958641241480877)
    ·
      refine ⟨32150882478734490465555329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85735686609958641241480877 32150882478734490465555329)
      ·
        refine ⟨24113161859050867849166497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32150882478734490465555329 24113161859050867849166497)
        ·
          refine ⟨18084871394288150886874873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24113161859050867849166497 18084871394288150886874873)
          ·
            refine ⟨13563653545716113165156155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18084871394288150886874873 13563653545716113165156155)
            ·
              refine ⟨20345480318574169747734233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13563653545716113165156155 20345480318574169747734233)
              ·
                refine ⟨15259110238930627310800675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20345480318574169747734233 15259110238930627310800675)
                ·
                  refine ⟨22888665358395940966201013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15259110238930627310800675 22888665358395940966201013)
                  ·
                    refine ⟨2145812377349619465581345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22888665358395940966201013 2145812377349619465581345)
                    ·
                      refine ⟨1609359283012214599186009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145812377349619465581345 1609359283012214599186009)
                      ·
                        rfl

theorem cell23_3134216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_3134216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134216 prefixEnd_3134216 := by exact prefixLift 3134216
  have htrace : WordTrace (prefixWord ++ tailWord_3134216) baseStart_3134216 baseEnd_3134216 := by
    simpa [prefixWord, tailWord_3134216, baseEnd_3134216] using wordTrace_append hprefix tailTrace_3134216
  have hstable : (prefixWord ++ tailWord_3134216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134216).length < 2 ^ (prefixWord ++ tailWord_3134216).sum := by decide
  have hdescent : baseEnd_3134216 < baseStart_3134216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134240 : List Nat := [2, 1, 1, 5, 1, 2, 3, 3, 1, 1, 3]
def baseStart_3134240 : Nat := 118140960795 + 3134240 * 2 ^ 59
def prefixEnd_3134240 : Nat := 4983230072969 + 3 ^ 40 * 3134240 * 2
def baseEnd_3134240 : Nat := 1609371606547922505285899

theorem tailTrace_3134240 : CollatzResearch.WordTrace tailWord_3134240 prefixEnd_3134240 1609371606547922505285899 := by
  unfold tailWord_3134240
  simp only [CollatzResearch.WordTrace]
  refine ⟨57157562082595620210424087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76210082776794160280565449 57157562082595620210424087)
  ·
    refine ⟨85736343123893430315636131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57157562082595620210424087 85736343123893430315636131)
    ·
      refine ⟨128604514685840145473454197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85736343123893430315636131 128604514685840145473454197)
      ·
        refine ⟨12056673251797513638136331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128604514685840145473454197 12056673251797513638136331)
        ·
          refine ⟨18085009877696270457204497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12056673251797513638136331 18085009877696270457204497)
          ·
            refine ⟨13563757408272202842903373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18085009877696270457204497 13563757408272202842903373)
            ·
              refine ⟨5086409028102076066088765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13563757408272202842903373 5086409028102076066088765)
              ·
                refine ⟨1907403385538278524783287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5086409028102076066088765 1907403385538278524783287)
                ·
                  refine ⟨2861105078307417787174931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907403385538278524783287 2861105078307417787174931)
                  ·
                    refine ⟨4291657617461126680762397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2861105078307417787174931 4291657617461126680762397)
                    ·
                      refine ⟨1609371606547922505285899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291657617461126680762397 1609371606547922505285899)
                      ·
                        rfl

theorem cell23_3134240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_3134240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134240 prefixEnd_3134240 := by exact prefixLift 3134240
  have htrace : WordTrace (prefixWord ++ tailWord_3134240) baseStart_3134240 baseEnd_3134240 := by
    simpa [prefixWord, tailWord_3134240, baseEnd_3134240] using wordTrace_append hprefix tailTrace_3134240
  have hstable : (prefixWord ++ tailWord_3134240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134240).length < 2 ^ (prefixWord ++ tailWord_3134240).sum := by decide
  have hdescent : baseEnd_3134240 < baseStart_3134240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134259 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 6]
def baseStart_3134259 : Nat := 118140960795 + 3134259 * 2 ^ 59
def prefixEnd_3134259 : Nat := 4983230072969 + 3 ^ 40 * 3134259 * 2
def baseEnd_3134259 : Nat := 1609381362680357930948311

theorem tailTrace_3134259 : CollatzResearch.WordTrace tailWord_3134259 prefixEnd_3134259 1609381362680357930948311 := by
  unfold tailWord_3134259
  simp only [CollatzResearch.WordTrace]
  refine ⟨114315817152122406665789831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76210544768081604443859887 114315817152122406665789831)
  ·
    refine ⟨171473725728183609998684747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114315817152122406665789831 171473725728183609998684747)
    ·
      refine ⟨257210588592275414998027121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171473725728183609998684747 257210588592275414998027121)
      ·
        refine ⟨192907941444206561248520341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257210588592275414998027121 192907941444206561248520341)
        ·
          refine ⟨9042559755197182558524391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192907941444206561248520341 9042559755197182558524391)
          ·
            refine ⟨13563839632795773837786587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9042559755197182558524391 13563839632795773837786587)
            ·
              refine ⟨20345759449193660756679881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13563839632795773837786587 20345759449193660756679881)
              ·
                refine ⟨15259319586895245567509911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20345759449193660756679881 15259319586895245567509911)
                ·
                  refine ⟨22888979380342868351264867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15259319586895245567509911 22888979380342868351264867)
                  ·
                    refine ⟨34333469070514302526897301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22888979380342868351264867 34333469070514302526897301)
                    ·
                      refine ⟨1609381362680357930948311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34333469070514302526897301 1609381362680357930948311)
                      ·
                        rfl

theorem cell23_3134259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_3134259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134259 prefixEnd_3134259 := by exact prefixLift 3134259
  have htrace : WordTrace (prefixWord ++ tailWord_3134259) baseStart_3134259 baseEnd_3134259 := by
    simpa [prefixWord, tailWord_3134259, baseEnd_3134259] using wordTrace_append hprefix tailTrace_3134259
  have hstable : (prefixWord ++ tailWord_3134259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134259).length < 2 ^ (prefixWord ++ tailWord_3134259).sum := by decide
  have hdescent : baseEnd_3134259 < baseStart_3134259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134296 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3134296 : Nat := 118140960795 + 3134296 * 2 ^ 59
def prefixEnd_3134296 : Nat := 4983230072969 + 3 ^ 40 * 3134296 * 2
def baseEnd_3134296 : Nat := 1609400361464574286185641

theorem tailTrace_3134296 : CollatzResearch.WordTrace tailWord_3134296 prefixEnd_3134296 1609400361464574286185641 := by
  unfold tailWord_3134296
  simp only [CollatzResearch.WordTrace]
  refine ⟨57158583326494180992443371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76211444435325574656591161 57158583326494180992443371)
  ·
    refine ⟨85737874989741271488665057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57158583326494180992443371 85737874989741271488665057)
    ·
      refine ⟨64303406242305953616498793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85737874989741271488665057 64303406242305953616498793)
      ·
        refine ⟨48227554681729465212374095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64303406242305953616498793 48227554681729465212374095)
        ·
          refine ⟨72341332022594197818561143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48227554681729465212374095 72341332022594197818561143)
          ·
            refine ⟨108511998033891296727841715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72341332022594197818561143 108511998033891296727841715)
            ·
              refine ⟨162767997050836945091762573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108511998033891296727841715 162767997050836945091762573)
              ·
                refine ⟨61037998894063854409410965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162767997050836945091762573 61037998894063854409410965)
                ·
                  refine ⟨2861156198159243175441139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61037998894063854409410965 2861156198159243175441139)
                  ·
                    refine ⟨4291734297238864763161709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2861156198159243175441139 4291734297238864763161709)
                    ·
                      refine ⟨1609400361464574286185641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291734297238864763161709 1609400361464574286185641)
                      ·
                        rfl

theorem cell23_3134296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3134296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134296 prefixEnd_3134296 := by exact prefixLift 3134296
  have htrace : WordTrace (prefixWord ++ tailWord_3134296) baseStart_3134296 baseEnd_3134296 := by
    simpa [prefixWord, tailWord_3134296, baseEnd_3134296] using wordTrace_append hprefix tailTrace_3134296
  have hstable : (prefixWord ++ tailWord_3134296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134296).length < 2 ^ (prefixWord ++ tailWord_3134296).sum := by decide
  have hdescent : baseEnd_3134296 < baseStart_3134296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134309 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3134309 : Nat := 118140960795 + 3134309 * 2 ^ 59
def prefixEnd_3134309 : Nat := 4983230072969 + 3 ^ 40 * 3134309 * 2
def baseEnd_3134309 : Nat := 1609407036713082735323081

theorem tailTrace_3134309 : CollatzResearch.WordTrace tailWord_3134309 prefixEnd_3134309 1609407036713082735323081 := by
  unfold tailWord_3134309
  simp only [CollatzResearch.WordTrace]
  refine ⟨114317640801941265205109981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76211760534627510136739987 114317640801941265205109981)
  ·
    refine ⟨42869115300727974451916243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114317640801941265205109981 42869115300727974451916243)
    ·
      refine ⟨64303672951091961677874365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42869115300727974451916243 64303672951091961677874365)
      ·
        refine ⟨24113877356659485629202887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64303672951091961677874365 24113877356659485629202887)
        ·
          refine ⟨36170816034989228443804331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24113877356659485629202887 36170816034989228443804331)
          ·
            refine ⟨54256224052483842665706497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36170816034989228443804331 54256224052483842665706497)
            ·
              refine ⟨40692168039362881999279873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54256224052483842665706497 40692168039362881999279873)
              ·
                refine ⟨30519126029522161499459905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40692168039362881999279873 30519126029522161499459905)
                ·
                  refine ⟨22889344522141621124594929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30519126029522161499459905 22889344522141621124594929)
                  ·
                    refine ⟨17167008391606215843446197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22889344522141621124594929 17167008391606215843446197)
                    ·
                      refine ⟨1609407036713082735323081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17167008391606215843446197 1609407036713082735323081)
                      ·
                        rfl

theorem cell23_3134309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3134309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134309 prefixEnd_3134309 := by exact prefixLift 3134309
  have htrace : WordTrace (prefixWord ++ tailWord_3134309) baseStart_3134309 baseEnd_3134309 := by
    simpa [prefixWord, tailWord_3134309, baseEnd_3134309] using wordTrace_append hprefix tailTrace_3134309
  have hstable : (prefixWord ++ tailWord_3134309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134309).length < 2 ^ (prefixWord ++ tailWord_3134309).sum := by decide
  have hdescent : baseEnd_3134309 < baseStart_3134309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134329 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 1, 8]
def baseStart_3134329 : Nat := 118140960795 + 3134329 * 2 ^ 59
def prefixEnd_3134329 : Nat := 4983230072969 + 3 ^ 40 * 3134329 * 2
def baseEnd_3134329 : Nat := 536472435442057552357663

theorem tailTrace_3134329 : CollatzResearch.WordTrace tailWord_3134329 prefixEnd_3134329 536472435442057552357663 := by
  unfold tailWord_3134329
  simp only [CollatzResearch.WordTrace]
  refine ⟨114318370261868808620838041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76212246841245872413892027 114318370261868808620838041)
  ·
    refine ⟨85738777696401606465628531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114318370261868808620838041 85738777696401606465628531)
    ·
      refine ⟨128608166544602409698442797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85738777696401606465628531 128608166544602409698442797)
      ·
        refine ⟨48228062454225903636916049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128608166544602409698442797 48228062454225903636916049)
        ·
          refine ⟨36171046840669427727687037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48228062454225903636916049 36171046840669427727687037)
          ·
            refine ⟨13564142565251035397882639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36171046840669427727687037 13564142565251035397882639)
            ·
              refine ⟨20346213847876553096823959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13564142565251035397882639 20346213847876553096823959)
              ·
                refine ⟨30519320771814829645235939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20346213847876553096823959 30519320771814829645235939)
                ·
                  refine ⟨45778981157722244467853909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30519320771814829645235939 45778981157722244467853909)
                  ·
                    refine ⟨536472435442057552357663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45778981157722244467853909 536472435442057552357663)
                    ·
                      rfl

theorem cell23_3134329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_3134329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134329 prefixEnd_3134329 := by exact prefixLift 3134329
  have htrace : WordTrace (prefixWord ++ tailWord_3134329) baseStart_3134329 baseEnd_3134329 := by
    simpa [prefixWord, tailWord_3134329, baseEnd_3134329] using wordTrace_append hprefix tailTrace_3134329
  have hstable : (prefixWord ++ tailWord_3134329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134329).length < 2 ^ (prefixWord ++ tailWord_3134329).sum := by decide
  have hdescent : baseEnd_3134329 < baseStart_3134329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134353 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 4, 2, 2]
def baseStart_3134353 : Nat := 118140960795 + 3134353 * 2 ^ 59
def prefixEnd_3134353 : Nat := 4983230072969 + 3 ^ 40 * 3134353 * 2
def baseEnd_3134353 : Nat := 1609429629861880563172879

theorem tailTrace_3134353 : CollatzResearch.WordTrace tailWord_3134353 prefixEnd_3134353 1609429629861880563172879 := by
  unfold tailWord_3134353
  simp only [CollatzResearch.WordTrace]
  refine ⟨114319245613781860719711713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76212830409187907146474475 114319245613781860719711713)
  ·
    refine ⟨85739434210336395539783785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114319245613781860719711713 85739434210336395539783785)
    ·
      refine ⟨64304575657752296654837839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85739434210336395539783785 64304575657752296654837839)
      ·
        refine ⟨96456863486628444982256759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64304575657752296654837839 96456863486628444982256759)
        ·
          refine ⟨144685295229942667473385139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96456863486628444982256759 144685295229942667473385139)
          ·
            refine ⟨217027942844914001210077709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144685295229942667473385139 217027942844914001210077709)
            ·
              refine ⟨81385478566842750453779141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217027942844914001210077709 81385478566842750453779141)
              ·
                refine ⟨15259777231283015710083589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81385478566842750453779141 15259777231283015710083589)
                ·
                  refine ⟨2861208230865565445640673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15259777231283015710083589 2861208230865565445640673)
                  ·
                    refine ⟨2145906173149174084230505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861208230865565445640673 2145906173149174084230505)
                    ·
                      refine ⟨1609429629861880563172879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145906173149174084230505 1609429629861880563172879)
                      ·
                        rfl

theorem cell23_3134353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_3134353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134353 prefixEnd_3134353 := by exact prefixLift 3134353
  have htrace : WordTrace (prefixWord ++ tailWord_3134353) baseStart_3134353 baseEnd_3134353 := by
    simpa [prefixWord, tailWord_3134353, baseEnd_3134353] using wordTrace_append hprefix tailTrace_3134353
  have hstable : (prefixWord ++ tailWord_3134353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134353).length < 2 ^ (prefixWord ++ tailWord_3134353).sum := by decide
  have hdescent : baseEnd_3134353 < baseStart_3134353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134356 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3134356 : Nat := 118140960795 + 3134356 * 2 ^ 59
def prefixEnd_3134356 : Nat := 4983230072969 + 3 ^ 40 * 3134356 * 2
def baseEnd_3134356 : Nat := 1609431170303844051435365

theorem tailTrace_3134356 : CollatzResearch.WordTrace tailWord_3134356 prefixEnd_3134356 1609431170303844051435365 := by
  unfold tailWord_3134356
  simp only [CollatzResearch.WordTrace]
  refine ⟨57159677516385496116035461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76212903355180661488047281 57159677516385496116035461)
  ·
    refine ⟨10717439534322280521756649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57159677516385496116035461 10717439534322280521756649)
    ·
      refine ⟨8038079650741710391317487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10717439534322280521756649 8038079650741710391317487)
      ·
        refine ⟨12057119476112565586976231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8038079650741710391317487 12057119476112565586976231)
        ·
          refine ⟨18085679214168848380464347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12057119476112565586976231 18085679214168848380464347)
          ·
            refine ⟨27128518821253272570696521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18085679214168848380464347 27128518821253272570696521)
            ·
              refine ⟨20346389115939954428022391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27128518821253272570696521 20346389115939954428022391)
              ·
                refine ⟨30519583673909931642033587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20346389115939954428022391 30519583673909931642033587)
                ·
                  refine ⟨45779375510864897463050381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30519583673909931642033587 45779375510864897463050381)
                  ·
                    refine ⟨17167265816574336548643893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45779375510864897463050381 17167265816574336548643893)
                    ·
                      refine ⟨1609431170303844051435365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17167265816574336548643893 1609431170303844051435365)
                      ·
                        rfl

theorem cell23_3134356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3134356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134356 prefixEnd_3134356 := by exact prefixLift 3134356
  have htrace : WordTrace (prefixWord ++ tailWord_3134356) baseStart_3134356 baseEnd_3134356 := by
    simpa [prefixWord, tailWord_3134356, baseEnd_3134356] using wordTrace_append hprefix tailTrace_3134356
  have hstable : (prefixWord ++ tailWord_3134356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134356).length < 2 ^ (prefixWord ++ tailWord_3134356).sum := by decide
  have hdescent : baseEnd_3134356 < baseStart_3134356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134357 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_3134357 : Nat := 118140960795 + 3134357 * 2 ^ 59
def prefixEnd_3134357 : Nat := 4983230072969 + 3 ^ 40 * 3134357 * 2
def baseEnd_3134357 : Nat := 1609431683784498547522861

theorem tailTrace_3134357 : CollatzResearch.WordTrace tailWord_3134357 prefixEnd_3134357 1609431683784498547522861 := by
  unfold tailWord_3134357
  simp only [CollatzResearch.WordTrace]
  refine ⟨114319391505767369402857325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76212927670511579601904883 114319391505767369402857325)
  ·
    refine ⟨42869771814662763526071497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114319391505767369402857325 42869771814662763526071497)
    ·
      refine ⟨32152328860997072644553623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42869771814662763526071497 32152328860997072644553623)
      ·
        refine ⟨48228493291495608966830435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32152328860997072644553623 48228493291495608966830435)
        ·
          refine ⟨72342739937243413450245653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48228493291495608966830435 72342739937243413450245653)
          ·
            refine ⟨3391065934558285005480265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72342739937243413450245653 3391065934558285005480265)
            ·
              refine ⟨2543299450918713754110199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3391065934558285005480265 2543299450918713754110199)
              ·
                refine ⟨3814949176378070631165299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543299450918713754110199 3814949176378070631165299)
                ·
                  refine ⟨5722423764567105946747949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814949176378070631165299 5722423764567105946747949)
                  ·
                    refine ⟨2145908911712664730030481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5722423764567105946747949 2145908911712664730030481)
                    ·
                      refine ⟨1609431683784498547522861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2145908911712664730030481 1609431683784498547522861)
                      ·
                        rfl

theorem cell23_3134357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_3134357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134357 prefixEnd_3134357 := by exact prefixLift 3134357
  have htrace : WordTrace (prefixWord ++ tailWord_3134357) baseStart_3134357 baseEnd_3134357 := by
    simpa [prefixWord, tailWord_3134357, baseEnd_3134357] using wordTrace_append hprefix tailTrace_3134357
  have hstable : (prefixWord ++ tailWord_3134357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134357).length < 2 ^ (prefixWord ++ tailWord_3134357).sum := by decide
  have hdescent : baseEnd_3134357 < baseStart_3134357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134359 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 9]
def baseStart_3134359 : Nat := 118140960795 + 3134359 * 2 ^ 59
def prefixEnd_3134359 : Nat := 4983230072969 + 3 ^ 40 * 3134359 * 2
def baseEnd_3134359 : Nat := 178825856749534171077539

theorem tailTrace_3134359 : CollatzResearch.WordTrace tailWord_3134359 prefixEnd_3134359 178825856749534171077539 := by
  unfold tailWord_3134359
  simp only [CollatzResearch.WordTrace]
  refine ⟨114319464451760123744430131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76212976301173415829620087 114319464451760123744430131)
  ·
    refine ⟨171479196677640185616645197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114319464451760123744430131 171479196677640185616645197)
    ·
      refine ⟨64304698754115069606241949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171479196677640185616645197 64304698754115069606241949)
      ·
        refine ⟨24114262032793151102340731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64304698754115069606241949 24114262032793151102340731)
        ·
          refine ⟨36171393049189726653511097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24114262032793151102340731 36171393049189726653511097)
          ·
            refine ⟨27128544786892294990133323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36171393049189726653511097 27128544786892294990133323)
            ·
              refine ⟨40692817180338442485199985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27128544786892294990133323 40692817180338442485199985)
              ·
                refine ⟨30519612885253831863899989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40692817180338442485199985 30519612885253831863899989)
                ·
                  refine ⟨178825856749534171077539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30519612885253831863899989 178825856749534171077539)
                  ·
                    rfl

theorem cell23_3134359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 9].length) (baseStart_3134359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134359 prefixEnd_3134359 := by exact prefixLift 3134359
  have htrace : WordTrace (prefixWord ++ tailWord_3134359) baseStart_3134359 baseEnd_3134359 := by
    simpa [prefixWord, tailWord_3134359, baseEnd_3134359] using wordTrace_append hprefix tailTrace_3134359
  have hstable : (prefixWord ++ tailWord_3134359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134359).length < 2 ^ (prefixWord ++ tailWord_3134359).sum := by decide
  have hdescent : baseEnd_3134359 < baseStart_3134359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134364 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3134364 : Nat := 118140960795 + 3134364 * 2 ^ 59
def prefixEnd_3134364 : Nat := 4983230072969 + 3 ^ 40 * 3134364 * 2
def baseEnd_3134364 : Nat := 1609435278149080020135329

theorem tailTrace_3134364 : CollatzResearch.WordTrace tailWord_3134364 prefixEnd_3134364 1609435278149080020135329 := by
  unfold tailWord_3134364
  simp only [CollatzResearch.WordTrace]
  refine ⟨57159823408371004799181073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76213097877828006398908097 57159823408371004799181073)
  ·
    refine ⟨42869867556278253599385805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57159823408371004799181073 42869867556278253599385805)
    ·
      refine ⟨16076200333604345099769677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42869867556278253599385805 16076200333604345099769677)
      ·
        refine ⟨6028575125101629412413629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16076200333604345099769677 6028575125101629412413629)
        ·
          refine ⟨2260715671913111029655111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6028575125101629412413629 2260715671913111029655111)
          ·
            refine ⟨3391073507869666544482667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260715671913111029655111 3391073507869666544482667)
            ·
              refine ⟨5086610261804499816724001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391073507869666544482667 5086610261804499816724001)
              ·
                refine ⟨3814957696353374862543001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5086610261804499816724001 3814957696353374862543001)
                ·
                  refine ⟨2861218272265031146907251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3814957696353374862543001 2861218272265031146907251)
                  ·
                    refine ⟨4291827408397546720360877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2861218272265031146907251 4291827408397546720360877)
                    ·
                      refine ⟨1609435278149080020135329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4291827408397546720360877 1609435278149080020135329)
                      ·
                        rfl

theorem cell23_3134364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3134364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134364 prefixEnd_3134364 := by exact prefixLift 3134364
  have htrace : WordTrace (prefixWord ++ tailWord_3134364) baseStart_3134364 baseEnd_3134364 := by
    simpa [prefixWord, tailWord_3134364, baseEnd_3134364] using wordTrace_append hprefix tailTrace_3134364
  have hstable : (prefixWord ++ tailWord_3134364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134364).length < 2 ^ (prefixWord ++ tailWord_3134364).sum := by decide
  have hdescent : baseEnd_3134364 < baseStart_3134364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134399 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_3134399 : Nat := 118140960795 + 3134399 * 2 ^ 59
def prefixEnd_3134399 : Nat := 4983230072969 + 3 ^ 40 * 3134399 * 2
def baseEnd_3134399 : Nat := 1609453249971987383197667

theorem tailTrace_3134399 : CollatzResearch.WordTrace tailWord_3134399 prefixEnd_3134399 1609453249971987383197667 := by
  unfold tailWord_3134399
  simp only [CollatzResearch.WordTrace]
  refine ⟨114320923371615210575886251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76213948914410140383924167 114320923371615210575886251)
  ·
    refine ⟨171481385057422815863829377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114320923371615210575886251 171481385057422815863829377)
    ·
      refine ⟨128611038793067111897872033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171481385057422815863829377 128611038793067111897872033)
      ·
        refine ⟨96458279094800333923404025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128611038793067111897872033 96458279094800333923404025)
        ·
          refine ⟨72343709321100250442553019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96458279094800333923404025 72343709321100250442553019)
          ·
            refine ⟨108515563981650375663829529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72343709321100250442553019 108515563981650375663829529)
            ·
              refine ⟨81386672986237781747872147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108515563981650375663829529 81386672986237781747872147)
              ·
                refine ⟨122080009479356672621808221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81386672986237781747872147 122080009479356672621808221)
                ·
                  refine ⟨45780003554758752233178083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122080009479356672621808221 45780003554758752233178083)
                  ·
                    refine ⟨68670005332138128349767125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45780003554758752233178083 68670005332138128349767125)
                    ·
                      refine ⟨1609453249971987383197667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68670005332138128349767125 1609453249971987383197667)
                      ·
                        rfl

theorem cell23_3134399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_3134399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134399 prefixEnd_3134399 := by exact prefixLift 3134399
  have htrace : WordTrace (prefixWord ++ tailWord_3134399) baseStart_3134399 baseEnd_3134399 := by
    simpa [prefixWord, tailWord_3134399, baseEnd_3134399] using wordTrace_append hprefix tailTrace_3134399
  have hstable : (prefixWord ++ tailWord_3134399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134399).length < 2 ^ (prefixWord ++ tailWord_3134399).sum := by decide
  have hdescent : baseEnd_3134399 < baseStart_3134399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134487 : List Nat := [1, 1, 3, 5, 1, 2, 1, 4, 1, 4]
def baseStart_3134487 : Nat := 118140960795 + 3134487 * 2 ^ 59
def prefixEnd_3134487 : Nat := 4983230072969 + 3 ^ 40 * 3134487 * 2
def baseEnd_3134487 : Nat := 536499478756527679632421

theorem tailTrace_3134487 : CollatzResearch.WordTrace tailWord_3134487 prefixEnd_3134487 536499478756527679632421 := by
  unfold tailWord_3134487
  simp only [CollatzResearch.WordTrace]
  refine ⟨114324132995296401605089715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76216088663530934403393143 114324132995296401605089715)
  ·
    refine ⟨171486199492944602407634573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114324132995296401605089715 171486199492944602407634573)
    ·
      refine ⟨64307324809854225902862965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171486199492944602407634573 64307324809854225902862965)
      ·
        refine ⟨6028811700923833678393403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64307324809854225902862965 6028811700923833678393403)
        ·
          refine ⟨9043217551385750517590105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028811700923833678393403 9043217551385750517590105)
          ·
            refine ⟨6782413163539312888192579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9043217551385750517590105 6782413163539312888192579)
            ·
              refine ⟨10173619745308969332288869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782413163539312888192579 10173619745308969332288869)
              ·
                refine ⟨1907553702245431749804163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10173619745308969332288869 1907553702245431749804163)
                ·
                  refine ⟨2861330553368147624706245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907553702245431749804163 2861330553368147624706245)
                  ·
                    refine ⟨536499478756527679632421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2861330553368147624706245 536499478756527679632421)
                    ·
                      rfl

theorem cell23_3134487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_3134487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134487 prefixEnd_3134487 := by exact prefixLift 3134487
  have htrace : WordTrace (prefixWord ++ tailWord_3134487) baseStart_3134487 baseEnd_3134487 := by
    simpa [prefixWord, tailWord_3134487, baseEnd_3134487] using wordTrace_append hprefix tailTrace_3134487
  have hstable : (prefixWord ++ tailWord_3134487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134487).length < 2 ^ (prefixWord ++ tailWord_3134487).sum := by decide
  have hdescent : baseEnd_3134487 < baseStart_3134487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134513 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 1, 5]
def baseStart_3134513 : Nat := 118140960795 + 3134513 * 2 ^ 59
def prefixEnd_3134513 : Nat := 4983230072969 + 3 ^ 40 * 3134513 * 2
def baseEnd_3134513 : Nat := 536503928922199979057381

theorem tailTrace_3134513 : CollatzResearch.WordTrace tailWord_3134513 prefixEnd_3134513 536503928922199979057381 := by
  unfold tailWord_3134513
  simp only [CollatzResearch.WordTrace]
  refine ⟨114325081293202208045536193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76216720862134805363690795 114325081293202208045536193)
  ·
    refine ⟨85743810969901656034152145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114325081293202208045536193 85743810969901656034152145)
    ·
      refine ⟨64307858227426242025614109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85743810969901656034152145 64307858227426242025614109)
      ·
        refine ⟨24115446835284840759605291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64307858227426242025614109 24115446835284840759605291)
        ·
          refine ⟨36173170252927261139407937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24115446835284840759605291 36173170252927261139407937)
          ·
            refine ⟨27129877689695445854555953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36173170252927261139407937 27129877689695445854555953)
            ·
              refine ⟨20347408267271584390916965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27129877689695445854555953 20347408267271584390916965)
              ·
                refine ⟨3815139050113422073296931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20347408267271584390916965 3815139050113422073296931)
                ·
                  refine ⟨5722708575170133109945397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815139050113422073296931 5722708575170133109945397)
                  ·
                    refine ⟨536503928922199979057381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5722708575170133109945397 536503928922199979057381)
                    ·
                      rfl

theorem cell23_3134513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_3134513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134513 prefixEnd_3134513 := by exact prefixLift 3134513
  have htrace : WordTrace (prefixWord ++ tailWord_3134513) baseStart_3134513 baseEnd_3134513 := by
    simpa [prefixWord, tailWord_3134513, baseEnd_3134513] using wordTrace_append hprefix tailTrace_3134513
  have hstable : (prefixWord ++ tailWord_3134513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134513).length < 2 ^ (prefixWord ++ tailWord_3134513).sum := by decide
  have hdescent : baseEnd_3134513 < baseStart_3134513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134520 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 1, 5, 2]
def baseStart_3134520 : Nat := 118140960795 + 3134520 * 2 ^ 59
def prefixEnd_3134520 : Nat := 4983230072969 + 3 ^ 40 * 3134520 * 2
def baseEnd_3134520 : Nat := 1609515381131181409784611

theorem tailTrace_3134520 : CollatzResearch.WordTrace tailWord_3134520 prefixEnd_3134520 1609515381131181409784611 := by
  unfold tailWord_3134520
  simp only [CollatzResearch.WordTrace]
  refine ⟨57162668302088424120520507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76216891069451232160694009 57162668302088424120520507)
  ·
    refine ⟨85744002453132636180780761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57162668302088424120520507 85744002453132636180780761)
    ·
      refine ⟨64308001839849477135585571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85744002453132636180780761 64308001839849477135585571)
      ·
        refine ⟨96462002759774215703378357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64308001839849477135585571 96462002759774215703378357)
        ·
          refine ⟨9043312758728832722191721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96462002759774215703378357 9043312758728832722191721)
          ·
            refine ⟨6782484569046624541643791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9043312758728832722191721 6782484569046624541643791)
            ·
              refine ⟨10173726853569936812465687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782484569046624541643791 10173726853569936812465687)
              ·
                refine ⟨15260590280354905218698531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10173726853569936812465687 15260590280354905218698531)
                ·
                  refine ⟨22890885420532357828047797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15260590280354905218698531 22890885420532357828047797)
                  ·
                    refine ⟨2146020508174908546379481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22890885420532357828047797 2146020508174908546379481)
                    ·
                      refine ⟨1609515381131181409784611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146020508174908546379481 1609515381131181409784611)
                      ·
                        rfl

theorem cell23_3134520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_3134520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134520 prefixEnd_3134520 := by exact prefixLift 3134520
  have htrace : WordTrace (prefixWord ++ tailWord_3134520) baseStart_3134520 baseEnd_3134520 := by
    simpa [prefixWord, tailWord_3134520, baseEnd_3134520] using wordTrace_append hprefix tailTrace_3134520
  have hstable : (prefixWord ++ tailWord_3134520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134520).length < 2 ^ (prefixWord ++ tailWord_3134520).sum := by decide
  have hdescent : baseEnd_3134520 < baseStart_3134520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134553 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 3]
def baseStart_3134553 : Nat := 118140960795 + 3134553 * 2 ^ 59
def prefixEnd_3134553 : Nat := 4983230072969 + 3 ^ 40 * 3134553 * 2
def baseEnd_3134553 : Nat := 1609532325992779780671959

theorem tailTrace_3134553 : CollatzResearch.WordTrace tailWord_3134553 prefixEnd_3134553 1609532325992779780671959 := by
  unfold tailWord_3134553
  simp only [CollatzResearch.WordTrace]
  refine ⟨114326540213057294876992313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76217693475371529917994875 114326540213057294876992313)
  ·
    refine ⟨85744905159792971157744235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114326540213057294876992313 85744905159792971157744235)
    ·
      refine ⟨128617357739689456736616353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85744905159792971157744235 128617357739689456736616353)
      ·
        refine ⟨96463018304767092552462265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128617357739689456736616353 96463018304767092552462265)
        ·
          refine ⟨72347263728575319414346699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96463018304767092552462265 72347263728575319414346699)
          ·
            refine ⟨108520895592862979121520049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72347263728575319414346699 108520895592862979121520049)
            ·
              refine ⟨81390671694647234341140037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108520895592862979121520049 81390671694647234341140037)
              ·
                refine ⟨15260750942746356438963757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81390671694647234341140037 15260750942746356438963757)
                ·
                  refine ⟨5722781603529883664611409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15260750942746356438963757 5722781603529883664611409)
                  ·
                    refine ⟨4292086202647412748458557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5722781603529883664611409 4292086202647412748458557)
                    ·
                      refine ⟨1609532325992779780671959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4292086202647412748458557 1609532325992779780671959)
                      ·
                        rfl

theorem cell23_3134553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_3134553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134553 prefixEnd_3134553 := by exact prefixLift 3134553
  have htrace : WordTrace (prefixWord ++ tailWord_3134553) baseStart_3134553 baseEnd_3134553 := by
    simpa [prefixWord, tailWord_3134553, baseEnd_3134553] using wordTrace_append hprefix tailTrace_3134553
  have hstable : (prefixWord ++ tailWord_3134553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134553).length < 2 ^ (prefixWord ++ tailWord_3134553).sum := by decide
  have hdescent : baseEnd_3134553 < baseStart_3134553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134567 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_3134567 : Nat := 118140960795 + 3134567 * 2 ^ 59
def prefixEnd_3134567 : Nat := 4983230072969 + 3 ^ 40 * 3134567 * 2
def baseEnd_3134567 : Nat := 1609539514721942725896895

theorem tailTrace_3134567 : CollatzResearch.WordTrace tailWord_3134567 prefixEnd_3134567 1609539514721942725896895 := by
  unfold tailWord_3134567
  simp only [CollatzResearch.WordTrace]
  refine ⟨114327050835006575268001955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76218033890004383512001303 114327050835006575268001955)
  ·
    refine ⟨171490576252509862902002933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114327050835006575268001955 171490576252509862902002933)
    ·
      refine ⟨16077241523672799647062775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171490576252509862902002933 16077241523672799647062775)
      ·
        refine ⟨24115862285509199470594163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077241523672799647062775 24115862285509199470594163)
        ·
          refine ⟨36173793428263799205891245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24115862285509199470594163 36173793428263799205891245)
          ·
            refine ⟨13565172535598924702209217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36173793428263799205891245 13565172535598924702209217)
            ·
              refine ⟨10173879401699193526656913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13565172535598924702209217 10173879401699193526656913)
              ·
                refine ⟨7630409551274395144992685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10173879401699193526656913 7630409551274395144992685)
                ·
                  refine ⟨2861403581727898179372257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7630409551274395144992685 2861403581727898179372257)
                  ·
                    refine ⟨2146052686295923634529193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861403581727898179372257 2146052686295923634529193)
                    ·
                      refine ⟨1609539514721942725896895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146052686295923634529193 1609539514721942725896895)
                      ·
                        rfl

theorem cell23_3134567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_3134567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134567 prefixEnd_3134567 := by exact prefixLift 3134567
  have htrace : WordTrace (prefixWord ++ tailWord_3134567) baseStart_3134567 baseEnd_3134567 := by
    simpa [prefixWord, tailWord_3134567, baseEnd_3134567] using wordTrace_append hprefix tailTrace_3134567
  have hstable : (prefixWord ++ tailWord_3134567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134567).length < 2 ^ (prefixWord ++ tailWord_3134567).sum := by decide
  have hdescent : baseEnd_3134567 < baseStart_3134567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134573 : List Nat := [1, 5, 1, 1, 2, 3, 1, 9]
def baseStart_3134573 : Nat := 118140960795 + 3134573 * 2 ^ 59
def prefixEnd_3134573 : Nat := 4983230072969 + 3 ^ 40 * 3134573 * 2
def baseEnd_3134573 : Nat := 59612688726143322311921

theorem tailTrace_3134573 : CollatzResearch.WordTrace tailWord_3134573 prefixEnd_3134573 59612688726143322311921 := by
  unfold tailWord_3134573
  simp only [CollatzResearch.WordTrace]
  refine ⟨114327269672984838292720373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76218179781989892195146915 114327269672984838292720373)
  ·
    refine ⟨10718181531842328589942535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114327269672984838292720373 10718181531842328589942535)
    ·
      refine ⟨16077272297763492884913803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718181531842328589942535 16077272297763492884913803)
      ·
        refine ⟨24115908446645239327370705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077272297763492884913803 24115908446645239327370705)
        ·
          refine ⟨18086931334983929495528029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24115908446645239327370705 18086931334983929495528029)
          ·
            refine ⟨6782599250618973560823011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18086931334983929495528029 6782599250618973560823011)
            ·
              refine ⟨10173898875928460341234517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782599250618973560823011 10173898875928460341234517)
              ·
                refine ⟨59612688726143322311921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10173898875928460341234517 59612688726143322311921)
                ·
                  rfl

theorem cell23_3134573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 9].length) (baseStart_3134573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134573 prefixEnd_3134573 := by exact prefixLift 3134573
  have htrace : WordTrace (prefixWord ++ tailWord_3134573) baseStart_3134573 baseEnd_3134573 := by
    simpa [prefixWord, tailWord_3134573, baseEnd_3134573] using wordTrace_append hprefix tailTrace_3134573
  have hstable : (prefixWord ++ tailWord_3134573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134573).length < 2 ^ (prefixWord ++ tailWord_3134573).sum := by decide
  have hdescent : baseEnd_3134573 < baseStart_3134573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134583 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_3134583 : Nat := 118140960795 + 3134583 * 2 ^ 59
def prefixEnd_3134583 : Nat := 4983230072969 + 3 ^ 40 * 3134583 * 2
def baseEnd_3134583 : Nat := 1609547730412414663296821

theorem tailTrace_3134583 : CollatzResearch.WordTrace tailWord_3134583 prefixEnd_3134583 1609547730412414663296821 := by
  unfold tailWord_3134583
  simp only [CollatzResearch.WordTrace]
  refine ⟨114327634402948610000584403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76218422935299073333722935 114327634402948610000584403)
  ·
    refine ⟨171491451604422915000876605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114327634402948610000584403 171491451604422915000876605)
    ·
      refine ⟨64309294351658593125328727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171491451604422915000876605 64309294351658593125328727)
      ·
        refine ⟨96463941527487889687993091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64309294351658593125328727 96463941527487889687993091)
        ·
          refine ⟨144695912291231834531989637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96463941527487889687993091 144695912291231834531989637)
          ·
            refine ⟨27130483554605968974748057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144695912291231834531989637 27130483554605968974748057)
            ·
              refine ⟨20347862665954476731061043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27130483554605968974748057 20347862665954476731061043)
              ·
                refine ⟨30521793998931715096591565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20347862665954476731061043 30521793998931715096591565)
                ·
                  refine ⟨11445672749599393161221837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30521793998931715096591565 11445672749599393161221837)
                  ·
                    refine ⟨4292127281099772435458189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11445672749599393161221837 4292127281099772435458189)
                    ·
                      refine ⟨1609547730412414663296821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4292127281099772435458189 1609547730412414663296821)
                      ·
                        rfl

theorem cell23_3134583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_3134583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134583 prefixEnd_3134583 := by exact prefixLift 3134583
  have htrace : WordTrace (prefixWord ++ tailWord_3134583) baseStart_3134583 baseEnd_3134583 := by
    simpa [prefixWord, tailWord_3134583, baseEnd_3134583] using wordTrace_append hprefix tailTrace_3134583
  have hstable : (prefixWord ++ tailWord_3134583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134583).length < 2 ^ (prefixWord ++ tailWord_3134583).sum := by decide
  have hdescent : baseEnd_3134583 < baseStart_3134583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134584 : List Nat := [2, 1, 2, 1, 1, 1, 7, 3, 1, 2, 2]
def baseStart_3134584 : Nat := 118140960795 + 3134584 * 2 ^ 59
def prefixEnd_3134584 : Nat := 4983230072969 + 3 ^ 40 * 3134584 * 2
def baseEnd_3134584 : Nat := 1609548243893069159384317

theorem tailTrace_3134584 : CollatzResearch.WordTrace tailWord_3134584 prefixEnd_3134584 1609548243893069159384317 := by
  unfold tailWord_3134584
  simp only [CollatzResearch.WordTrace]
  refine ⟨57163835437972493585685403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76218447250629991447580537 57163835437972493585685403)
  ·
    refine ⟨85745753156958740378528105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57163835437972493585685403 85745753156958740378528105)
    ·
      refine ⟨64309314867719055283896079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85745753156958740378528105 64309314867719055283896079)
      ·
        refine ⟨96463972301578582925844119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64309314867719055283896079 96463972301578582925844119)
        ·
          refine ⟨144695958452367874388766179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96463972301578582925844119 144695958452367874388766179)
          ·
            refine ⟨217043937678551811583149269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144695958452367874388766179 217043937678551811583149269)
            ·
              refine ⟨5086967289341058083980061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 217043937678551811583149269 5086967289341058083980061)
              ·
                refine ⟨1907612733502896781492523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5086967289341058083980061 1907612733502896781492523)
                ·
                  refine ⟨2861419100254345172238785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907612733502896781492523 2861419100254345172238785)
                  ·
                    refine ⟨2146064325190758879179089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861419100254345172238785 2146064325190758879179089)
                    ·
                      refine ⟨1609548243893069159384317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146064325190758879179089 1609548243893069159384317)
                      ·
                        rfl

theorem cell23_3134584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_3134584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134584 prefixEnd_3134584 := by exact prefixLift 3134584
  have htrace : WordTrace (prefixWord ++ tailWord_3134584) baseStart_3134584 baseEnd_3134584 := by
    simpa [prefixWord, tailWord_3134584, baseEnd_3134584] using wordTrace_append hprefix tailTrace_3134584
  have hstable : (prefixWord ++ tailWord_3134584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134584).length < 2 ^ (prefixWord ++ tailWord_3134584).sum := by decide
  have hdescent : baseEnd_3134584 < baseStart_3134584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134601 : List Nat := [1, 2, 1, 1, 4, 4, 3, 2, 1, 2, 2]
def baseStart_3134601 : Nat := 118140960795 + 3134601 * 2 ^ 59
def prefixEnd_3134601 : Nat := 4983230072969 + 3 ^ 40 * 3134601 * 2
def baseEnd_3134601 : Nat := 1609556973064195592871739

theorem tailTrace_3134601 : CollatzResearch.WordTrace tailWord_3134601 prefixEnd_3134601 1609556973064195592871739 := by
  unfold tailWord_3134601
  simp only [CollatzResearch.WordTrace]
  refine ⟨114328290916883399074739657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76218860611255599383159771 114328290916883399074739657)
  ·
    refine ⟨85746218187662549306054743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114328290916883399074739657 85746218187662549306054743)
    ·
      refine ⟨128619327281493823959082115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85746218187662549306054743 128619327281493823959082115)
      ·
        refine ⟨192928990922240735938623173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128619327281493823959082115 192928990922240735938623173)
        ·
          refine ⟨36174185797920137988491845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192928990922240735938623173 36174185797920137988491845)
          ·
            refine ⟨6782659837110025872842221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36174185797920137988491845 6782659837110025872842221)
            ·
              refine ⟨2543497438916259702315833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6782659837110025872842221 2543497438916259702315833)
              ·
                refine ⟨1907623079187194776736875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2543497438916259702315833 1907623079187194776736875)
                ·
                  refine ⟨2861434618780792165105313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907623079187194776736875 2861434618780792165105313)
                  ·
                    refine ⟨2146075964085594123828985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861434618780792165105313 2146075964085594123828985)
                    ·
                      refine ⟨1609556973064195592871739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146075964085594123828985 1609556973064195592871739)
                      ·
                        rfl

theorem cell23_3134601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 2, 2].length) (baseStart_3134601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134601 prefixEnd_3134601 := by exact prefixLift 3134601
  have htrace : WordTrace (prefixWord ++ tailWord_3134601) baseStart_3134601 baseEnd_3134601 := by
    simpa [prefixWord, tailWord_3134601, baseEnd_3134601] using wordTrace_append hprefix tailTrace_3134601
  have hstable : (prefixWord ++ tailWord_3134601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134601).length < 2 ^ (prefixWord ++ tailWord_3134601).sum := by decide
  have hdescent : baseEnd_3134601 < baseStart_3134601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134640 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 1, 4, 2]
def baseStart_3134640 : Nat := 118140960795 + 3134640 * 2 ^ 59
def prefixEnd_3134640 : Nat := 4983230072969 + 3 ^ 40 * 3134640 * 2
def baseEnd_3134640 : Nat := 1609576998809720940284059

theorem tailTrace_3134640 : CollatzResearch.WordTrace tailWord_3134640 prefixEnd_3134640 1609576998809720940284059 := by
  unfold tailWord_3134640
  simp only [CollatzResearch.WordTrace]
  refine ⟨57164856681871054367704687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76219808909161405823606249 57164856681871054367704687)
  ·
    refine ⟨85747285022806581551557031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57164856681871054367704687 85747285022806581551557031)
    ·
      refine ⟨128620927534209872327335547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85747285022806581551557031 128620927534209872327335547)
      ·
        refine ⟨192931391301314808491003321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128620927534209872327335547 192931391301314808491003321)
        ·
          refine ⟨144698543475986106368252491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192931391301314808491003321 144698543475986106368252491)
          ·
            refine ⟨217047815213979159552378737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144698543475986106368252491 217047815213979159552378737)
            ·
              refine ⟨162785861410484369664284053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217047815213979159552378737 162785861410484369664284053)
              ·
                refine ⟨7630587253616454828013315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162785861410484369664284053 7630587253616454828013315)
                ·
                  refine ⟨11445880880424682242019973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7630587253616454828013315 11445880880424682242019973)
                  ·
                    refine ⟨2146102665079627920378745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11445880880424682242019973 2146102665079627920378745)
                    ·
                      refine ⟨1609576998809720940284059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146102665079627920378745 1609576998809720940284059)
                      ·
                        rfl

theorem cell23_3134640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 4, 2].length) (baseStart_3134640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134640 prefixEnd_3134640 := by exact prefixLift 3134640
  have htrace : WordTrace (prefixWord ++ tailWord_3134640) baseStart_3134640 baseEnd_3134640 := by
    simpa [prefixWord, tailWord_3134640, baseEnd_3134640] using wordTrace_append hprefix tailTrace_3134640
  have hstable : (prefixWord ++ tailWord_3134640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134640).length < 2 ^ (prefixWord ++ tailWord_3134640).sum := by decide
  have hdescent : baseEnd_3134640 < baseStart_3134640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134643 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 5]
def baseStart_3134643 : Nat := 118140960795 + 3134643 * 2 ^ 59
def prefixEnd_3134643 : Nat := 4983230072969 + 3 ^ 40 * 3134643 * 2
def baseEnd_3134643 : Nat := 1609578539251684428546545

theorem tailTrace_3134643 : CollatzResearch.WordTrace tailWord_3134643 prefixEnd_3134643 1609578539251684428546545 := by
  unfold tailWord_3134643
  simp only [CollatzResearch.WordTrace]
  refine ⟨114329822782731240247768583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76219881855154160165179055 114329822782731240247768583)
  ·
    refine ⟨171494734174096860371652875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114329822782731240247768583 171494734174096860371652875)
    ·
      refine ⟨257242101261145290557479313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171494734174096860371652875 257242101261145290557479313)
      ·
        refine ⟨192931575945858967918109485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257242101261145290557479313 192931575945858967918109485)
        ·
          refine ⟨72349340979697112969291057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192931575945858967918109485 72349340979697112969291057)
          ·
            refine ⟨54262005734772834726968293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72349340979697112969291057 54262005734772834726968293)
            ·
              refine ⟨10174126075269906511306555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54262005734772834726968293 10174126075269906511306555)
              ·
                refine ⟨15261189112904859766959833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10174126075269906511306555 15261189112904859766959833)
                ·
                  refine ⟨11445891834678644825219875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15261189112904859766959833 11445891834678644825219875)
                  ·
                    refine ⟨17168837752017967237829813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11445891834678644825219875 17168837752017967237829813)
                    ·
                      refine ⟨1609578539251684428546545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17168837752017967237829813 1609578539251684428546545)
                      ·
                        rfl

theorem cell23_3134643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_3134643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134643 prefixEnd_3134643 := by exact prefixLift 3134643
  have htrace : WordTrace (prefixWord ++ tailWord_3134643) baseStart_3134643 baseEnd_3134643 := by
    simpa [prefixWord, tailWord_3134643, baseEnd_3134643] using wordTrace_append hprefix tailTrace_3134643
  have hstable : (prefixWord ++ tailWord_3134643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134643).length < 2 ^ (prefixWord ++ tailWord_3134643).sum := by decide
  have hdescent : baseEnd_3134643 < baseStart_3134643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134674 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_3134674 : Nat := 118140960795 + 3134674 * 2 ^ 59
def prefixEnd_3134674 : Nat := 4983230072969 + 3 ^ 40 * 3134674 * 2
def baseEnd_3134674 : Nat := 1609594457151973807258903

theorem tailTrace_3134674 : CollatzResearch.WordTrace tailWord_3134674 prefixEnd_3134674 1609594457151973807258903 := by
  unfold tailWord_3134674
  simp only [CollatzResearch.WordTrace]
  refine ⟨28582738361404733135536769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76220635630412621694764717 28582738361404733135536769)
  ·
    refine ⟨21437053771053549851652577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28582738361404733135536769 21437053771053549851652577)
    ·
      refine ⟨16077790328290162388739433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21437053771053549851652577 16077790328290162388739433)
      ·
        refine ⟨12058342746217621791554575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16077790328290162388739433 12058342746217621791554575)
        ·
          refine ⟨18087514119326432687331863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12058342746217621791554575 18087514119326432687331863)
          ·
            refine ⟨27131271178989649030997795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18087514119326432687331863 27131271178989649030997795)
            ·
              refine ⟨40696906768484473546496693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27131271178989649030997795 40696906768484473546496693)
              ·
                refine ⟨3815335009545419394984065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40696906768484473546496693 3815335009545419394984065)
                ·
                  refine ⟨2861501257159064546238049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3815335009545419394984065 2861501257159064546238049)
                  ·
                    refine ⟨2146125942869298409678537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861501257159064546238049 2146125942869298409678537)
                    ·
                      refine ⟨1609594457151973807258903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146125942869298409678537 1609594457151973807258903)
                      ·
                        rfl

theorem cell23_3134674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_3134674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134674 prefixEnd_3134674 := by exact prefixLift 3134674
  have htrace : WordTrace (prefixWord ++ tailWord_3134674) baseStart_3134674 baseEnd_3134674 := by
    simpa [prefixWord, tailWord_3134674, baseEnd_3134674] using wordTrace_append hprefix tailTrace_3134674
  have hstable : (prefixWord ++ tailWord_3134674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134674).length < 2 ^ (prefixWord ++ tailWord_3134674).sum := by decide
  have hdescent : baseEnd_3134674 < baseStart_3134674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134680 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 7]
def baseStart_3134680 : Nat := 118140960795 + 3134680 * 2 ^ 59
def prefixEnd_3134680 : Nat := 4983230072969 + 3 ^ 40 * 3134680 * 2
def baseEnd_3134680 : Nat := 178844170892877864864875

theorem tailTrace_3134680 : CollatzResearch.WordTrace tailWord_3134680 prefixEnd_3134680 178844170892877864864875 := by
  unfold tailWord_3134680
  simp only [CollatzResearch.WordTrace]
  refine ⟨57165586141798597783432747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76220781522398130377910329 57165586141798597783432747)
  ·
    refine ⟨85748379212697896675149121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57165586141798597783432747 85748379212697896675149121)
    ·
      refine ⟨64311284409523422506361841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85748379212697896675149121 64311284409523422506361841)
      ·
        refine ⟨48233463307142566879771381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64311284409523422506361841 48233463307142566879771381)
        ·
          refine ⟨4521887185044615644978567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48233463307142566879771381 4521887185044615644978567)
          ·
            refine ⟨6782830777566923467467851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521887185044615644978567 6782830777566923467467851)
            ·
              refine ⟨10174246166350385201201777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782830777566923467467851 10174246166350385201201777)
              ·
                refine ⟨7630684624762788900901333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10174246166350385201201777 7630684624762788900901333)
                ·
                  refine ⟨178844170892877864864875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7630684624762788900901333 178844170892877864864875)
                  ·
                    rfl

theorem cell23_3134680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 7].length) (baseStart_3134680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134680 prefixEnd_3134680 := by exact prefixLift 3134680
  have htrace : WordTrace (prefixWord ++ tailWord_3134680) baseStart_3134680 baseEnd_3134680 := by
    simpa [prefixWord, tailWord_3134680, baseEnd_3134680] using wordTrace_append hprefix tailTrace_3134680
  have hstable : (prefixWord ++ tailWord_3134680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134680).length < 2 ^ (prefixWord ++ tailWord_3134680).sum := by decide
  have hdescent : baseEnd_3134680 < baseStart_3134680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134710 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_3134710 : Nat := 118140960795 + 3134710 * 2 ^ 59
def prefixEnd_3134710 : Nat := 4983230072969 + 3 ^ 40 * 3134710 * 2
def baseEnd_3134710 : Nat := 536537647485178555469579

theorem tailTrace_3134710 : CollatzResearch.WordTrace tailWord_3134710 prefixEnd_3134710 536537647485178555469579 := by
  unfold tailWord_3134710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145766654593031918153599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76221510982325673793638389 7145766654593031918153599)
  ·
    refine ⟨10718649981889547877230399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7145766654593031918153599 10718649981889547877230399)
    ·
      refine ⟨16077974972834321815845599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718649981889547877230399 16077974972834321815845599)
      ·
        refine ⟨24116962459251482723768399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077974972834321815845599 24116962459251482723768399)
        ·
          refine ⟨36175443688877224085652599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24116962459251482723768399 36175443688877224085652599)
          ·
            refine ⟨54263165533315836128478899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36175443688877224085652599 54263165533315836128478899)
            ·
              refine ⟨81394748299973754192718349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54263165533315836128478899 81394748299973754192718349)
              ·
                refine ⟨30523030612490157822269381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81394748299973754192718349 30523030612490157822269381)
                ·
                  refine ⟨5723068239841904591675509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30523030612490157822269381 5723068239841904591675509)
                  ·
                    refine ⟨536537647485178555469579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5723068239841904591675509 536537647485178555469579)
                    ·
                      rfl

theorem cell23_3134710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_3134710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134710 prefixEnd_3134710 := by exact prefixLift 3134710
  have htrace : WordTrace (prefixWord ++ tailWord_3134710) baseStart_3134710 baseEnd_3134710 := by
    simpa [prefixWord, tailWord_3134710, baseEnd_3134710] using wordTrace_append hprefix tailTrace_3134710
  have hstable : (prefixWord ++ tailWord_3134710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134710).length < 2 ^ (prefixWord ++ tailWord_3134710).sum := by decide
  have hdescent : baseEnd_3134710 < baseStart_3134710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134770 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 8]
def baseStart_3134770 : Nat := 118140960795 + 3134770 * 2 ^ 59
def prefixEnd_3134770 : Nat := 4983230072969 + 3 ^ 40 * 3134770 * 2
def baseEnd_3134770 : Nat := 178849305699422825739829

theorem tailTrace_3134770 : CollatzResearch.WordTrace tailWord_3134770 prefixEnd_3134770 178849305699422825739829 := by
  unfold tailWord_3134770
  simp only [CollatzResearch.WordTrace]
  refine ⟨28583613713317785234410441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76222969902180760625094509 28583613713317785234410441)
  ·
    refine ⟨21437710284988338925807831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28583613713317785234410441 21437710284988338925807831)
    ·
      refine ⟨32156565427482508388711747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21437710284988338925807831 32156565427482508388711747)
      ·
        refine ⟨48234848141223762583067621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32156565427482508388711747 48234848141223762583067621)
        ·
          refine ⟨9044034026479455484325179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48234848141223762583067621 9044034026479455484325179)
          ·
            refine ⟨13566051039719183226487769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9044034026479455484325179 13566051039719183226487769)
            ·
              refine ⟨10174538279789387419865827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13566051039719183226487769 10174538279789387419865827)
              ·
                refine ⟨15261807419684081129798741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10174538279789387419865827 15261807419684081129798741)
                ·
                  refine ⟨178849305699422825739829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15261807419684081129798741 178849305699422825739829)
                  ·
                    rfl

theorem cell23_3134770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_3134770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134770 prefixEnd_3134770 := by exact prefixLift 3134770
  have htrace : WordTrace (prefixWord ++ tailWord_3134770) baseStart_3134770 baseEnd_3134770 := by
    simpa [prefixWord, tailWord_3134770, baseEnd_3134770] using wordTrace_append hprefix tailTrace_3134770
  have hstable : (prefixWord ++ tailWord_3134770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134770).length < 2 ^ (prefixWord ++ tailWord_3134770).sum := by decide
  have hdescent : baseEnd_3134770 < baseStart_3134770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134800 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 3, 5]
def baseStart_3134800 : Nat := 118140960795 + 3134800 * 2 ^ 59
def prefixEnd_3134800 : Nat := 4983230072969 + 3 ^ 40 * 3134800 * 2
def baseEnd_3134800 : Nat := 536553051904813438094441

theorem tailTrace_3134800 : CollatzResearch.WordTrace tailWord_3134800 prefixEnd_3134800 536553051904813438094441 := by
  unfold tailWord_3134800
  simp only [CollatzResearch.WordTrace]
  refine ⟨57167774521581228030616927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76223699362108304040822569 57167774521581228030616927)
  ·
    refine ⟨85751661782371842045925391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57167774521581228030616927 85751661782371842045925391)
    ·
      refine ⟨128627492673557763068888087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85751661782371842045925391 128627492673557763068888087)
      ·
        refine ⟨192941239010336644603332131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128627492673557763068888087 192941239010336644603332131)
        ·
          refine ⟨289411858515504966904998197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192941239010336644603332131 289411858515504966904998197)
          ·
            refine ⟨27132361735828590647343581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 289411858515504966904998197 27132361735828590647343581)
            ·
              refine ⟨10174635650935721492753843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27132361735828590647343581 10174635650935721492753843)
              ·
                refine ⟨15261953476403582239130765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10174635650935721492753843 15261953476403582239130765)
                ·
                  refine ⟨5723232553651343339674037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15261953476403582239130765 5723232553651343339674037)
                  ·
                    refine ⟨536553051904813438094441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5723232553651343339674037 536553051904813438094441)
                    ·
                      rfl

theorem cell23_3134800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_3134800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134800 prefixEnd_3134800 := by exact prefixLift 3134800
  have htrace : WordTrace (prefixWord ++ tailWord_3134800) baseStart_3134800 baseEnd_3134800 := by
    simpa [prefixWord, tailWord_3134800, baseEnd_3134800] using wordTrace_append hprefix tailTrace_3134800
  have hstable : (prefixWord ++ tailWord_3134800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134800).length < 2 ^ (prefixWord ++ tailWord_3134800).sum := by decide
  have hdescent : baseEnd_3134800 < baseStart_3134800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134874 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3134874 : Nat := 118140960795 + 3134874 * 2 ^ 59
def prefixEnd_3134874 : Nat := 4983230072969 + 3 ^ 40 * 3134874 * 2
def baseEnd_3134874 : Nat := 1609697153282873024757983

theorem tailTrace_3134874 : CollatzResearch.WordTrace tailWord_3134874 prefixEnd_3134874 1609697153282873024757983 := by
  unfold tailWord_3134874
  simp only [CollatzResearch.WordTrace]
  refine ⟨28584562011223591674856919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76225498696596244466285117 28584562011223591674856919)
  ·
    refine ⟨42876843016835387512285379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28584562011223591674856919 42876843016835387512285379)
    ·
      refine ⟨64315264525253081268428069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42876843016835387512285379 64315264525253081268428069)
      ·
        refine ⟨12059112098484952737830263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64315264525253081268428069 12059112098484952737830263)
        ·
          refine ⟨18088668147727429106745395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12059112098484952737830263 18088668147727429106745395)
          ·
            refine ⟨27133002221591143660118093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18088668147727429106745395 27133002221591143660118093)
            ·
              refine ⟨10174875833096678872544285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27133002221591143660118093 10174875833096678872544285)
              ·
                refine ⟨3815578437411254577204107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10174875833096678872544285 3815578437411254577204107)
                ·
                  refine ⟨5723367656116881865806161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815578437411254577204107 5723367656116881865806161)
                  ·
                    refine ⟨4292525742087661399354621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723367656116881865806161 4292525742087661399354621)
                    ·
                      refine ⟨1609697153282873024757983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4292525742087661399354621 1609697153282873024757983)
                      ·
                        rfl

theorem cell23_3134874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3134874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134874 prefixEnd_3134874 := by exact prefixLift 3134874
  have htrace : WordTrace (prefixWord ++ tailWord_3134874) baseStart_3134874 baseEnd_3134874 := by
    simpa [prefixWord, tailWord_3134874, baseEnd_3134874] using wordTrace_append hprefix tailTrace_3134874
  have hstable : (prefixWord ++ tailWord_3134874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134874).length < 2 ^ (prefixWord ++ tailWord_3134874).sum := by decide
  have hdescent : baseEnd_3134874 < baseStart_3134874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134904 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_3134904 : Nat := 118140960795 + 3134904 * 2 ^ 59
def prefixEnd_3134904 : Nat := 4983230072969 + 3 ^ 40 * 3134904 * 2
def baseEnd_3134904 : Nat := 1609712557702507907382845

theorem tailTrace_3134904 : CollatzResearch.WordTrace tailWord_3134904 prefixEnd_3134904 1609712557702507907382845 := by
  unfold tailWord_3134904
  simp only [CollatzResearch.WordTrace]
  refine ⟨57169671117392840911509883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76226228156523787882013177 57169671117392840911509883)
  ·
    refine ⟨85754506676089261367264825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57169671117392840911509883 85754506676089261367264825)
    ·
      refine ⟨64315880007066946025448619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85754506676089261367264825 64315880007066946025448619)
      ·
        refine ⟨96473820010600419038172929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64315880007066946025448619 96473820010600419038172929)
        ·
          refine ⟨72355365007950314278629697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96473820010600419038172929 72355365007950314278629697)
          ·
            refine ⟨54266523755962735708972273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72355365007950314278629697 54266523755962735708972273)
            ·
              refine ⟨40699892816972051781729205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54266523755962735708972273 40699892816972051781729205)
              ·
                refine ⟨3815614951591129854537113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40699892816972051781729205 3815614951591129854537113)
                ·
                  refine ⟨2861711213693347390902835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3815614951591129854537113 2861711213693347390902835)
                  ·
                    refine ⟨4292566820540021086354253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2861711213693347390902835 4292566820540021086354253)
                    ·
                      refine ⟨1609712557702507907382845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4292566820540021086354253 1609712557702507907382845)
                      ·
                        rfl

theorem cell23_3134904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_3134904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134904 prefixEnd_3134904 := by exact prefixLift 3134904
  have htrace : WordTrace (prefixWord ++ tailWord_3134904) baseStart_3134904 baseEnd_3134904 := by
    simpa [prefixWord, tailWord_3134904, baseEnd_3134904] using wordTrace_append hprefix tailTrace_3134904
  have hstable : (prefixWord ++ tailWord_3134904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134904).length < 2 ^ (prefixWord ++ tailWord_3134904).sum := by decide
  have hdescent : baseEnd_3134904 < baseStart_3134904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134965 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_3134965 : Nat := 118140960795 + 3134965 * 2 ^ 59
def prefixEnd_3134965 : Nat := 4983230072969 + 3 ^ 40 * 3134965 * 2
def baseEnd_3134965 : Nat := 1609743880022432168720065

theorem tailTrace_3134965 : CollatzResearch.WordTrace tailWord_3134965 prefixEnd_3134965 1609743880022432168720065 := by
  unfold tailWord_3134965
  simp only [CollatzResearch.WordTrace]
  refine ⟨114341567087564689240990349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76227711391709792827326899 114341567087564689240990349)
  ·
    refine ⟨42878087657836758465371381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114341567087564689240990349 42878087657836758465371381)
    ·
      refine ⟨4019820717922196106128567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42878087657836758465371381 4019820717922196106128567)
      ·
        refine ⟨6029731076883294159192851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019820717922196106128567 6029731076883294159192851)
        ·
          refine ⟨9044596615324941238789277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029731076883294159192851 9044596615324941238789277)
          ·
            refine ⟨3391723730746852964545979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9044596615324941238789277 3391723730746852964545979)
            ·
              refine ⟨5087585596120279446818969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3391723730746852964545979 5087585596120279446818969)
              ·
                refine ⟨3815689197090209585114227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087585596120279446818969 3815689197090209585114227)
                ·
                  refine ⟨5723533795635314377671341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815689197090209585114227 5723533795635314377671341)
                  ·
                    refine ⟨2146325173363242891626753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5723533795635314377671341 2146325173363242891626753)
                    ·
                      refine ⟨1609743880022432168720065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146325173363242891626753 1609743880022432168720065)
                      ·
                        rfl

theorem cell23_3134965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_3134965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134965 prefixEnd_3134965 := by exact prefixLift 3134965
  have htrace : WordTrace (prefixWord ++ tailWord_3134965) baseStart_3134965 baseEnd_3134965 := by
    simpa [prefixWord, tailWord_3134965, baseEnd_3134965] using wordTrace_append hprefix tailTrace_3134965
  have hstable : (prefixWord ++ tailWord_3134965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134965).length < 2 ^ (prefixWord ++ tailWord_3134965).sum := by decide
  have hdescent : baseEnd_3134965 < baseStart_3134965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3134978 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3134978 : Nat := 118140960795 + 3134978 * 2 ^ 59
def prefixEnd_3134978 : Nat := 4983230072969 + 3 ^ 40 * 3134978 * 2
def baseEnd_3134978 : Nat := 1609750555270940617857505

theorem tailTrace_3134978 : CollatzResearch.WordTrace tailWord_3134978 prefixEnd_3134978 1609750555270940617857505 := by
  unfold tailWord_3134978
  simp only [CollatzResearch.WordTrace]
  refine ⟨28585510309129398115303397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76228027491011728307475725 28585510309129398115303397)
  ·
    refine ⟨5359783182961762146619387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28585510309129398115303397 5359783182961762146619387)
    ·
      refine ⟨8039674774442643219929081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5359783182961762146619387 8039674774442643219929081)
      ·
        refine ⟨6029756080831982414946811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8039674774442643219929081 6029756080831982414946811)
        ·
          refine ⟨9044634121247973622420217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029756080831982414946811 9044634121247973622420217)
          ·
            refine ⟨6783475590935980216815163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9044634121247973622420217 6783475590935980216815163)
            ·
              refine ⟨10175213386403970325222745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783475590935980216815163 10175213386403970325222745)
              ·
                refine ⟨7631410039802977743917059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10175213386403970325222745 7631410039802977743917059)
                ·
                  refine ⟨11447115059704466615875589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7631410039802977743917059 11447115059704466615875589)
                  ·
                    refine ⟨2146334073694587490476673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11447115059704466615875589 2146334073694587490476673)
                    ·
                      refine ⟨1609750555270940617857505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146334073694587490476673 1609750555270940617857505)
                      ·
                        rfl

theorem cell23_3134978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3134978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3134978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3134978 prefixEnd_3134978 := by exact prefixLift 3134978
  have htrace : WordTrace (prefixWord ++ tailWord_3134978) baseStart_3134978 baseEnd_3134978 := by
    simpa [prefixWord, tailWord_3134978, baseEnd_3134978] using wordTrace_append hprefix tailTrace_3134978
  have hstable : (prefixWord ++ tailWord_3134978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3134978).length < 2 ^ (prefixWord ++ tailWord_3134978).sum := by decide
  have hdescent : baseEnd_3134978 < baseStart_3134978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3134978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135004 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_3135004 : Nat := 118140960795 + 3135004 * 2 ^ 59
def prefixEnd_3135004 : Nat := 4983230072969 + 3 ^ 40 * 3135004 * 2
def baseEnd_3135004 : Nat := 1609763905767957516132385

theorem tailTrace_3135004 : CollatzResearch.WordTrace tailWord_3135004 prefixEnd_3135004 1609763905767957516132385 := by
  unfold tailWord_3135004
  simp only [CollatzResearch.WordTrace]
  refine ⟨57171494767211699450830033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76228659689615599267773377 57171494767211699450830033)
  ·
    refine ⟨42878621075408774588122525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57171494767211699450830033 42878621075408774588122525)
    ·
      refine ⟨16079482903278290470545947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42878621075408774588122525 16079482903278290470545947)
      ·
        refine ⟨24119224354917435705818921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16079482903278290470545947 24119224354917435705818921)
        ·
          refine ⟨18089418266188076779364191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24119224354917435705818921 18089418266188076779364191)
          ·
            refine ⟨27134127399282115169046287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18089418266188076779364191 27134127399282115169046287)
            ·
              refine ⟨40701191098923172753569431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27134127399282115169046287 40701191098923172753569431)
              ·
                refine ⟨61051786648384759130354147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40701191098923172753569431 61051786648384759130354147)
                ·
                  refine ⟨91577679972577138695531221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61051786648384759130354147 91577679972577138695531221)
                  ·
                    refine ⟨2146351874357276688176513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 91577679972577138695531221 2146351874357276688176513)
                    ·
                      refine ⟨1609763905767957516132385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146351874357276688176513 1609763905767957516132385)
                      ·
                        rfl

theorem cell23_3135004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_3135004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135004 prefixEnd_3135004 := by exact prefixLift 3135004
  have htrace : WordTrace (prefixWord ++ tailWord_3135004) baseStart_3135004 baseEnd_3135004 := by
    simpa [prefixWord, tailWord_3135004, baseEnd_3135004] using wordTrace_append hprefix tailTrace_3135004
  have hstable : (prefixWord ++ tailWord_3135004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135004).length < 2 ^ (prefixWord ++ tailWord_3135004).sum := by decide
  have hdescent : baseEnd_3135004 < baseStart_3135004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135007 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3135007 : Nat := 118140960795 + 3135007 * 2 ^ 59
def prefixEnd_3135007 : Nat := 4983230072969 + 3 ^ 40 * 3135007 * 2
def baseEnd_3135007 : Nat := 1609765446209921004394871

theorem tailTrace_3135007 : CollatzResearch.WordTrace tailWord_3135007 prefixEnd_3135007 1609765446209921004394871 := by
  unfold tailWord_3135007
  simp only [CollatzResearch.WordTrace]
  refine ⟨114343098953412530414019275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76228732635608353609346183 114343098953412530414019275)
  ·
    refine ⟨171514648430118795621028913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114343098953412530414019275 171514648430118795621028913)
    ·
      refine ⟨128635986322589096715771685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171514648430118795621028913 128635986322589096715771685)
      ·
        refine ⟨24119247435485455634207191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128635986322589096715771685 24119247435485455634207191)
        ·
          refine ⟨36178871153228183451310787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24119247435485455634207191 36178871153228183451310787)
          ·
            refine ⟨54268306729842275176966181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36178871153228183451310787 54268306729842275176966181)
            ·
              refine ⟨10175307511845426595681159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54268306729842275176966181 10175307511845426595681159)
              ·
                refine ⟨15262961267768139893521739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10175307511845426595681159 15262961267768139893521739)
                ·
                  refine ⟨22894441901652209840282609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15262961267768139893521739 22894441901652209840282609)
                  ·
                    refine ⟨17170831426239157380211957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22894441901652209840282609 17170831426239157380211957)
                    ·
                      refine ⟨1609765446209921004394871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17170831426239157380211957 1609765446209921004394871)
                      ·
                        rfl

theorem cell23_3135007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3135007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135007 prefixEnd_3135007 := by exact prefixLift 3135007
  have htrace : WordTrace (prefixWord ++ tailWord_3135007) baseStart_3135007 baseEnd_3135007 := by
    simpa [prefixWord, tailWord_3135007, baseEnd_3135007] using wordTrace_append hprefix tailTrace_3135007
  have hstable : (prefixWord ++ tailWord_3135007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135007).length < 2 ^ (prefixWord ++ tailWord_3135007).sum := by decide
  have hdescent : baseEnd_3135007 < baseStart_3135007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135034 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2]
def baseStart_3135034 : Nat := 118140960795 + 3135034 * 2 ^ 59
def prefixEnd_3135034 : Nat := 4983230072969 + 3 ^ 40 * 3135034 * 2
def baseEnd_3135034 : Nat := 1609779310187592398757247

theorem tailTrace_3135034 : CollatzResearch.WordTrace tailWord_3135034 prefixEnd_3135034 1609779310187592398757247 := by
  unfold tailWord_3135034
  simp only [CollatzResearch.WordTrace]
  refine ⟨28586020931078678506313039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76229389149543142683501437 28586020931078678506313039)
  ·
    refine ⟨42879031396618017759469559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28586020931078678506313039 42879031396618017759469559)
    ·
      refine ⟨64318547094927026639204339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42879031396618017759469559 64318547094927026639204339)
      ·
        refine ⟨96477820642390539958806509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64318547094927026639204339 96477820642390539958806509)
        ·
          refine ⟨36179182740896452484552441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96477820642390539958806509 36179182740896452484552441)
          ·
            refine ⟨27134387055672339363414331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36179182740896452484552441 27134387055672339363414331)
            ·
              refine ⟨40701580583508509045121497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27134387055672339363414331 40701580583508509045121497)
              ·
                refine ⟨30526185437631381783841123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40701580583508509045121497 30526185437631381783841123)
                ·
                  refine ⟨45789278156447072675761685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30526185437631381783841123 45789278156447072675761685)
                  ·
                    refine ⟨2146372413583456531676329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45789278156447072675761685 2146372413583456531676329)
                    ·
                      refine ⟨1609779310187592398757247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146372413583456531676329 1609779310187592398757247)
                      ·
                        rfl

theorem cell23_3135034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_3135034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135034 prefixEnd_3135034 := by exact prefixLift 3135034
  have htrace : WordTrace (prefixWord ++ tailWord_3135034) baseStart_3135034 baseEnd_3135034 := by
    simpa [prefixWord, tailWord_3135034, baseEnd_3135034] using wordTrace_append hprefix tailTrace_3135034
  have hstable : (prefixWord ++ tailWord_3135034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135034).length < 2 ^ (prefixWord ++ tailWord_3135034).sum := by decide
  have hdescent : baseEnd_3135034 < baseStart_3135034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135054 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_3135054 : Nat := 118140960795 + 3135054 * 2 ^ 59
def prefixEnd_3135054 : Nat := 4983230072969 + 3 ^ 40 * 3135054 * 2
def baseEnd_3135054 : Nat := 1609789579800682320507155

theorem tailTrace_3135054 : CollatzResearch.WordTrace tailWord_3135054 prefixEnd_3135054 1609789579800682320507155 := by
  unfold tailWord_3135054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14293101648030282180122527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76229875456161504960653477 14293101648030282180122527)
  ·
    refine ⟨21439652472045423270183791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14293101648030282180122527 21439652472045423270183791)
    ·
      refine ⟨32159478708068134905275687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21439652472045423270183791 32159478708068134905275687)
      ·
        refine ⟨48239218062102202357913531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32159478708068134905275687 48239218062102202357913531)
        ·
          refine ⟨72358827093153303536870297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48239218062102202357913531 72358827093153303536870297)
          ·
            refine ⟨54269120319864977652652723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72358827093153303536870297 54269120319864977652652723)
            ·
              refine ⟨81403680479797466478979085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54269120319864977652652723 81403680479797466478979085)
              ·
                refine ⟨30526380179924049929617157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81403680479797466478979085 30526380179924049929617157)
                ·
                  refine ⟨5723696283735759361803217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30526380179924049929617157 5723696283735759361803217)
                  ·
                    refine ⟨4292772212801819521352413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723696283735759361803217 4292772212801819521352413)
                    ·
                      refine ⟨1609789579800682320507155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4292772212801819521352413 1609789579800682320507155)
                      ·
                        rfl

theorem cell23_3135054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_3135054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135054 prefixEnd_3135054 := by exact prefixLift 3135054
  have htrace : WordTrace (prefixWord ++ tailWord_3135054) baseStart_3135054 baseEnd_3135054 := by
    simpa [prefixWord, tailWord_3135054, baseEnd_3135054] using wordTrace_append hprefix tailTrace_3135054
  have hstable : (prefixWord ++ tailWord_3135054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135054).length < 2 ^ (prefixWord ++ tailWord_3135054).sum := by decide
  have hdescent : baseEnd_3135054 < baseStart_3135054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135057 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 8]
def baseStart_3135057 : Nat := 118140960795 + 3135057 * 2 ^ 59
def prefixEnd_3135057 : Nat := 4983230072969 + 3 ^ 40 * 3135057 * 2
def baseEnd_3135057 : Nat := 178865680026960645418849

theorem tailTrace_3135057 : CollatzResearch.WordTrace tailWord_3135057 prefixEnd_3135057 178865680026960645418849 := by
  unfold tailWord_3135057
  simp only [CollatzResearch.WordTrace]
  refine ⟨114344922603231388953339425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76229948402154259302226283 114344922603231388953339425)
  ·
    refine ⟨85758691952423541715004569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114344922603231388953339425 85758691952423541715004569)
    ·
      refine ⟨64319018964317656286253427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85758691952423541715004569 64319018964317656286253427)
      ·
        refine ⟨96478528446476484429380141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64319018964317656286253427 96478528446476484429380141)
        ·
          refine ⟨36179448167428681661017553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96478528446476484429380141 36179448167428681661017553)
          ·
            refine ⟨27134586125571511245763165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36179448167428681661017553 27134586125571511245763165)
            ·
              refine ⟨10175469797089316717161187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27134586125571511245763165 10175469797089316717161187)
              ·
                refine ⟨15263204695633975075741781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10175469797089316717161187 15263204695633975075741781)
                ·
                  refine ⟨178865680026960645418849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15263204695633975075741781 178865680026960645418849)
                  ·
                    rfl

theorem cell23_3135057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 8].length) (baseStart_3135057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135057 prefixEnd_3135057 := by exact prefixLift 3135057
  have htrace : WordTrace (prefixWord ++ tailWord_3135057) baseStart_3135057 baseEnd_3135057 := by
    simpa [prefixWord, tailWord_3135057, baseEnd_3135057] using wordTrace_append hprefix tailTrace_3135057
  have hstable : (prefixWord ++ tailWord_3135057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135057).length < 2 ^ (prefixWord ++ tailWord_3135057).sum := by decide
  have hdescent : baseEnd_3135057 < baseStart_3135057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135104 : List Nat := [2, 1, 1, 2, 1, 4, 1, 5, 1, 5]
def baseStart_3135104 : Nat := 118140960795 + 3135104 * 2 ^ 59
def prefixEnd_3135104 : Nat := 4983230072969 + 3 ^ 40 * 3135104 * 2
def baseEnd_3135104 : Nat := 536605084611135708293975

theorem tailTrace_3135104 : CollatzResearch.WordTrace tailWord_3135104 prefixEnd_3135104 536605084611135708293975 := by
  unfold tailWord_3135104
  simp only [CollatzResearch.WordTrace]
  refine ⟨57173318417030557990150183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76231091222707410653533577 57173318417030557990150183)
  ·
    refine ⟨85759977625545836985225275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57173318417030557990150183 85759977625545836985225275)
    ·
      refine ⟨128639966438318755477837913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85759977625545836985225275 128639966438318755477837913)
      ·
        refine ⟨96479974828739066608378435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128639966438318755477837913 96479974828739066608378435)
        ·
          refine ⟨144719962243108599912567653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96479974828739066608378435 144719962243108599912567653)
          ·
            refine ⟨27134992920582862483606435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144719962243108599912567653 27134992920582862483606435)
            ·
              refine ⟨40702489380874293725409653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27134992920582862483606435 40702489380874293725409653)
              ·
                refine ⟨3815858379456965036757155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40702489380874293725409653 3815858379456965036757155)
                ·
                  refine ⟨5723787569185447555135733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815858379456965036757155 5723787569185447555135733)
                  ·
                    refine ⟨536605084611135708293975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5723787569185447555135733 536605084611135708293975)
                    ·
                      rfl

theorem cell23_3135104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_3135104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135104 prefixEnd_3135104 := by exact prefixLift 3135104
  have htrace : WordTrace (prefixWord ++ tailWord_3135104) baseStart_3135104 baseEnd_3135104 := by
    simpa [prefixWord, tailWord_3135104, baseEnd_3135104] using wordTrace_append hprefix tailTrace_3135104
  have hstable : (prefixWord ++ tailWord_3135104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135104).length < 2 ^ (prefixWord ++ tailWord_3135104).sum := by decide
  have hdescent : baseEnd_3135104 < baseStart_3135104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135111 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_3135111 : Nat := 118140960795 + 3135111 * 2 ^ 59
def prefixEnd_3135111 : Nat := 4983230072969 + 3 ^ 40 * 3135111 * 2
def baseEnd_3135111 : Nat := 1609818848197988597494393

theorem tailTrace_3135111 : CollatzResearch.WordTrace tailWord_3135111 prefixEnd_3135111 1609818848197988597494393 := by
  unfold tailWord_3135111
  simp only [CollatzResearch.WordTrace]
  refine ⟨114346892145035756175805187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76231261430023837450536791 114346892145035756175805187)
  ·
    refine ⟨171520338217553634263707781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114346892145035756175805187 171520338217553634263707781)
    ·
      refine ⟨32160063415791306424445209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171520338217553634263707781 32160063415791306424445209)
      ·
        refine ⟨24120047561843479818333907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32160063415791306424445209 24120047561843479818333907)
        ·
          refine ⟨36180071342765219727500861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24120047561843479818333907 36180071342765219727500861)
          ·
            refine ⟨13567526753536957397812823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36180071342765219727500861 13567526753536957397812823)
            ·
              refine ⟨20351290130305436096719235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13567526753536957397812823 20351290130305436096719235)
              ·
                refine ⟨30526935195458154145078853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20351290130305436096719235 30526935195458154145078853)
                ·
                  refine ⟨5723800349148403902202285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30526935195458154145078853 5723800349148403902202285)
                  ·
                    refine ⟨2146425130930651463325857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5723800349148403902202285 2146425130930651463325857)
                    ·
                      refine ⟨1609818848197988597494393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146425130930651463325857 1609818848197988597494393)
                      ·
                        rfl

theorem cell23_3135111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_3135111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135111 prefixEnd_3135111 := by exact prefixLift 3135111
  have htrace : WordTrace (prefixWord ++ tailWord_3135111) baseStart_3135111 baseEnd_3135111 := by
    simpa [prefixWord, tailWord_3135111, baseEnd_3135111] using wordTrace_append hprefix tailTrace_3135111
  have hstable : (prefixWord ++ tailWord_3135111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135111).length < 2 ^ (prefixWord ++ tailWord_3135111).sum := by decide
  have hdescent : baseEnd_3135111 < baseStart_3135111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135112 : List Nat := [2, 1, 3, 5, 1, 1, 3, 2, 1, 4]
def baseStart_3135112 : Nat := 118140960795 + 3135112 * 2 ^ 59
def prefixEnd_3135112 : Nat := 4983230072969 + 3 ^ 40 * 3135112 * 2
def baseEnd_3135112 : Nat := 536606453892881031193963

theorem tailTrace_3135112 : CollatzResearch.WordTrace tailWord_3135112 prefixEnd_3135112 536606453892881031193963 := by
  unfold tailWord_3135112
  simp only [CollatzResearch.WordTrace]
  refine ⟨57173464309016066673295795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76231285745354755564394393 57173464309016066673295795)
  ·
    refine ⟨85760196463524100009943693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57173464309016066673295795 85760196463524100009943693)
    ·
      refine ⟨32160073673821537503728885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85760196463524100009943693 32160073673821537503728885)
      ·
        refine ⟨3015006906920769140974583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32160073673821537503728885 3015006906920769140974583)
        ·
          refine ⟨4522510360381153711461875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015006906920769140974583 4522510360381153711461875)
          ·
            refine ⟨6783765540571730567192813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522510360381153711461875 6783765540571730567192813)
            ·
              refine ⟨2543912077714398962697305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6783765540571730567192813 2543912077714398962697305)
              ·
                refine ⟨1907934058285799222022979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2543912077714398962697305 1907934058285799222022979)
                ·
                  refine ⟨2861901087428698833034469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907934058285799222022979 2861901087428698833034469)
                  ·
                    refine ⟨536606453892881031193963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2861901087428698833034469 536606453892881031193963)
                    ·
                      rfl

theorem cell23_3135112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_3135112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135112 prefixEnd_3135112 := by exact prefixLift 3135112
  have htrace : WordTrace (prefixWord ++ tailWord_3135112) baseStart_3135112 baseEnd_3135112 := by
    simpa [prefixWord, tailWord_3135112, baseEnd_3135112] using wordTrace_append hprefix tailTrace_3135112
  have hstable : (prefixWord ++ tailWord_3135112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135112).length < 2 ^ (prefixWord ++ tailWord_3135112).sum := by decide
  have hdescent : baseEnd_3135112 < baseStart_3135112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135118 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3135118 : Nat := 118140960795 + 3135118 * 2 ^ 59
def prefixEnd_3135118 : Nat := 4983230072969 + 3 ^ 40 * 3135118 * 2
def baseEnd_3135118 : Nat := 1609822442562570070106861

theorem tailTrace_3135118 : CollatzResearch.WordTrace tailWord_3135118 prefixEnd_3135118 1609822442562570070106861 := by
  unfold tailWord_3135118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14293393432001299546413751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76231431637340264247540005 14293393432001299546413751)
  ·
    refine ⟨21440090148001949319620627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14293393432001299546413751 21440090148001949319620627)
    ·
      refine ⟨32160135222002923979430941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21440090148001949319620627 32160135222002923979430941)
      ·
        refine ⟨12060050708251096492286603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32160135222002923979430941 12060050708251096492286603)
        ·
          refine ⟨18090076062376644738429905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12060050708251096492286603 18090076062376644738429905)
          ·
            refine ⟨13567557046782483553822429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18090076062376644738429905 13567557046782483553822429)
            ·
              refine ⟨5087833892543431332683411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13567557046782483553822429 5087833892543431332683411)
              ·
                refine ⟨7631750838815146999025117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087833892543431332683411 7631750838815146999025117)
                ·
                  refine ⟨2861906564555680124634419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7631750838815146999025117 2861906564555680124634419)
                  ·
                    refine ⟨4292859846833520186951629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2861906564555680124634419 4292859846833520186951629)
                    ·
                      refine ⟨1609822442562570070106861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4292859846833520186951629 1609822442562570070106861)
                      ·
                        rfl

theorem cell23_3135118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3135118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135118 prefixEnd_3135118 := by exact prefixLift 3135118
  have htrace : WordTrace (prefixWord ++ tailWord_3135118) baseStart_3135118 baseEnd_3135118 := by
    simpa [prefixWord, tailWord_3135118, baseEnd_3135118] using wordTrace_append hprefix tailTrace_3135118
  have hstable : (prefixWord ++ tailWord_3135118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135118).length < 2 ^ (prefixWord ++ tailWord_3135118).sum := by decide
  have hdescent : baseEnd_3135118 < baseStart_3135118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135138 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3135138 : Nat := 118140960795 + 3135138 * 2 ^ 59
def prefixEnd_3135138 : Nat := 4983230072969 + 3 ^ 40 * 3135138 * 2
def baseEnd_3135138 : Nat := 536610904058553330618923

theorem tailTrace_3135138 : CollatzResearch.WordTrace tailWord_3135138 prefixEnd_3135138 536610904058553330618923 := by
  unfold tailWord_3135138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28586969228984484946759517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76231917943958626524692045 28586969228984484946759517)
  ·
    refine ⟨10720113460869181855034819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28586969228984484946759517 10720113460869181855034819)
    ·
      refine ⟨16080170191303772782552229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10720113460869181855034819 16080170191303772782552229)
      ·
        refine ⟨3015031910869457396728543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16080170191303772782552229 3015031910869457396728543)
        ·
          refine ⟨4522547866304186095092815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015031910869457396728543 4522547866304186095092815)
          ·
            refine ⟨6783821799456279142639223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522547866304186095092815 6783821799456279142639223)
            ·
              refine ⟨10175732699184418713958835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783821799456279142639223 10175732699184418713958835)
              ·
                refine ⟨15263599048776628070938253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10175732699184418713958835 15263599048776628070938253)
                ·
                  refine ⟨5723849643291235526601845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15263599048776628070938253 5723849643291235526601845)
                  ·
                    refine ⟨536610904058553330618923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5723849643291235526601845 536610904058553330618923)
                    ·
                      rfl

theorem cell23_3135138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3135138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135138 prefixEnd_3135138 := by exact prefixLift 3135138
  have htrace : WordTrace (prefixWord ++ tailWord_3135138) baseStart_3135138 baseEnd_3135138 := by
    simpa [prefixWord, tailWord_3135138, baseEnd_3135138] using wordTrace_append hprefix tailTrace_3135138
  have hstable : (prefixWord ++ tailWord_3135138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135138).length < 2 ^ (prefixWord ++ tailWord_3135138).sum := by decide
  have hdescent : baseEnd_3135138 < baseStart_3135138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135141 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_3135141 : Nat := 118140960795 + 3135141 * 2 ^ 59
def prefixEnd_3135141 : Nat := 4983230072969 + 3 ^ 40 * 3135141 * 2
def baseEnd_3135141 : Nat := 1609834252617623480119255

theorem tailTrace_3135141 : CollatzResearch.WordTrace tailWord_3135141 prefixEnd_3135141 1609834252617623480119255 := by
  unfold tailWord_3135141
  simp only [CollatzResearch.WordTrace]
  refine ⟨114347986334927071299397277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76231990889951380866264851 114347986334927071299397277)
  ·
    refine ⟨42880494875597651737273979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114347986334927071299397277 42880494875597651737273979)
    ·
      refine ⟨64320742313396477605910969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42880494875597651737273979 64320742313396477605910969)
      ·
        refine ⟨48240556735047358204433227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64320742313396477605910969 48240556735047358204433227)
        ·
          refine ⟨72360835102571037306649841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48240556735047358204433227 72360835102571037306649841)
          ·
            refine ⟨54270626326928277979987381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72360835102571037306649841 54270626326928277979987381)
            ·
              refine ⟨5087871218149526060623817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54270626326928277979987381 5087871218149526060623817)
              ·
                refine ⟨3815903413612144545467863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087871218149526060623817 3815903413612144545467863)
                ·
                  refine ⟨5723855120418216818201795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815903413612144545467863 5723855120418216818201795)
                  ·
                    refine ⟨8585782680627325227302693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5723855120418216818201795 8585782680627325227302693)
                    ·
                      refine ⟨1609834252617623480119255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8585782680627325227302693 1609834252617623480119255)
                      ·
                        rfl

theorem cell23_3135141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_3135141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135141 prefixEnd_3135141 := by exact prefixLift 3135141
  have htrace : WordTrace (prefixWord ++ tailWord_3135141) baseStart_3135141 baseEnd_3135141 := by
    simpa [prefixWord, tailWord_3135141, baseEnd_3135141] using wordTrace_append hprefix tailTrace_3135141
  have hstable : (prefixWord ++ tailWord_3135141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135141).length < 2 ^ (prefixWord ++ tailWord_3135141).sum := by decide
  have hdescent : baseEnd_3135141 < baseStart_3135141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135154 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3135154 : Nat := 118140960795 + 3135154 * 2 ^ 59
def prefixEnd_3135154 : Nat := 4983230072969 + 3 ^ 40 * 3135154 * 2
def baseEnd_3135154 : Nat := 1609840927866131929256695

theorem tailTrace_3135154 : CollatzResearch.WordTrace tailWord_3135154 prefixEnd_3135154 1609840927866131929256695 := by
  unfold tailWord_3135154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28587115120969993629905129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76232306989253316346413677 28587115120969993629905129)
  ·
    refine ⟨21440336340727495222428847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28587115120969993629905129 21440336340727495222428847)
    ·
      refine ⟨32160504511091242833643271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21440336340727495222428847 32160504511091242833643271)
      ·
        refine ⟨48240756766636864250464907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32160504511091242833643271 48240756766636864250464907)
        ·
          refine ⟨72361135149955296375697361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48240756766636864250464907 72361135149955296375697361)
          ·
            refine ⟨54270851362466472281773021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72361135149955296375697361 54270851362466472281773021)
            ·
              refine ⟨20351569260924927105664883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54270851362466472281773021 20351569260924927105664883)
              ·
                refine ⟨30527353891387390658497325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20351569260924927105664883 30527353891387390658497325)
                ·
                  refine ⟨11447757709270271496936497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30527353891387390658497325 11447757709270271496936497)
                  ·
                    refine ⟨8585818281952703622702373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11447757709270271496936497 8585818281952703622702373)
                    ·
                      refine ⟨1609840927866131929256695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8585818281952703622702373 1609840927866131929256695)
                      ·
                        rfl

theorem cell23_3135154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3135154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135154 prefixEnd_3135154 := by exact prefixLift 3135154
  have htrace : WordTrace (prefixWord ++ tailWord_3135154) baseStart_3135154 baseEnd_3135154 := by
    simpa [prefixWord, tailWord_3135154, baseEnd_3135154] using wordTrace_append hprefix tailTrace_3135154
  have hstable : (prefixWord ++ tailWord_3135154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135154).length < 2 ^ (prefixWord ++ tailWord_3135154).sum := by decide
  have hdescent : baseEnd_3135154 < baseStart_3135154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135161 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 3]
def baseStart_3135161 : Nat := 118140960795 + 3135161 * 2 ^ 59
def prefixEnd_3135161 : Nat := 4983230072969 + 3 ^ 40 * 3135161 * 2
def baseEnd_3135161 : Nat := 1609844522230713401869163

theorem tailTrace_3135161 : CollatzResearch.WordTrace tailWord_3135161 prefixEnd_3135161 1609844522230713401869163 := by
  unfold tailWord_3135161
  simp only [CollatzResearch.WordTrace]
  refine ⟨114348715794854614715125337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76232477196569743143416891 114348715794854614715125337)
  ·
    refine ⟨85761536846140961036344003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114348715794854614715125337 85761536846140961036344003)
    ·
      refine ⟨128642305269211441554516005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85761536846140961036344003 128642305269211441554516005)
      ·
        refine ⟨24120432237977145291471751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128642305269211441554516005 24120432237977145291471751)
        ·
          refine ⟨36180648356965717937207627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24120432237977145291471751 36180648356965717937207627)
          ·
            refine ⟨54270972535448576905811441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36180648356965717937207627 54270972535448576905811441)
            ·
              refine ⟨40703229401586432679358581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54270972535448576905811441 40703229401586432679358581)
              ·
                refine ⟨3815927756398728063689867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40703229401586432679358581 3815927756398728063689867)
                ·
                  refine ⟨5723891634598092095534801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815927756398728063689867 5723891634598092095534801)
                  ·
                    refine ⟨4292918725948569071651101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723891634598092095534801 4292918725948569071651101)
                    ·
                      refine ⟨1609844522230713401869163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4292918725948569071651101 1609844522230713401869163)
                      ·
                        rfl

theorem cell23_3135161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_3135161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135161 prefixEnd_3135161 := by exact prefixLift 3135161
  have htrace : WordTrace (prefixWord ++ tailWord_3135161) baseStart_3135161 baseEnd_3135161 := by
    simpa [prefixWord, tailWord_3135161, baseEnd_3135161] using wordTrace_append hprefix tailTrace_3135161
  have hstable : (prefixWord ++ tailWord_3135161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135161).length < 2 ^ (prefixWord ++ tailWord_3135161).sum := by decide
  have hdescent : baseEnd_3135161 < baseStart_3135161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135175 : List Nat := [1, 1, 4, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_3135175 : Nat := 118140960795 + 3135175 * 2 ^ 59
def prefixEnd_3135175 : Nat := 4983230072969 + 3 ^ 40 * 3135175 * 2
def baseEnd_3135175 : Nat := 1609851710959876347094099

theorem tailTrace_3135175 : CollatzResearch.WordTrace tailWord_3135175 prefixEnd_3135175 1609851710959876347094099 := by
  unfold tailWord_3135175
  simp only [CollatzResearch.WordTrace]
  refine ⟨114349226416803895106134979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76232817611202596737423319 114349226416803895106134979)
  ·
    refine ⟨171523839625205842659202469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114349226416803895106134979 171523839625205842659202469)
    ·
      refine ⟨32160719929726095498600463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171523839625205842659202469 32160719929726095498600463)
      ·
        refine ⟨48241079894589143247900695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32160719929726095498600463 48241079894589143247900695)
        ·
          refine ⟨72361619841883714871851043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48241079894589143247900695 72361619841883714871851043)
          ·
            refine ⟨108542429762825572307776565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72361619841883714871851043 108542429762825572307776565)
            ·
              refine ⟨10175852790264897403854053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108542429762825572307776565 10175852790264897403854053)
              ·
                refine ⟨1907972398174668263222635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10175852790264897403854053 1907972398174668263222635)
                ·
                  refine ⟨2861958597262002394833953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1907972398174668263222635 2861958597262002394833953)
                  ·
                    refine ⟨2146468947946501796125465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2861958597262002394833953 2146468947946501796125465)
                    ·
                      refine ⟨1609851710959876347094099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146468947946501796125465 1609851710959876347094099)
                      ·
                        rfl

theorem cell23_3135175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_3135175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135175 prefixEnd_3135175 := by exact prefixLift 3135175
  have htrace : WordTrace (prefixWord ++ tailWord_3135175) baseStart_3135175 baseEnd_3135175 := by
    simpa [prefixWord, tailWord_3135175, baseEnd_3135175] using wordTrace_append hprefix tailTrace_3135175
  have hstable : (prefixWord ++ tailWord_3135175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135175).length < 2 ^ (prefixWord ++ tailWord_3135175).sum := by decide
  have hdescent : baseEnd_3135175 < baseStart_3135175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135188 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3135188 : Nat := 118140960795 + 3135188 * 2 ^ 59
def prefixEnd_3135188 : Nat := 4983230072969 + 3 ^ 40 * 3135188 * 2
def baseEnd_3135188 : Nat := 1609858386208384796231539

theorem tailTrace_3135188 : CollatzResearch.WordTrace tailWord_3135188 prefixEnd_3135188 1609858386208384796231539 := by
  unfold tailWord_3135188
  simp only [CollatzResearch.WordTrace]
  refine ⟨57174850282878399163179109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76233133710504532217572145 57174850282878399163179109)
  ·
    refine ⟨10720284428039699843096083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57174850282878399163179109 10720284428039699843096083)
    ·
      refine ⟨16080426642059549764644125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10720284428039699843096083 16080426642059549764644125)
      ·
        refine ⟨6030159990772331161741547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16080426642059549764644125 6030159990772331161741547)
        ·
          refine ⟨9045239986158496742612321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6030159990772331161741547 9045239986158496742612321)
          ·
            refine ⟨6783929989618872556959241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9045239986158496742612321 6783929989618872556959241)
            ·
              refine ⟨5087947492214154417719431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6783929989618872556959241 5087947492214154417719431)
              ·
                refine ⟨7631921238321231626579147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087947492214154417719431 7631921238321231626579147)
                ·
                  refine ⟨11447881857481847439868721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7631921238321231626579147 11447881857481847439868721)
                  ·
                    refine ⟨8585911393111385579901541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11447881857481847439868721 8585911393111385579901541)
                    ·
                      refine ⟨1609858386208384796231539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8585911393111385579901541 1609858386208384796231539)
                      ·
                        rfl

theorem cell23_3135188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3135188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135188 prefixEnd_3135188 := by exact prefixLift 3135188
  have htrace : WordTrace (prefixWord ++ tailWord_3135188) baseStart_3135188 baseEnd_3135188 := by
    simpa [prefixWord, tailWord_3135188, baseEnd_3135188] using wordTrace_append hprefix tailTrace_3135188
  have hstable : (prefixWord ++ tailWord_3135188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135188).length < 2 ^ (prefixWord ++ tailWord_3135188).sum := by decide
  have hdescent : baseEnd_3135188 < baseStart_3135188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135191 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_3135191 : Nat := 118140960795 + 3135191 * 2 ^ 59
def prefixEnd_3135191 : Nat := 4983230072969 + 3 ^ 40 * 3135191 * 2
def baseEnd_3135191 : Nat := 1609859926650348284494025

theorem tailTrace_3135191 : CollatzResearch.WordTrace tailWord_3135191 prefixEnd_3135191 1609859926650348284494025 := by
  unfold tailWord_3135191
  simp only [CollatzResearch.WordTrace]
  refine ⟨114349809984745929838717427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76233206656497286559144951 114349809984745929838717427)
  ·
    refine ⟨171524714977118894758076141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114349809984745929838717427 171524714977118894758076141)
    ·
      refine ⟨64321768116419585534278553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171524714977118894758076141 64321768116419585534278553)
      ·
        refine ⟨48241326087314689150708915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64321768116419585534278553 48241326087314689150708915)
        ·
          refine ⟨72361989130972033726063373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48241326087314689150708915 72361989130972033726063373)
          ·
            refine ⟨27135745924114512647273765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72361989130972033726063373 27135745924114512647273765)
            ·
              refine ⟨5087952360771471121363831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27135745924114512647273765 5087952360771471121363831)
              ·
                refine ⟨7631928541157206682045747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087952360771471121363831 7631928541157206682045747)
                ·
                  refine ⟨11447892811735810023068621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7631928541157206682045747 11447892811735810023068621)
                  ·
                    refine ⟨4292959804400928758650733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11447892811735810023068621 4292959804400928758650733)
                    ·
                      refine ⟨1609859926650348284494025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4292959804400928758650733 1609859926650348284494025)
                      ·
                        rfl

theorem cell23_3135191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_3135191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135191 prefixEnd_3135191 := by exact prefixLift 3135191
  have htrace : WordTrace (prefixWord ++ tailWord_3135191) baseStart_3135191 baseEnd_3135191 := by
    simpa [prefixWord, tailWord_3135191, baseEnd_3135191] using wordTrace_append hprefix tailTrace_3135191
  have hstable : (prefixWord ++ tailWord_3135191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135191).length < 2 ^ (prefixWord ++ tailWord_3135191).sum := by decide
  have hdescent : baseEnd_3135191 < baseStart_3135191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135204 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_3135204 : Nat := 118140960795 + 3135204 * 2 ^ 59
def prefixEnd_3135204 : Nat := 4983230072969 + 3 ^ 40 * 3135204 * 2
def baseEnd_3135204 : Nat := 1609866601898856733631465

theorem tailTrace_3135204 : CollatzResearch.WordTrace tailWord_3135204 prefixEnd_3135204 1609866601898856733631465 := by
  unfold tailWord_3135204
  simp only [CollatzResearch.WordTrace]
  refine ⟨57175142066849416529470333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76233522755799222039293777 57175142066849416529470333)
  ·
    refine ⟨21440678275068531198551375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57175142066849416529470333 21440678275068531198551375)
    ·
      refine ⟨32161017412602796797827063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21440678275068531198551375 32161017412602796797827063)
      ·
        refine ⟨48241526118904195196740595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32161017412602796797827063 48241526118904195196740595)
        ·
          refine ⟨72362289178356292795110893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48241526118904195196740595 72362289178356292795110893)
          ·
            refine ⟨27135858441883609798166585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72362289178356292795110893 27135858441883609798166585)
            ·
              refine ⟨20351893831412707348624939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27135858441883609798166585 20351893831412707348624939)
              ·
                refine ⟨30527840747119061022937409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20351893831412707348624939 30527840747119061022937409)
                ·
                  refine ⟨22895880560339295767203057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30527840747119061022937409 22895880560339295767203057)
                  ·
                    refine ⟨17171910420254471825402293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22895880560339295767203057 17171910420254471825402293)
                    ·
                      refine ⟨1609866601898856733631465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17171910420254471825402293 1609866601898856733631465)
                      ·
                        rfl

theorem cell23_3135204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_3135204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135204 prefixEnd_3135204 := by exact prefixLift 3135204
  have htrace : WordTrace (prefixWord ++ tailWord_3135204) baseStart_3135204 baseEnd_3135204 := by
    simpa [prefixWord, tailWord_3135204, baseEnd_3135204] using wordTrace_append hprefix tailTrace_3135204
  have hstable : (prefixWord ++ tailWord_3135204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135204).length < 2 ^ (prefixWord ++ tailWord_3135204).sum := by decide
  have hdescent : baseEnd_3135204 < baseStart_3135204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135231 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 3, 4, 2]
def baseStart_3135231 : Nat := 118140960795 + 3135231 * 2 ^ 59
def prefixEnd_3135231 : Nat := 4983230072969 + 3 ^ 40 * 3135231 * 2
def baseEnd_3135231 : Nat := 1609880465876528127993841

theorem tailTrace_3135231 : CollatzResearch.WordTrace tailWord_3135231 prefixEnd_3135231 1609880465876528127993841 := by
  unfold tailWord_3135231
  simp only [CollatzResearch.WordTrace]
  refine ⟨114351268904601016670173547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76234179269734011113449031 114351268904601016670173547)
  ·
    refine ⟨171526903356901525005260321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114351268904601016670173547 171526903356901525005260321)
    ·
      refine ⟨128645177517676143753945241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171526903356901525005260321 128645177517676143753945241)
      ·
        refine ⟨96483883138257107815458931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128645177517676143753945241 96483883138257107815458931)
        ·
          refine ⟨144725824707385661723188397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96483883138257107815458931 144725824707385661723188397)
          ·
            refine ⟨54272184265269623146195649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144725824707385661723188397 54272184265269623146195649)
            ·
              refine ⟨40704138198952217359646737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54272184265269623146195649 40704138198952217359646737)
              ·
                refine ⟨30528103649214163019735053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40704138198952217359646737 30528103649214163019735053)
                ·
                  refine ⟨11448038868455311132400645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30528103649214163019735053 11448038868455311132400645)
                  ·
                    refine ⟨2146507287835370837325121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11448038868455311132400645 2146507287835370837325121)
                    ·
                      refine ⟨1609880465876528127993841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146507287835370837325121 1609880465876528127993841)
                      ·
                        rfl

theorem cell23_3135231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_3135231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135231 prefixEnd_3135231 := by exact prefixLift 3135231
  have htrace : WordTrace (prefixWord ++ tailWord_3135231) baseStart_3135231 baseEnd_3135231 := by
    simpa [prefixWord, tailWord_3135231, baseEnd_3135231] using wordTrace_append hprefix tailTrace_3135231
  have hstable : (prefixWord ++ tailWord_3135231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135231).length < 2 ^ (prefixWord ++ tailWord_3135231).sum := by decide
  have hdescent : baseEnd_3135231 < baseStart_3135231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135431 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_3135431 : Nat := 118140960795 + 3135431 * 2 ^ 59
def prefixEnd_3135431 : Nat := 4983230072969 + 3 ^ 40 * 3135431 * 2
def baseEnd_3135431 : Nat := 1609983162007427345492921

theorem tailTrace_3135431 : CollatzResearch.WordTrace tailWord_3135431 prefixEnd_3135431 1609983162007427345492921 := by
  unfold tailWord_3135431
  simp only [CollatzResearch.WordTrace]
  refine ⟨114358563503876450827454147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76239042335917633884969431 114358563503876450827454147)
  ·
    refine ⟨171537845255814676241181221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114358563503876450827454147 171537845255814676241181221)
    ·
      refine ⟨32163345985465251795221479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171537845255814676241181221 32163345985465251795221479)
      ·
        refine ⟨48245018978197877692832219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32163345985465251795221479 48245018978197877692832219)
        ·
          refine ⟨72367528467296816539248329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48245018978197877692832219 72367528467296816539248329)
          ·
            refine ⟨54275646350472612404436247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72367528467296816539248329 54275646350472612404436247)
            ·
              refine ⟨81413469525708918606654371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54275646350472612404436247 81413469525708918606654371)
              ·
                refine ⟨122120204288563377909981557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81413469525708918606654371 122120204288563377909981557)
                ·
                  refine ⟨11448769152052816679060771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122120204288563377909981557 11448769152052816679060771)
                  ·
                    refine ⟨17173153728079225018591157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11448769152052816679060771 17173153728079225018591157)
                    ·
                      refine ⟨1609983162007427345492921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17173153728079225018591157 1609983162007427345492921)
                      ·
                        rfl

theorem cell23_3135431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_3135431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135431 prefixEnd_3135431 := by exact prefixLift 3135431
  have htrace : WordTrace (prefixWord ++ tailWord_3135431) baseStart_3135431 baseEnd_3135431 := by
    simpa [prefixWord, tailWord_3135431, baseEnd_3135431] using wordTrace_append hprefix tailTrace_3135431
  have hstable : (prefixWord ++ tailWord_3135431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135431).length < 2 ^ (prefixWord ++ tailWord_3135431).sum := by decide
  have hdescent : baseEnd_3135431 < baseStart_3135431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135438 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_3135438 : Nat := 118140960795 + 3135438 * 2 ^ 59
def prefixEnd_3135438 : Nat := 4983230072969 + 3 ^ 40 * 3135438 * 2
def baseEnd_3135438 : Nat := 536662252124002939368463

theorem tailTrace_3135438 : CollatzResearch.WordTrace tailWord_3135438 prefixEnd_3135438 536662252124002939368463 := by
  unfold tailWord_3135438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14294852351856386377869871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76239212543234060681972645 14294852351856386377869871)
  ·
    refine ⟨21442278527784579566804807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14294852351856386377869871 21442278527784579566804807)
    ·
      refine ⟨32163417791676869350207211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21442278527784579566804807 32163417791676869350207211)
      ·
        refine ⟨48245126687515304025310817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32163417791676869350207211 48245126687515304025310817)
        ·
          refine ⟨36183845015636478018983113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48245126687515304025310817 36183845015636478018983113)
          ·
            refine ⟨27137883761727358514237335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36183845015636478018983113 27137883761727358514237335)
            ·
              refine ⟨40706825642591037771356003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27137883761727358514237335 40706825642591037771356003)
              ·
                refine ⟨61060238463886556657034005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40706825642591037771356003 61060238463886556657034005)
                ·
                  refine ⟨2862198677994682343298469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61060238463886556657034005 2862198677994682343298469)
                  ·
                    refine ⟨536662252124002939368463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2862198677994682343298469 536662252124002939368463)
                    ·
                      rfl

theorem cell23_3135438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3135438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135438 prefixEnd_3135438 := by exact prefixLift 3135438
  have htrace : WordTrace (prefixWord ++ tailWord_3135438) baseStart_3135438 baseEnd_3135438 := by
    simpa [prefixWord, tailWord_3135438, baseEnd_3135438] using wordTrace_append hprefix tailTrace_3135438
  have hstable : (prefixWord ++ tailWord_3135438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135438).length < 2 ^ (prefixWord ++ tailWord_3135438).sum := by decide
  have hdescent : baseEnd_3135438 < baseStart_3135438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135445 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3135445 : Nat := 118140960795 + 3135445 * 2 ^ 59
def prefixEnd_3135445 : Nat := 4983230072969 + 3 ^ 40 * 3135445 * 2
def baseEnd_3135445 : Nat := 1609990350736590290717857

theorem tailTrace_3135445 : CollatzResearch.WordTrace tailWord_3135445 prefixEnd_3135445 1609990350736590290717857 := by
  unfold tailWord_3135445
  simp only [CollatzResearch.WordTrace]
  refine ⟨114359074125825731218463789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76239382750550487478975859 114359074125825731218463789)
  ·
    refine ⟨42884652797184649206923921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114359074125825731218463789 42884652797184649206923921)
    ·
      refine ⟨32163489597888486905192941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42884652797184649206923921 32163489597888486905192941)
      ·
        refine ⟨12061308599208182589447353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32163489597888486905192941 12061308599208182589447353)
        ·
          refine ⟨9045981449406136942085515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12061308599208182589447353 9045981449406136942085515)
          ·
            refine ⟨13568972174109205413128273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9045981449406136942085515 13568972174109205413128273)
            ·
              refine ⟨10176729130581904059846205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13568972174109205413128273 10176729130581904059846205)
              ·
                refine ⟨3816273423968214022442327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10176729130581904059846205 3816273423968214022442327)
                ·
                  refine ⟨5724410135952321033663491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816273423968214022442327 5724410135952321033663491)
                  ·
                    refine ⟨8586615203928481550495237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5724410135952321033663491 8586615203928481550495237)
                    ·
                      refine ⟨1609990350736590290717857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8586615203928481550495237 1609990350736590290717857)
                      ·
                        rfl

theorem cell23_3135445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3135445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135445 prefixEnd_3135445 := by exact prefixLift 3135445
  have htrace : WordTrace (prefixWord ++ tailWord_3135445) baseStart_3135445 baseEnd_3135445 := by
    simpa [prefixWord, tailWord_3135445, baseEnd_3135445] using wordTrace_append hprefix tailTrace_3135445
  have hstable : (prefixWord ++ tailWord_3135445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135445).length < 2 ^ (prefixWord ++ tailWord_3135445).sum := by decide
  have hdescent : baseEnd_3135445 < baseStart_3135445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135448 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3135448 : Nat := 118140960795 + 3135448 * 2 ^ 59
def prefixEnd_3135448 : Nat := 4983230072969 + 3 ^ 40 * 3135448 * 2
def baseEnd_3135448 : Nat := 1609991891178553778980343

theorem tailTrace_3135448 : CollatzResearch.WordTrace tailWord_3135448 prefixEnd_3135448 1609991891178553778980343 := by
  unfold tailWord_3135448
  simp only [CollatzResearch.WordTrace]
  refine ⟨57179591772407431365411499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76239455696543241820548665 57179591772407431365411499)
  ·
    refine ⟨85769387658611147048117249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57179591772407431365411499 85769387658611147048117249)
    ·
      refine ⟨64327040743958360286087937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85769387658611147048117249 64327040743958360286087937)
      ·
        refine ⟨48245280557968770214565953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64327040743958360286087937 48245280557968770214565953)
        ·
          refine ⟨36183960418476577660924465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48245280557968770214565953 36183960418476577660924465)
          ·
            refine ⟨27137970313857433245693349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36183960418476577660924465 27137970313857433245693349)
            ·
              refine ⟨5088369433848268733567503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27137970313857433245693349 5088369433848268733567503)
              ·
                refine ⟨7632554150772403100351255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088369433848268733567503 7632554150772403100351255)
                ·
                  refine ⟨11448831226158604650526883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7632554150772403100351255 11448831226158604650526883)
                  ·
                    refine ⟨17173246839237906975790325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11448831226158604650526883 17173246839237906975790325)
                    ·
                      refine ⟨1609991891178553778980343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17173246839237906975790325 1609991891178553778980343)
                      ·
                        rfl

theorem cell23_3135448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3135448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135448 prefixEnd_3135448 := by exact prefixLift 3135448
  have htrace : WordTrace (prefixWord ++ tailWord_3135448) baseStart_3135448 baseEnd_3135448 := by
    simpa [prefixWord, tailWord_3135448, baseEnd_3135448] using wordTrace_append hprefix tailTrace_3135448
  have hstable : (prefixWord ++ tailWord_3135448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135448).length < 2 ^ (prefixWord ++ tailWord_3135448).sum := by decide
  have hdescent : baseEnd_3135448 < baseStart_3135448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135471 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_3135471 : Nat := 118140960795 + 3135471 * 2 ^ 59
def prefixEnd_3135471 : Nat := 4983230072969 + 3 ^ 40 * 3135471 * 2
def baseEnd_3135471 : Nat := 1610003701233607188992737

theorem tailTrace_3135471 : CollatzResearch.WordTrace tailWord_3135471 prefixEnd_3135471 1610003701233607188992737 := by
  unfold tailWord_3135471
  simp only [CollatzResearch.WordTrace]
  refine ⟨114360022423731537658910267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76240014949154358439273511 114360022423731537658910267)
  ·
    refine ⟨171540033635597306488365401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114360022423731537658910267 171540033635597306488365401)
    ·
      refine ⟨128655025226697979866274051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171540033635597306488365401 128655025226697979866274051)
      ·
        refine ⟨192982537840046969799411077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128655025226697979866274051 192982537840046969799411077)
        ·
          refine ⟨36184225845008806837389577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192982537840046969799411077 36184225845008806837389577)
          ·
            refine ⟨27138169383756605128042183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36184225845008806837389577 27138169383756605128042183)
            ·
              refine ⟨40707254075634907692063275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27138169383756605128042183 40707254075634907692063275)
              ·
                refine ⟨61060881113452361538094913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40707254075634907692063275 61060881113452361538094913)
                ·
                  refine ⟨45795660835089271153571185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61060881113452361538094913 45795660835089271153571185)
                  ·
                    refine ⟨34346745626316953365178389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45795660835089271153571185 34346745626316953365178389)
                    ·
                      refine ⟨1610003701233607188992737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34346745626316953365178389 1610003701233607188992737)
                      ·
                        rfl

theorem cell23_3135471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_3135471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135471 prefixEnd_3135471 := by exact prefixLift 3135471
  have htrace : WordTrace (prefixWord ++ tailWord_3135471) baseStart_3135471 baseEnd_3135471 := by
    simpa [prefixWord, tailWord_3135471, baseEnd_3135471] using wordTrace_append hprefix tailTrace_3135471
  have hstable : (prefixWord ++ tailWord_3135471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135471).length < 2 ^ (prefixWord ++ tailWord_3135471).sum := by decide
  have hdescent : baseEnd_3135471 < baseStart_3135471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135491 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 5]
def baseStart_3135491 : Nat := 118140960795 + 3135491 * 2 ^ 59
def prefixEnd_3135491 : Nat := 4983230072969 + 3 ^ 40 * 3135491 * 2
def baseEnd_3135491 : Nat := 1610013970846697110742645

theorem tailTrace_3135491 : CollatzResearch.WordTrace tailWord_3135491 prefixEnd_3135491 1610013970846697110742645 := by
  unfold tailWord_3135491
  simp only [CollatzResearch.WordTrace]
  refine ⟨114360751883659081074638327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76240501255772720716425551 114360751883659081074638327)
  ·
    refine ⟨171541127825488621611957491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114360751883659081074638327 171541127825488621611957491)
    ·
      refine ⟨257311691738232932417936237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171541127825488621611957491 257311691738232932417936237)
      ·
        refine ⟨96491884401837349656726089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257311691738232932417936237 96491884401837349656726089)
        ·
          refine ⟨72368913301378012242544567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96491884401837349656726089 72368913301378012242544567)
          ·
            refine ⟨108553369952067018363816851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72368913301378012242544567 108553369952067018363816851)
            ·
              refine ⟨162830054928100527545725277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108553369952067018363816851 162830054928100527545725277)
              ·
                refine ⟨61061270598037697829646979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162830054928100527545725277 61061270598037697829646979)
                ·
                  refine ⟨91591905897056546744470469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61061270598037697829646979 91591905897056546744470469)
                  ·
                    refine ⟨17173482355698102514588213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91591905897056546744470469 17173482355698102514588213)
                    ·
                      refine ⟨1610013970846697110742645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17173482355698102514588213 1610013970846697110742645)
                      ·
                        rfl

theorem cell23_3135491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_3135491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135491 prefixEnd_3135491 := by exact prefixLift 3135491
  have htrace : WordTrace (prefixWord ++ tailWord_3135491) baseStart_3135491 baseEnd_3135491 := by
    simpa [prefixWord, tailWord_3135491, baseEnd_3135491] using wordTrace_append hprefix tailTrace_3135491
  have hstable : (prefixWord ++ tailWord_3135491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135491).length < 2 ^ (prefixWord ++ tailWord_3135491).sum := by decide
  have hdescent : baseEnd_3135491 < baseStart_3135491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135492 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3135492 : Nat := 118140960795 + 3135492 * 2 ^ 59
def prefixEnd_3135492 : Nat := 4983230072969 + 3 ^ 40 * 3135492 * 2
def baseEnd_3135492 : Nat := 1610014484327351606830141

theorem tailTrace_3135492 : CollatzResearch.WordTrace tailWord_3135492 prefixEnd_3135492 1610014484327351606830141 := by
  unfold tailWord_3135492
  simp only [CollatzResearch.WordTrace]
  refine ⟨57180394178327729122712365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76240525571103638830283153 57180394178327729122712365)
  ·
    refine ⟨21442647816872898421017137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57180394178327729122712365 21442647816872898421017137)
    ·
      refine ⟨16081985862654673815762853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21442647816872898421017137 16081985862654673815762853)
      ·
        refine ⟨3015372349247751340455535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16081985862654673815762853 3015372349247751340455535)
        ·
          refine ⟨4523058523871627010683303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015372349247751340455535 4523058523871627010683303)
          ·
            refine ⟨6784587785807440516024955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523058523871627010683303 6784587785807440516024955)
            ·
              refine ⟨10176881678711160774037433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784587785807440516024955 10176881678711160774037433)
              ·
                refine ⟨7632661259033370580528075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10176881678711160774037433 7632661259033370580528075)
                ·
                  refine ⟨11448991888550055870792113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7632661259033370580528075 11448991888550055870792113)
                  ·
                    refine ⟨8586743916412541903094085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11448991888550055870792113 8586743916412541903094085)
                    ·
                      refine ⟨1610014484327351606830141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8586743916412541903094085 1610014484327351606830141)
                      ·
                        rfl

theorem cell23_3135492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3135492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135492 prefixEnd_3135492 := by exact prefixLift 3135492
  have htrace : WordTrace (prefixWord ++ tailWord_3135492) baseStart_3135492 baseEnd_3135492 := by
    simpa [prefixWord, tailWord_3135492, baseEnd_3135492] using wordTrace_append hprefix tailTrace_3135492
  have hstable : (prefixWord ++ tailWord_3135492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135492).length < 2 ^ (prefixWord ++ tailWord_3135492).sum := by decide
  have hdescent : baseEnd_3135492 < baseStart_3135492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135495 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3135495 : Nat := 118140960795 + 3135495 * 2 ^ 59
def prefixEnd_3135495 : Nat := 4983230072969 + 3 ^ 40 * 3135495 * 2
def baseEnd_3135495 : Nat := 1610016024769315095092627

theorem tailTrace_3135495 : CollatzResearch.WordTrace tailWord_3135495 prefixEnd_3135495 1610016024769315095092627 := by
  unfold tailWord_3135495
  simp only [CollatzResearch.WordTrace]
  refine ⟨114360897775644589757783939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76240598517096393171855959 114360897775644589757783939)
  ·
    refine ⟨171541346663466884636675909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114360897775644589757783939 171541346663466884636675909)
    ·
      refine ⟨32164002499400040869376733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171541346663466884636675909 32164002499400040869376733)
      ·
        refine ⟨12061500937275015326016275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32164002499400040869376733 12061500937275015326016275)
        ·
          refine ⟨18092251405912522989024413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12061500937275015326016275 18092251405912522989024413)
          ·
            refine ⟨6784594277217196120884155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18092251405912522989024413 6784594277217196120884155)
            ·
              refine ⟨10176891415825794181326233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784594277217196120884155 10176891415825794181326233)
              ·
                refine ⟨7632668561869345635994675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10176891415825794181326233 7632668561869345635994675)
                ·
                  refine ⟨11449002842804018453992013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7632668561869345635994675 11449002842804018453992013)
                  ·
                    refine ⟨4293376066051506920247005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11449002842804018453992013 4293376066051506920247005)
                    ·
                      refine ⟨1610016024769315095092627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4293376066051506920247005 1610016024769315095092627)
                      ·
                        rfl

theorem cell23_3135495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3135495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135495 prefixEnd_3135495 := by exact prefixLift 3135495
  have htrace : WordTrace (prefixWord ++ tailWord_3135495) baseStart_3135495 baseEnd_3135495 := by
    simpa [prefixWord, tailWord_3135495, baseEnd_3135495] using wordTrace_append hprefix tailTrace_3135495
  have hstable : (prefixWord ++ tailWord_3135495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135495).length < 2 ^ (prefixWord ++ tailWord_3135495).sum := by decide
  have hdescent : baseEnd_3135495 < baseStart_3135495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135512 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3135512 : Nat := 118140960795 + 3135512 * 2 ^ 59
def prefixEnd_3135512 : Nat := 4983230072969 + 3 ^ 40 * 3135512 * 2
def baseEnd_3135512 : Nat := 1610024753940441528580049

theorem tailTrace_3135512 : CollatzResearch.WordTrace tailWord_3135512 prefixEnd_3135512 1610024753940441528580049 := by
  unfold tailWord_3135512
  simp only [CollatzResearch.WordTrace]
  refine ⟨57180758908291500830576395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76241011877722001107435193 57180758908291500830576395)
  ·
    refine ⟨85771138362437251245864593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57180758908291500830576395 85771138362437251245864593)
    ·
      refine ⟨64328353771827938434398445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85771138362437251245864593 64328353771827938434398445)
      ·
        refine ⟨24123132664435476912899417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64328353771827938434398445 24123132664435476912899417)
        ·
          refine ⟨18092349498326607684674563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24123132664435476912899417 18092349498326607684674563)
          ·
            refine ⟨27138524247489911527011845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18092349498326607684674563 27138524247489911527011845)
            ·
              refine ⟨5088473296404358411314721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27138524247489911527011845 5088473296404358411314721)
              ·
                refine ⟨3816354972303268808486041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5088473296404358411314721 3816354972303268808486041)
                ·
                  refine ⟨2862266229227451606364531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816354972303268808486041 2862266229227451606364531)
                  ·
                    refine ⟨4293399343841177409546797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2862266229227451606364531 4293399343841177409546797)
                    ·
                      refine ⟨1610024753940441528580049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4293399343841177409546797 1610024753940441528580049)
                      ·
                        rfl

theorem cell23_3135512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3135512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135512 prefixEnd_3135512 := by exact prefixLift 3135512
  have htrace : WordTrace (prefixWord ++ tailWord_3135512) baseStart_3135512 baseEnd_3135512 := by
    simpa [prefixWord, tailWord_3135512, baseEnd_3135512] using wordTrace_append hprefix tailTrace_3135512
  have hstable : (prefixWord ++ tailWord_3135512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135512).length < 2 ^ (prefixWord ++ tailWord_3135512).sum := by decide
  have hdescent : baseEnd_3135512 < baseStart_3135512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135548 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_3135548 : Nat := 118140960795 + 3135548 * 2 ^ 59
def prefixEnd_3135548 : Nat := 4983230072969 + 3 ^ 40 * 3135548 * 2
def baseEnd_3135548 : Nat := 1610043239244003387729883

theorem tailTrace_3135548 : CollatzResearch.WordTrace tailWord_3135548 prefixEnd_3135548 1610043239244003387729883 := by
  unfold tailWord_3135548
  simp only [CollatzResearch.WordTrace]
  refine ⟨57181415422226289904731649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76241887229635053206308865 57181415422226289904731649)
  ·
    refine ⟨42886061566669717428548737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57181415422226289904731649 42886061566669717428548737)
    ·
      refine ⟨32164546175002288071411553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42886061566669717428548737 32164546175002288071411553)
      ·
        refine ⟨24123409631251716053558665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32164546175002288071411553 24123409631251716053558665)
        ·
          refine ⟨18092557223438787040168999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24123409631251716053558665 18092557223438787040168999)
          ·
            refine ⟨27138835835158180560253499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18092557223438787040168999 27138835835158180560253499)
            ·
              refine ⟨40708253752737270840380249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27138835835158180560253499 40708253752737270840380249)
              ·
                refine ⟨30531190314552953130285187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40708253752737270840380249 30531190314552953130285187)
                ·
                  refine ⟨45796785471829429695427781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30531190314552953130285187 45796785471829429695427781)
                  ·
                    refine ⟨8586897275968018067892709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45796785471829429695427781 8586897275968018067892709)
                    ·
                      refine ⟨1610043239244003387729883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8586897275968018067892709 1610043239244003387729883)
                      ·
                        rfl

theorem cell23_3135548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_3135548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135548 prefixEnd_3135548 := by exact prefixLift 3135548
  have htrace : WordTrace (prefixWord ++ tailWord_3135548) baseStart_3135548 baseEnd_3135548 := by
    simpa [prefixWord, tailWord_3135548, baseEnd_3135548] using wordTrace_append hprefix tailTrace_3135548
  have hstable : (prefixWord ++ tailWord_3135548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135548).length < 2 ^ (prefixWord ++ tailWord_3135548).sum := by decide
  have hdescent : baseEnd_3135548 < baseStart_3135548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135565 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3135565 : Nat := 118140960795 + 3135565 * 2 ^ 59
def prefixEnd_3135565 : Nat := 4983230072969 + 3 ^ 40 * 3135565 * 2
def baseEnd_3135565 : Nat := 1610051968415129821217305

theorem tailTrace_3135565 : CollatzResearch.WordTrace tailWord_3135565 prefixEnd_3135565 1610051968415129821217305 := by
  unfold tailWord_3135565
  simp only [CollatzResearch.WordTrace]
  refine ⟨114363450885390991712832149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76242300590260661141888099 114363450885390991712832149)
  ·
    refine ⟨5360786760252702736539007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114363450885390991712832149 5360786760252702736539007)
    ·
      refine ⟨8041180140379054104808511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5360786760252702736539007 8041180140379054104808511)
      ·
        refine ⟨12061770210568581157212767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8041180140379054104808511 12061770210568581157212767)
        ·
          refine ⟨18092655315852871735819151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12061770210568581157212767 18092655315852871735819151)
          ·
            refine ⟨27138982973779307603728727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18092655315852871735819151 27138982973779307603728727)
            ·
              refine ⟨40708474460668961405593091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27138982973779307603728727 40708474460668961405593091)
              ·
                refine ⟨61062711691003442108389637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40708474460668961405593091 61062711691003442108389637)
                ·
                  refine ⟨11449258442063145395323057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61062711691003442108389637 11449258442063145395323057)
                  ·
                    refine ⟨8586943831547359046492293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11449258442063145395323057 8586943831547359046492293)
                    ·
                      refine ⟨1610051968415129821217305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8586943831547359046492293 1610051968415129821217305)
                      ·
                        rfl

theorem cell23_3135565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3135565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135565 prefixEnd_3135565 := by exact prefixLift 3135565
  have htrace : WordTrace (prefixWord ++ tailWord_3135565) baseStart_3135565 baseEnd_3135565 := by
    simpa [prefixWord, tailWord_3135565, baseEnd_3135565] using wordTrace_append hprefix tailTrace_3135565
  have hstable : (prefixWord ++ tailWord_3135565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135565).length < 2 ^ (prefixWord ++ tailWord_3135565).sum := by decide
  have hdescent : baseEnd_3135565 < baseStart_3135565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135575 : List Nat := [1, 1, 3, 2, 2, 1, 4, 4, 5]
def baseStart_3135575 : Nat := 118140960795 + 3135575 * 2 ^ 59
def prefixEnd_3135575 : Nat := 4983230072969 + 3 ^ 40 * 3135575 * 2
def baseEnd_3135575 : Nat := 178895233691297198010251

theorem tailTrace_3135575 : CollatzResearch.WordTrace tailWord_3135575 prefixEnd_3135575 178895233691297198010251 := by
  unfold tailWord_3135575
  simp only [CollatzResearch.WordTrace]
  refine ⟨114363815615354763420696179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76242543743569842280464119 114363815615354763420696179)
  ·
    refine ⟨171545723423032145131044269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114363815615354763420696179 171545723423032145131044269)
    ·
      refine ⟨64329646283637054424141601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171545723423032145131044269 64329646283637054424141601)
      ·
        refine ⟨48247234712727790818106201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64329646283637054424141601 48247234712727790818106201)
        ·
          refine ⟨36185426034545843113579651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48247234712727790818106201 36185426034545843113579651)
          ·
            refine ⟨54278139051818764670369477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36185426034545843113579651 54278139051818764670369477)
            ·
              refine ⟨10177151072216018375694277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54278139051818764670369477 10177151072216018375694277)
              ·
                refine ⟨1908215826040503445442677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10177151072216018375694277 1908215826040503445442677)
                ·
                  refine ⟨178895233691297198010251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1908215826040503445442677 178895233691297198010251)
                  ·
                    rfl

theorem cell23_3135575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 5].length) (baseStart_3135575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135575 prefixEnd_3135575 := by exact prefixLift 3135575
  have htrace : WordTrace (prefixWord ++ tailWord_3135575) baseStart_3135575 baseEnd_3135575 := by
    simpa [prefixWord, tailWord_3135575, baseEnd_3135575] using wordTrace_append hprefix tailTrace_3135575
  have hstable : (prefixWord ++ tailWord_3135575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135575).length < 2 ^ (prefixWord ++ tailWord_3135575).sum := by decide
  have hdescent : baseEnd_3135575 < baseStart_3135575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135586 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3135586 : Nat := 118140960795 + 3135586 * 2 ^ 59
def prefixEnd_3135586 : Nat := 4983230072969 + 3 ^ 40 * 3135586 * 2
def baseEnd_3135586 : Nat := 1610062751508874239054709

theorem tailTrace_3135586 : CollatzResearch.WordTrace tailWord_3135586 prefixEnd_3135586 1610062751508874239054709 := by
  unfold tailWord_3135586
  simp only [CollatzResearch.WordTrace]
  refine ⟨28591054204578728074836653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76242811212209941532897741 28591054204578728074836653)
  ·
    refine ⟨10721645326717023028063745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28591054204578728074836653 10721645326717023028063745)
    ·
      refine ⟨8041233995037767271047809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10721645326717023028063745 8041233995037767271047809)
      ·
        refine ⟨6030925496278325453285857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8041233995037767271047809 6030925496278325453285857)
        ·
          refine ⟨4523194122208744089964393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6030925496278325453285857 4523194122208744089964393)
          ·
            refine ⟨3392395591656558067473295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4523194122208744089964393 3392395591656558067473295)
            ·
              refine ⟨5088593387484837101209943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392395591656558067473295 5088593387484837101209943)
              ·
                refine ⟨7632890081227255651814915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088593387484837101209943 7632890081227255651814915)
                ·
                  refine ⟨11449335121840883477722373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7632890081227255651814915 11449335121840883477722373)
                  ·
                    refine ⟨2146750335345165652072945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11449335121840883477722373 2146750335345165652072945)
                    ·
                      refine ⟨1610062751508874239054709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146750335345165652072945 1610062751508874239054709)
                      ·
                        rfl

theorem cell23_3135586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3135586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135586 prefixEnd_3135586 := by exact prefixLift 3135586
  have htrace : WordTrace (prefixWord ++ tailWord_3135586) baseStart_3135586 baseEnd_3135586 := by
    simpa [prefixWord, tailWord_3135586, baseEnd_3135586] using wordTrace_append hprefix tailTrace_3135586
  have hstable : (prefixWord ++ tailWord_3135586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135586).length < 2 ^ (prefixWord ++ tailWord_3135586).sum := by decide
  have hdescent : baseEnd_3135586 < baseStart_3135586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135588 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_3135588 : Nat := 118140960795 + 3135588 * 2 ^ 59
def prefixEnd_3135588 : Nat := 4983230072969 + 3 ^ 40 * 3135588 * 2
def baseEnd_3135588 : Nat := 536687926156727743743233

theorem tailTrace_3135588 : CollatzResearch.WordTrace tailWord_3135588 prefixEnd_3135588 536687926156727743743233 := by
  unfold tailWord_3135588
  simp only [CollatzResearch.WordTrace]
  refine ⟨57182144882153833320459709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76242859842871777760612945 57182144882153833320459709)
  ·
    refine ⟨21443304330807687495172391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57182144882153833320459709 21443304330807687495172391)
    ·
      refine ⟨32164956496211531242758587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21443304330807687495172391 32164956496211531242758587)
      ·
        refine ⟨48247434744317296864137881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32164956496211531242758587 48247434744317296864137881)
        ·
          refine ⟨36185576058237972648103411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48247434744317296864137881 36185576058237972648103411)
          ·
            refine ⟨54278364087356958972155117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36185576058237972648103411 54278364087356958972155117)
            ·
              refine ⟨20354386532758859614558169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54278364087356958972155117 20354386532758859614558169)
              ·
                refine ⟨15265789899569144710918627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20354386532758859614558169 15265789899569144710918627)
                ·
                  refine ⟨22898684849353717066377941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15265789899569144710918627 22898684849353717066377941)
                  ·
                    refine ⟨536687926156727743743233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22898684849353717066377941 536687926156727743743233)
                    ·
                      rfl

theorem cell23_3135588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_3135588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135588 prefixEnd_3135588 := by exact prefixLift 3135588
  have htrace : WordTrace (prefixWord ++ tailWord_3135588) baseStart_3135588 baseEnd_3135588 := by
    simpa [prefixWord, tailWord_3135588, baseEnd_3135588] using wordTrace_append hprefix tailTrace_3135588
  have hstable : (prefixWord ++ tailWord_3135588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135588).length < 2 ^ (prefixWord ++ tailWord_3135588).sum := by decide
  have hdescent : baseEnd_3135588 < baseStart_3135588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135625 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_3135625 : Nat := 118140960795 + 3135625 * 2 ^ 59
def prefixEnd_3135625 : Nat := 4983230072969 + 3 ^ 40 * 3135625 * 2
def baseEnd_3135625 : Nat := 1610082777254399586467029

theorem tailTrace_3135625 : CollatzResearch.WordTrace tailWord_3135625 prefixEnd_3135625 1610082777254399586467029 := by
  unfold tailWord_3135625
  simp only [CollatzResearch.WordTrace]
  refine ⟨114365639265173621960016329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76243759510115747973344219 114365639265173621960016329)
  ·
    refine ⟨85774229448880216470012247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114365639265173621960016329 85774229448880216470012247)
    ·
      refine ⟨128661344173320324705018371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85774229448880216470012247 128661344173320324705018371)
      ·
        refine ⟨192992016259980487057527557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128661344173320324705018371 192992016259980487057527557)
        ·
          refine ⟨36186003048746341323286417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192992016259980487057527557 36186003048746341323286417)
          ·
            refine ⟨27139502286559755992464813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36186003048746341323286417 27139502286559755992464813)
            ·
              refine ⟨10177313357459908497174305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27139502286559755992464813 10177313357459908497174305)
              ·
                refine ⟨7632985018094931372880729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10177313357459908497174305 7632985018094931372880729)
                ·
                  refine ⟨5724738763571198529660547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7632985018094931372880729 5724738763571198529660547)
                  ·
                    refine ⟨8587108145356797794490821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5724738763571198529660547 8587108145356797794490821)
                    ·
                      refine ⟨1610082777254399586467029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8587108145356797794490821 1610082777254399586467029)
                      ·
                        rfl

theorem cell23_3135625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_3135625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135625 prefixEnd_3135625 := by exact prefixLift 3135625
  have htrace : WordTrace (prefixWord ++ tailWord_3135625) baseStart_3135625 baseEnd_3135625 := by
    simpa [prefixWord, tailWord_3135625, baseEnd_3135625] using wordTrace_append hprefix tailTrace_3135625
  have hstable : (prefixWord ++ tailWord_3135625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135625).length < 2 ^ (prefixWord ++ tailWord_3135625).sum := by decide
  have hdescent : baseEnd_3135625 < baseStart_3135625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135709 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3135709 : Nat := 118140960795 + 3135709 * 2 ^ 59
def prefixEnd_3135709 : Nat := 4983230072969 + 3 ^ 40 * 3135709 * 2
def baseEnd_3135709 : Nat := 1610125909629377257816643

theorem tailTrace_3135709 : CollatzResearch.WordTrace tailWord_3135709 prefixEnd_3135709 1610125909629377257816643 := by
  unfold tailWord_3135709
  simp only [CollatzResearch.WordTrace]
  refine ⟨114368702996869304306074181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76245801997912869537382787 114368702996869304306074181)
  ·
    refine ⟨21444131811912994557388909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114368702996869304306074181 21444131811912994557388909)
    ·
      refine ⟨8041549429467372959020841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21444131811912994557388909 8041549429467372959020841)
      ·
        refine ⟨6031162072100529719265631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8041549429467372959020841 6031162072100529719265631)
        ·
          refine ⟨9046743108150794578898447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031162072100529719265631 9046743108150794578898447)
          ·
            refine ⟨13570114662226191868347671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9046743108150794578898447 13570114662226191868347671)
            ·
              refine ⟨20355171993339287802521507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13570114662226191868347671 20355171993339287802521507)
              ·
                refine ⟨30532757990008931703782261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20355171993339287802521507 30532757990008931703782261)
                ·
                  refine ⟨2862446061563337347229587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30532757990008931703782261 2862446061563337347229587)
                  ·
                    refine ⟨4293669092345006020844381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2862446061563337347229587 4293669092345006020844381)
                    ·
                      refine ⟨1610125909629377257816643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4293669092345006020844381 1610125909629377257816643)
                      ·
                        rfl

theorem cell23_3135709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3135709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135709 prefixEnd_3135709 := by exact prefixLift 3135709
  have htrace : WordTrace (prefixWord ++ tailWord_3135709) baseStart_3135709 baseEnd_3135709 := by
    simpa [prefixWord, tailWord_3135709, baseEnd_3135709] using wordTrace_append hprefix tailTrace_3135709
  have hstable : (prefixWord ++ tailWord_3135709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135709).length < 2 ^ (prefixWord ++ tailWord_3135709).sum := by decide
  have hdescent : baseEnd_3135709 < baseStart_3135709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135719 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3135719 : Nat := 118140960795 + 3135719 * 2 ^ 59
def prefixEnd_3135719 : Nat := 4983230072969 + 3 ^ 40 * 3135719 * 2
def baseEnd_3135719 : Nat := 1610131044435922218691597

theorem tailTrace_3135719 : CollatzResearch.WordTrace tailWord_3135719 prefixEnd_3135719 1610131044435922218691597 := by
  unfold tailWord_3135719
  simp only [CollatzResearch.WordTrace]
  refine ⟨114369067726833076013938211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76246045151222050675958807 114369067726833076013938211)
  ·
    refine ⟨171553601590249614020907317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114369067726833076013938211 171553601590249614020907317)
    ·
      refine ⟨16083150149085901314460061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171553601590249614020907317 16083150149085901314460061)
      ·
        refine ⟨6031181305907212992922523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16083150149085901314460061 6031181305907212992922523)
        ·
          refine ⟨9046771958860819489383785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031181305907212992922523 9046771958860819489383785)
          ·
            refine ⟨6785078969145614617037839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9046771958860819489383785 6785078969145614617037839)
            ·
              refine ⟨10177618453718421925556759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785078969145614617037839 10177618453718421925556759)
              ·
                refine ⟨15266427680577632888335139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10177618453718421925556759 15266427680577632888335139)
                ·
                  refine ⟨22899641520866449332502709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15266427680577632888335139 22899641520866449332502709)
                  ·
                    refine ⟨2146841392581229624922129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22899641520866449332502709 2146841392581229624922129)
                    ·
                      refine ⟨1610131044435922218691597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146841392581229624922129 1610131044435922218691597)
                      ·
                        rfl

theorem cell23_3135719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3135719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135719 prefixEnd_3135719 := by exact prefixLift 3135719
  have htrace : WordTrace (prefixWord ++ tailWord_3135719) baseStart_3135719 baseEnd_3135719 := by
    simpa [prefixWord, tailWord_3135719, baseEnd_3135719] using wordTrace_append hprefix tailTrace_3135719
  have hstable : (prefixWord ++ tailWord_3135719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135719).length < 2 ^ (prefixWord ++ tailWord_3135719).sum := by decide
  have hdescent : baseEnd_3135719 < baseStart_3135719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135745 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3135745 : Nat := 118140960795 + 3135745 * 2 ^ 59
def prefixEnd_3135745 : Nat := 4983230072969 + 3 ^ 40 * 3135745 * 2
def baseEnd_3135745 : Nat := 1610144394932939116966477

theorem tailTrace_3135745 : CollatzResearch.WordTrace tailWord_3135745 prefixEnd_3135745 1610144394932939116966477 := by
  unfold tailWord_3135745
  simp only [CollatzResearch.WordTrace]
  refine ⟨114370016024738882454384689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76246677349825921636256459 114370016024738882454384689)
  ·
    refine ⟨85777512018554161840788517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114370016024738882454384689 85777512018554161840788517)
    ·
      refine ⟨16083283503478905345147847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85777512018554161840788517 16083283503478905345147847)
      ·
        refine ⟨24124925255218358017721771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16083283503478905345147847 24124925255218358017721771)
        ·
          refine ⟨36187387882827537026582657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24124925255218358017721771 36187387882827537026582657)
          ·
            refine ⟨27140540912120652769936993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36187387882827537026582657 27140540912120652769936993)
            ·
              refine ⟨20355405684090489577452745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27140540912120652769936993 20355405684090489577452745)
              ·
                refine ⟨15266554263067867183089559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20355405684090489577452745 15266554263067867183089559)
                ·
                  refine ⟨22899831394601800774634339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15266554263067867183089559 22899831394601800774634339)
                  ·
                    refine ⟨34349747091902701161951509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22899831394601800774634339 34349747091902701161951509)
                    ·
                      refine ⟨1610144394932939116966477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34349747091902701161951509 1610144394932939116966477)
                      ·
                        rfl

theorem cell23_3135745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3135745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135745 prefixEnd_3135745 := by exact prefixLift 3135745
  have htrace : WordTrace (prefixWord ++ tailWord_3135745) baseStart_3135745 baseEnd_3135745 := by
    simpa [prefixWord, tailWord_3135745, baseEnd_3135745] using wordTrace_append hprefix tailTrace_3135745
  have hstable : (prefixWord ++ tailWord_3135745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135745).length < 2 ^ (prefixWord ++ tailWord_3135745).sum := by decide
  have hdescent : baseEnd_3135745 < baseStart_3135745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135752 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3135752 : Nat := 118140960795 + 3135752 * 2 ^ 59
def prefixEnd_3135752 : Nat := 4983230072969 + 3 ^ 40 * 3135752 * 2
def baseEnd_3135752 : Nat := 1610147989297520589578945

theorem tailTrace_3135752 : CollatzResearch.WordTrace tailWord_3135752 prefixEnd_3135752 1610147989297520589578945 := by
  unfold tailWord_3135752
  simp only [CollatzResearch.WordTrace]
  refine ⟨57185135667856761324944755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76246847557142348433259673 57185135667856761324944755)
  ·
    refine ⟨85777703501785141987417133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57185135667856761324944755 85777703501785141987417133)
    ·
      refine ⟨32166638813169428245281425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85777703501785141987417133 32166638813169428245281425)
      ·
        refine ⟨24124979109877071183961069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32166638813169428245281425 24124979109877071183961069)
        ·
          refine ⟨9046867166203901693985401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24124979109877071183961069 9046867166203901693985401)
          ·
            refine ⟨6785150374652926270489051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9046867166203901693985401 6785150374652926270489051)
            ·
              refine ⟨10177725561979389405733577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785150374652926270489051 10177725561979389405733577)
              ·
                refine ⟨7633294171484542054300183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10177725561979389405733577 7633294171484542054300183)
                ·
                  refine ⟨11449941257226813081450275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7633294171484542054300183 11449941257226813081450275)
                  ·
                    refine ⟨17174911885840219622175413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11449941257226813081450275 17174911885840219622175413)
                    ·
                      refine ⟨1610147989297520589578945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17174911885840219622175413 1610147989297520589578945)
                      ·
                        rfl

theorem cell23_3135752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3135752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135752 prefixEnd_3135752 := by exact prefixLift 3135752
  have htrace : WordTrace (prefixWord ++ tailWord_3135752) baseStart_3135752 baseEnd_3135752 := by
    simpa [prefixWord, tailWord_3135752, baseEnd_3135752] using wordTrace_append hprefix tailTrace_3135752
  have hstable : (prefixWord ++ tailWord_3135752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135752).length < 2 ^ (prefixWord ++ tailWord_3135752).sum := by decide
  have hdescent : baseEnd_3135752 < baseStart_3135752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135789 : List Nat := [1, 5, 3, 1, 2, 2, 9]
def baseStart_3135789 : Nat := 118140960795 + 3135789 * 2 ^ 59
def prefixEnd_3135789 : Nat := 4983230072969 + 3 ^ 40 * 3135789 * 2
def baseEnd_3135789 : Nat := 19878604791132554874275

theorem tailTrace_3135789 : CollatzResearch.WordTrace tailWord_3135789 prefixEnd_3135789 19878604791132554874275 := by
  unfold tailWord_3135789
  simp only [CollatzResearch.WordTrace]
  refine ⟨114371620836579477968986421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76247747224386318645990947 114371620836579477968986421)
  ·
    refine ⟨10722339453429326059592477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114371620836579477968986421 10722339453429326059592477)
    ·
      refine ⟨4020877295035997272347179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10722339453429326059592477 4020877295035997272347179)
      ·
        refine ⟨6031315942553995908520769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020877295035997272347179 6031315942553995908520769)
        ·
          refine ⟨4523486956915496931390577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6031315942553995908520769 4523486956915496931390577)
          ·
            refine ⟨3392615217686622698542933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4523486956915496931390577 3392615217686622698542933)
            ·
              refine ⟨19878604791132554874275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3392615217686622698542933 19878604791132554874275)
              ·
                rfl

theorem cell23_3135789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 9].length) (baseStart_3135789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135789 prefixEnd_3135789 := by exact prefixLift 3135789
  have htrace : WordTrace (prefixWord ++ tailWord_3135789) baseStart_3135789 baseEnd_3135789 := by
    simpa [prefixWord, tailWord_3135789, baseEnd_3135789] using wordTrace_append hprefix tailTrace_3135789
  have hstable : (prefixWord ++ tailWord_3135789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135789).length < 2 ^ (prefixWord ++ tailWord_3135789).sum := by decide
  have hdescent : baseEnd_3135789 < baseStart_3135789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135795 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 5]
def baseStart_3135795 : Nat := 118140960795 + 3135795 * 2 ^ 59
def prefixEnd_3135795 : Nat := 4983230072969 + 3 ^ 40 * 3135795 * 2
def baseEnd_3135795 : Nat := 1610170068965663921341247

theorem tailTrace_3135795 : CollatzResearch.WordTrace tailWord_3135795 prefixEnd_3135795 1610170068965663921341247 := by
  unfold tailWord_3135795
  simp only [CollatzResearch.WordTrace]
  refine ⟨114371839674557740993704839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76247893116371827329136559 114371839674557740993704839)
  ·
    refine ⟨171557759511836611490557259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114371839674557740993704839 171557759511836611490557259)
    ·
      refine ⟨257336639267754917235835889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171557759511836611490557259 257336639267754917235835889)
      ·
        refine ⟨193002479450816187926876917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257336639267754917235835889 193002479450816187926876917)
        ·
          refine ⟨18093982448514017618144711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193002479450816187926876917 18093982448514017618144711)
          ·
            refine ⟨27140973672771026427217067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18093982448514017618144711 27140973672771026427217067)
            ·
              refine ⟨40711460509156539640825601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27140973672771026427217067 40711460509156539640825601)
              ·
                refine ⟨30533595381867404730619201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40711460509156539640825601 30533595381867404730619201)
                ·
                  refine ⟨22900196536400553547964401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30533595381867404730619201 22900196536400553547964401)
                  ·
                    refine ⟨17175147402300415160973301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22900196536400553547964401 17175147402300415160973301)
                    ·
                      refine ⟨1610170068965663921341247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17175147402300415160973301 1610170068965663921341247)
                      ·
                        rfl

theorem cell23_3135795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_3135795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135795 prefixEnd_3135795 := by exact prefixLift 3135795
  have htrace : WordTrace (prefixWord ++ tailWord_3135795) baseStart_3135795 baseEnd_3135795 := by
    simpa [prefixWord, tailWord_3135795, baseEnd_3135795] using wordTrace_append hprefix tailTrace_3135795
  have hstable : (prefixWord ++ tailWord_3135795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135795).length < 2 ^ (prefixWord ++ tailWord_3135795).sum := by decide
  have hdescent : baseEnd_3135795 < baseStart_3135795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135815 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 1, 8]
def baseStart_3135815 : Nat := 118140960795 + 3135815 * 2 ^ 59
def prefixEnd_3135815 : Nat := 4983230072969 + 3 ^ 40 * 3135815 * 2
def baseEnd_3135815 : Nat := 536726779526251281030385

theorem tailTrace_3135815 : CollatzResearch.WordTrace tailWord_3135815 prefixEnd_3135815 536726779526251281030385 := by
  unfold tailWord_3135815
  simp only [CollatzResearch.WordTrace]
  refine ⟨114372569134485284409432899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76248379422990189606288599 114372569134485284409432899)
  ·
    refine ⟨171558853701727926614149349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114372569134485284409432899 171558853701727926614149349)
    ·
      refine ⟨32167285069073986240153003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171558853701727926614149349 32167285069073986240153003)
      ·
        refine ⟨48250927603610979360229505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32167285069073986240153003 48250927603610979360229505)
        ·
          refine ⟨36188195702708234520172129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48250927603610979360229505 36188195702708234520172129)
          ·
            refine ⟨27141146777031175890129097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36188195702708234520172129 27141146777031175890129097)
            ·
              refine ⟨20355860082773381917596823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27141146777031175890129097 20355860082773381917596823)
              ·
                refine ⟨30533790124160072876395235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20355860082773381917596823 30533790124160072876395235)
                ·
                  refine ⟨45800685186240109314592853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30533790124160072876395235 45800685186240109314592853)
                  ·
                    refine ⟨536726779526251281030385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45800685186240109314592853 536726779526251281030385)
                    ·
                      rfl

theorem cell23_3135815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_3135815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135815 prefixEnd_3135815 := by exact prefixLift 3135815
  have htrace : WordTrace (prefixWord ++ tailWord_3135815) baseStart_3135815 baseEnd_3135815 := by
    simpa [prefixWord, tailWord_3135815, baseEnd_3135815] using wordTrace_append hprefix tailTrace_3135815
  have hstable : (prefixWord ++ tailWord_3135815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135815).length < 2 ^ (prefixWord ++ tailWord_3135815).sum := by decide
  have hdescent : baseEnd_3135815 < baseStart_3135815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135816 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_3135816 : Nat := 118140960795 + 3135816 * 2 ^ 59
def prefixEnd_3135816 : Nat := 4983230072969 + 3 ^ 40 * 3135816 * 2
def baseEnd_3135816 : Nat := 1610180852059408339178651

theorem tailTrace_3135816 : CollatzResearch.WordTrace tailWord_3135816 prefixEnd_3135816 1610180852059408339178651 := by
  unfold tailWord_3135816
  simp only [CollatzResearch.WordTrace]
  refine ⟨57186302803740830790109651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76248403738321107720146201 57186302803740830790109651)
  ·
    refine ⟨85779454205611246185164477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57186302803740830790109651 85779454205611246185164477)
    ·
      refine ⟨32167295327104217319436679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85779454205611246185164477 32167295327104217319436679)
      ·
        refine ⟨48250942990656325979155019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32167295327104217319436679 48250942990656325979155019)
        ·
          refine ⟨72376414485984488968732529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48250942990656325979155019 72376414485984488968732529)
          ·
            refine ⟨54282310864488366726549397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72376414485984488968732529 54282310864488366726549397)
            ·
              refine ⟨2544483321772892190307003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54282310864488366726549397 2544483321772892190307003)
              ·
                refine ⟨3816724982659338285460505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544483321772892190307003 3816724982659338285460505)
                ·
                  refine ⟨2862543736994503714095379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816724982659338285460505 2862543736994503714095379)
                  ·
                    refine ⟨4293815605491755571143069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2862543736994503714095379 4293815605491755571143069)
                    ·
                      refine ⟨1610180852059408339178651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4293815605491755571143069 1610180852059408339178651)
                      ·
                        rfl

theorem cell23_3135816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_3135816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135816 prefixEnd_3135816 := by exact prefixLift 3135816
  have htrace : WordTrace (prefixWord ++ tailWord_3135816) baseStart_3135816 baseEnd_3135816 := by
    simpa [prefixWord, tailWord_3135816, baseEnd_3135816] using wordTrace_append hprefix tailTrace_3135816
  have hstable : (prefixWord ++ tailWord_3135816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135816).length < 2 ^ (prefixWord ++ tailWord_3135816).sum := by decide
  have hdescent : baseEnd_3135816 < baseStart_3135816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135826 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_3135826 : Nat := 118140960795 + 3135826 * 2 ^ 59
def prefixEnd_3135826 : Nat := 4983230072969 + 3 ^ 40 * 3135826 * 2
def baseEnd_3135826 : Nat := 1610185986865953300053605

theorem tailTrace_3135826 : CollatzResearch.WordTrace tailWord_3135826 prefixEnd_3135826 1610185986865953300053605 := by
  unfold tailWord_3135826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28593242584361358322020833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76248646891630288858722221 28593242584361358322020833)
  ·
    refine ⟨21444931938271018741515625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28593242584361358322020833 21444931938271018741515625)
    ·
      refine ⟨16083698953703264056136719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21444931938271018741515625 16083698953703264056136719)
      ·
        refine ⟨24125548430554896084205079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16083698953703264056136719 24125548430554896084205079)
        ·
          refine ⟨36188322645832344126307619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24125548430554896084205079 36188322645832344126307619)
          ·
            refine ⟨54282483968748516189461429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36188322645832344126307619 54282483968748516189461429)
            ·
              refine ⟨5088982872070173392762009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54282483968748516189461429 5088982872070173392762009)
              ·
                refine ⟨3816737154052630044571507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5088982872070173392762009 3816737154052630044571507)
                ·
                  refine ⟨5725105731078945066857261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816737154052630044571507 5725105731078945066857261)
                  ·
                    refine ⟨2146914649154604400071473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5725105731078945066857261 2146914649154604400071473)
                    ·
                      refine ⟨1610185986865953300053605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146914649154604400071473 1610185986865953300053605)
                      ·
                        rfl

theorem cell23_3135826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_3135826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135826 prefixEnd_3135826 := by exact prefixLift 3135826
  have htrace : WordTrace (prefixWord ++ tailWord_3135826) baseStart_3135826 baseEnd_3135826 := by
    simpa [prefixWord, tailWord_3135826, baseEnd_3135826] using wordTrace_append hprefix tailTrace_3135826
  have hstable : (prefixWord ++ tailWord_3135826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135826).length < 2 ^ (prefixWord ++ tailWord_3135826).sum := by decide
  have hdescent : baseEnd_3135826 < baseStart_3135826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135839 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 6, 2, 2]
def baseStart_3135839 : Nat := 118140960795 + 3135839 * 2 ^ 59
def prefixEnd_3135839 : Nat := 4983230072969 + 3 ^ 40 * 3135839 * 2
def baseEnd_3135839 : Nat := 1610192662114461749191045

theorem tailTrace_3135839 : CollatzResearch.WordTrace tailWord_3135839 prefixEnd_3135839 1610192662114461749191045 := by
  unfold tailWord_3135839
  simp only [CollatzResearch.WordTrace]
  refine ⟨114373444486398336508306571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76248962990932224338871047 114373444486398336508306571)
  ·
    refine ⟨171560166729597504762459857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114373444486398336508306571 171560166729597504762459857)
    ·
      refine ⟨128670125047198128571844893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171560166729597504762459857 128670125047198128571844893)
      ·
        refine ⟨48251296892699298214441835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128670125047198128571844893 48251296892699298214441835)
        ·
          refine ⟨72376945339048947321662753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48251296892699298214441835 72376945339048947321662753)
          ·
            refine ⟨54282709004286710491247065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72376945339048947321662753 54282709004286710491247065)
            ·
              refine ⟨40712031753215032868435299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54282709004286710491247065 40712031753215032868435299)
              ·
                refine ⟨61068047629822549302652949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40712031753215032868435299 61068047629822549302652949)
                ·
                  refine ⟨2862564732647931998561857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61068047629822549302652949 2862564732647931998561857)
                  ·
                    refine ⟨2146923549485948998921393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2862564732647931998561857 2146923549485948998921393)
                    ·
                      refine ⟨1610192662114461749191045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146923549485948998921393 1610192662114461749191045)
                      ·
                        rfl

theorem cell23_3135839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_3135839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135839 prefixEnd_3135839 := by exact prefixLift 3135839
  have htrace : WordTrace (prefixWord ++ tailWord_3135839) baseStart_3135839 baseEnd_3135839 := by
    simpa [prefixWord, tailWord_3135839, baseEnd_3135839] using wordTrace_append hprefix tailTrace_3135839
  have hstable : (prefixWord ++ tailWord_3135839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135839).length < 2 ^ (prefixWord ++ tailWord_3135839).sum := by decide
  have hdescent : baseEnd_3135839 < baseStart_3135839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135856 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 2, 2, 2]
def baseStart_3135856 : Nat := 118140960795 + 3135856 * 2 ^ 59
def prefixEnd_3135856 : Nat := 4983230072969 + 3 ^ 40 * 3135856 * 2
def baseEnd_3135856 : Nat := 1610201391285588182678467

theorem tailTrace_3135856 : CollatzResearch.WordTrace tailWord_3135856 prefixEnd_3135856 1610201391285588182678467 := by
  unfold tailWord_3135856
  simp only [CollatzResearch.WordTrace]
  refine ⟨57187032263668374205837711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76249376351557832274450281 57187032263668374205837711)
  ·
    refine ⟨85780548395502561308756567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57187032263668374205837711 85780548395502561308756567)
    ·
      refine ⟨128670822593253841963134851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85780548395502561308756567 128670822593253841963134851)
      ·
        refine ⟨193006233889880762944702277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128670822593253841963134851 193006233889880762944702277)
        ·
          refine ⟨36188668854352643052131677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193006233889880762944702277 36188668854352643052131677)
          ·
            refine ⟨13570750820382241144549379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36188668854352643052131677 13570750820382241144549379)
            ·
              refine ⟨20356126230573361716824069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13570750820382241144549379 20356126230573361716824069)
              ·
                refine ⟨3816773668232505321904513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20356126230573361716824069 3816773668232505321904513)
                ·
                  refine ⟨2862580251174378991428385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816773668232505321904513 2862580251174378991428385)
                  ·
                    refine ⟨2146935188380784243571289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2862580251174378991428385 2146935188380784243571289)
                    ·
                      refine ⟨1610201391285588182678467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146935188380784243571289 1610201391285588182678467)
                      ·
                        rfl

theorem cell23_3135856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 2, 2].length) (baseStart_3135856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135856 prefixEnd_3135856 := by exact prefixLift 3135856
  have htrace : WordTrace (prefixWord ++ tailWord_3135856) baseStart_3135856 baseEnd_3135856 := by
    simpa [prefixWord, tailWord_3135856, baseEnd_3135856] using wordTrace_append hprefix tailTrace_3135856
  have hstable : (prefixWord ++ tailWord_3135856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135856).length < 2 ^ (prefixWord ++ tailWord_3135856).sum := by decide
  have hdescent : baseEnd_3135856 < baseStart_3135856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135865 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_3135865 : Nat := 118140960795 + 3135865 * 2 ^ 59
def prefixEnd_3135865 : Nat := 4983230072969 + 3 ^ 40 * 3135865 * 2
def baseEnd_3135865 : Nat := 1610206012611478647465925

theorem tailTrace_3135865 : CollatzResearch.WordTrace tailWord_3135865 prefixEnd_3135865 1610206012611478647465925 := by
  unfold tailWord_3135865
  simp only [CollatzResearch.WordTrace]
  refine ⟨114374392784304142948753049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76249595189536095299168699 114374392784304142948753049)
  ·
    refine ⟨85780794588228107211564787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114374392784304142948753049 85780794588228107211564787)
    ·
      refine ⟨128671191882342160817347181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85780794588228107211564787 128671191882342160817347181)
      ·
        refine ⟨48251696955878310306505193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128671191882342160817347181 48251696955878310306505193)
        ·
          refine ⟨36188772716908732729878895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48251696955878310306505193 36188772716908732729878895)
          ·
            refine ⟨54283159075363099094818343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36188772716908732729878895 54283159075363099094818343)
            ·
              refine ⟨81424738613044648642227515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54283159075363099094818343 81424738613044648642227515)
              ·
                refine ⟨122137107919566972963341273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81424738613044648642227515 122137107919566972963341273)
                ·
                  refine ⟨91602830939675229722505955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122137107919566972963341273 91602830939675229722505955)
                  ·
                    refine ⟨137404246409512844583758933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91602830939675229722505955 137404246409512844583758933)
                    ·
                      refine ⟨1610206012611478647465925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 137404246409512844583758933 1610206012611478647465925)
                      ·
                        rfl

theorem cell23_3135865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_3135865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135865 prefixEnd_3135865 := by exact prefixLift 3135865
  have htrace : WordTrace (prefixWord ++ tailWord_3135865) baseStart_3135865 baseEnd_3135865 := by
    simpa [prefixWord, tailWord_3135865, baseEnd_3135865] using wordTrace_append hprefix tailTrace_3135865
  have hstable : (prefixWord ++ tailWord_3135865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135865).length < 2 ^ (prefixWord ++ tailWord_3135865).sum := by decide
  have hdescent : baseEnd_3135865 < baseStart_3135865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135873 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_3135873 : Nat := 118140960795 + 3135873 * 2 ^ 59
def prefixEnd_3135873 : Nat := 4983230072969 + 3 ^ 40 * 3135873 * 2
def baseEnd_3135873 : Nat := 1610210120456714616165889

theorem tailTrace_3135873 : CollatzResearch.WordTrace tailWord_3135873 prefixEnd_3135873 1610210120456714616165889 := by
  unfold tailWord_3135873
  simp only [CollatzResearch.WordTrace]
  refine ⟨114374684568275160315044273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76249789712183440210029515 114374684568275160315044273)
  ·
    refine ⟨85781013426206370236283205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114374684568275160315044273 85781013426206370236283205)
    ·
      refine ⟨16083940017413694419303101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85781013426206370236283205 16083940017413694419303101)
      ·
        refine ⟨6031477506530135407238663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16083940017413694419303101 6031477506530135407238663)
        ·
          refine ⟨9047216259795203110857995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031477506530135407238663 9047216259795203110857995)
          ·
            refine ⟨13570824389692804666286993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9047216259795203110857995 13570824389692804666286993)
            ·
              refine ⟨10178118292269603499715245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13570824389692804666286993 10178118292269603499715245)
              ·
                refine ⟨3816794359601101312393217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10178118292269603499715245 3816794359601101312393217)
                ·
                  refine ⟨2862595769700825984294913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816794359601101312393217 2862595769700825984294913)
                  ·
                    refine ⟨2146946827275619488221185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2862595769700825984294913 2146946827275619488221185)
                    ·
                      refine ⟨1610210120456714616165889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146946827275619488221185 1610210120456714616165889)
                      ·
                        rfl

theorem cell23_3135873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_3135873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135873 prefixEnd_3135873 := by exact prefixLift 3135873
  have htrace : WordTrace (prefixWord ++ tailWord_3135873) baseStart_3135873 baseEnd_3135873 := by
    simpa [prefixWord, tailWord_3135873, baseEnd_3135873] using wordTrace_append hprefix tailTrace_3135873
  have hstable : (prefixWord ++ tailWord_3135873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135873).length < 2 ^ (prefixWord ++ tailWord_3135873).sum := by decide
  have hdescent : baseEnd_3135873 < baseStart_3135873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135896 : List Nat := [2, 1, 2, 5, 1, 2, 2, 3, 5]
def baseStart_3135896 : Nat := 118140960795 + 3135896 * 2 ^ 59
def prefixEnd_3135896 : Nat := 4983230072969 + 3 ^ 40 * 3135896 * 2
def baseEnd_3135896 : Nat := 178913547834640891797587

theorem tailTrace_3135896 : CollatzResearch.WordTrace tailWord_3135896 prefixEnd_3135896 178913547834640891797587 := by
  unfold tailWord_3135896
  simp only [CollatzResearch.WordTrace]
  refine ⟨57187761723595917621565771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76250348964794556828754361 57187761723595917621565771)
  ·
    refine ⟨85781642585393876432348657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57187761723595917621565771 85781642585393876432348657)
    ·
      refine ⟨64336231939045407324261493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85781642585393876432348657 64336231939045407324261493)
      ·
        refine ⟨6031521744285506936649515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64336231939045407324261493 6031521744285506936649515)
        ·
          refine ⟨9047282616428260404974273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031521744285506936649515 9047282616428260404974273)
          ·
            refine ⟨6785461962321195303730705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9047282616428260404974273 6785461962321195303730705)
            ·
              refine ⟨5089096471740896477798029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6785461962321195303730705 5089096471740896477798029)
              ·
                refine ⟨1908411176902836179174261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5089096471740896477798029 1908411176902836179174261)
                ·
                  refine ⟨178913547834640891797587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1908411176902836179174261 178913547834640891797587)
                  ·
                    rfl

theorem cell23_3135896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 5].length) (baseStart_3135896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135896 prefixEnd_3135896 := by exact prefixLift 3135896
  have htrace : WordTrace (prefixWord ++ tailWord_3135896) baseStart_3135896 baseEnd_3135896 := by
    simpa [prefixWord, tailWord_3135896, baseEnd_3135896] using wordTrace_append hprefix tailTrace_3135896
  have hstable : (prefixWord ++ tailWord_3135896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135896).length < 2 ^ (prefixWord ++ tailWord_3135896).sum := by decide
  have hdescent : baseEnd_3135896 < baseStart_3135896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135915 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 11]
def baseStart_3135915 : Nat := 118140960795 + 3135915 * 2 ^ 59
def prefixEnd_3135915 : Nat := 4983230072969 + 3 ^ 40 * 3135915 * 2
def baseEnd_3135915 : Nat := 1610231686644203451840695

theorem tailTrace_3135915 : CollatzResearch.WordTrace tailWord_3135915 prefixEnd_3135915 1610231686644203451840695 := by
  unfold tailWord_3135915
  simp only [CollatzResearch.WordTrace]
  refine ⟨114376216434123001488073199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76250810956082000992048799 114376216434123001488073199)
  ·
    refine ⟨171564324651184502232109799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114376216434123001488073199 171564324651184502232109799)
    ·
      refine ⟨257346486976776753348164699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171564324651184502232109799 257346486976776753348164699)
      ·
        refine ⟨386019730465165130022247049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257346486976776753348164699 386019730465165130022247049)
        ·
          refine ⟨289514797848873847516685287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386019730465165130022247049 289514797848873847516685287)
          ·
            refine ⟨434272196773310771275027931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289514797848873847516685287 434272196773310771275027931)
            ·
              refine ⟨651408295159966156912541897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434272196773310771275027931 651408295159966156912541897)
              ·
                refine ⟨488556221369974617684406423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651408295159966156912541897 488556221369974617684406423)
                ·
                  refine ⟨732834332054961926526609635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488556221369974617684406423 732834332054961926526609635)
                  ·
                    refine ⟨1099251498082442889789914453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 732834332054961926526609635 1099251498082442889789914453)
                    ·
                      refine ⟨1610231686644203451840695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1099251498082442889789914453 1610231686644203451840695)
                      ·
                        rfl

theorem cell23_3135915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_3135915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135915 prefixEnd_3135915 := by exact prefixLift 3135915
  have htrace : WordTrace (prefixWord ++ tailWord_3135915) baseStart_3135915 baseEnd_3135915 := by
    simpa [prefixWord, tailWord_3135915, baseEnd_3135915] using wordTrace_append hprefix tailTrace_3135915
  have hstable : (prefixWord ++ tailWord_3135915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135915).length < 2 ^ (prefixWord ++ tailWord_3135915).sum := by decide
  have hdescent : baseEnd_3135915 < baseStart_3135915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135924 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3135924 : Nat := 118140960795 + 3135924 * 2 ^ 59
def prefixEnd_3135924 : Nat := 4983230072969 + 3 ^ 40 * 3135924 * 2
def baseEnd_3135924 : Nat := 1610236307970093916628155

theorem tailTrace_3135924 : CollatzResearch.WordTrace tailWord_3135924 prefixEnd_3135924 1610236307970093916628155 := by
  unfold tailWord_3135924
  simp only [CollatzResearch.WordTrace]
  refine ⟨57188272345545198012575413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76251029794060264016767217 57188272345545198012575413)
  ·
    refine ⟨5361400532394862313678945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57188272345545198012575413 5361400532394862313678945)
    ·
      refine ⟨4021050399296146735259209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5361400532394862313678945 4021050399296146735259209)
      ·
        refine ⟨3015787799472110051444407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4021050399296146735259209 3015787799472110051444407)
        ·
          refine ⟨4523681699208165077166611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015787799472110051444407 4523681699208165077166611)
          ·
            refine ⟨6785522548812247615749917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523681699208165077166611 6785522548812247615749917)
            ·
              refine ⟨2544570955804592855906219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6785522548812247615749917 2544570955804592855906219)
              ·
                refine ⟨3816856433706889283859329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544570955804592855906219 3816856433706889283859329)
                ·
                  refine ⟨2862642325280166962894497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3816856433706889283859329 2862642325280166962894497)
                  ·
                    refine ⟨2146981743960125222170873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2862642325280166962894497 2146981743960125222170873)
                    ·
                      refine ⟨1610236307970093916628155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2146981743960125222170873 1610236307970093916628155)
                      ·
                        rfl

theorem cell23_3135924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3135924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135924 prefixEnd_3135924 := by exact prefixLift 3135924
  have htrace : WordTrace (prefixWord ++ tailWord_3135924) baseStart_3135924 baseEnd_3135924 := by
    simpa [prefixWord, tailWord_3135924, baseEnd_3135924] using wordTrace_append hprefix tailTrace_3135924
  have hstable : (prefixWord ++ tailWord_3135924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135924).length < 2 ^ (prefixWord ++ tailWord_3135924).sum := by decide
  have hdescent : baseEnd_3135924 < baseStart_3135924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135973 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_3135973 : Nat := 118140960795 + 3135973 * 2 ^ 59
def prefixEnd_3135973 : Nat := 4983230072969 + 3 ^ 40 * 3135973 * 2
def baseEnd_3135973 : Nat := 536753822840721408305143

theorem tailTrace_3135973 : CollatzResearch.WordTrace tailWord_3135973 prefixEnd_3135973 536753822840721408305143 := by
  unfold tailWord_3135973
  simp only [CollatzResearch.WordTrace]
  refine ⟨114378331867912877393684573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76252221245275251595789715 114378331867912877393684573)
  ·
    refine ⟨42891874450467329022631715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114378331867912877393684573 42891874450467329022631715)
    ·
      refine ⟨64337811675700993533947573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42891874450467329022631715 64337811675700993533947573)
      ·
        refine ⟨6031669844596968143807585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64337811675700993533947573 6031669844596968143807585)
        ·
          refine ⟨4523752383447726107855689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6031669844596968143807585 4523752383447726107855689)
          ·
            refine ⟨3392814287585794580891767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4523752383447726107855689 3392814287585794580891767)
            ·
              refine ⟨5089221431378691871337651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392814287585794580891767 5089221431378691871337651)
              ·
                refine ⟨7633832147068037807006477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5089221431378691871337651 7633832147068037807006477)
                ·
                  refine ⟨2862687055150514177627429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7633832147068037807006477 2862687055150514177627429)
                  ·
                    refine ⟨536753822840721408305143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2862687055150514177627429 536753822840721408305143)
                    ·
                      rfl

theorem cell23_3135973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_3135973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135973 prefixEnd_3135973 := by exact prefixLift 3135973
  have htrace : WordTrace (prefixWord ++ tailWord_3135973) baseStart_3135973 baseEnd_3135973 := by
    simpa [prefixWord, tailWord_3135973, baseEnd_3135973] using wordTrace_append hprefix tailTrace_3135973
  have hstable : (prefixWord ++ tailWord_3135973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135973).length < 2 ^ (prefixWord ++ tailWord_3135973).sum := by decide
  have hdescent : baseEnd_3135973 < baseStart_3135973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3135986 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 6]
def baseStart_3135986 : Nat := 118140960795 + 3135986 * 2 ^ 59
def prefixEnd_3135986 : Nat := 4983230072969 + 3 ^ 40 * 3135986 * 2
def baseEnd_3135986 : Nat := 178918682641185852672541

theorem tailTrace_3135986 : CollatzResearch.WordTrace tailWord_3135986 prefixEnd_3135986 178918682641185852672541 := by
  unfold tailWord_3135986
  simp only [CollatzResearch.WordTrace]
  refine ⟨28594701504216445153476953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76252537344577187075938541 28594701504216445153476953)
  ·
    refine ⟨21446026128162333865107715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28594701504216445153476953 21446026128162333865107715)
    ·
      refine ⟨32169039192243500797661573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21446026128162333865107715 32169039192243500797661573)
      ·
        refine ⟨6031694848545656399561545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32169039192243500797661573 6031694848545656399561545)
        ·
          refine ⟨4523771136409242299671159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6031694848545656399561545 4523771136409242299671159)
          ·
            refine ⟨6785656704613863449506739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523771136409242299671159 6785656704613863449506739)
            ·
              refine ⟨10178485056920795174260109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785656704613863449506739 10178485056920795174260109)
              ·
                refine ⟨3816931896345298190347541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10178485056920795174260109 3816931896345298190347541)
                ·
                  refine ⟨178918682641185852672541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3816931896345298190347541 178918682641185852672541)
                  ·
                    rfl

theorem cell23_3135986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_3135986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3135986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3135986 prefixEnd_3135986 := by exact prefixLift 3135986
  have htrace : WordTrace (prefixWord ++ tailWord_3135986) baseStart_3135986 baseEnd_3135986 := by
    simpa [prefixWord, tailWord_3135986, baseEnd_3135986] using wordTrace_append hprefix tailTrace_3135986
  have hstable : (prefixWord ++ tailWord_3135986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3135986).length < 2 ^ (prefixWord ++ tailWord_3135986).sum := by decide
  have hdescent : baseEnd_3135986 < baseStart_3135986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3135986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136049 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3136049 : Nat := 118140960795 + 3136049 * 2 ^ 59
def prefixEnd_3136049 : Nat := 4983230072969 + 3 ^ 40 * 3136049 * 2
def baseEnd_3136049 : Nat := 1610300493051905927565079

theorem tailTrace_3136049 : CollatzResearch.WordTrace tailWord_3136049 prefixEnd_3136049 1610300493051905927565079 := by
  unfold tailWord_3136049
  simp only [CollatzResearch.WordTrace]
  refine ⟨114381103815637542373451201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76254069210425028248967467 114381103815637542373451201)
  ·
    refine ⟨85785827861728156780088401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114381103815637542373451201 85785827861728156780088401)
    ·
      refine ⟨64339370896296117585066301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85785827861728156780088401 64339370896296117585066301)
      ·
        refine ⟨24127264086111044094399863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64339370896296117585066301 24127264086111044094399863)
        ·
          refine ⟨36190896129166566141599795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24127264086111044094399863 36190896129166566141599795)
          ·
            refine ⟨54286344193749849212399693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36190896129166566141599795 54286344193749849212399693)
            ·
              refine ⟨20357379072656193454649885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54286344193749849212399693 20357379072656193454649885)
              ·
                refine ⟨7634017152246072545493707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20357379072656193454649885 7634017152246072545493707)
                ·
                  refine ⟨11451025728369108818240561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7634017152246072545493707 11451025728369108818240561)
                  ·
                    refine ⟨8588269296276831613680421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11451025728369108818240561 8588269296276831613680421)
                    ·
                      refine ⟨1610300493051905927565079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8588269296276831613680421 1610300493051905927565079)
                      ·
                        rfl

theorem cell23_3136049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3136049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136049 prefixEnd_3136049 := by exact prefixLift 3136049
  have htrace : WordTrace (prefixWord ++ tailWord_3136049) baseStart_3136049 baseEnd_3136049 := by
    simpa [prefixWord, tailWord_3136049, baseEnd_3136049] using wordTrace_append hprefix tailTrace_3136049
  have hstable : (prefixWord ++ tailWord_3136049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136049).length < 2 ^ (prefixWord ++ tailWord_3136049).sum := by decide
  have hdescent : baseEnd_3136049 < baseStart_3136049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136053 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 3, 2, 2]
def baseStart_3136053 : Nat := 118140960795 + 3136053 * 2 ^ 59
def prefixEnd_3136053 : Nat := 4983230072969 + 3 ^ 40 * 3136053 * 2
def baseEnd_3136053 : Nat := 1610302546974523911915061

theorem tailTrace_3136053 : CollatzResearch.WordTrace tailWord_3136053 prefixEnd_3136053 1610302546974523911915061 := by
  unfold tailWord_3136053
  simp only [CollatzResearch.WordTrace]
  refine ⟨114381249707623051056596813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76254166471748700704397875 114381249707623051056596813)
  ·
    refine ⟨42892968640358644146223805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114381249707623051056596813 42892968640358644146223805)
    ·
      refine ⟨16084863240134491554833927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42892968640358644146223805 16084863240134491554833927)
      ·
        refine ⟨24127294860201737332250891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16084863240134491554833927 24127294860201737332250891)
        ·
          refine ⟨36190942290302605998376337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24127294860201737332250891 36190942290302605998376337)
          ·
            refine ⟨27143206717726954498782253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36190942290302605998376337 27143206717726954498782253)
            ·
              refine ⟨10178702519147607937043345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27143206717726954498782253 10178702519147607937043345)
              ·
                refine ⟨7634026889360705952782509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10178702519147607937043345 7634026889360705952782509)
                ·
                  refine ⟨2862760083510264732293441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7634026889360705952782509 2862760083510264732293441)
                  ·
                    refine ⟨2147070062632698549220081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2862760083510264732293441 2147070062632698549220081)
                    ·
                      refine ⟨1610302546974523911915061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2147070062632698549220081 1610302546974523911915061)
                      ·
                        rfl

theorem cell23_3136053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_3136053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136053 prefixEnd_3136053 := by exact prefixLift 3136053
  have htrace : WordTrace (prefixWord ++ tailWord_3136053) baseStart_3136053 baseEnd_3136053 := by
    simpa [prefixWord, tailWord_3136053, baseEnd_3136053] using wordTrace_append hprefix tailTrace_3136053
  have hstable : (prefixWord ++ tailWord_3136053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136053).length < 2 ^ (prefixWord ++ tailWord_3136053).sum := by decide
  have hdescent : baseEnd_3136053 < baseStart_3136053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136056 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_3136056 : Nat := 118140960795 + 3136056 * 2 ^ 59
def prefixEnd_3136056 : Nat := 4983230072969 + 3 ^ 40 * 3136056 * 2
def baseEnd_3136056 : Nat := 1610304087416487400177547

theorem tailTrace_3136056 : CollatzResearch.WordTrace tailWord_3136056 prefixEnd_3136056 1610304087416487400177547 := by
  unfold tailWord_3136056
  simp only [CollatzResearch.WordTrace]
  refine ⟨57190679563306091284478011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76254239417741455045970681 57190679563306091284478011)
  ·
    refine ⟨85786019344959136926717017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57190679563306091284478011 85786019344959136926717017)
    ·
      refine ⟨64339514508719352695037763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85786019344959136926717017 64339514508719352695037763)
      ·
        refine ⟨96509271763079029042556645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64339514508719352695037763 96509271763079029042556645)
        ·
          refine ⟨18095488455577317945479371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96509271763079029042556645 18095488455577317945479371)
          ·
            refine ⟨27143232683365976918219057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18095488455577317945479371 27143232683365976918219057)
            ·
              refine ⟨20357424512524482688664293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27143232683365976918219057 20357424512524482688664293)
              ·
                refine ⟨3817017096098340504124555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20357424512524482688664293 3817017096098340504124555)
                ·
                  refine ⟨5725525644147510756186833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3817017096098340504124555 5725525644147510756186833)
                  ·
                    refine ⟨4294144233110633067140125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5725525644147510756186833 4294144233110633067140125)
                    ·
                      refine ⟨1610304087416487400177547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4294144233110633067140125 1610304087416487400177547)
                      ·
                        rfl

theorem cell23_3136056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_3136056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136056 prefixEnd_3136056 := by exact prefixLift 3136056
  have htrace : WordTrace (prefixWord ++ tailWord_3136056) baseStart_3136056 baseEnd_3136056 := by
    simpa [prefixWord, tailWord_3136056, baseEnd_3136056] using wordTrace_append hprefix tailTrace_3136056
  have hstable : (prefixWord ++ tailWord_3136056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136056).length < 2 ^ (prefixWord ++ tailWord_3136056).sum := by decide
  have hdescent : baseEnd_3136056 < baseStart_3136056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136070 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3136070 : Nat := 118140960795 + 3136070 * 2 ^ 59
def prefixEnd_3136070 : Nat := 4983230072969 + 3 ^ 40 * 3136070 * 2
def baseEnd_3136070 : Nat := 1610311276145650345402483

theorem tailTrace_3136070 : CollatzResearch.WordTrace tailWord_3136070 prefixEnd_3136070 1610311276145650345402483 := by
  unfold tailWord_3136070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574433429642545717498927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76254579832374308639977109 3574433429642545717498927)
  ·
    refine ⟨5361650144463818576248391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3574433429642545717498927 5361650144463818576248391)
    ·
      refine ⟨8042475216695727864372587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5361650144463818576248391 8042475216695727864372587)
      ·
        refine ⟨12063712825043591796558881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8042475216695727864372587 12063712825043591796558881)
        ·
          refine ⟨9047784618782693847419161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12063712825043591796558881 9047784618782693847419161)
          ·
            refine ⟨6785838464087020385564371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9047784618782693847419161 6785838464087020385564371)
            ·
              refine ⟨10178757696130530578346557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785838464087020385564371 10178757696130530578346557)
              ·
                refine ⟨3817034136048948966879959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10178757696130530578346557 3817034136048948966879959)
                ·
                  refine ⟨5725551204073423450319939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3817034136048948966879959 5725551204073423450319939)
                  ·
                    refine ⟨8588326806110135175479909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5725551204073423450319939 8588326806110135175479909)
                    ·
                      refine ⟨1610311276145650345402483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8588326806110135175479909 1610311276145650345402483)
                      ·
                        rfl

theorem cell23_3136070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3136070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136070 prefixEnd_3136070 := by exact prefixLift 3136070
  have htrace : WordTrace (prefixWord ++ tailWord_3136070) baseStart_3136070 baseEnd_3136070 := by
    simpa [prefixWord, tailWord_3136070, baseEnd_3136070] using wordTrace_append hprefix tailTrace_3136070
  have hstable : (prefixWord ++ tailWord_3136070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136070).length < 2 ^ (prefixWord ++ tailWord_3136070).sum := by decide
  have hdescent : baseEnd_3136070 < baseStart_3136070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136096 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 5, 3, 2]
def baseStart_3136096 : Nat := 118140960795 + 3136096 * 2 ^ 59
def prefixEnd_3136096 : Nat := 4983230072969 + 3 ^ 40 * 3136096 * 2
def baseEnd_3136096 : Nat := 1610324626642667243677363

theorem tailTrace_3136096 : CollatzResearch.WordTrace tailWord_3136096 prefixEnd_3136096 1610324626642667243677363 := by
  unfold tailWord_3136096
  simp only [CollatzResearch.WordTrace]
  refine ⟨57191409023233634700206071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76255212030978179600274761 57191409023233634700206071)
  ·
    refine ⟨85787113534850452050309107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57191409023233634700206071 85787113534850452050309107)
    ·
      refine ⟨128680670302275678075463661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85787113534850452050309107 128680670302275678075463661)
      ·
        refine ⟨48255251363353379278298873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128680670302275678075463661 48255251363353379278298873)
        ·
          refine ⟨36191438522515034458724155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48255251363353379278298873 36191438522515034458724155)
          ·
            refine ⟨54287157783772551688086233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36191438522515034458724155 54287157783772551688086233)
            ·
              refine ⟨40715368337829413766064675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54287157783772551688086233 40715368337829413766064675)
              ·
                refine ⟨61073052506744120649097013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40715368337829413766064675 61073052506744120649097013)
                ·
                  refine ⟨5725598672507261310852845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61073052506744120649097013 5725598672507261310852845)
                  ·
                    refine ⟨2147099502190222991569817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5725598672507261310852845 2147099502190222991569817)
                    ·
                      refine ⟨1610324626642667243677363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2147099502190222991569817 1610324626642667243677363)
                      ·
                        rfl

theorem cell23_3136096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_3136096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136096 prefixEnd_3136096 := by exact prefixLift 3136096
  have htrace : WordTrace (prefixWord ++ tailWord_3136096) baseStart_3136096 baseEnd_3136096 := by
    simpa [prefixWord, tailWord_3136096, baseEnd_3136096] using wordTrace_append hprefix tailTrace_3136096
  have hstable : (prefixWord ++ tailWord_3136096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136096).length < 2 ^ (prefixWord ++ tailWord_3136096).sum := by decide
  have hdescent : baseEnd_3136096 < baseStart_3136096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136139 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 4]
def baseStart_3136139 : Nat := 118140960795 + 3136139 * 2 ^ 59
def prefixEnd_3136139 : Nat := 4983230072969 + 3 ^ 40 * 3136139 * 2
def baseEnd_3136139 : Nat := 1610346706310810575439665

theorem tailTrace_3136139 : CollatzResearch.WordTrace tailWord_3136139 prefixEnd_3136139 1610346706310810575439665 := by
  unfold tailWord_3136139
  simp only [CollatzResearch.WordTrace]
  refine ⟨114384386385311487744227471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76256257590207658496151647 114384386385311487744227471)
  ·
    refine ⟨171576579577967231616341207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114384386385311487744227471 171576579577967231616341207)
    ·
      refine ⟨257364869366950847424511811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171576579577967231616341207 257364869366950847424511811)
      ·
        refine ⟨386047304050426271136767717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257364869366950847424511811 386047304050426271136767717)
        ·
          refine ⟨72383869509454925838143947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386047304050426271136767717 72383869509454925838143947)
          ·
            refine ⟨108575804264182388757215921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72383869509454925838143947 108575804264182388757215921)
            ·
              refine ⟨81431853198136791567911941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108575804264182388757215921 81431853198136791567911941)
              ·
                refine ⟨15268472474650648418983489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81431853198136791567911941 15268472474650648418983489)
                ·
                  refine ⟨11451354355987986314237617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15268472474650648418983489 11451354355987986314237617)
                  ·
                    refine ⟨8588515766990989735678213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11451354355987986314237617 8588515766990989735678213)
                    ·
                      refine ⟨1610346706310810575439665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8588515766990989735678213 1610346706310810575439665)
                      ·
                        rfl

theorem cell23_3136139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 4].length) (baseStart_3136139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136139 prefixEnd_3136139 := by exact prefixLift 3136139
  have htrace : WordTrace (prefixWord ++ tailWord_3136139) baseStart_3136139 baseEnd_3136139 := by
    simpa [prefixWord, tailWord_3136139, baseEnd_3136139] using wordTrace_append hprefix tailTrace_3136139
  have hstable : (prefixWord ++ tailWord_3136139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136139).length < 2 ^ (prefixWord ++ tailWord_3136139).sum := by decide
  have hdescent : baseEnd_3136139 < baseStart_3136139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136154 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3136154 : Nat := 118140960795 + 3136154 * 2 ^ 59
def prefixEnd_3136154 : Nat := 4983230072969 + 3 ^ 40 * 3136154 * 2
def baseEnd_3136154 : Nat := 1610354408520628016752097

theorem tailTrace_3136154 : CollatzResearch.WordTrace tailWord_3136154 prefixEnd_3136154 1610354408520628016752097 := by
  unfold tailWord_3136154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28596233370064286326505879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76256622320171430204015677 28596233370064286326505879)
  ·
    refine ⟨42894350055096429489758819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28596233370064286326505879 42894350055096429489758819)
    ·
      refine ⟨64341525082644644234638229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42894350055096429489758819 64341525082644644234638229)
      ·
        refine ⟨3016008988248967698498667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64341525082644644234638229 3016008988248967698498667)
        ·
          refine ⟨4524013482373451547748001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3016008988248967698498667 4524013482373451547748001)
          ·
            refine ⟨3393010111780088660811001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4524013482373451547748001 3393010111780088660811001)
            ·
              refine ⟨2544757583835066495608251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3393010111780088660811001 2544757583835066495608251)
              ·
                refine ⟨3817136375752599743412377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544757583835066495608251 3817136375752599743412377)
                ·
                  refine ⟨2862852281814449807559283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3817136375752599743412377 2862852281814449807559283)
                  ·
                    refine ⟨4294278422721674711338925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2862852281814449807559283 4294278422721674711338925)
                    ·
                      refine ⟨1610354408520628016752097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4294278422721674711338925 1610354408520628016752097)
                      ·
                        rfl

theorem cell23_3136154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3136154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136154 prefixEnd_3136154 := by exact prefixLift 3136154
  have htrace : WordTrace (prefixWord ++ tailWord_3136154) baseStart_3136154 baseEnd_3136154 := by
    simpa [prefixWord, tailWord_3136154, baseEnd_3136154] using wordTrace_append hprefix tailTrace_3136154
  have hstable : (prefixWord ++ tailWord_3136154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136154).length < 2 ^ (prefixWord ++ tailWord_3136154).sum := by decide
  have hdescent : baseEnd_3136154 < baseStart_3136154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136200 : List Nat := [2, 1, 3, 1, 2, 5, 2, 2, 5]
def baseStart_3136200 : Nat := 118140960795 + 3136200 * 2 ^ 59
def prefixEnd_3136200 : Nat := 4983230072969 + 3 ^ 40 * 3136200 * 2
def baseEnd_3136200 : Nat := 178930892070081648530765

theorem tailTrace_3136200 : CollatzResearch.WordTrace tailWord_3136200 prefixEnd_3136200 178930892070081648530765 := by
  unfold tailWord_3136200
  simp only [CollatzResearch.WordTrace]
  refine ⟨57193305619045247581099027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76257740825393663441465369 57193305619045247581099027)
  ·
    refine ⟨85789958428567871371648541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57193305619045247581099027 85789958428567871371648541)
    ·
      refine ⟨32171234410712951764368203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85789958428567871371648541 32171234410712951764368203)
      ·
        refine ⟨48256851616069427646552305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32171234410712951764368203 48256851616069427646552305)
        ·
          refine ⟨36192638712052070734914229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48256851616069427646552305 36192638712052070734914229)
          ·
            refine ⟨3393059879254881631398209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36192638712052070734914229 3393059879254881631398209)
            ·
              refine ⟨2544794909441161223548657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3393059879254881631398209 2544794909441161223548657)
              ·
                refine ⟨1908596182080870917661493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2544794909441161223548657 1908596182080870917661493)
                ·
                  refine ⟨178930892070081648530765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1908596182080870917661493 178930892070081648530765)
                  ·
                    rfl

theorem cell23_3136200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 5].length) (baseStart_3136200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136200 prefixEnd_3136200 := by exact prefixLift 3136200
  have htrace : WordTrace (prefixWord ++ tailWord_3136200) baseStart_3136200 baseEnd_3136200 := by
    simpa [prefixWord, tailWord_3136200, baseEnd_3136200] using wordTrace_append hprefix tailTrace_3136200
  have hstable : (prefixWord ++ tailWord_3136200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136200).length < 2 ^ (prefixWord ++ tailWord_3136200).sum := by decide
  have hdescent : baseEnd_3136200 < baseStart_3136200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136206 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3136206 : Nat := 118140960795 + 3136206 * 2 ^ 59
def prefixEnd_3136206 : Nat := 4983230072969 + 3 ^ 40 * 3136206 * 2
def baseEnd_3136206 : Nat := 1610381109514661813301857

theorem tailTrace_3136206 : CollatzResearch.WordTrace tailWord_3136206 prefixEnd_3136206 1610381109514661813301857 := by
  unfold tailWord_3136206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14298353759508594773364559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76257886717379172124610981 14298353759508594773364559)
  ·
    refine ⟨21447530639262892160046839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14298353759508594773364559 21447530639262892160046839)
    ·
      refine ⟨32171295958894338240070259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21447530639262892160046839 32171295958894338240070259)
      ·
        refine ⟨48256943938341507360105389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32171295958894338240070259 48256943938341507360105389)
        ·
          refine ⟨18096353976878065260039521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48256943938341507360105389 18096353976878065260039521)
          ·
            refine ⟨13572265482658548945029641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18096353976878065260039521 13572265482658548945029641)
            ·
              refine ⟨10179199111993911708772231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13572265482658548945029641 10179199111993911708772231)
              ·
                refine ⟨15268798667990867563158347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10179199111993911708772231 15268798667990867563158347)
                ·
                  refine ⟨22903198001986301344737521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15268798667990867563158347 22903198001986301344737521)
                  ·
                    refine ⟨17177398501489726008553141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22903198001986301344737521 17177398501489726008553141)
                    ·
                      refine ⟨1610381109514661813301857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17177398501489726008553141 1610381109514661813301857)
                      ·
                        rfl

theorem cell23_3136206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3136206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136206 prefixEnd_3136206 := by exact prefixLift 3136206
  have htrace : WordTrace (prefixWord ++ tailWord_3136206) baseStart_3136206 baseEnd_3136206 := by
    simpa [prefixWord, tailWord_3136206, baseEnd_3136206] using wordTrace_append hprefix tailTrace_3136206
  have hstable : (prefixWord ++ tailWord_3136206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136206).length < 2 ^ (prefixWord ++ tailWord_3136206).sum := by decide
  have hdescent : baseEnd_3136206 < baseStart_3136206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136246 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3136246 : Nat := 118140960795 + 3136246 * 2 ^ 59
def prefixEnd_3136246 : Nat := 4983230072969 + 3 ^ 40 * 3136246 * 2
def baseEnd_3136246 : Nat := 1610401648740841656801673

theorem tailTrace_3136246 : CollatzResearch.WordTrace tailWord_3136246 prefixEnd_3136246 1610401648740841656801673 := by
  unfold tailWord_3136246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7149268062245240313648287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76258859330615896678915061 7149268062245240313648287)
  ·
    refine ⟨10723902093367860470472431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7149268062245240313648287 10723902093367860470472431)
    ·
      refine ⟨16085853140051790705708647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10723902093367860470472431 16085853140051790705708647)
      ·
        refine ⟨24128779710077686058562971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16085853140051790705708647 24128779710077686058562971)
        ·
          refine ⟨36193169565116529087844457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24128779710077686058562971 36193169565116529087844457)
          ·
            refine ⟨27144877173837396815883343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36193169565116529087844457 27144877173837396815883343)
            ·
              refine ⟨40717315760756095223825015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27144877173837396815883343 40717315760756095223825015)
              ·
                refine ⟨61075973641134142835737523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40717315760756095223825015 61075973641134142835737523)
                ·
                  refine ⟨91613960461701214253606285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61075973641134142835737523 91613960461701214253606285)
                  ·
                    refine ⟨34355235173137955345102357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91613960461701214253606285 34355235173137955345102357)
                    ·
                      refine ⟨1610401648740841656801673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34355235173137955345102357 1610401648740841656801673)
                      ·
                        rfl

theorem cell23_3136246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3136246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136246 prefixEnd_3136246 := by exact prefixLift 3136246
  have htrace : WordTrace (prefixWord ++ tailWord_3136246) baseStart_3136246 baseEnd_3136246 := by
    simpa [prefixWord, tailWord_3136246, baseEnd_3136246] using wordTrace_append hprefix tailTrace_3136246
  have hstable : (prefixWord ++ tailWord_3136246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136246).length < 2 ^ (prefixWord ++ tailWord_3136246).sum := by decide
  have hdescent : baseEnd_3136246 < baseStart_3136246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136260 : List Nat := [2, 3, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_3136260 : Nat := 118140960795 + 3136260 * 2 ^ 59
def prefixEnd_3136260 : Nat := 4983230072969 + 3 ^ 40 * 3136260 * 2
def baseEnd_3136260 : Nat := 536802945823334867342203

theorem tailTrace_3136260 : CollatzResearch.WordTrace tailWord_3136260 prefixEnd_3136260 536802945823334867342203 := by
  unfold tailWord_3136260
  simp only [CollatzResearch.WordTrace]
  refine ⟨57194399808936562704691117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76259199745248750272921489 57194399808936562704691117)
  ·
    refine ⟨21447899928351211014259169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57194399808936562704691117 21447899928351211014259169)
    ·
      refine ⟨16085924946263408260694377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21447899928351211014259169 16085924946263408260694377)
      ·
        refine ⟨12064443709697556195520783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16085924946263408260694377 12064443709697556195520783)
        ·
          refine ⟨18096665564546334293281175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12064443709697556195520783 18096665564546334293281175)
          ·
            refine ⟨27144998346819501439921763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18096665564546334293281175 27144998346819501439921763)
            ·
              refine ⟨40717497520229252159882645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27144998346819501439921763 40717497520229252159882645)
              ·
                refine ⟨1908632696260746194994499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40717497520229252159882645 1908632696260746194994499)
                ·
                  refine ⟨2862949044391119292491749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908632696260746194994499 2862949044391119292491749)
                  ·
                    refine ⟨536802945823334867342203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2862949044391119292491749 536802945823334867342203)
                    ·
                      rfl

theorem cell23_3136260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_3136260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136260 prefixEnd_3136260 := by exact prefixLift 3136260
  have htrace : WordTrace (prefixWord ++ tailWord_3136260) baseStart_3136260 baseEnd_3136260 := by
    simpa [prefixWord, tailWord_3136260, baseEnd_3136260] using wordTrace_append hprefix tailTrace_3136260
  have hstable : (prefixWord ++ tailWord_3136260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136260).length < 2 ^ (prefixWord ++ tailWord_3136260).sum := by decide
  have hdescent : baseEnd_3136260 < baseStart_3136260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136293 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 1, 5, 2]
def baseStart_3136293 : Nat := 118140960795 + 3136293 * 2 ^ 59
def prefixEnd_3136293 : Nat := 4983230072969 + 3 ^ 40 * 3136293 * 2
def baseEnd_3136293 : Nat := 1610425782331602972913957

theorem tailTrace_3136293 : CollatzResearch.WordTrace tailWord_3136293 prefixEnd_3136293 1610425782331602972913957 := by
  unfold tailWord_3136293
  simp only [CollatzResearch.WordTrace]
  refine ⟨114390003226753572045333533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76260002151169048030222355 114390003226753572045333533)
  ·
    refine ⟨42896251210032589517000075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114390003226753572045333533 42896251210032589517000075)
    ·
      refine ⟨64344376815048884275500113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42896251210032589517000075 64344376815048884275500113)
      ·
        refine ⟨48258282611286663206625085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64344376815048884275500113 48258282611286663206625085)
        ·
          refine ⟨18096855979232498702484407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48258282611286663206625085 18096855979232498702484407)
          ·
            refine ⟨27145283968848748053726611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18096855979232498702484407 27145283968848748053726611)
            ·
              refine ⟨40717925953273122080589917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27145283968848748053726611 40717925953273122080589917)
              ·
                refine ⟨15269222232477420780221219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40717925953273122080589917 15269222232477420780221219)
                ·
                  refine ⟨22903833348716131170331829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15269222232477420780221219 22903833348716131170331829)
                  ·
                    refine ⟨2147234376442137297218609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22903833348716131170331829 2147234376442137297218609)
                    ·
                      refine ⟨1610425782331602972913957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2147234376442137297218609 1610425782331602972913957)
                      ·
                        rfl

theorem cell23_3136293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_3136293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136293 prefixEnd_3136293 := by exact prefixLift 3136293
  have htrace : WordTrace (prefixWord ++ tailWord_3136293) baseStart_3136293 baseEnd_3136293 := by
    simpa [prefixWord, tailWord_3136293, baseEnd_3136293] using wordTrace_append hprefix tailTrace_3136293
  have hstable : (prefixWord ++ tailWord_3136293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136293).length < 2 ^ (prefixWord ++ tailWord_3136293).sum := by decide
  have hdescent : baseEnd_3136293 < baseStart_3136293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136324 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 6]
def baseStart_3136324 : Nat := 118140960795 + 3136324 * 2 ^ 59
def prefixEnd_3136324 : Nat := 4983230072969 + 3 ^ 40 * 3136324 * 2
def baseEnd_3136324 : Nat := 178937966692432483514035

theorem tailTrace_3136324 : CollatzResearch.WordTrace tailWord_3136324 prefixEnd_3136324 178937966692432483514035 := by
  unfold tailWord_3136324
  simp only [CollatzResearch.WordTrace]
  refine ⟨57195566944820632169856013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76260755926427509559808017 57195566944820632169856013)
  ·
    refine ⟨21448337604307737063696005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57195566944820632169856013 21448337604307737063696005)
    ·
      refine ⟨4021563300807700699443001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21448337604307737063696005 4021563300807700699443001)
      ·
        refine ⟨3016172475605775524582251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4021563300807700699443001 3016172475605775524582251)
        ·
          refine ⟨4524258713408663286873377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3016172475605775524582251 4524258713408663286873377)
          ·
            refine ⟨3393194035056497465155033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4524258713408663286873377 3393194035056497465155033)
            ·
              refine ⟨2544895526292373098866275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3393194035056497465155033 2544895526292373098866275)
              ·
                refine ⟨3817343289438559648299413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2544895526292373098866275 3817343289438559648299413)
                ·
                  refine ⟨178937966692432483514035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3817343289438559648299413 178937966692432483514035)
                  ·
                    rfl

theorem cell23_3136324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_3136324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136324 prefixEnd_3136324 := by exact prefixLift 3136324
  have htrace : WordTrace (prefixWord ++ tailWord_3136324) baseStart_3136324 baseEnd_3136324 := by
    simpa [prefixWord, tailWord_3136324, baseEnd_3136324] using wordTrace_append hprefix tailTrace_3136324
  have hstable : (prefixWord ++ tailWord_3136324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136324).length < 2 ^ (prefixWord ++ tailWord_3136324).sum := by decide
  have hdescent : baseEnd_3136324 < baseStart_3136324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136336 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_3136336 : Nat := 118140960795 + 3136336 * 2 ^ 59
def prefixEnd_3136336 : Nat := 4983230072969 + 3 ^ 40 * 3136336 * 2
def baseEnd_3136336 : Nat := 1610447861999746304676259

theorem tailTrace_3136336 : CollatzResearch.WordTrace tailWord_3136336 prefixEnd_3136336 1610447861999746304676259 := by
  unfold tailWord_3136336
  simp only [CollatzResearch.WordTrace]
  refine ⟨57195785782798895194574431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76261047710398526926099241 57195785782798895194574431)
  ·
    refine ⟨85793678674198342791861647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57195785782798895194574431 85793678674198342791861647)
    ·
      refine ⟨128690518011297514187792471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85793678674198342791861647 128690518011297514187792471)
      ·
        refine ⟨193035777016946271281688707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128690518011297514187792471 193035777016946271281688707)
        ·
          refine ⟨289553665525419406922533061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193035777016946271281688707 289553665525419406922533061)
          ·
            refine ⟨54291312286016138797974949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289553665525419406922533061 54291312286016138797974949)
            ·
              refine ⟨10179621053628026024620303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54291312286016138797974949 10179621053628026024620303)
              ·
                refine ⟨15269431580442039036930455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10179621053628026024620303 15269431580442039036930455)
                ·
                  refine ⟨22904147370663058555395683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15269431580442039036930455 22904147370663058555395683)
                  ·
                    refine ⟨34356221055994587833093525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22904147370663058555395683 34356221055994587833093525)
                    ·
                      refine ⟨1610447861999746304676259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34356221055994587833093525 1610447861999746304676259)
                      ·
                        rfl

theorem cell23_3136336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_3136336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136336 prefixEnd_3136336 := by exact prefixLift 3136336
  have htrace : WordTrace (prefixWord ++ tailWord_3136336) baseStart_3136336 baseEnd_3136336 := by
    simpa [prefixWord, tailWord_3136336, baseEnd_3136336] using wordTrace_append hprefix tailTrace_3136336
  have hstable : (prefixWord ++ tailWord_3136336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136336).length < 2 ^ (prefixWord ++ tailWord_3136336).sum := by decide
  have hdescent : baseEnd_3136336 < baseStart_3136336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136337 : List Nat := [1, 2, 2, 1, 7, 1, 1, 2, 1, 5]
def baseStart_3136337 : Nat := 118140960795 + 3136337 * 2 ^ 59
def prefixEnd_3136337 : Nat := 4983230072969 + 3 ^ 40 * 3136337 * 2
def baseEnd_3136337 : Nat := 536816125160133600254585

theorem tailTrace_3136337 : CollatzResearch.WordTrace tailWord_3136337 prefixEnd_3136337 536816125160133600254585 := by
  unfold tailWord_3136337
  simp only [CollatzResearch.WordTrace]
  refine ⟨114391608038594167559935265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76261072025729445039956843 114391608038594167559935265)
  ·
    refine ⟨85793706028945625669951449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114391608038594167559935265 85793706028945625669951449)
    ·
      refine ⟨64345279521709219252463587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85793706028945625669951449 64345279521709219252463587)
      ·
        refine ⟨96517919282563828878695381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64345279521709219252463587 96517919282563828878695381)
        ·
          refine ⟨2262138733185089739344423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 96517919282563828878695381 2262138733185089739344423)
          ·
            refine ⟨3393208099777634609016635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262138733185089739344423 3393208099777634609016635)
            ·
              refine ⟨5089812149666451913524953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393208099777634609016635 5089812149666451913524953)
              ·
                refine ⟨3817359112249838935143715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5089812149666451913524953 3817359112249838935143715)
                ·
                  refine ⟨5726038668374758402715573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3817359112249838935143715 5726038668374758402715573)
                  ·
                    refine ⟨536816125160133600254585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5726038668374758402715573 536816125160133600254585)
                    ·
                      rfl

theorem cell23_3136337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_3136337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136337 prefixEnd_3136337 := by exact prefixLift 3136337
  have htrace : WordTrace (prefixWord ++ tailWord_3136337) baseStart_3136337 baseEnd_3136337 := by
    simpa [prefixWord, tailWord_3136337, baseEnd_3136337] using wordTrace_append hprefix tailTrace_3136337
  have hstable : (prefixWord ++ tailWord_3136337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136337).length < 2 ^ (prefixWord ++ tailWord_3136337).sum := by decide
  have hdescent : baseEnd_3136337 < baseStart_3136337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136340 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_3136340 : Nat := 118140960795 + 3136340 * 2 ^ 59
def prefixEnd_3136340 : Nat := 4983230072969 + 3 ^ 40 * 3136340 * 2
def baseEnd_3136340 : Nat := 1610449915922364289026241

theorem tailTrace_3136340 : CollatzResearch.WordTrace tailWord_3136340 prefixEnd_3136340 1610449915922364289026241 := by
  unfold tailWord_3136340
  simp only [CollatzResearch.WordTrace]
  refine ⟨57195858728791649536147237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76261144971722199381529649 57195858728791649536147237)
  ·
    refine ⟨10724223511648434288027607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57195858728791649536147237 10724223511648434288027607)
    ·
      refine ⟨16086335267472651432041411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10724223511648434288027607 16086335267472651432041411)
      ·
        refine ⟨24129502901208977148062117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16086335267472651432041411 24129502901208977148062117)
        ·
          refine ⟨4524281793976683215261647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24129502901208977148062117 4524281793976683215261647)
          ·
            refine ⟨6786422690965024822892471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524281793976683215261647 6786422690965024822892471)
            ·
              refine ⟨10179634036447537234338707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786422690965024822892471 10179634036447537234338707)
              ·
                refine ⟨15269451054671305851508061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10179634036447537234338707 15269451054671305851508061)
                ·
                  refine ⟨5726044145501739694315523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15269451054671305851508061 5726044145501739694315523)
                  ·
                    refine ⟨8589066218252609541473285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5726044145501739694315523 8589066218252609541473285)
                    ·
                      refine ⟨1610449915922364289026241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8589066218252609541473285 1610449915922364289026241)
                      ·
                        rfl

theorem cell23_3136340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_3136340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136340 prefixEnd_3136340 := by exact prefixLift 3136340
  have htrace : WordTrace (prefixWord ++ tailWord_3136340) baseStart_3136340 baseEnd_3136340 := by
    simpa [prefixWord, tailWord_3136340, baseEnd_3136340] using wordTrace_append hprefix tailTrace_3136340
  have hstable : (prefixWord ++ tailWord_3136340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136340).length < 2 ^ (prefixWord ++ tailWord_3136340).sum := by decide
  have hdescent : baseEnd_3136340 < baseStart_3136340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136346 : List Nat := [3, 1, 1, 2, 1, 4, 2, 9]
def baseStart_3136346 : Nat := 118140960795 + 3136346 * 2 ^ 59
def prefixEnd_3136346 : Nat := 4983230072969 + 3 ^ 40 * 3136346 * 2
def baseEnd_3136346 : Nat := 59646407289121898724119

theorem tailTrace_3136346 : CollatzResearch.WordTrace tailWord_3136346 prefixEnd_3136346 59646407289121898724119 := by
  unfold tailWord_3136346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28597984073890390524253223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76261290863707708064675261 28597984073890390524253223)
  ·
    refine ⟨42896976110835585786379835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28597984073890390524253223 42896976110835585786379835)
    ·
      refine ⟨64345464166253378679569753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42896976110835585786379835 64345464166253378679569753)
      ·
        refine ⟨48259098124690034009677315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64345464166253378679569753 48259098124690034009677315)
        ·
          refine ⟨72388647187035051014515973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48259098124690034009677315 72388647187035051014515973)
          ·
            refine ⟨13572871347569072065221745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72388647187035051014515973 13572871347569072065221745)
            ·
              refine ⟨10179653510676804048916309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13572871347569072065221745 10179653510676804048916309)
              ·
                refine ⟨59646407289121898724119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10179653510676804048916309 59646407289121898724119)
                ·
                  rfl

theorem cell23_3136346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 9].length) (baseStart_3136346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136346 prefixEnd_3136346 := by exact prefixLift 3136346
  have htrace : WordTrace (prefixWord ++ tailWord_3136346) baseStart_3136346 baseEnd_3136346 := by
    simpa [prefixWord, tailWord_3136346, baseEnd_3136346] using wordTrace_append hprefix tailTrace_3136346
  have hstable : (prefixWord ++ tailWord_3136346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136346).length < 2 ^ (prefixWord ++ tailWord_3136346).sum := by decide
  have hdescent : baseEnd_3136346 < baseStart_3136346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136360 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3136360 : Nat := 118140960795 + 3136360 * 2 ^ 59
def prefixEnd_3136360 : Nat := 4983230072969 + 3 ^ 40 * 3136360 * 2
def baseEnd_3136360 : Nat := 1610460185535454210776149

theorem tailTrace_3136360 : CollatzResearch.WordTrace tailWord_3136360 prefixEnd_3136360 1610460185535454210776149 := by
  unfold tailWord_3136360
  simp only [CollatzResearch.WordTrace]
  refine ⟨57196223458755421244011267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76261631278340561658681689 57196223458755421244011267)
  ·
    refine ⟨85794335188133131866016901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57196223458755421244011267 85794335188133131866016901)
    ·
      refine ⟨16086437847774962224878169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85794335188133131866016901 16086437847774962224878169)
      ·
        refine ⟨12064828385831221668658627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16086437847774962224878169 12064828385831221668658627)
        ·
          refine ⟨18097242578746832502987941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12064828385831221668658627 18097242578746832502987941)
          ·
            refine ⟨3393232983515031094310239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18097242578746832502987941 3393232983515031094310239)
            ·
              refine ⟨5089849475272546641465359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393232983515031094310239 5089849475272546641465359)
              ·
                refine ⟨7634774212908819962198039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5089849475272546641465359 7634774212908819962198039)
                ·
                  refine ⟨11452161319363229943297059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7634774212908819962198039 11452161319363229943297059)
                  ·
                    refine ⟨17178241979044844914945589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11452161319363229943297059 17178241979044844914945589)
                    ·
                      refine ⟨1610460185535454210776149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17178241979044844914945589 1610460185535454210776149)
                      ·
                        rfl

theorem cell23_3136360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3136360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136360 prefixEnd_3136360 := by exact prefixLift 3136360
  have htrace : WordTrace (prefixWord ++ tailWord_3136360) baseStart_3136360 baseEnd_3136360 := by
    simpa [prefixWord, tailWord_3136360, baseEnd_3136360] using wordTrace_append hprefix tailTrace_3136360
  have hstable : (prefixWord ++ tailWord_3136360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136360).length < 2 ^ (prefixWord ++ tailWord_3136360).sum := by decide
  have hdescent : baseEnd_3136360 < baseStart_3136360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136438 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3136438 : Nat := 118140960795 + 3136438 * 2 ^ 59
def prefixEnd_3136438 : Nat := 4983230072969 + 3 ^ 40 * 3136438 * 2
def baseEnd_3136438 : Nat := 1610500237026504905600791

theorem tailTrace_3136438 : CollatzResearch.WordTrace tailWord_3136438 prefixEnd_3136438 1610500237026504905600791 := by
  unfold tailWord_3136438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7149705738201766363085123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76263527874152174539574645 7149705738201766363085123)
  ·
    refine ⟨10724558607302649544627685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7149705738201766363085123 10724558607302649544627685)
    ·
      refine ⟨2010854738869246789617691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10724558607302649544627685 2010854738869246789617691)
      ·
        refine ⟨3016282108303870184426537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010854738869246789617691 3016282108303870184426537)
        ·
          refine ⟨2262211581227902638319903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016282108303870184426537 2262211581227902638319903)
          ·
            refine ⟨3393317371841853957479855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262211581227902638319903 3393317371841853957479855)
            ·
              refine ⟨5089976057762780936219783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393317371841853957479855 5089976057762780936219783)
              ·
                refine ⟨7634964086644171404329675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5089976057762780936219783 7634964086644171404329675)
                ·
                  refine ⟨11452446129966257106494513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7634964086644171404329675 11452446129966257106494513)
                  ·
                    refine ⟨8589334597474692829870885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11452446129966257106494513 8589334597474692829870885)
                    ·
                      refine ⟨1610500237026504905600791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8589334597474692829870885 1610500237026504905600791)
                      ·
                        rfl

theorem cell23_3136438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3136438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136438 prefixEnd_3136438 := by exact prefixLift 3136438
  have htrace : WordTrace (prefixWord ++ tailWord_3136438) baseStart_3136438 baseEnd_3136438 := by
    simpa [prefixWord, tailWord_3136438, baseEnd_3136438] using wordTrace_append hprefix tailTrace_3136438
  have hstable : (prefixWord ++ tailWord_3136438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136438).length < 2 ^ (prefixWord ++ tailWord_3136438).sum := by decide
  have hdescent : baseEnd_3136438 < baseStart_3136438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136520 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3136520 : Nat := 118140960795 + 3136520 * 2 ^ 59
def prefixEnd_3136520 : Nat := 4983230072969 + 3 ^ 40 * 3136520 * 2
def baseEnd_3136520 : Nat := 1610542342440173584775413

theorem tailTrace_3136520 : CollatzResearch.WordTrace tailWord_3136520 prefixEnd_3136520 1610542342440173584775413 := by
  unfold tailWord_3136520
  simp only [CollatzResearch.WordTrace]
  refine ⟨57199141298465594906923507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76265521731287459875898009 57199141298465594906923507)
  ·
    refine ⟨85798711947698392360385261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57199141298465594906923507 85798711947698392360385261)
    ·
      refine ⟨32174516980386897135144473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85798711947698392360385261 32174516980386897135144473)
      ·
        refine ⟨24130887735290172851358355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32174516980386897135144473 24130887735290172851358355)
        ·
          refine ⟨36196331602935259277037533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24130887735290172851358355 36196331602935259277037533)
          ·
            refine ⟨13573624351100722228889075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36196331602935259277037533 13573624351100722228889075)
            ·
              refine ⟨20360436526651083343333613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13573624351100722228889075 20360436526651083343333613)
              ·
                refine ⟨7635163697494156253750105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20360436526651083343333613 7635163697494156253750105)
                ·
                  refine ⟨5726372773120617190312579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635163697494156253750105 5726372773120617190312579)
                  ·
                    refine ⟨8589559159680925785468869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5726372773120617190312579 8589559159680925785468869)
                    ·
                      refine ⟨1610542342440173584775413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8589559159680925785468869 1610542342440173584775413)
                      ·
                        rfl

theorem cell23_3136520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3136520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136520 prefixEnd_3136520 := by exact prefixLift 3136520
  have htrace : WordTrace (prefixWord ++ tailWord_3136520) baseStart_3136520 baseEnd_3136520 := by
    simpa [prefixWord, tailWord_3136520, baseEnd_3136520] using wordTrace_append hprefix tailTrace_3136520
  have hstable : (prefixWord ++ tailWord_3136520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136520).length < 2 ^ (prefixWord ++ tailWord_3136520).sum := by decide
  have hdescent : baseEnd_3136520 < baseStart_3136520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136554 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_3136554 : Nat := 118140960795 + 3136554 * 2 ^ 59
def prefixEnd_3136554 : Nat := 4983230072969 + 3 ^ 40 * 3136554 * 2
def baseEnd_3136554 : Nat := 1610559800782426451750257

theorem tailTrace_3136554 : CollatzResearch.WordTrace tailWord_3136554 prefixEnd_3136554 1610559800782426451750257 := by
  unfold tailWord_3136554
  simp only [CollatzResearch.WordTrace]
  refine ⟨28599880669702003405146179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76266348452538675747056477 28599880669702003405146179)
  ·
    refine ⟨42899821004553005107719269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28599880669702003405146179 42899821004553005107719269)
    ·
      refine ⟨8043716438353688457697363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42899821004553005107719269 8043716438353688457697363)
      ·
        refine ⟨12065574657530532686546045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043716438353688457697363 12065574657530532686546045)
        ·
          refine ⟨4524590496573949757454767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12065574657530532686546045 4524590496573949757454767)
          ·
            refine ⟨6786885744860924636182151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524590496573949757454767 6786885744860924636182151)
            ·
              refine ⟨10180328617291386954273227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786885744860924636182151 10180328617291386954273227)
              ·
                refine ⟨15270492925937080431409841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10180328617291386954273227 15270492925937080431409841)
                ·
                  refine ⟨11452869694452810323557381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15270492925937080431409841 11452869694452810323557381)
                  ·
                    refine ⟨2147413067709901935667009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11452869694452810323557381 2147413067709901935667009)
                    ·
                      refine ⟨1610559800782426451750257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2147413067709901935667009 1610559800782426451750257)
                      ·
                        rfl

theorem cell23_3136554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_3136554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136554 prefixEnd_3136554 := by exact prefixLift 3136554
  have htrace : WordTrace (prefixWord ++ tailWord_3136554) baseStart_3136554 baseEnd_3136554 := by
    simpa [prefixWord, tailWord_3136554, baseEnd_3136554] using wordTrace_append hprefix tailTrace_3136554
  have hstable : (prefixWord ++ tailWord_3136554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136554).length < 2 ^ (prefixWord ++ tailWord_3136554).sum := by decide
  have hdescent : baseEnd_3136554 < baseStart_3136554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136564 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3136564 : Nat := 118140960795 + 3136564 * 2 ^ 59
def prefixEnd_3136564 : Nat := 4983230072969 + 3 ^ 40 * 3136564 * 2
def baseEnd_3136564 : Nat := 536854978529657137541737

theorem tailTrace_3136564 : CollatzResearch.WordTrace tailWord_3136564 prefixEnd_3136564 536854978529657137541737 := by
  unfold tailWord_3136564
  simp only [CollatzResearch.WordTrace]
  refine ⟨57199943704385892664224373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76266591605847856885632497 57199943704385892664224373)
  ·
    refine ⟨5362494722286177437271035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57199943704385892664224373 5362494722286177437271035)
    ·
      refine ⟨8043742083429266155906553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362494722286177437271035 8043742083429266155906553)
      ·
        refine ⟨6032806562571949616929915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8043742083429266155906553 6032806562571949616929915)
        ·
          refine ⟨9049209843857924425394873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032806562571949616929915 9049209843857924425394873)
          ·
            refine ⟨6786907382893443319046155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9049209843857924425394873 6786907382893443319046155)
            ·
              refine ⟨10180361074340164978569233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786907382893443319046155 10180361074340164978569233)
              ·
                refine ⟨7635270805755123733926925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10180361074340164978569233 7635270805755123733926925)
                ·
                  refine ⟨2863226552158171400222597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7635270805755123733926925 2863226552158171400222597)
                  ·
                    refine ⟨536854978529657137541737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2863226552158171400222597 536854978529657137541737)
                    ·
                      rfl

theorem cell23_3136564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3136564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136564 prefixEnd_3136564 := by exact prefixLift 3136564
  have htrace : WordTrace (prefixWord ++ tailWord_3136564) baseStart_3136564 baseEnd_3136564 := by
    simpa [prefixWord, tailWord_3136564, baseEnd_3136564] using wordTrace_append hprefix tailTrace_3136564
  have hstable : (prefixWord ++ tailWord_3136564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136564).length < 2 ^ (prefixWord ++ tailWord_3136564).sum := by decide
  have hdescent : baseEnd_3136564 < baseStart_3136564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136574 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3136574 : Nat := 118140960795 + 3136574 * 2 ^ 59
def prefixEnd_3136574 : Nat := 4983230072969 + 3 ^ 40 * 3136574 * 2
def baseEnd_3136574 : Nat := 1610570070395516373500165

theorem tailTrace_3136574 : CollatzResearch.WordTrace tailWord_3136574 prefixEnd_3136574 1610570070395516373500165 := by
  unfold tailWord_3136574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14300031517341944629539097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76266834759157038024208517 14300031517341944629539097)
  ·
    refine ⟨10725023638006458472154323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14300031517341944629539097 10725023638006458472154323)
    ·
      refine ⟨16087535457009687708231485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10725023638006458472154323 16087535457009687708231485)
      ·
        refine ⟨6032825796378632890586807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16087535457009687708231485 6032825796378632890586807)
        ·
          refine ⟨9049238694567949335880211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032825796378632890586807 9049238694567949335880211)
          ·
            refine ⟨13573858041851924003820317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9049238694567949335880211 13573858041851924003820317)
            ·
              refine ⟨5090196765694471501432619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13573858041851924003820317 5090196765694471501432619)
              ·
                refine ⟨7635295148541707252148929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090196765694471501432619 7635295148541707252148929)
                ·
                  refine ⟨5726471361406280439111697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635295148541707252148929 5726471361406280439111697)
                  ·
                    refine ⟨4294853521054710329333773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5726471361406280439111697 4294853521054710329333773)
                    ·
                      refine ⟨1610570070395516373500165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4294853521054710329333773 1610570070395516373500165)
                      ·
                        rfl

theorem cell23_3136574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3136574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136574 prefixEnd_3136574 := by exact prefixLift 3136574
  have htrace : WordTrace (prefixWord ++ tailWord_3136574) baseStart_3136574 baseEnd_3136574 := by
    simpa [prefixWord, tailWord_3136574, baseEnd_3136574] using wordTrace_append hprefix tailTrace_3136574
  have hstable : (prefixWord ++ tailWord_3136574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136574).length < 2 ^ (prefixWord ++ tailWord_3136574).sum := by decide
  have hdescent : baseEnd_3136574 < baseStart_3136574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136597 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 4, 3, 2]
def baseStart_3136597 : Nat := 118140960795 + 3136597 * 2 ^ 59
def prefixEnd_3136597 : Nat := 4983230072969 + 3 ^ 40 * 3136597 * 2
def baseEnd_3136597 : Nat := 1610581880450569783512559

theorem tailTrace_3136597 : CollatzResearch.WordTrace tailWord_3136597 prefixEnd_3136597 1610581880450569783512559 := by
  unfold tailWord_3136597
  simp only [CollatzResearch.WordTrace]
  refine ⟨114401091017652231964400045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76267394011768154642933363 114401091017652231964400045)
  ·
    refine ⟨42900409131619586986650017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114401091017652231964400045 42900409131619586986650017)
    ·
      refine ⟨32175306848714690239987513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42900409131619586986650017 32175306848714690239987513)
      ·
        refine ⟨24131480136536017679990635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32175306848714690239987513 24131480136536017679990635)
        ·
          refine ⟨36197220204804026519985953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24131480136536017679990635 36197220204804026519985953)
          ·
            refine ⟨27147915153603019889989465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36197220204804026519985953 27147915153603019889989465)
            ·
              refine ⟨20360936365202264917492099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27147915153603019889989465 20360936365202264917492099)
              ·
                refine ⟨30541404547803397376238149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20360936365202264917492099 30541404547803397376238149)
                ·
                  refine ⟨5726513352713137008044653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30541404547803397376238149 5726513352713137008044653)
                  ·
                    refine ⟨2147442507267426378016745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5726513352713137008044653 2147442507267426378016745)
                    ·
                      refine ⟨1610581880450569783512559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2147442507267426378016745 1610581880450569783512559)
                      ·
                        rfl

theorem cell23_3136597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_3136597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136597 prefixEnd_3136597 := by exact prefixLift 3136597
  have htrace : WordTrace (prefixWord ++ tailWord_3136597) baseStart_3136597 baseEnd_3136597 := by
    simpa [prefixWord, tailWord_3136597, baseEnd_3136597] using wordTrace_append hprefix tailTrace_3136597
  have hstable : (prefixWord ++ tailWord_3136597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136597).length < 2 ^ (prefixWord ++ tailWord_3136597).sum := by decide
  have hdescent : baseEnd_3136597 < baseStart_3136597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136604 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3136604 : Nat := 118140960795 + 3136604 * 2 ^ 59
def prefixEnd_3136604 : Nat := 4983230072969 + 3 ^ 40 * 3136604 * 2
def baseEnd_3136604 : Nat := 1610585474815151256125027

theorem tailTrace_3136604 : CollatzResearch.WordTrace tailWord_3136604 prefixEnd_3136604 1610585474815151256125027 := by
  unfold tailWord_3136604
  simp only [CollatzResearch.WordTrace]
  refine ⟨57200673164313436079952433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76267564219084581439936577 57200673164313436079952433)
  ·
    refine ⟨42900504873235077059964325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57200673164313436079952433 42900504873235077059964325)
    ·
      refine ⟨8043844663731576948743311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42900504873235077059964325 8043844663731576948743311)
      ·
        refine ⟨12065766995597365423114967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043844663731576948743311 12065766995597365423114967)
        ·
          refine ⟨18098650493396048134672451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12065766995597365423114967 18098650493396048134672451)
          ·
            refine ⟨27147975740094072202008677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18098650493396048134672451 27147975740094072202008677)
            ·
              refine ⟨5090245451267638537876627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27147975740094072202008677 5090245451267638537876627)
              ·
                refine ⟨7635368176901457806814941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090245451267638537876627 7635368176901457806814941)
                ·
                  refine ⟨2863263066338046677555603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7635368176901457806814941 2863263066338046677555603)
                  ·
                    refine ⟨4294894599507070016333405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2863263066338046677555603 4294894599507070016333405)
                    ·
                      refine ⟨1610585474815151256125027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4294894599507070016333405 1610585474815151256125027)
                      ·
                        rfl

theorem cell23_3136604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3136604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136604 prefixEnd_3136604 := by exact prefixLift 3136604
  have htrace : WordTrace (prefixWord ++ tailWord_3136604) baseStart_3136604 baseEnd_3136604 := by
    simpa [prefixWord, tailWord_3136604, baseEnd_3136604] using wordTrace_append hprefix tailTrace_3136604
  have hstable : (prefixWord ++ tailWord_3136604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136604).length < 2 ^ (prefixWord ++ tailWord_3136604).sum := by decide
  have hdescent : baseEnd_3136604 < baseStart_3136604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136640 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_3136640 : Nat := 118140960795 + 3136640 * 2 ^ 59
def prefixEnd_3136640 : Nat := 4983230072969 + 3 ^ 40 * 3136640 * 2
def baseEnd_3136640 : Nat := 1610603960118713115274861

theorem tailTrace_3136640 : CollatzResearch.WordTrace tailWord_3136640 prefixEnd_3136640 1610603960118713115274861 := by
  unfold tailWord_3136640
  simp only [CollatzResearch.WordTrace]
  refine ⟨57201329678248225154107687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76268439570997633538810249 57201329678248225154107687)
  ·
    refine ⟨85801994517372337731161531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57201329678248225154107687 85801994517372337731161531)
    ·
      refine ⟨128702991776058506596742297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85801994517372337731161531 128702991776058506596742297)
      ·
        refine ⟨96527243832043879947556723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128702991776058506596742297 96527243832043879947556723)
        ·
          refine ⟨144790865748065819921335085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96527243832043879947556723 144790865748065819921335085)
          ·
            refine ⟨54296574655524682470500657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144790865748065819921335085 54296574655524682470500657)
            ·
              refine ⟨40722430991643511852875493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54296574655524682470500657 40722430991643511852875493)
              ·
                refine ⟨7635455810933158472414155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40722430991643511852875493 7635455810933158472414155)
                ·
                  refine ⟨11453183716399737708621233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7635455810933158472414155 11453183716399737708621233)
                  ·
                    refine ⟨8589887787299803281465925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11453183716399737708621233 8589887787299803281465925)
                    ·
                      refine ⟨1610603960118713115274861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8589887787299803281465925 1610603960118713115274861)
                      ·
                        rfl

theorem cell23_3136640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_3136640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136640 prefixEnd_3136640 := by exact prefixLift 3136640
  have htrace : WordTrace (prefixWord ++ tailWord_3136640) baseStart_3136640 baseEnd_3136640 := by
    simpa [prefixWord, tailWord_3136640, baseEnd_3136640] using wordTrace_append hprefix tailTrace_3136640
  have hstable : (prefixWord ++ tailWord_3136640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136640).length < 2 ^ (prefixWord ++ tailWord_3136640).sum := by decide
  have hdescent : baseEnd_3136640 < baseStart_3136640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136740 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 9]
def baseStart_3136740 : Nat := 118140960795 + 3136740 * 2 ^ 59
def prefixEnd_3136740 : Nat := 4983230072969 + 3 ^ 40 * 3136740 * 2
def baseEnd_3136740 : Nat := 178961700909351413780489

theorem tailTrace_3136740 : CollatzResearch.WordTrace tailWord_3136740 prefixEnd_3136740 178961700909351413780489 := by
  unfold tailWord_3136740
  simp only [CollatzResearch.WordTrace]
  refine ⟨57203153328067083693427837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76270871104089444924570449 57203153328067083693427837)
  ·
    refine ⟨21451182498025156385035439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57203153328067083693427837 21451182498025156385035439)
    ·
      refine ⟨32176773747037734577553159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21451182498025156385035439 32176773747037734577553159)
      ·
        refine ⟨48265160620556601866329739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32176773747037734577553159 48265160620556601866329739)
        ·
          refine ⟨72397740930834902799494609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48265160620556601866329739 72397740930834902799494609)
          ·
            refine ⟨54298305698126177099620957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72397740930834902799494609 54298305698126177099620957)
            ·
              refine ⟨20361864636797316412357859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54298305698126177099620957 20361864636797316412357859)
              ·
                refine ⟨30542796955195974618536789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20361864636797316412357859 30542796955195974618536789)
                ·
                  refine ⟨178961700909351413780489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30542796955195974618536789 178961700909351413780489)
                  ·
                    rfl

theorem cell23_3136740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_3136740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136740 prefixEnd_3136740 := by exact prefixLift 3136740
  have htrace : WordTrace (prefixWord ++ tailWord_3136740) baseStart_3136740 baseEnd_3136740 := by
    simpa [prefixWord, tailWord_3136740, baseEnd_3136740] using wordTrace_append hprefix tailTrace_3136740
  have hstable : (prefixWord ++ tailWord_3136740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136740).length < 2 ^ (prefixWord ++ tailWord_3136740).sum := by decide
  have hdescent : baseEnd_3136740 < baseStart_3136740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136767 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 3]
def baseStart_3136767 : Nat := 118140960795 + 3136767 * 2 ^ 59
def prefixEnd_3136767 : Nat := 4983230072969 + 3 ^ 40 * 3136767 * 2
def baseEnd_3136767 : Nat := 1610669172161834118386777

theorem tailTrace_3136767 : CollatzResearch.WordTrace tailWord_3136767 prefixEnd_3136767 1610669172161834118386777 := by
  unfold tailWord_3136767
  simp only [CollatzResearch.WordTrace]
  refine ⟨114407291427036350998088555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76271527618024233998725703 114407291427036350998088555)
  ·
    refine ⟨171610937140554526497132833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114407291427036350998088555 171610937140554526497132833)
    ·
      refine ⟨128708202855415894872849625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171610937140554526497132833 128708202855415894872849625)
      ·
        refine ⟨96531152141561921154637219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128708202855415894872849625 96531152141561921154637219)
        ·
          refine ⟨144796728212342881731955829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96531152141561921154637219 144796728212342881731955829)
          ·
            refine ⟨13574693269907145162370859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144796728212342881731955829 13574693269907145162370859)
            ·
              refine ⟨20362039904860717743556289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13574693269907145162370859 20362039904860717743556289)
              ·
                refine ⟨15271529928645538307667217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20362039904860717743556289 15271529928645538307667217)
                ·
                  refine ⟨11453647446484153730750413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15271529928645538307667217 11453647446484153730750413)
                  ·
                    refine ⟨4295117792431557649031405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11453647446484153730750413 4295117792431557649031405)
                    ·
                      refine ⟨1610669172161834118386777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4295117792431557649031405 1610669172161834118386777)
                      ·
                        rfl

theorem cell23_3136767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_3136767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136767 prefixEnd_3136767 := by exact prefixLift 3136767
  have htrace : WordTrace (prefixWord ++ tailWord_3136767) baseStart_3136767 baseEnd_3136767 := by
    simpa [prefixWord, tailWord_3136767, baseEnd_3136767] using wordTrace_append hprefix tailTrace_3136767
  have hstable : (prefixWord ++ tailWord_3136767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136767).length < 2 ^ (prefixWord ++ tailWord_3136767).sum := by decide
  have hdescent : baseEnd_3136767 < baseStart_3136767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136857 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 3]
def baseStart_3136857 : Nat := 118140960795 + 3136857 * 2 ^ 59
def prefixEnd_3136857 : Nat := 4983230072969 + 3 ^ 40 * 3136857 * 2
def baseEnd_3136857 : Nat := 1610715385420738766261363

theorem tailTrace_3136857 : CollatzResearch.WordTrace tailWord_3136857 prefixEnd_3136857 1610715385420738766261363 := by
  unfold tailWord_3136857
  simp only [CollatzResearch.WordTrace]
  refine ⟨114410573996710296368864825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76273715997806864245909883 114410573996710296368864825)
  ·
    refine ⟨85807930497532722276648619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114410573996710296368864825 85807930497532722276648619)
    ·
      refine ⟨128711895746299083414972929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85807930497532722276648619 128711895746299083414972929)
      ·
        refine ⟨96533921809724312561229697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128711895746299083414972929 96533921809724312561229697)
        ·
          refine ⟨72400441357293234420922273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96533921809724312561229697 72400441357293234420922273)
          ·
            refine ⟨54300331017969925815691705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72400441357293234420922273 54300331017969925815691705)
            ·
              refine ⟨40725248263477444361768779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54300331017969925815691705 40725248263477444361768779)
              ·
                refine ⟨61087872395216166542653169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40725248263477444361768779 61087872395216166542653169)
                ·
                  refine ⟨45815904296412124906989877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61087872395216166542653169 45815904296412124906989877)
                  ·
                    refine ⟨4295241027788636710030301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45815904296412124906989877 4295241027788636710030301)
                    ·
                      refine ⟨1610715385420738766261363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4295241027788636710030301 1610715385420738766261363)
                      ·
                        rfl

theorem cell23_3136857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_3136857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136857 prefixEnd_3136857 := by exact prefixLift 3136857
  have htrace : WordTrace (prefixWord ++ tailWord_3136857) baseStart_3136857 baseEnd_3136857 := by
    simpa [prefixWord, tailWord_3136857, baseEnd_3136857] using wordTrace_append hprefix tailTrace_3136857
  have hstable : (prefixWord ++ tailWord_3136857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136857).length < 2 ^ (prefixWord ++ tailWord_3136857).sum := by decide
  have hdescent : baseEnd_3136857 < baseStart_3136857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136925 : List Nat := [1, 4, 2, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_3136925 : Nat := 118140960795 + 3136925 * 2 ^ 59
def prefixEnd_3136925 : Nat := 4983230072969 + 3 ^ 40 * 3136925 * 2
def baseEnd_3136925 : Nat := 1610750302105244500211051

theorem tailTrace_3136925 : CollatzResearch.WordTrace tailWord_3136925 prefixEnd_3136925 1610750302105244500211051 := by
  unfold tailWord_3136925
  simp only [CollatzResearch.WordTrace]
  refine ⟨114413054160463943982340229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76275369440309295988226819 114413054160463943982340229)
  ·
    refine ⟨21452447655086989496688793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114413054160463943982340229 21452447655086989496688793)
    ·
      refine ⟨16089335741315242122516595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21452447655086989496688793 16089335741315242122516595)
      ·
        refine ⟨24134003611972863183774893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16089335741315242122516595 24134003611972863183774893)
        ·
          refine ⟨9050251354489823693915585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24134003611972863183774893 9050251354489823693915585)
          ·
            refine ⟨6787688515867367770436689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9050251354489823693915585 6787688515867367770436689)
            ·
              refine ⟨5090766386900525827827517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6787688515867367770436689 5090766386900525827827517)
              ·
                refine ⟨1909037395087697185435319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5090766386900525827827517 1909037395087697185435319)
                ·
                  refine ⟨2863556092631545778152979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909037395087697185435319 2863556092631545778152979)
                  ·
                    refine ⟨4295334138947318667229469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2863556092631545778152979 4295334138947318667229469)
                    ·
                      refine ⟨1610750302105244500211051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4295334138947318667229469 1610750302105244500211051)
                      ·
                        rfl

theorem cell23_3136925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_3136925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136925 prefixEnd_3136925 := by exact prefixLift 3136925
  have htrace : WordTrace (prefixWord ++ tailWord_3136925) baseStart_3136925 baseEnd_3136925 := by
    simpa [prefixWord, tailWord_3136925, baseEnd_3136925] using wordTrace_append hprefix tailTrace_3136925
  have hstable : (prefixWord ++ tailWord_3136925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136925).length < 2 ^ (prefixWord ++ tailWord_3136925).sum := by decide
  have hdescent : baseEnd_3136925 < baseStart_3136925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136931 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 5, 2, 2]
def baseStart_3136931 : Nat := 118140960795 + 3136931 * 2 ^ 59
def prefixEnd_3136931 : Nat := 4983230072969 + 3 ^ 40 * 3136931 * 2
def baseEnd_3136931 : Nat := 1610753382989171476736023

theorem tailTrace_3136931 : CollatzResearch.WordTrace tailWord_3136931 prefixEnd_3136931 1610753382989171476736023 := by
  unfold tailWord_3136931
  simp only [CollatzResearch.WordTrace]
  refine ⟨114413272998442207007058647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76275515332294804671372431 114413272998442207007058647)
  ·
    refine ⟨171619909497663310510587971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114413272998442207007058647 171619909497663310510587971)
    ·
      refine ⟨257429864246494965765881957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171619909497663310510587971 257429864246494965765881957)
      ·
        refine ⟨48268099546217806081102867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257429864246494965765881957 48268099546217806081102867)
        ·
          refine ⟨72402149319326709121654301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48268099546217806081102867 72402149319326709121654301)
          ·
            refine ⟨27150805994747515920620363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72402149319326709121654301 27150805994747515920620363)
            ·
              refine ⟨40726208992121273880930545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27150805994747515920620363 40726208992121273880930545)
              ·
                refine ⟨30544656744090955410697909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40726208992121273880930545 30544656744090955410697909)
                ·
                  refine ⟨2863561569758527069752929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30544656744090955410697909 2863561569758527069752929)
                  ·
                    refine ⟨2147671177318895302314697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2863561569758527069752929 2147671177318895302314697)
                    ·
                      refine ⟨1610753382989171476736023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2147671177318895302314697 1610753382989171476736023)
                      ·
                        rfl

theorem cell23_3136931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_3136931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136931 prefixEnd_3136931 := by exact prefixLift 3136931
  have htrace : WordTrace (prefixWord ++ tailWord_3136931) baseStart_3136931 baseEnd_3136931 := by
    simpa [prefixWord, tailWord_3136931, baseEnd_3136931] using wordTrace_append hprefix tailTrace_3136931
  have hstable : (prefixWord ++ tailWord_3136931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136931).length < 2 ^ (prefixWord ++ tailWord_3136931).sum := by decide
  have hdescent : baseEnd_3136931 < baseStart_3136931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3136981 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3136981 : Nat := 118140960795 + 3136981 * 2 ^ 59
def prefixEnd_3136981 : Nat := 4983230072969 + 3 ^ 40 * 3136981 * 2
def baseEnd_3136981 : Nat := 1610779057021896281110793

theorem tailTrace_3136981 : CollatzResearch.WordTrace tailWord_3136981 prefixEnd_3136981 1610779057021896281110793 := by
  unfold tailWord_3136981
  simp only [CollatzResearch.WordTrace]
  refine ⟨114415096648261065546378797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76276731098840710364252531 114415096648261065546378797)
  ·
    refine ⟨42905661243097899579892049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114415096648261065546378797 42905661243097899579892049)
    ·
      refine ⟨32179245932323424684919037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42905661243097899579892049 32179245932323424684919037)
      ·
        refine ⟨12067217224621284256844639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32179245932323424684919037 12067217224621284256844639)
        ·
          refine ⟨18100825836931926385266959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12067217224621284256844639 18100825836931926385266959)
          ·
            refine ⟨27151238755397889577900439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18100825836931926385266959 27151238755397889577900439)
            ·
              refine ⟨40726858133096834366850659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27151238755397889577900439 40726858133096834366850659)
              ·
                refine ⟨61090287199645251550275989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40726858133096834366850659 61090287199645251550275989)
                ·
                  refine ⟨2863607212483371166419187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61090287199645251550275989 2863607212483371166419187)
                  ·
                    refine ⟨4295410818725056749628781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2863607212483371166419187 4295410818725056749628781)
                    ·
                      refine ⟨1610779057021896281110793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4295410818725056749628781 1610779057021896281110793)
                      ·
                        rfl

theorem cell23_3136981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3136981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3136981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3136981 prefixEnd_3136981 := by exact prefixLift 3136981
  have htrace : WordTrace (prefixWord ++ tailWord_3136981) baseStart_3136981 baseEnd_3136981 := by
    simpa [prefixWord, tailWord_3136981, baseEnd_3136981] using wordTrace_append hprefix tailTrace_3136981
  have hstable : (prefixWord ++ tailWord_3136981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3136981).length < 2 ^ (prefixWord ++ tailWord_3136981).sum := by decide
  have hdescent : baseEnd_3136981 < baseStart_3136981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3136981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137074 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_3137074 : Nat := 118140960795 + 3137074 * 2 ^ 59
def prefixEnd_3137074 : Nat := 4983230072969 + 3 ^ 40 * 3137074 * 2
def baseEnd_3137074 : Nat := 536942270240921472415955

theorem tailTrace_3137074 : CollatzResearch.WordTrace tailWord_3137074 prefixEnd_3137074 536942270240921472415955 := by
  unfold tailWord_3137074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28604622159231035607378569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76278992424616094953009517 28604622159231035607378569)
  ·
    refine ⟨21453466619423276705533927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28604622159231035607378569 21453466619423276705533927)
    ·
      refine ⟨32180199929134915058300891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21453466619423276705533927 32180199929134915058300891)
      ·
        refine ⟨48270299893702372587451337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32180199929134915058300891 48270299893702372587451337)
        ·
          refine ⟨36202724920276779440588503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48270299893702372587451337 36202724920276779440588503)
          ·
            refine ⟨54304087380415169160882755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36202724920276779440588503 54304087380415169160882755)
            ·
              refine ⟨81456131070622753741324133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54304087380415169160882755 81456131070622753741324133)
              ·
                refine ⟨15273024575741766326498275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81456131070622753741324133 15273024575741766326498275)
                ·
                  refine ⟨22909536863612649489747413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15273024575741766326498275 22909536863612649489747413)
                  ·
                    refine ⟨536942270240921472415955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22909536863612649489747413 536942270240921472415955)
                    ·
                      rfl

theorem cell23_3137074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_3137074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137074 prefixEnd_3137074 := by exact prefixLift 3137074
  have htrace : WordTrace (prefixWord ++ tailWord_3137074) baseStart_3137074 baseEnd_3137074 := by
    simpa [prefixWord, tailWord_3137074, baseEnd_3137074] using wordTrace_append hprefix tailTrace_3137074
  have hstable : (prefixWord ++ tailWord_3137074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137074).length < 2 ^ (prefixWord ++ tailWord_3137074).sum := by decide
  have hdescent : baseEnd_3137074 < baseStart_3137074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137078 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_3137078 : Nat := 118140960795 + 3137078 * 2 ^ 59
def prefixEnd_3137078 : Nat := 4983230072969 + 3 ^ 40 * 3137078 * 2
def baseEnd_3137078 : Nat := 178980984960598044621983

theorem tailTrace_3137078 : CollatzResearch.WordTrace tailWord_3137078 prefixEnd_3137078 178980984960598044621983 := by
  unfold tailWord_3137078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7151164658056853194541243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76279089685939767408439925 7151164658056853194541243)
  ·
    refine ⟨10726746987085279791811865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7151164658056853194541243 10726746987085279791811865)
    ·
      refine ⟨8045060240313959843858899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10726746987085279791811865 8045060240313959843858899)
      ·
        refine ⟨12067590360470939765788349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8045060240313959843858899 12067590360470939765788349)
        ·
          refine ⟨4525346385176602412170631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12067590360470939765788349 4525346385176602412170631)
          ·
            refine ⟨6788019577764903618255947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4525346385176602412170631 6788019577764903618255947)
            ·
              refine ⟨10182029366647355427383921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788019577764903618255947 10182029366647355427383921)
              ·
                refine ⟨7636522024985516570537941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10182029366647355427383921 7636522024985516570537941)
                ·
                  refine ⟨178980984960598044621983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7636522024985516570537941 178980984960598044621983)
                  ·
                    rfl

theorem cell23_3137078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_3137078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137078 prefixEnd_3137078 := by exact prefixLift 3137078
  have htrace : WordTrace (prefixWord ++ tailWord_3137078) baseStart_3137078 baseEnd_3137078 := by
    simpa [prefixWord, tailWord_3137078, baseEnd_3137078] using wordTrace_append hprefix tailTrace_3137078
  have hstable : (prefixWord ++ tailWord_3137078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137078).length < 2 ^ (prefixWord ++ tailWord_3137078).sum := by decide
  have hdescent : baseEnd_3137078 < baseStart_3137078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137114 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_3137114 : Nat := 118140960795 + 3137114 * 2 ^ 59
def prefixEnd_3137114 : Nat := 4983230072969 + 3 ^ 40 * 3137114 * 2
def baseEnd_3137114 : Nat := 1610847349948944260747681

theorem tailTrace_3137114 : CollatzResearch.WordTrace tailWord_3137114 prefixEnd_3137114 1610847349948944260747681 := by
  unfold tailWord_3137114
  simp only [CollatzResearch.WordTrace]
  refine ⟨28604986889194807315242599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76279965037852819507313597 28604986889194807315242599)
  ·
    refine ⟨42907480333792210972863899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28604986889194807315242599 42907480333792210972863899)
    ·
      refine ⟨64361220500688316459295849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42907480333792210972863899 64361220500688316459295849)
      ·
        refine ⟨48270915375516237344471887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64361220500688316459295849 48270915375516237344471887)
        ·
          refine ⟨72406373063274356016707831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48270915375516237344471887 72406373063274356016707831)
          ·
            refine ⟨108609559594911534025061747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72406373063274356016707831 108609559594911534025061747)
            ·
              refine ⟨162914339392367301037592621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108609559594911534025061747 162914339392367301037592621)
              ·
                refine ⟨61092877272137737889097233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162914339392367301037592621 61092877272137737889097233)
                ·
                  refine ⟨45819657954103303416822925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61092877272137737889097233 45819657954103303416822925)
                  ·
                    refine ⟨17182371732788738781308597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45819657954103303416822925 17182371732788738781308597)
                    ·
                      refine ⟨1610847349948944260747681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17182371732788738781308597 1610847349948944260747681)
                      ·
                        rfl

theorem cell23_3137114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_3137114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137114 prefixEnd_3137114 := by exact prefixLift 3137114
  have htrace : WordTrace (prefixWord ++ tailWord_3137114) baseStart_3137114 baseEnd_3137114 := by
    simpa [prefixWord, tailWord_3137114, baseEnd_3137114] using wordTrace_append hprefix tailTrace_3137114
  have hstable : (prefixWord ++ tailWord_3137114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137114).length < 2 ^ (prefixWord ++ tailWord_3137114).sum := by decide
  have hdescent : baseEnd_3137114 < baseStart_3137114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137138 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_3137138 : Nat := 118140960795 + 3137138 * 2 ^ 59
def prefixEnd_3137138 : Nat := 4983230072969 + 3 ^ 40 * 3137138 * 2
def baseEnd_3137138 : Nat := 536953224494884055615857

theorem tailTrace_3137138 : CollatzResearch.WordTrace tailWord_3137138 prefixEnd_3137138 536953224494884055615857 := by
  unfold tailWord_3137138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28605205727173070339961017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76280548605794854239896045 28605205727173070339961017)
  ·
    refine ⟨21453904295379802754970763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28605205727173070339961017 21453904295379802754970763)
    ·
      refine ⟨32180856443069704132456145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21453904295379802754970763 32180856443069704132456145)
      ·
        refine ⟨24135642332302278099342109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32180856443069704132456145 24135642332302278099342109)
        ·
          refine ⟨9050865874613354287253291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24135642332302278099342109 9050865874613354287253291)
          ·
            refine ⟨13576298811920031430879937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9050865874613354287253291 13576298811920031430879937)
            ·
              refine ⟨10182224108940023573159953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13576298811920031430879937 10182224108940023573159953)
              ·
                refine ⟨7636668081705017679869965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10182224108940023573159953 7636668081705017679869965)
                ·
                  refine ⟨2863750530639381629951237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7636668081705017679869965 2863750530639381629951237)
                  ·
                    refine ⟨536953224494884055615857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2863750530639381629951237 536953224494884055615857)
                    ·
                      rfl

theorem cell23_3137138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_3137138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137138 prefixEnd_3137138 := by exact prefixLift 3137138
  have htrace : WordTrace (prefixWord ++ tailWord_3137138) baseStart_3137138 baseEnd_3137138 := by
    simpa [prefixWord, tailWord_3137138, baseEnd_3137138] using wordTrace_append hprefix tailTrace_3137138
  have hstable : (prefixWord ++ tailWord_3137138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137138).length < 2 ^ (prefixWord ++ tailWord_3137138).sum := by decide
  have hdescent : baseEnd_3137138 < baseStart_3137138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137172 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3137172 : Nat := 118140960795 + 3137172 * 2 ^ 59
def prefixEnd_3137172 : Nat := 4983230072969 + 3 ^ 40 * 3137172 * 2
def baseEnd_3137172 : Nat := 536959043942301677940805

theorem tailTrace_3137172 : CollatzResearch.WordTrace tailWord_3137172 prefixEnd_3137172 536959043942301677940805 := by
  unfold tailWord_3137172
  simp only [CollatzResearch.WordTrace]
  refine ⟨57211031495284552583290885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76281375327046070111054513 57211031495284552583290885)
  ·
    refine ⟨10727068405365853609367041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57211031495284552583290885 10727068405365853609367041)
    ·
      refine ⟨8045301304024390207025281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10727068405365853609367041 8045301304024390207025281)
      ·
        refine ⟨6033975978018292655268961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8045301304024390207025281 6033975978018292655268961)
        ·
          refine ⟨4525481983513719491451721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6033975978018292655268961 4525481983513719491451721)
          ·
            refine ⟨3394111487635289618588791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4525481983513719491451721 3394111487635289618588791)
            ·
              refine ⟨5091167231452934427883187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394111487635289618588791 5091167231452934427883187)
              ·
                refine ⟨7636750847179401641824781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091167231452934427883187 7636750847179401641824781)
                ·
                  refine ⟨2863781567692275615684293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7636750847179401641824781 2863781567692275615684293)
                  ·
                    refine ⟨536959043942301677940805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2863781567692275615684293 536959043942301677940805)
                    ·
                      rfl

theorem cell23_3137172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3137172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137172 prefixEnd_3137172 := by exact prefixLift 3137172
  have htrace : WordTrace (prefixWord ++ tailWord_3137172) baseStart_3137172 baseEnd_3137172 := by
    simpa [prefixWord, tailWord_3137172, baseEnd_3137172] using wordTrace_append hprefix tailTrace_3137172
  have hstable : (prefixWord ++ tailWord_3137172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137172).length < 2 ^ (prefixWord ++ tailWord_3137172).sum := by decide
  have hdescent : baseEnd_3137172 < baseStart_3137172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137181 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_3137181 : Nat := 118140960795 + 3137181 * 2 ^ 59
def prefixEnd_3137181 : Nat := 4983230072969 + 3 ^ 40 * 3137181 * 2
def baseEnd_3137181 : Nat := 536960584384265166203291

theorem tailTrace_3137181 : CollatzResearch.WordTrace tailWord_3137181 prefixEnd_3137181 536960584384265166203291 := by
  unfold tailWord_3137181
  simp only [CollatzResearch.WordTrace]
  refine ⟨114422391247536499703659397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76281594165024333135772931 114422391247536499703659397)
  ·
    refine ⟨21454198358913093694436137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114422391247536499703659397 21454198358913093694436137)
    ·
      refine ⟨16090648769184820270827103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21454198358913093694436137 16090648769184820270827103)
      ·
        refine ⟨24135973153777230406240655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16090648769184820270827103 24135973153777230406240655)
        ·
          refine ⟨36203959730665845609360983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24135973153777230406240655 36203959730665845609360983)
          ·
            refine ⟨54305939595998768414041475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36203959730665845609360983 54305939595998768414041475)
            ·
              refine ⟨81458909393998152621062213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54305939595998768414041475 81458909393998152621062213)
              ·
                refine ⟨15273545511374653616449165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81458909393998152621062213 15273545511374653616449165)
                ·
                  refine ⟨5727579566765495106168437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15273545511374653616449165 5727579566765495106168437)
                  ·
                    refine ⟨536960584384265166203291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5727579566765495106168437 536960584384265166203291)
                    ·
                      rfl

theorem cell23_3137181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_3137181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137181 prefixEnd_3137181 := by exact prefixLift 3137181
  have htrace : WordTrace (prefixWord ++ tailWord_3137181) baseStart_3137181 baseEnd_3137181 := by
    simpa [prefixWord, tailWord_3137181, baseEnd_3137181] using wordTrace_append hprefix tailTrace_3137181
  have hstable : (prefixWord ++ tailWord_3137181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137181).length < 2 ^ (prefixWord ++ tailWord_3137181).sum := by decide
  have hdescent : baseEnd_3137181 < baseStart_3137181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137185 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 6]
def baseStart_3137185 : Nat := 118140960795 + 3137185 * 2 ^ 59
def prefixEnd_3137185 : Nat := 4983230072969 + 3 ^ 40 * 3137185 * 2
def baseEnd_3137185 : Nat := 178987089675045942551095

theorem tailTrace_3137185 : CollatzResearch.WordTrace tailWord_3137185 prefixEnd_3137185 178987089675045942551095 := by
  unfold tailWord_3137185
  simp only [CollatzResearch.WordTrace]
  refine ⟨114422537139522008386805009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76281691426348005591203339 114422537139522008386805009)
  ·
    refine ⟨85816902854641506290103757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114422537139522008386805009 85816902854641506290103757)
    ·
      refine ⟨32181338570490564858788909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85816902854641506290103757 32181338570490564858788909)
      ·
        refine ⟨12068001963933961822045841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32181338570490564858788909 12068001963933961822045841)
        ·
          refine ⟨9051001472950471366534381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12068001963933961822045841 9051001472950471366534381)
          ·
            refine ⟨3394125552356426762450393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9051001472950471366534381 3394125552356426762450393)
            ·
              refine ⟨2545594164267320071837795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3394125552356426762450393 2545594164267320071837795)
              ·
                refine ⟨3818391246400980107756693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545594164267320071837795 3818391246400980107756693)
                ·
                  refine ⟨178987089675045942551095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3818391246400980107756693 178987089675045942551095)
                  ·
                    rfl

theorem cell23_3137185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 6].length) (baseStart_3137185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137185 prefixEnd_3137185 := by exact prefixLift 3137185
  have htrace : WordTrace (prefixWord ++ tailWord_3137185) baseStart_3137185 baseEnd_3137185 := by
    simpa [prefixWord, tailWord_3137185, baseEnd_3137185] using wordTrace_append hprefix tailTrace_3137185
  have hstable : (prefixWord ++ tailWord_3137185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137185).length < 2 ^ (prefixWord ++ tailWord_3137185).sum := by decide
  have hdescent : baseEnd_3137185 < baseStart_3137185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137211 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 6, 4]
def baseStart_3137211 : Nat := 118140960795 + 3137211 * 2 ^ 59
def prefixEnd_3137211 : Nat := 4983230072969 + 3 ^ 40 * 3137211 * 2
def baseEnd_3137211 : Nat := 536965719190810127078245

theorem tailTrace_3137211 : CollatzResearch.WordTrace tailWord_3137211 prefixEnd_3137211 536965719190810127078245 := by
  unfold tailWord_3137211
  simp only [CollatzResearch.WordTrace]
  refine ⟨114423485437427814827251487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76282323624951876551500991 114423485437427814827251487)
  ·
    refine ⟨171635228156141722240877231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114423485437427814827251487 171635228156141722240877231)
    ·
      refine ⟨257452842234212583361315847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171635228156141722240877231 257452842234212583361315847)
      ·
        refine ⟨386179263351318875041973771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257452842234212583361315847 386179263351318875041973771)
        ·
          refine ⟨579268895026978312562960657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386179263351318875041973771 579268895026978312562960657)
          ·
            refine ⟨434451671270233734422220493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579268895026978312562960657 434451671270233734422220493)
            ·
              refine ⟨162919376726337650408332685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434451671270233734422220493 162919376726337650408332685)
              ·
                refine ⟨61094766272376618903124757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162919376726337650408332685 61094766272376618903124757)
                ·
                  refine ⟨2863817169017654011083973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61094766272376618903124757 2863817169017654011083973)
                  ·
                    refine ⟨536965719190810127078245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2863817169017654011083973 536965719190810127078245)
                    ·
                      rfl

theorem cell23_3137211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 4].length) (baseStart_3137211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137211 prefixEnd_3137211 := by exact prefixLift 3137211
  have htrace : WordTrace (prefixWord ++ tailWord_3137211) baseStart_3137211 baseEnd_3137211 := by
    simpa [prefixWord, tailWord_3137211, baseEnd_3137211] using wordTrace_append hprefix tailTrace_3137211
  have hstable : (prefixWord ++ tailWord_3137211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137211).length < 2 ^ (prefixWord ++ tailWord_3137211).sum := by decide
  have hdescent : baseEnd_3137211 < baseStart_3137211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137241 : List Nat := [1, 2, 1, 2, 3, 3, 3, 8]
def baseStart_3137241 : Nat := 118140960795 + 3137241 * 2 ^ 59
def prefixEnd_3137241 : Nat := 4983230072969 + 3 ^ 40 * 3137241 * 2
def baseEnd_3137241 : Nat := 59663428221928343105911

theorem tailTrace_3137241 : CollatzResearch.WordTrace tailWord_3137241 prefixEnd_3137241 59663428221928343105911 := by
  unfold tailWord_3137241
  simp only [CollatzResearch.WordTrace]
  refine ⟨114424579627319129950843577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76283053084879419967229051 114424579627319129950843577)
  ·
    refine ⟨85818434720489347463132683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114424579627319129950843577 85818434720489347463132683)
    ·
      refine ⟨128727652080734021194699025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85818434720489347463132683 128727652080734021194699025)
      ·
        refine ⟨96545739060550515896024269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128727652080734021194699025 96545739060550515896024269)
        ·
          refine ⟨36204652147706443461009101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96545739060550515896024269 36204652147706443461009101)
          ·
            refine ⟨13576744555389916297878413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36204652147706443461009101 13576744555389916297878413)
            ·
              refine ⟨5091279208271218611704405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13576744555389916297878413 5091279208271218611704405)
              ·
                refine ⟨59663428221928343105911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5091279208271218611704405 59663428221928343105911)
                ·
                  rfl

theorem cell23_3137241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 8].length) (baseStart_3137241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137241 prefixEnd_3137241 := by exact prefixLift 3137241
  have htrace : WordTrace (prefixWord ++ tailWord_3137241) baseStart_3137241 baseEnd_3137241 := by
    simpa [prefixWord, tailWord_3137241, baseEnd_3137241] using wordTrace_append hprefix tailTrace_3137241
  have hstable : (prefixWord ++ tailWord_3137241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137241).length < 2 ^ (prefixWord ++ tailWord_3137241).sum := by decide
  have hdescent : baseEnd_3137241 < baseStart_3137241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137291 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 4]
def baseStart_3137291 : Nat := 118140960795 + 3137291 * 2 ^ 59
def prefixEnd_3137291 : Nat := 4983230072969 + 3 ^ 40 * 3137291 * 2
def baseEnd_3137291 : Nat := 1610938236024790068234367

theorem tailTrace_3137291 : CollatzResearch.WordTrace tailWord_3137291 prefixEnd_3137291 1610938236024790068234367 := by
  unfold tailWord_3137291
  simp only [CollatzResearch.WordTrace]
  refine ⟨114426403277137988490163727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76284268851425325660109151 114426403277137988490163727)
  ·
    refine ⟨171639604915706982735245591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114426403277137988490163727 171639604915706982735245591)
    ·
      refine ⟨257459407373560474102868387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171639604915706982735245591 257459407373560474102868387)
      ·
        refine ⟨386189111060340711154302581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257459407373560474102868387 386189111060340711154302581)
        ·
          refine ⟨36205229161906941670715867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 386189111060340711154302581 36205229161906941670715867)
          ·
            refine ⟨54307843742860412506073801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36205229161906941670715867 54307843742860412506073801)
            ·
              refine ⟨40730882807145309379555351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54307843742860412506073801 40730882807145309379555351)
              ·
                refine ⟨61096324210717964069333027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40730882807145309379555351 61096324210717964069333027)
                ·
                  refine ⟨91644486316076946103999541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61096324210717964069333027 91644486316076946103999541)
                  ·
                    refine ⟨8591670592132213697249957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91644486316076946103999541 8591670592132213697249957)
                    ·
                      refine ⟨1610938236024790068234367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8591670592132213697249957 1610938236024790068234367)
                      ·
                        rfl

theorem cell23_3137291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 4].length) (baseStart_3137291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137291 prefixEnd_3137291 := by exact prefixLift 3137291
  have htrace : WordTrace (prefixWord ++ tailWord_3137291) baseStart_3137291 baseEnd_3137291 := by
    simpa [prefixWord, tailWord_3137291, baseEnd_3137291] using wordTrace_append hprefix tailTrace_3137291
  have hstable : (prefixWord ++ tailWord_3137291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137291).length < 2 ^ (prefixWord ++ tailWord_3137291).sum := by decide
  have hdescent : baseEnd_3137291 < baseStart_3137291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137312 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 1, 3, 2]
def baseStart_3137312 : Nat := 118140960795 + 3137312 * 2 ^ 59
def prefixEnd_3137312 : Nat := 4983230072969 + 3 ^ 40 * 3137312 * 2
def baseEnd_3137312 : Nat := 1610949019118534486071771

theorem tailTrace_3137312 : CollatzResearch.WordTrace tailWord_3137312 prefixEnd_3137312 1610949019118534486071771 := by
  unfold tailWord_3137312
  simp only [CollatzResearch.WordTrace]
  refine ⟨57213584605030954538339095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76284779473374606051118793 57213584605030954538339095)
  ·
    refine ⟨85820376907546431807508643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57213584605030954538339095 85820376907546431807508643)
    ·
      refine ⟨128730565361319647711262965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85820376907546431807508643 128730565361319647711262965)
      ·
        refine ⟨12068490502623716972930903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128730565361319647711262965 12068490502623716972930903)
        ·
          refine ⟨18102735753935575459396355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12068490502623716972930903 18102735753935575459396355)
          ·
            refine ⟨27154103630903363189094533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18102735753935575459396355 27154103630903363189094533)
            ·
              refine ⟨5091394430794380597955225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27154103630903363189094533 5091394430794380597955225)
              ·
                refine ⟨3818545823095785448466419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5091394430794380597955225 3818545823095785448466419)
                ·
                  refine ⟨5727818734643678172699629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818545823095785448466419 5727818734643678172699629)
                  ·
                    refine ⟨2147932025491379314762361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5727818734643678172699629 2147932025491379314762361)
                    ·
                      refine ⟨1610949019118534486071771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2147932025491379314762361 1610949019118534486071771)
                      ·
                        rfl

theorem cell23_3137312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_3137312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137312 prefixEnd_3137312 := by exact prefixLift 3137312
  have htrace : WordTrace (prefixWord ++ tailWord_3137312) baseStart_3137312 baseEnd_3137312 := by
    simpa [prefixWord, tailWord_3137312, baseEnd_3137312] using wordTrace_append hprefix tailTrace_3137312
  have hstable : (prefixWord ++ tailWord_3137312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137312).length < 2 ^ (prefixWord ++ tailWord_3137312).sum := by decide
  have hdescent : baseEnd_3137312 < baseStart_3137312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137388 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_3137388 : Nat := 118140960795 + 3137388 * 2 ^ 59
def prefixEnd_3137388 : Nat := 4983230072969 + 3 ^ 40 * 3137388 * 2
def baseEnd_3137388 : Nat := 1610988043648276188721421

theorem tailTrace_3137388 : CollatzResearch.WordTrace tailWord_3137388 prefixEnd_3137388 1610988043648276188721421 := by
  unfold tailWord_3137388
  simp only [CollatzResearch.WordTrace]
  refine ⟨57214970578893287028222409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76286627438524382704296545 57214970578893287028222409)
  ·
    refine ⟨42911227934169965271166807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57214970578893287028222409 42911227934169965271166807)
    ·
      refine ⟨64366841901254947906750211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42911227934169965271166807 64366841901254947906750211)
      ·
        refine ⟨96550262851882421860125317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64366841901254947906750211 96550262851882421860125317)
        ·
          refine ⟨18103174284727954098773497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96550262851882421860125317 18103174284727954098773497)
          ·
            refine ⟨13577380713545965574080123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18103174284727954098773497 13577380713545965574080123)
            ·
              refine ⟨20366071070318948361120185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13577380713545965574080123 20366071070318948361120185)
              ·
                refine ⟨15274553302739211270840139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20366071070318948361120185 15274553302739211270840139)
                ·
                  refine ⟨22911829954108816906260209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15274553302739211270840139 22911829954108816906260209)
                  ·
                    refine ⟨17183872465581612679695157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22911829954108816906260209 17183872465581612679695157)
                    ·
                      refine ⟨1610988043648276188721421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17183872465581612679695157 1610988043648276188721421)
                      ·
                        rfl

theorem cell23_3137388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_3137388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137388 prefixEnd_3137388 := by exact prefixLift 3137388
  have htrace : WordTrace (prefixWord ++ tailWord_3137388) baseStart_3137388 baseEnd_3137388 := by
    simpa [prefixWord, tailWord_3137388, baseEnd_3137388] using wordTrace_append hprefix tailTrace_3137388
  have hstable : (prefixWord ++ tailWord_3137388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137388).length < 2 ^ (prefixWord ++ tailWord_3137388).sum := by decide
  have hdescent : baseEnd_3137388 < baseStart_3137388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137432 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3137432 : Nat := 118140960795 + 3137432 * 2 ^ 59
def prefixEnd_3137432 : Nat := 4983230072969 + 3 ^ 40 * 3137432 * 2
def baseEnd_3137432 : Nat := 1611010636797074016571219

theorem tailTrace_3137432 : CollatzResearch.WordTrace tailWord_3137432 prefixEnd_3137432 1611010636797074016571219 := by
  unfold tailWord_3137432
  simp only [CollatzResearch.WordTrace]
  refine ⟨57215772984813584785523275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76287697313084779714031033 57215772984813584785523275)
  ·
    refine ⟨85823659477220377178284913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57215772984813584785523275 85823659477220377178284913)
    ·
      refine ⟨64367744607915282883713685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85823659477220377178284913 64367744607915282883713685)
      ·
        refine ⟨3017238028496028885174079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64367744607915282883713685 3017238028496028885174079)
        ·
          refine ⟨4525857042744043327761119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3017238028496028885174079 4525857042744043327761119)
          ·
            refine ⟨6788785564116064991641679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4525857042744043327761119 6788785564116064991641679)
            ·
              refine ⟨10183178346174097487462519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788785564116064991641679 10183178346174097487462519)
              ·
                refine ⟨15274767519261146231193779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10183178346174097487462519 15274767519261146231193779)
                ·
                  refine ⟨22912151278891719346790669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15274767519261146231193779 22912151278891719346790669)
                  ·
                    refine ⟨8592056729584394755046501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22912151278891719346790669 8592056729584394755046501)
                    ·
                      refine ⟨1611010636797074016571219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8592056729584394755046501 1611010636797074016571219)
                      ·
                        rfl

theorem cell23_3137432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3137432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137432 prefixEnd_3137432 := by exact prefixLift 3137432
  have htrace : WordTrace (prefixWord ++ tailWord_3137432) baseStart_3137432 baseEnd_3137432 := by
    simpa [prefixWord, tailWord_3137432, baseEnd_3137432] using wordTrace_append hprefix tailTrace_3137432
  have hstable : (prefixWord ++ tailWord_3137432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137432).length < 2 ^ (prefixWord ++ tailWord_3137432).sum := by decide
  have hdescent : baseEnd_3137432 < baseStart_3137432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137482 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_3137482 : Nat := 118140960795 + 3137482 * 2 ^ 59
def prefixEnd_3137482 : Nat := 4983230072969 + 3 ^ 40 * 3137482 * 2
def baseEnd_3137482 : Nat := 1611036310829798820945989

theorem tailTrace_3137482 : CollatzResearch.WordTrace tailWord_3137482 prefixEnd_3137482 1611036310829798820945989 := by
  unfold tailWord_3137482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28608342404861507027591675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76288913079630685406911133 28608342404861507027591675)
  ·
    refine ⟨42912513607292260541387513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28608342404861507027591675 42912513607292260541387513)
    ·
      refine ⟨32184385205469195406040635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42912513607292260541387513 32184385205469195406040635)
      ·
        refine ⟨48276577808203793109060953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32184385205469195406040635 48276577808203793109060953)
        ·
          refine ⟨36207433356152844831795715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48276577808203793109060953 36207433356152844831795715)
          ·
            refine ⟨54311150034229267247693573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36207433356152844831795715 54311150034229267247693573)
            ·
              refine ⟨10183340631417987608942545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54311150034229267247693573 10183340631417987608942545)
              ·
                refine ⟨7637505473563490706706909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10183340631417987608942545 7637505473563490706706909)
                ·
                  refine ⟨2864064552586309015015091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7637505473563490706706909 2864064552586309015015091)
                  ·
                    refine ⟨4296096828879463522522637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2864064552586309015015091 4296096828879463522522637)
                    ·
                      refine ⟨1611036310829798820945989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4296096828879463522522637 1611036310829798820945989)
                      ·
                        rfl

theorem cell23_3137482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_3137482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137482 prefixEnd_3137482 := by exact prefixLift 3137482
  have htrace : WordTrace (prefixWord ++ tailWord_3137482) baseStart_3137482 baseEnd_3137482 := by
    simpa [prefixWord, tailWord_3137482, baseEnd_3137482] using wordTrace_append hprefix tailTrace_3137482
  have hstable : (prefixWord ++ tailWord_3137482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137482).length < 2 ^ (prefixWord ++ tailWord_3137482).sum := by decide
  have hdescent : baseEnd_3137482 < baseStart_3137482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137492 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3137492 : Nat := 118140960795 + 3137492 * 2 ^ 59
def prefixEnd_3137492 : Nat := 4983230072969 + 3 ^ 40 * 3137492 * 2
def baseEnd_3137492 : Nat := 1611041445636343781820943

theorem tailTrace_3137492 : CollatzResearch.WordTrace tailWord_3137492 prefixEnd_3137492 1611041445636343781820943 := by
  unfold tailWord_3137492
  simp only [CollatzResearch.WordTrace]
  refine ⟨57216867174704899909115365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76289156232939866545487153 57216867174704899909115365)
  ·
    refine ⟨10728162595257168732959131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57216867174704899909115365 10728162595257168732959131)
    ·
      refine ⟨16092243892885753099438697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10728162595257168732959131 16092243892885753099438697)
      ·
        refine ⟨12069182919664314824579023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16092243892885753099438697 12069182919664314824579023)
        ·
          refine ⟨18103774379496472236868535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12069182919664314824579023 18103774379496472236868535)
          ·
            refine ⟨27155661569244708355302803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18103774379496472236868535 27155661569244708355302803)
            ·
              refine ⟨40733492353867062532954205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27155661569244708355302803 40733492353867062532954205)
              ·
                refine ⟨15275059632700148449857827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40733492353867062532954205 15275059632700148449857827)
                ·
                  refine ⟨22912589449050222674786741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15275059632700148449857827 22912589449050222674786741)
                  ·
                    refine ⟨2148055260848458375761257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22912589449050222674786741 2148055260848458375761257)
                    ·
                      refine ⟨1611041445636343781820943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148055260848458375761257 1611041445636343781820943)
                      ·
                        rfl

theorem cell23_3137492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3137492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137492 prefixEnd_3137492 := by exact prefixLift 3137492
  have htrace : WordTrace (prefixWord ++ tailWord_3137492) baseStart_3137492 baseEnd_3137492 := by
    simpa [prefixWord, tailWord_3137492, baseEnd_3137492] using wordTrace_append hprefix tailTrace_3137492
  have hstable : (prefixWord ++ tailWord_3137492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137492).length < 2 ^ (prefixWord ++ tailWord_3137492).sum := by decide
  have hdescent : baseEnd_3137492 < baseStart_3137492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137528 : List Nat := [2, 1, 2, 1, 1, 3, 3, 10]
def baseStart_3137528 : Nat := 118140960795 + 3137528 * 2 ^ 59
def prefixEnd_3137528 : Nat := 4983230072969 + 3 ^ 40 * 3137528 * 2
def baseEnd_3137528 : Nat := 59668886331107616332251

theorem tailTrace_3137528 : CollatzResearch.WordTrace tailWord_3137528 prefixEnd_3137528 59668886331107616332251 := by
  unfold tailWord_3137528
  simp only [CollatzResearch.WordTrace]
  refine ⟨57217523688639688983270619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76290031584852918644360825 57217523688639688983270619)
  ·
    refine ⟨85826285532959533474905929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57217523688639688983270619 85826285532959533474905929)
    ·
      refine ⟨64369714149719650106179447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85826285532959533474905929 64369714149719650106179447)
      ·
        refine ⟨96554571224579475159269171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64369714149719650106179447 96554571224579475159269171)
        ·
          refine ⟨144831856836869212738903757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96554571224579475159269171 144831856836869212738903757)
          ·
            refine ⟨54311946313825954777088909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144831856836869212738903757 54311946313825954777088909)
            ·
              refine ⟨20366979867684733041408341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54311946313825954777088909 20366979867684733041408341)
              ·
                refine ⟨59668886331107616332251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20366979867684733041408341 59668886331107616332251)
                ·
                  rfl

theorem cell23_3137528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 10].length) (baseStart_3137528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137528 prefixEnd_3137528 := by exact prefixLift 3137528
  have htrace : WordTrace (prefixWord ++ tailWord_3137528) baseStart_3137528 baseEnd_3137528 := by
    simpa [prefixWord, tailWord_3137528, baseEnd_3137528] using wordTrace_append hprefix tailTrace_3137528
  have hstable : (prefixWord ++ tailWord_3137528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137528).length < 2 ^ (prefixWord ++ tailWord_3137528).sum := by decide
  have hdescent : baseEnd_3137528 < baseStart_3137528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137532 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_3137532 : Nat := 118140960795 + 3137532 * 2 ^ 59
def prefixEnd_3137532 : Nat := 4983230072969 + 3 ^ 40 * 3137532 * 2
def baseEnd_3137532 : Nat := 537020661620841208440253

theorem tailTrace_3137532 : CollatzResearch.WordTrace tailWord_3137532 prefixEnd_3137532 537020661620841208440253 := by
  unfold tailWord_3137532
  simp only [CollatzResearch.WordTrace]
  refine ⟨57217596634632443324843425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76290128846176591099791233 57217596634632443324843425)
  ·
    refine ⟨42913197475974332493632569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57217596634632443324843425 42913197475974332493632569)
    ·
      refine ⟨32184898106980749370224427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42913197475974332493632569 32184898106980749370224427)
      ·
        refine ⟨48277347160471124055336641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32184898106980749370224427 48277347160471124055336641)
        ·
          refine ⟨36208010370353343041502481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48277347160471124055336641 36208010370353343041502481)
          ·
            refine ⟨27156007777765007281126861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36208010370353343041502481 27156007777765007281126861)
            ·
              refine ⟨10183502916661877730422573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27156007777765007281126861 10183502916661877730422573)
              ·
                refine ⟨3818813593748204148908465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10183502916661877730422573 3818813593748204148908465)
                ·
                  refine ⟨2864110195311153111681349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3818813593748204148908465 2864110195311153111681349)
                  ·
                    refine ⟨537020661620841208440253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864110195311153111681349 537020661620841208440253)
                    ·
                      rfl

theorem cell23_3137532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_3137532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137532 prefixEnd_3137532 := by exact prefixLift 3137532
  have htrace : WordTrace (prefixWord ++ tailWord_3137532) baseStart_3137532 baseEnd_3137532 := by
    simpa [prefixWord, tailWord_3137532, baseEnd_3137532] using wordTrace_append hprefix tailTrace_3137532
  have hstable : (prefixWord ++ tailWord_3137532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137532).length < 2 ^ (prefixWord ++ tailWord_3137532).sum := by decide
  have hdescent : baseEnd_3137532 < baseStart_3137532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137555 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 3]
def baseStart_3137555 : Nat := 118140960795 + 3137555 * 2 ^ 59
def prefixEnd_3137555 : Nat := 4983230072969 + 3 ^ 40 * 3137555 * 2
def baseEnd_3137555 : Nat := 1611073794917577035333153

theorem tailTrace_3137555 : CollatzResearch.WordTrace tailWord_3137555 prefixEnd_3137555 1611073794917577035333153 := by
  unfold tailWord_3137555
  simp only [CollatzResearch.WordTrace]
  refine ⟨114436032148181561577774119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76290688098787707718516079 114436032148181561577774119)
  ·
    refine ⟨171654048222272342366661179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114436032148181561577774119 171654048222272342366661179)
    ·
      refine ⟨257481072333408513549991769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171654048222272342366661179 257481072333408513549991769)
      ·
        refine ⟨193110804250056385162493827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257481072333408513549991769 193110804250056385162493827)
        ·
          refine ⟨289666206375084577743740741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193110804250056385162493827 289666206375084577743740741)
          ·
            refine ⟨54312413695328358326951389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289666206375084577743740741 54312413695328358326951389)
            ·
              refine ⟨20367155135748134372606771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54312413695328358326951389 20367155135748134372606771)
              ·
                refine ⟨30550732703622201558910157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20367155135748134372606771 30550732703622201558910157)
                ·
                  refine ⟨11456524763858325584591309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30550732703622201558910157 11456524763858325584591309)
                  ·
                    refine ⟨4296196786446872094221741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11456524763858325584591309 4296196786446872094221741)
                    ·
                      refine ⟨1611073794917577035333153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4296196786446872094221741 1611073794917577035333153)
                      ·
                        rfl

theorem cell23_3137555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_3137555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137555 prefixEnd_3137555 := by exact prefixLift 3137555
  have htrace : WordTrace (prefixWord ++ tailWord_3137555) baseStart_3137555 baseEnd_3137555 := by
    simpa [prefixWord, tailWord_3137555, baseEnd_3137555] using wordTrace_append hprefix tailTrace_3137555
  have hstable : (prefixWord ++ tailWord_3137555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137555).length < 2 ^ (prefixWord ++ tailWord_3137555).sum := by decide
  have hdescent : baseEnd_3137555 < baseStart_3137555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137559 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3137559 : Nat := 118140960795 + 3137559 * 2 ^ 59
def prefixEnd_3137559 : Nat := 4983230072969 + 3 ^ 40 * 3137559 * 2
def baseEnd_3137559 : Nat := 1611075848840195019683135

theorem tailTrace_3137559 : CollatzResearch.WordTrace tailWord_3137559 prefixEnd_3137559 1611075848840195019683135 := by
  unfold tailWord_3137559
  simp only [CollatzResearch.WordTrace]
  refine ⟨114436178040167070260919731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76290785360111380173946487 114436178040167070260919731)
  ·
    refine ⟨171654267060250605391379597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114436178040167070260919731 171654267060250605391379597)
    ·
      refine ⟨64370350147593977021767349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171654267060250605391379597 64370350147593977021767349)
      ·
        refine ⟨6034720326336935345790689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64370350147593977021767349 6034720326336935345790689)
        ·
          refine ⟨4526040244752701509343017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6034720326336935345790689 4526040244752701509343017)
          ·
            refine ⟨3394530183564526132007263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4526040244752701509343017 3394530183564526132007263)
            ·
              refine ⟨5091795275346789198010895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394530183564526132007263 5091795275346789198010895)
              ·
                refine ⟨7637692913020183797016343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091795275346789198010895 7637692913020183797016343)
                ·
                  refine ⟨11456539369530275695524515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7637692913020183797016343 11456539369530275695524515)
                  ·
                    refine ⟨17184809054295413543286773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11456539369530275695524515 17184809054295413543286773)
                    ·
                      refine ⟨1611075848840195019683135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17184809054295413543286773 1611075848840195019683135)
                      ·
                        rfl

theorem cell23_3137559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3137559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137559 prefixEnd_3137559 := by exact prefixLift 3137559
  have htrace : WordTrace (prefixWord ++ tailWord_3137559) baseStart_3137559 baseEnd_3137559 := by
    simpa [prefixWord, tailWord_3137559, baseEnd_3137559] using wordTrace_append hprefix tailTrace_3137559
  have hstable : (prefixWord ++ tailWord_3137559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137559).length < 2 ^ (prefixWord ++ tailWord_3137559).sum := by decide
  have hdescent : baseEnd_3137559 < baseStart_3137559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137573 : List Nat := [1, 3, 1, 2, 2, 3, 4, 2, 1, 2, 2]
def baseStart_3137573 : Nat := 118140960795 + 3137573 * 2 ^ 59
def prefixEnd_3137573 : Nat := 4983230072969 + 3 ^ 40 * 3137573 * 2
def baseEnd_3137573 : Nat := 1611083037569357964908071

theorem tailTrace_3137573 : CollatzResearch.WordTrace tailWord_3137573 prefixEnd_3137573 1611083037569357964908071 := by
  unfold tailWord_3137573
  simp only [CollatzResearch.WordTrace]
  refine ⟨114436688662116350651929373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76291125774744233767952915 114436688662116350651929373)
  ·
    refine ⟨42913758248293631494473515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114436688662116350651929373 42913758248293631494473515)
    ·
      refine ⟨64370637372440447241710273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42913758248293631494473515 64370637372440447241710273)
      ·
        refine ⟨48277978029330335431282705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64370637372440447241710273 48277978029330335431282705)
        ·
          refine ⟨36208483521997751573462029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48277978029330335431282705 36208483521997751573462029)
          ·
            refine ⟨13578181320749156840048261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36208483521997751573462029 13578181320749156840048261)
            ·
              refine ⟨2545908997640466907509049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13578181320749156840048261 2545908997640466907509049)
              ·
                refine ⟨1909431748230350180631787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2545908997640466907509049 1909431748230350180631787)
                ·
                  refine ⟨2864147622345525270947681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909431748230350180631787 2864147622345525270947681)
                  ·
                    refine ⟨2148110716759143953210761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2864147622345525270947681 2148110716759143953210761)
                    ·
                      refine ⟨1611083037569357964908071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148110716759143953210761 1611083037569357964908071)
                      ·
                        rfl

theorem cell23_3137573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_3137573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137573 prefixEnd_3137573 := by exact prefixLift 3137573
  have htrace : WordTrace (prefixWord ++ tailWord_3137573) baseStart_3137573 baseEnd_3137573 := by
    simpa [prefixWord, tailWord_3137573, baseEnd_3137573] using wordTrace_append hprefix tailTrace_3137573
  have hstable : (prefixWord ++ tailWord_3137573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137573).length < 2 ^ (prefixWord ++ tailWord_3137573).sum := by decide
  have hdescent : baseEnd_3137573 < baseStart_3137573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137589 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_3137589 : Nat := 118140960795 + 3137589 * 2 ^ 59
def prefixEnd_3137589 : Nat := 4983230072969 + 3 ^ 40 * 3137589 * 2
def baseEnd_3137589 : Nat := 1611091253259829902307997

theorem tailTrace_3137589 : CollatzResearch.WordTrace tailWord_3137589 prefixEnd_3137589 1611091253259829902307997 := by
  unfold tailWord_3137589
  simp only [CollatzResearch.WordTrace]
  refine ⟨114437272230058385384511821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76291514820038923589674547 114437272230058385384511821)
  ·
    refine ⟨42913977086271894519191933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114437272230058385384511821 42913977086271894519191933)
    ·
      refine ⟨16092741407351960444696975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42913977086271894519191933 16092741407351960444696975)
      ·
        refine ⟨24139112111027940667045463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16092741407351960444696975 24139112111027940667045463)
        ·
          refine ⟨36208668166541911000568195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24139112111027940667045463 36208668166541911000568195)
          ·
            refine ⟨54313002249812866500852293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36208668166541911000568195 54313002249812866500852293)
            ·
              refine ⟨10183687921839912468909805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54313002249812866500852293 10183687921839912468909805)
              ·
                refine ⟨3818882970689967175841177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10183687921839912468909805 3818882970689967175841177)
                ·
                  refine ⟨2864162228017475381880883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3818882970689967175841177 2864162228017475381880883)
                  ·
                    refine ⟨4296243342026213072821325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2864162228017475381880883 4296243342026213072821325)
                    ·
                      refine ⟨1611091253259829902307997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4296243342026213072821325 1611091253259829902307997)
                      ·
                        rfl

theorem cell23_3137589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_3137589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137589 prefixEnd_3137589 := by exact prefixLift 3137589
  have htrace : WordTrace (prefixWord ++ tailWord_3137589) baseStart_3137589 baseEnd_3137589 := by
    simpa [prefixWord, tailWord_3137589, baseEnd_3137589] using wordTrace_append hprefix tailTrace_3137589
  have hstable : (prefixWord ++ tailWord_3137589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137589).length < 2 ^ (prefixWord ++ tailWord_3137589).sum := by decide
  have hdescent : baseEnd_3137589 < baseStart_3137589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137606 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_3137606 : Nat := 118140960795 + 3137606 * 2 ^ 59
def prefixEnd_3137606 : Nat := 4983230072969 + 3 ^ 40 * 3137606 * 2
def baseEnd_3137606 : Nat := 1611099982430956335795419

theorem tailTrace_3137606 : CollatzResearch.WordTrace tailWord_3137606 prefixEnd_3137606 1611099982430956335795419 := by
  unfold tailWord_3137606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3576184133468649915246271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76291928180664531525253781 3576184133468649915246271)
  ·
    refine ⟨5364276200202974872869407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3576184133468649915246271 5364276200202974872869407)
    ·
      refine ⟨8046414300304462309304111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5364276200202974872869407 8046414300304462309304111)
      ·
        refine ⟨12069621450456693463956167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8046414300304462309304111 12069621450456693463956167)
        ·
          refine ⟨18104432175685040195934251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12069621450456693463956167 18104432175685040195934251)
          ·
            refine ⟨27156648263527560293901377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18104432175685040195934251 27156648263527560293901377)
            ·
              refine ⟨20367486197645670220426033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27156648263527560293901377 20367486197645670220426033)
              ·
                refine ⟨15275614648234252665319525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20367486197645670220426033 15275614648234252665319525)
                ·
                  refine ⟨2864177746543922374747411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15275614648234252665319525 2864177746543922374747411)
                  ·
                    refine ⟨4296266619815883562121117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2864177746543922374747411 4296266619815883562121117)
                    ·
                      refine ⟨1611099982430956335795419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4296266619815883562121117 1611099982430956335795419)
                      ·
                        rfl

theorem cell23_3137606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_3137606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137606 prefixEnd_3137606 := by exact prefixLift 3137606
  have htrace : WordTrace (prefixWord ++ tailWord_3137606) baseStart_3137606 baseEnd_3137606 := by
    simpa [prefixWord, tailWord_3137606, baseEnd_3137606] using wordTrace_append hprefix tailTrace_3137606
  have hstable : (prefixWord ++ tailWord_3137606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137606).length < 2 ^ (prefixWord ++ tailWord_3137606).sum := by decide
  have hdescent : baseEnd_3137606 < baseStart_3137606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137615 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 3]
def baseStart_3137615 : Nat := 118140960795 + 3137615 * 2 ^ 59
def prefixEnd_3137615 : Nat := 4983230072969 + 3 ^ 40 * 3137615 * 2
def baseEnd_3137615 : Nat := 1611104603756846800582877

theorem tailTrace_3137615 : CollatzResearch.WordTrace tailWord_3137615 prefixEnd_3137615 1611104603756846800582877 := by
  unfold tailWord_3137615
  simp only [CollatzResearch.WordTrace]
  refine ⟨114438220527964191824958299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76292147018642794549972199 114438220527964191824958299)
  ·
    refine ⟨171657330791946287737437449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114438220527964191824958299 171657330791946287737437449)
    ·
      refine ⟨128742998093959715803078087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171657330791946287737437449 128742998093959715803078087)
      ·
        refine ⟨193114497140939573704617131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128742998093959715803078087 193114497140939573704617131)
        ·
          refine ⟨289671745711409360556925697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193114497140939573704617131 289671745711409360556925697)
          ·
            refine ⟨217253809283557020417694273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289671745711409360556925697 217253809283557020417694273)
            ·
              refine ⟨162940356962667765313270705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217253809283557020417694273 162940356962667765313270705)
              ·
                refine ⟨122205267722000823984953029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162940356962667765313270705 122205267722000823984953029)
                ·
                  refine ⟨22913487697875154497178693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122205267722000823984953029 22913487697875154497178693)
                  ·
                    refine ⟨4296278943351591468221005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22913487697875154497178693 4296278943351591468221005)
                    ·
                      refine ⟨1611104603756846800582877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4296278943351591468221005 1611104603756846800582877)
                      ·
                        rfl

theorem cell23_3137615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_3137615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137615 prefixEnd_3137615 := by exact prefixLift 3137615
  have htrace : WordTrace (prefixWord ++ tailWord_3137615) baseStart_3137615 baseEnd_3137615 := by
    simpa [prefixWord, tailWord_3137615, baseEnd_3137615] using wordTrace_append hprefix tailTrace_3137615
  have hstable : (prefixWord ++ tailWord_3137615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137615).length < 2 ^ (prefixWord ++ tailWord_3137615).sum := by decide
  have hdescent : baseEnd_3137615 < baseStart_3137615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137625 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_3137625 : Nat := 118140960795 + 3137625 * 2 ^ 59
def prefixEnd_3137625 : Nat := 4983230072969 + 3 ^ 40 * 3137625 * 2
def baseEnd_3137625 : Nat := 1611109738563391761457831

theorem tailTrace_3137625 : CollatzResearch.WordTrace tailWord_3137625 prefixEnd_3137625 1611109738563391761457831 := by
  unfold tailWord_3137625
  simp only [CollatzResearch.WordTrace]
  refine ⟨114438585257927963532822329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76292390171951975688548219 114438585257927963532822329)
  ·
    refine ⟨85828938943445972649616747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114438585257927963532822329 85828938943445972649616747)
    ·
      refine ⟨128743408415168958974425121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85828938943445972649616747 128743408415168958974425121)
      ·
        refine ⟨96557556311376719230818841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128743408415168958974425121 96557556311376719230818841)
        ·
          refine ⟨72418167233532539423114131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96557556311376719230818841 72418167233532539423114131)
          ·
            refine ⟨108627250850298809134671197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72418167233532539423114131 108627250850298809134671197)
            ·
              refine ⟨40735219068862053425501699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108627250850298809134671197 40735219068862053425501699)
              ·
                refine ⟨61102828603293080138252549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40735219068862053425501699 61102828603293080138252549)
                ·
                  refine ⟨11456780363117452525922353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61102828603293080138252549 11456780363117452525922353)
                  ·
                    refine ⟨8592585272338089394441765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11456780363117452525922353 8592585272338089394441765)
                    ·
                      refine ⟨1611109738563391761457831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8592585272338089394441765 1611109738563391761457831)
                      ·
                        rfl

theorem cell23_3137625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_3137625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137625 prefixEnd_3137625 := by exact prefixLift 3137625
  have htrace : WordTrace (prefixWord ++ tailWord_3137625) baseStart_3137625 baseEnd_3137625 := by
    simpa [prefixWord, tailWord_3137625, baseEnd_3137625] using wordTrace_append hprefix tailTrace_3137625
  have hstable : (prefixWord ++ tailWord_3137625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137625).length < 2 ^ (prefixWord ++ tailWord_3137625).sum := by decide
  have hdescent : baseEnd_3137625 < baseStart_3137625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137635 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 7]
def baseStart_3137635 : Nat := 118140960795 + 3137635 * 2 ^ 59
def prefixEnd_3137635 : Nat := 4983230072969 + 3 ^ 40 * 3137635 * 2
def baseEnd_3137635 : Nat := 179012763707770746925865

theorem tailTrace_3137635 : CollatzResearch.WordTrace tailWord_3137635 prefixEnd_3137635 179012763707770746925865 := by
  unfold tailWord_3137635
  simp only [CollatzResearch.WordTrace]
  refine ⟨114438949987891735240686359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76292633325261156827124239 114438949987891735240686359)
  ·
    refine ⟨171658424981837602861029539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114438949987891735240686359 171658424981837602861029539)
    ·
      refine ⟨257487637472756404291544309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171658424981837602861029539 257487637472756404291544309)
      ·
        refine ⟨24139466013070912902332279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257487637472756404291544309 24139466013070912902332279)
        ·
          refine ⟨36209199019606369353498419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24139466013070912902332279 36209199019606369353498419)
          ·
            refine ⟨54313798529409554030247629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36209199019606369353498419 54313798529409554030247629)
            ·
              refine ⟨20367674448528582761342861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54313798529409554030247629 20367674448528582761342861)
              ·
                refine ⟨7637877918198218535503573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20367674448528582761342861 7637877918198218535503573)
                ·
                  refine ⟨179012763707770746925865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7637877918198218535503573 179012763707770746925865)
                  ·
                    rfl

theorem cell23_3137635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 7].length) (baseStart_3137635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137635 prefixEnd_3137635 := by exact prefixLift 3137635
  have htrace : WordTrace (prefixWord ++ tailWord_3137635) baseStart_3137635 baseEnd_3137635 := by
    simpa [prefixWord, tailWord_3137635, baseEnd_3137635] using wordTrace_append hprefix tailTrace_3137635
  have hstable : (prefixWord ++ tailWord_3137635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137635).length < 2 ^ (prefixWord ++ tailWord_3137635).sum := by decide
  have hdescent : baseEnd_3137635 < baseStart_3137635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137669 : List Nat := [1, 3, 1, 1, 5, 1, 3, 3, 5]
def baseStart_3137669 : Nat := 118140960795 + 3137669 * 2 ^ 59
def prefixEnd_3137669 : Nat := 4983230072969 + 3 ^ 40 * 3137669 * 2
def baseEnd_3137669 : Nat := 179014703523576621034181

theorem tailTrace_3137669 : CollatzResearch.WordTrace tailWord_3137669 prefixEnd_3137669 179014703523576621034181 := by
  unfold tailWord_3137669
  simp only [CollatzResearch.WordTrace]
  refine ⟨114440190069768559047424061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76293460046512372698282707 114440190069768559047424061)
  ·
    refine ⟨42915071276163209642784023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114440190069768559047424061 42915071276163209642784023)
    ·
      refine ⟨64372606914244814464176035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42915071276163209642784023 64372606914244814464176035)
      ·
        refine ⟨96558910371367221696264053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64372606914244814464176035 96558910371367221696264053)
        ·
          refine ⟨9052397847315677034024755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96558910371367221696264053 9052397847315677034024755)
          ·
            refine ⟨13578596770973515551037133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052397847315677034024755 13578596770973515551037133)
            ·
              refine ⟨5091973789115068331638925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13578596770973515551037133 5091973789115068331638925)
              ·
                refine ⟨1909490170918150624364597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5091973789115068331638925 1909490170918150624364597)
                ·
                  refine ⟨179014703523576621034181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1909490170918150624364597 179014703523576621034181)
                  ·
                    rfl

theorem cell23_3137669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_3137669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137669 prefixEnd_3137669 := by exact prefixLift 3137669
  have htrace : WordTrace (prefixWord ++ tailWord_3137669) baseStart_3137669 baseEnd_3137669 := by
    simpa [prefixWord, tailWord_3137669, baseEnd_3137669] using wordTrace_append hprefix tailTrace_3137669
  have hstable : (prefixWord ++ tailWord_3137669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137669).length < 2 ^ (prefixWord ++ tailWord_3137669).sum := by decide
  have hdescent : baseEnd_3137669 < baseStart_3137669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137692 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3137692 : Nat := 118140960795 + 3137692 * 2 ^ 59
def prefixEnd_3137692 : Nat := 4983230072969 + 3 ^ 40 * 3137692 * 2
def baseEnd_3137692 : Nat := 1611144141767242999320023

theorem tailTrace_3137692 : CollatzResearch.WordTrace tailWord_3137692 prefixEnd_3137692 1611144141767242999320023 := by
  unfold tailWord_3137692
  simp only [CollatzResearch.WordTrace]
  refine ⟨57220514474342616987755665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76294019299123489317007553 57220514474342616987755665)
  ·
    refine ⟨42915385855756962740816749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57220514474342616987755665 42915385855756962740816749)
    ·
      refine ⟨16093269695908861027806281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42915385855756962740816749 16093269695908861027806281)
      ·
        refine ⟨12069952271931645770854711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16093269695908861027806281 12069952271931645770854711)
        ·
          refine ⟨18104928407897468656282067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12069952271931645770854711 18104928407897468656282067)
          ·
            refine ⟨27157392611846202984423101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18104928407897468656282067 27157392611846202984423101)
            ·
              refine ⟨10184022229442326119158663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27157392611846202984423101 10184022229442326119158663)
              ·
                refine ⟨15276033344163489178737995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10184022229442326119158663 15276033344163489178737995)
                ·
                  refine ⟨22914050016245233768106993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15276033344163489178737995 22914050016245233768106993)
                  ·
                    refine ⟨17185537512183925326080245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22914050016245233768106993 17185537512183925326080245)
                    ·
                      refine ⟨1611144141767242999320023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17185537512183925326080245 1611144141767242999320023)
                      ·
                        rfl

theorem cell23_3137692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3137692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137692 prefixEnd_3137692 := by exact prefixLift 3137692
  have htrace : WordTrace (prefixWord ++ tailWord_3137692) baseStart_3137692 baseEnd_3137692 := by
    simpa [prefixWord, tailWord_3137692, baseEnd_3137692] using wordTrace_append hprefix tailTrace_3137692
  have hstable : (prefixWord ++ tailWord_3137692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137692).length < 2 ^ (prefixWord ++ tailWord_3137692).sum := by decide
  have hdescent : baseEnd_3137692 < baseStart_3137692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137715 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 6]
def baseStart_3137715 : Nat := 118140960795 + 3137715 * 2 ^ 59
def prefixEnd_3137715 : Nat := 4983230072969 + 3 ^ 40 * 3137715 * 2
def baseEnd_3137715 : Nat := 1611155951822296409332417

theorem tailTrace_3137715 : CollatzResearch.WordTrace tailWord_3137715 prefixEnd_3137715 1611155951822296409332417 := by
  unfold tailWord_3137715
  simp only [CollatzResearch.WordTrace]
  refine ⟨114441867827601908903598599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76294578551734605935732399 114441867827601908903598599)
  ·
    refine ⟨171662801741402863355397899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114441867827601908903598599 171662801741402863355397899)
    ·
      refine ⟨257494202612104295033096849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171662801741402863355397899 257494202612104295033096849)
      ·
        refine ⟨193120651959078221274822637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257494202612104295033096849 193120651959078221274822637)
        ·
          refine ⟨72420244484654332978058489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193120651959078221274822637 72420244484654332978058489)
          ·
            refine ⟨54315183363490749733543867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72420244484654332978058489 54315183363490749733543867)
            ·
              refine ⟨81472775045236124600315801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54315183363490749733543867 81472775045236124600315801)
              ·
                refine ⟨61104581283927093450236851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81472775045236124600315801 61104581283927093450236851)
                ·
                  refine ⟨91656871925890640175355277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61104581283927093450236851 91656871925890640175355277)
                  ·
                    refine ⟨34371326972208990065758229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91656871925890640175355277 34371326972208990065758229)
                    ·
                      refine ⟨1611155951822296409332417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34371326972208990065758229 1611155951822296409332417)
                      ·
                        rfl

theorem cell23_3137715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_3137715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137715 prefixEnd_3137715 := by exact prefixLift 3137715
  have htrace : WordTrace (prefixWord ++ tailWord_3137715) baseStart_3137715 baseEnd_3137715 := by
    simpa [prefixWord, tailWord_3137715, baseEnd_3137715] using wordTrace_append hprefix tailTrace_3137715
  have hstable : (prefixWord ++ tailWord_3137715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137715).length < 2 ^ (prefixWord ++ tailWord_3137715).sum := by decide
  have hdescent : baseEnd_3137715 < baseStart_3137715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137719 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_3137719 : Nat := 118140960795 + 3137719 * 2 ^ 59
def prefixEnd_3137719 : Nat := 4983230072969 + 3 ^ 40 * 3137719 * 2
def baseEnd_3137719 : Nat := 1611158005744914393682399

theorem tailTrace_3137719 : CollatzResearch.WordTrace tailWord_3137719 prefixEnd_3137719 1611158005744914393682399 := by
  unfold tailWord_3137719
  simp only [CollatzResearch.WordTrace]
  refine ⟨114442013719587417586744211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76294675813058278391162807 114442013719587417586744211)
  ·
    refine ⟨171663020579381126380116317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114442013719587417586744211 171663020579381126380116317)
    ·
      refine ⟨64373632717267922392543619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171663020579381126380116317 64373632717267922392543619)
      ·
        refine ⟨96560449075901883588815429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64373632717267922392543619 96560449075901883588815429)
        ·
          refine ⟨18105084201731603172902893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96560449075901883588815429 18105084201731603172902893)
          ·
            refine ⟨6789406575649351189838585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18105084201731603172902893 6789406575649351189838585)
            ·
              refine ⟨5092054931737013392378939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6789406575649351189838585 5092054931737013392378939)
              ·
                refine ⟨7638082397605520088568409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092054931737013392378939 7638082397605520088568409)
                ·
                  refine ⟨5728561798204140066426307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7638082397605520088568409 5728561798204140066426307)
                  ·
                    refine ⟨8592842697306210099639461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5728561798204140066426307 8592842697306210099639461)
                    ·
                      refine ⟨1611158005744914393682399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8592842697306210099639461 1611158005744914393682399)
                      ·
                        rfl

theorem cell23_3137719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_3137719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137719 prefixEnd_3137719 := by exact prefixLift 3137719
  have htrace : WordTrace (prefixWord ++ tailWord_3137719) baseStart_3137719 baseEnd_3137719 := by
    simpa [prefixWord, tailWord_3137719, baseEnd_3137719] using wordTrace_append hprefix tailTrace_3137719
  have hstable : (prefixWord ++ tailWord_3137719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137719).length < 2 ^ (prefixWord ++ tailWord_3137719).sum := by decide
  have hdescent : baseEnd_3137719 < baseStart_3137719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137722 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_3137722 : Nat := 118140960795 + 3137722 * 2 ^ 59
def prefixEnd_3137722 : Nat := 4983230072969 + 3 ^ 40 * 3137722 * 2
def baseEnd_3137722 : Nat := 1611159546186877881944885

theorem tailTrace_3137722 : CollatzResearch.WordTrace tailWord_3137722 prefixEnd_3137722 1611159546186877881944885 := by
  unfold tailWord_3137722
  simp only [CollatzResearch.WordTrace]
  refine ⟨28610530784644137274775855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76294748759051032732735613 28610530784644137274775855)
  ·
    refine ⟨42915796176966205912163783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28610530784644137274775855 42915796176966205912163783)
    ·
      refine ⟨64373694265449308868245675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42915796176966205912163783 64373694265449308868245675)
      ·
        refine ⟨96560541398173963302368513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64373694265449308868245675 96560541398173963302368513)
        ·
          refine ⟨72420406048630472476776385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96560541398173963302368513 72420406048630472476776385)
          ·
            refine ⟨54315304536472854357582289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72420406048630472476776385 54315304536472854357582289)
            ·
              refine ⟨40736478402354640768186717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54315304536472854357582289 40736478402354640768186717)
              ·
                refine ⟨15276179400882990288070019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40736478402354640768186717 15276179400882990288070019)
                ·
                  refine ⟨22914269101324485432105029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15276179400882990288070019 22914269101324485432105029)
                  ·
                    refine ⟨4296425456498341018519693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22914269101324485432105029 4296425456498341018519693)
                    ·
                      refine ⟨1611159546186877881944885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4296425456498341018519693 1611159546186877881944885)
                      ·
                        rfl

theorem cell23_3137722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_3137722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137722 prefixEnd_3137722 := by exact prefixLift 3137722
  have htrace : WordTrace (prefixWord ++ tailWord_3137722) baseStart_3137722 baseEnd_3137722 := by
    simpa [prefixWord, tailWord_3137722, baseEnd_3137722] using wordTrace_append hprefix tailTrace_3137722
  have hstable : (prefixWord ++ tailWord_3137722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137722).length < 2 ^ (prefixWord ++ tailWord_3137722).sum := by decide
  have hdescent : baseEnd_3137722 < baseStart_3137722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137755 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 2, 9]
def baseStart_3137755 : Nat := 118140960795 + 3137755 * 2 ^ 59
def prefixEnd_3137755 : Nat := 4983230072969 + 3 ^ 40 * 3137755 * 2
def baseEnd_3137755 : Nat := 537058830349492084277411

theorem tailTrace_3137755 : CollatzResearch.WordTrace tailWord_3137755 prefixEnd_3137755 537058830349492084277411 := by
  unfold tailWord_3137755
  simp only [CollatzResearch.WordTrace]
  refine ⟨114443326747456995735054719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76295551164971330490036479 114443326747456995735054719)
  ·
    refine ⟨171664990121185493602582079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114443326747456995735054719 171664990121185493602582079)
    ·
      refine ⟨257497485181778240403873119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171664990121185493602582079 257497485181778240403873119)
      ·
        refine ⟨386246227772667360605809679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257497485181778240403873119 386246227772667360605809679)
        ·
          refine ⟨579369341659001040908714519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386246227772667360605809679 579369341659001040908714519)
          ·
            refine ⟨869054012488501561363071779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579369341659001040908714519 869054012488501561363071779)
            ·
              refine ⟨1303581018732752342044607669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869054012488501561363071779 1303581018732752342044607669)
              ·
                refine ⟨122210720506195532066681969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1303581018732752342044607669 122210720506195532066681969)
                ·
                  refine ⟨91658040379646649050011477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122210720506195532066681969 91658040379646649050011477)
                  ·
                    refine ⟨537058830349492084277411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 91658040379646649050011477 537058830349492084277411)
                    ·
                      rfl

theorem cell23_3137755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 9].length) (baseStart_3137755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137755 prefixEnd_3137755 := by exact prefixLift 3137755
  have htrace : WordTrace (prefixWord ++ tailWord_3137755) baseStart_3137755 baseEnd_3137755 := by
    simpa [prefixWord, tailWord_3137755, baseEnd_3137755] using wordTrace_append hprefix tailTrace_3137755
  have hstable : (prefixWord ++ tailWord_3137755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137755).length < 2 ^ (prefixWord ++ tailWord_3137755).sum := by decide
  have hdescent : baseEnd_3137755 < baseStart_3137755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137769 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 3]
def baseStart_3137769 : Nat := 118140960795 + 3137769 * 2 ^ 59
def prefixEnd_3137769 : Nat := 4983230072969 + 3 ^ 40 * 3137769 * 2
def baseEnd_3137769 : Nat := 1611183679777639198057169

theorem tailTrace_3137769 : CollatzResearch.WordTrace tailWord_3137769 prefixEnd_3137769 1611183679777639198057169 := by
  unfold tailWord_3137769
  simp only [CollatzResearch.WordTrace]
  refine ⟨114443837369406276126064361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76295891579604184084042907 114443837369406276126064361)
  ·
    refine ⟨85832878027054707094548271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114443837369406276126064361 85832878027054707094548271)
    ·
      refine ⟨128749317040582060641822407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85832878027054707094548271 128749317040582060641822407)
      ·
        refine ⟨193123975560873090962733611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128749317040582060641822407 193123975560873090962733611)
        ·
          refine ⟨289685963341309636444100417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193123975560873090962733611 289685963341309636444100417)
          ·
            refine ⟨217264472505982227333075313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289685963341309636444100417 217264472505982227333075313)
            ·
              refine ⟨162948354379486670499806485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217264472505982227333075313 162948354379486670499806485)
              ·
                refine ⟨7638204111538437679678429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162948354379486670499806485 7638204111538437679678429)
                ·
                  refine ⟨2864326541826914129879411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7638204111538437679678429 2864326541826914129879411)
                  ·
                    refine ⟨4296489812740371194819117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2864326541826914129879411 4296489812740371194819117)
                    ·
                      refine ⟨1611183679777639198057169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4296489812740371194819117 1611183679777639198057169)
                      ·
                        rfl

theorem cell23_3137769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 3].length) (baseStart_3137769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137769 prefixEnd_3137769 := by exact prefixLift 3137769
  have htrace : WordTrace (prefixWord ++ tailWord_3137769) baseStart_3137769 baseEnd_3137769 := by
    simpa [prefixWord, tailWord_3137769, baseEnd_3137769] using wordTrace_append hprefix tailTrace_3137769
  have hstable : (prefixWord ++ tailWord_3137769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137769).length < 2 ^ (prefixWord ++ tailWord_3137769).sum := by decide
  have hdescent : baseEnd_3137769 < baseStart_3137769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137772 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_3137772 : Nat := 118140960795 + 3137772 * 2 ^ 59
def prefixEnd_3137772 : Nat := 4983230072969 + 3 ^ 40 * 3137772 * 2
def baseEnd_3137772 : Nat := 537061740073200895439885

theorem tailTrace_3137772 : CollatzResearch.WordTrace tailWord_3137772 prefixEnd_3137772 537061740073200895439885 := by
  unfold tailWord_3137772
  simp only [CollatzResearch.WordTrace]
  refine ⟨57221973394197703819211785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76295964525596938425615713 57221973394197703819211785)
  ·
    refine ⟨42916480045648277864408839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57221973394197703819211785 42916480045648277864408839)
    ·
      refine ⟨64374720068472416796613259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42916480045648277864408839 64374720068472416796613259)
      ·
        refine ⟨96562080102708625194919889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64374720068472416796613259 96562080102708625194919889)
        ·
          refine ⟨72421560077031468896189917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96562080102708625194919889 72421560077031468896189917)
          ·
            refine ⟨27158085028886800836071219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72421560077031468896189917 27158085028886800836071219)
            ·
              refine ⟨40737127543330201254106829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27158085028886800836071219 40737127543330201254106829)
              ·
                refine ⟨15276422828748825470290061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40737127543330201254106829 15276422828748825470290061)
                ·
                  refine ⟨5728658560780809551358773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15276422828748825470290061 5728658560780809551358773)
                  ·
                    refine ⟨537061740073200895439885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5728658560780809551358773 537061740073200895439885)
                    ·
                      rfl

theorem cell23_3137772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_3137772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137772 prefixEnd_3137772 := by exact prefixLift 3137772
  have htrace : WordTrace (prefixWord ++ tailWord_3137772) baseStart_3137772 baseEnd_3137772 := by
    simpa [prefixWord, tailWord_3137772, baseEnd_3137772] using wordTrace_append hprefix tailTrace_3137772
  have hstable : (prefixWord ++ tailWord_3137772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137772).length < 2 ^ (prefixWord ++ tailWord_3137772).sum := by decide
  have hdescent : baseEnd_3137772 < baseStart_3137772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137773 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3137773 : Nat := 118140960795 + 3137773 * 2 ^ 59
def prefixEnd_3137773 : Nat := 4983230072969 + 3 ^ 40 * 3137773 * 2
def baseEnd_3137773 : Nat := 1611185733700257182407151

theorem tailTrace_3137773 : CollatzResearch.WordTrace tailWord_3137773 prefixEnd_3137773 1611185733700257182407151 := by
  unfold tailWord_3137773
  simp only [CollatzResearch.WordTrace]
  refine ⟨114443983261391784809209973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76295988840927856539473315 114443983261391784809209973)
  ·
    refine ⟨10729123430755479825863435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114443983261391784809209973 10729123430755479825863435)
    ·
      refine ⟨16093685146133219738795153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10729123430755479825863435 16093685146133219738795153)
      ·
        refine ⟨12070263859599914804096365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16093685146133219738795153 12070263859599914804096365)
        ·
          refine ⟨4526348947349968051536137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12070263859599914804096365 4526348947349968051536137)
          ·
            refine ⟨3394761710512476038652103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4526348947349968051536137 3394761710512476038652103)
            ·
              refine ⟨5092142565768714057978155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394761710512476038652103 5092142565768714057978155)
              ·
                refine ⟨7638213848653071086967233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092142565768714057978155 7638213848653071086967233)
                ·
                  refine ⟨5728660386489803315225425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7638213848653071086967233 5728660386489803315225425)
                  ·
                    refine ⟨4296495289867352486419069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5728660386489803315225425 4296495289867352486419069)
                    ·
                      refine ⟨1611185733700257182407151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4296495289867352486419069 1611185733700257182407151)
                      ·
                        rfl

theorem cell23_3137773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3137773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137773 prefixEnd_3137773 := by exact prefixLift 3137773
  have htrace : WordTrace (prefixWord ++ tailWord_3137773) baseStart_3137773 baseEnd_3137773 := by
    simpa [prefixWord, tailWord_3137773, baseEnd_3137773] using wordTrace_append hprefix tailTrace_3137773
  have hstable : (prefixWord ++ tailWord_3137773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137773).length < 2 ^ (prefixWord ++ tailWord_3137773).sum := by decide
  have hdescent : baseEnd_3137773 < baseStart_3137773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137779 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 1, 5, 2]
def baseStart_3137779 : Nat := 118140960795 + 3137779 * 2 ^ 59
def prefixEnd_3137779 : Nat := 4983230072969 + 3 ^ 40 * 3137779 * 2
def baseEnd_3137779 : Nat := 1611188814584184158932123

theorem tailTrace_3137779 : CollatzResearch.WordTrace tailWord_3137779 prefixEnd_3137779 1611188814584184158932123 := by
  unfold tailWord_3137779
  simp only [CollatzResearch.WordTrace]
  refine ⟨114444202099370047833928391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76296134732913365222618927 114444202099370047833928391)
  ·
    refine ⟨171666303149055071750892587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114444202099370047833928391 171666303149055071750892587)
    ·
      refine ⟨257499454723582607626338881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171666303149055071750892587 257499454723582607626338881)
      ·
        refine ⟨193124591042686955719754161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257499454723582607626338881 193124591042686955719754161)
        ·
          refine ⟨144843443282015216789815621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193124591042686955719754161 144843443282015216789815621)
          ·
            refine ⟨27158145615377853148090429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144843443282015216789815621 27158145615377853148090429)
            ·
              refine ⟨10184304605766694930533911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27158145615377853148090429 10184304605766694930533911)
              ·
                refine ⟨15276456908650042395800867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10184304605766694930533911 15276456908650042395800867)
                ·
                  refine ⟨22914685362975063593701301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15276456908650042395800867 22914685362975063593701301)
                  ·
                    refine ⟨2148251752778912211909497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22914685362975063593701301 2148251752778912211909497)
                    ·
                      refine ⟨1611188814584184158932123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148251752778912211909497 1611188814584184158932123)
                      ·
                        rfl

theorem cell23_3137779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 5, 2].length) (baseStart_3137779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137779 prefixEnd_3137779 := by exact prefixLift 3137779
  have htrace : WordTrace (prefixWord ++ tailWord_3137779) baseStart_3137779 baseEnd_3137779 := by
    simpa [prefixWord, tailWord_3137779, baseEnd_3137779] using wordTrace_append hprefix tailTrace_3137779
  have hstable : (prefixWord ++ tailWord_3137779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137779).length < 2 ^ (prefixWord ++ tailWord_3137779).sum := by decide
  have hdescent : baseEnd_3137779 < baseStart_3137779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137802 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_3137802 : Nat := 118140960795 + 3137802 * 2 ^ 59
def prefixEnd_3137802 : Nat := 4983230072969 + 3 ^ 40 * 3137802 * 2
def baseEnd_3137802 : Nat := 537066874879745856314839

theorem tailTrace_3137802 : CollatzResearch.WordTrace tailWord_3137802 prefixEnd_3137802 537066874879745856314839 := by
  unfold tailWord_3137802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28611260244571680690503915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76296693985524481841343773 28611260244571680690503915)
  ·
    refine ⟨42916890366857521035755873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28611260244571680690503915 42916890366857521035755873)
    ·
      refine ⟨32187667775143140776816905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42916890366857521035755873 32187667775143140776816905)
      ·
        refine ⟨24140750831357355582612679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32187667775143140776816905 24140750831357355582612679)
        ·
          refine ⟨36211126247036033373919019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24140750831357355582612679 36211126247036033373919019)
          ·
            refine ⟨54316689370554050060878529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36211126247036033373919019 54316689370554050060878529)
            ·
              refine ⟨40737517027915537545658897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54316689370554050060878529 40737517027915537545658897)
              ·
                refine ⟨30553137770936653159244173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40737517027915537545658897 30553137770936653159244173)
                ·
                  refine ⟨11457426664101244934716565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30553137770936653159244173 11457426664101244934716565)
                  ·
                    refine ⟨537066874879745856314839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11457426664101244934716565 537066874879745856314839)
                    ·
                      rfl

theorem cell23_3137802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_3137802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137802 prefixEnd_3137802 := by exact prefixLift 3137802
  have htrace : WordTrace (prefixWord ++ tailWord_3137802) baseStart_3137802 baseEnd_3137802 := by
    simpa [prefixWord, tailWord_3137802, baseEnd_3137802] using wordTrace_append hprefix tailTrace_3137802
  have hstable : (prefixWord ++ tailWord_3137802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137802).length < 2 ^ (prefixWord ++ tailWord_3137802).sum := by decide
  have hdescent : baseEnd_3137802 < baseStart_3137802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137819 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 2, 4]
def baseStart_3137819 : Nat := 118140960795 + 3137819 * 2 ^ 59
def prefixEnd_3137819 : Nat := 4983230072969 + 3 ^ 40 * 3137819 * 2
def baseEnd_3137819 : Nat := 537069784603454667477313

theorem tailTrace_3137819 : CollatzResearch.WordTrace tailWord_3137819 prefixEnd_3137819 537069784603454667477313 := by
  unfold tailWord_3137819
  simp only [CollatzResearch.WordTrace]
  refine ⟨114445661019225134665384511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76297107346150089776923007 114445661019225134665384511)
  ·
    refine ⟨171668491528837701998076767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114445661019225134665384511 171668491528837701998076767)
    ·
      refine ⟨257502737293256552997115151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171668491528837701998076767 257502737293256552997115151)
      ·
        refine ⟨386254105939884829495672727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257502737293256552997115151 386254105939884829495672727)
        ·
          refine ⟨579381158909827244243509091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386254105939884829495672727 579381158909827244243509091)
          ·
            refine ⟨869071738364740866365263637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579381158909827244243509091 869071738364740866365263637)
            ·
              refine ⟨40737737735847228110871733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 869071738364740866365263637 40737737735847228110871733)
              ·
                refine ⟨3819162912735677635394225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40737737735847228110871733 3819162912735677635394225)
                ·
                  refine ⟨2864372184551758226545669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819162912735677635394225 2864372184551758226545669)
                  ·
                    refine ⟨537069784603454667477313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864372184551758226545669 537069784603454667477313)
                    ·
                      rfl

theorem cell23_3137819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 4].length) (baseStart_3137819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137819 prefixEnd_3137819 := by exact prefixLift 3137819
  have htrace : WordTrace (prefixWord ++ tailWord_3137819) baseStart_3137819 baseEnd_3137819 := by
    simpa [prefixWord, tailWord_3137819, baseEnd_3137819] using wordTrace_append hprefix tailTrace_3137819
  have hstable : (prefixWord ++ tailWord_3137819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137819).length < 2 ^ (prefixWord ++ tailWord_3137819).sum := by decide
  have hdescent : baseEnd_3137819 < baseStart_3137819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137826 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_3137826 : Nat := 118140960795 + 3137826 * 2 ^ 59
def prefixEnd_3137826 : Nat := 4983230072969 + 3 ^ 40 * 3137826 * 2
def baseEnd_3137826 : Nat := 1611212948174945475044407

theorem tailTrace_3137826 : CollatzResearch.WordTrace tailWord_3137826 prefixEnd_3137826 1611212948174945475044407 := by
  unfold tailWord_3137826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28611479082549943715222333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76297277553466516573926221 28611479082549943715222333)
  ·
    refine ⟨10729304655956228893208375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28611479082549943715222333 10729304655956228893208375)
    ·
      refine ⟨16093956983934343339812563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10729304655956228893208375 16093956983934343339812563)
      ·
        refine ⟨24140935475901515009718845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16093956983934343339812563 24140935475901515009718845)
        ·
          refine ⟨9052850803463068128644567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24140935475901515009718845 9052850803463068128644567)
          ·
            refine ⟨13579276205194602192966851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052850803463068128644567 13579276205194602192966851)
            ·
              refine ⟨20368914307791903289450277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13579276205194602192966851 20368914307791903289450277)
              ·
                refine ⟨3819171432710981866771927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20368914307791903289450277 3819171432710981866771927)
                ·
                  refine ⟨5728757149066472800157891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819171432710981866771927 5728757149066472800157891)
                  ·
                    refine ⟨8593135723599709200236837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5728757149066472800157891 8593135723599709200236837)
                    ·
                      refine ⟨1611212948174945475044407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8593135723599709200236837 1611212948174945475044407)
                      ·
                        rfl

theorem cell23_3137826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_3137826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137826 prefixEnd_3137826 := by exact prefixLift 3137826
  have htrace : WordTrace (prefixWord ++ tailWord_3137826) baseStart_3137826 baseEnd_3137826 := by
    simpa [prefixWord, tailWord_3137826, baseEnd_3137826] using wordTrace_append hprefix tailTrace_3137826
  have hstable : (prefixWord ++ tailWord_3137826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137826).length < 2 ^ (prefixWord ++ tailWord_3137826).sum := by decide
  have hdescent : baseEnd_3137826 < baseStart_3137826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137849 : List Nat := [1, 2, 1, 6, 1, 3, 9]
def baseStart_3137849 : Nat := 118140960795 + 3137849 * 2 ^ 59
def prefixEnd_3137849 : Nat := 4983230072969 + 3 ^ 40 * 3137849 * 2
def baseEnd_3137849 : Nat := 19891663681851838087121

theorem tailTrace_3137849 : CollatzResearch.WordTrace tailWord_3137849 prefixEnd_3137849 19891663681851838087121 := by
  unfold tailWord_3137849
  simp only [CollatzResearch.WordTrace]
  refine ⟨114446755209116449788976601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76297836806077633192651067 114446755209116449788976601)
  ·
    refine ⟨85835066406837337341732451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114446755209116449788976601 85835066406837337341732451)
    ·
      refine ⟨128752599610256006012598677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85835066406837337341732451 128752599610256006012598677)
      ·
        refine ⟨6035278106730750281840563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128752599610256006012598677 6035278106730750281840563)
        ·
          refine ⟨9052917160096125422760845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035278106730750281840563 9052917160096125422760845)
          ·
            refine ⟨3394843935036047033535317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9052917160096125422760845 3394843935036047033535317)
            ·
              refine ⟨19891663681851838087121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3394843935036047033535317 19891663681851838087121)
              ·
                rfl

theorem cell23_3137849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 9].length) (baseStart_3137849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137849 prefixEnd_3137849 := by exact prefixLift 3137849
  have htrace : WordTrace (prefixWord ++ tailWord_3137849) baseStart_3137849 baseEnd_3137849 := by
    simpa [prefixWord, tailWord_3137849, baseEnd_3137849] using wordTrace_append hprefix tailTrace_3137849
  have hstable : (prefixWord ++ tailWord_3137849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137849).length < 2 ^ (prefixWord ++ tailWord_3137849).sum := by decide
  have hdescent : baseEnd_3137849 < baseStart_3137849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137882 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_3137882 : Nat := 118140960795 + 3137882 * 2 ^ 59
def prefixEnd_3137882 : Nat := 4983230072969 + 3 ^ 40 * 3137882 * 2
def baseEnd_3137882 : Nat := 1611241703091597255944149

theorem tailTrace_3137882 : CollatzResearch.WordTrace tailWord_3137882 prefixEnd_3137882 1611241703091597255944149 := by
  unfold tailWord_3137882
  simp only [CollatzResearch.WordTrace]
  refine ⟨28611989704499224106231975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76298639211997930949951933 28611989704499224106231975)
  ·
    refine ⟨42917984556748836159347963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28611989704499224106231975 42917984556748836159347963)
    ·
      refine ⟨64376976835123254239021945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42917984556748836159347963 64376976835123254239021945)
      ·
        refine ⟨48282732626342440679266459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64376976835123254239021945 48282732626342440679266459)
        ·
          refine ⟨72424098939513661018899689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48282732626342440679266459 72424098939513661018899689)
          ·
            refine ⟨54318074204635245764174767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72424098939513661018899689 54318074204635245764174767)
            ·
              refine ⟨81477111306952868646262151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54318074204635245764174767 81477111306952868646262151)
              ·
                refine ⟨122215666960429302969393227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81477111306952868646262151 122215666960429302969393227)
                ·
                  refine ⟨183323500440643954454089841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122215666960429302969393227 183323500440643954454089841)
                  ·
                    refine ⟨137492625330482965840567381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183323500440643954454089841 137492625330482965840567381)
                    ·
                      refine ⟨1611241703091597255944149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 137492625330482965840567381 1611241703091597255944149)
                      ·
                        rfl

theorem cell23_3137882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_3137882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137882 prefixEnd_3137882 := by exact prefixLift 3137882
  have htrace : WordTrace (prefixWord ++ tailWord_3137882) baseStart_3137882 baseEnd_3137882 := by
    simpa [prefixWord, tailWord_3137882, baseEnd_3137882] using wordTrace_append hprefix tailTrace_3137882
  have hstable : (prefixWord ++ tailWord_3137882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137882).length < 2 ^ (prefixWord ++ tailWord_3137882).sum := by decide
  have hdescent : baseEnd_3137882 < baseStart_3137882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137929 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_3137929 : Nat := 118140960795 + 3137929 * 2 ^ 59
def prefixEnd_3137929 : Nat := 4983230072969 + 3 ^ 40 * 3137929 * 2
def baseEnd_3137929 : Nat := 1611265836682358572056433

theorem tailTrace_3137929 : CollatzResearch.WordTrace tailWord_3137929 prefixEnd_3137929 1611265836682358572056433 := by
  unfold tailWord_3137929
  simp only [CollatzResearch.WordTrace]
  refine ⟨114449673048826623451888841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76299782032551082301259227 114449673048826623451888841)
  ·
    refine ⟨85837254786619967588916631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114449673048826623451888841 85837254786619967588916631)
    ·
      refine ⟨128755882179929951383374947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85837254786619967588916631 128755882179929951383374947)
      ·
        refine ⟨193133823269894927075062421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128755882179929951383374947 193133823269894927075062421)
        ·
          refine ⟨9053147965776324706643551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193133823269894927075062421 9053147965776324706643551)
          ·
            refine ⟨13579721948664487059965327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9053147965776324706643551 13579721948664487059965327)
            ·
              refine ⟨20369582922996730589947991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13579721948664487059965327 20369582922996730589947991)
              ·
                refine ⟨30554374384495095884921987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20369582922996730589947991 30554374384495095884921987)
                ·
                  refine ⟨45831561576742643827382981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30554374384495095884921987 45831561576742643827382981)
                  ·
                    refine ⟨8593417795639245717634309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45831561576742643827382981 8593417795639245717634309)
                    ·
                      refine ⟨1611265836682358572056433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8593417795639245717634309 1611265836682358572056433)
                      ·
                        rfl

theorem cell23_3137929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_3137929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137929 prefixEnd_3137929 := by exact prefixLift 3137929
  have htrace : WordTrace (prefixWord ++ tailWord_3137929) baseStart_3137929 baseEnd_3137929 := by
    simpa [prefixWord, tailWord_3137929, baseEnd_3137929] using wordTrace_append hprefix tailTrace_3137929
  have hstable : (prefixWord ++ tailWord_3137929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137929).length < 2 ^ (prefixWord ++ tailWord_3137929).sum := by decide
  have hdescent : baseEnd_3137929 < baseStart_3137929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137950 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3137950 : Nat := 118140960795 + 3137950 * 2 ^ 59
def prefixEnd_3137950 : Nat := 4983230072969 + 3 ^ 40 * 3137950 * 2
def baseEnd_3137950 : Nat := 1611276619776102989893837

theorem tailTrace_3137950 : CollatzResearch.WordTrace tailWord_3137950 prefixEnd_3137950 1611276619776102989893837 := by
  unfold tailWord_3137950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14306304872718818004800413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76300292654500362692268869 14306304872718818004800413)
  ·
    refine ⟨5364864327269556751800155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14306304872718818004800413 5364864327269556751800155)
    ·
      refine ⟨8047296490904335127700233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5364864327269556751800155 8047296490904335127700233)
      ·
        refine ⟨6035472368178251345775175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8047296490904335127700233 6035472368178251345775175)
        ·
          refine ⟨9053208552267377018662763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035472368178251345775175 9053208552267377018662763)
          ·
            refine ⟨13579812828401065527994145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9053208552267377018662763 13579812828401065527994145)
            ·
              refine ⟨10184859621300799145995609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13579812828401065527994145 10184859621300799145995609)
              ·
                refine ⟨7638644715975599359496707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10184859621300799145995609 7638644715975599359496707)
                ·
                  refine ⟨11457967073963399039245061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7638644715975599359496707 11457967073963399039245061)
                  ·
                    refine ⟨2148368826368137319858449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11457967073963399039245061 2148368826368137319858449)
                    ·
                      refine ⟨1611276619776102989893837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148368826368137319858449 1611276619776102989893837)
                      ·
                        rfl

theorem cell23_3137950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3137950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137950 prefixEnd_3137950 := by exact prefixLift 3137950
  have htrace : WordTrace (prefixWord ++ tailWord_3137950) baseStart_3137950 baseEnd_3137950 := by
    simpa [prefixWord, tailWord_3137950, baseEnd_3137950] using wordTrace_append hprefix tailTrace_3137950
  have hstable : (prefixWord ++ tailWord_3137950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137950).length < 2 ^ (prefixWord ++ tailWord_3137950).sum := by decide
  have hdescent : baseEnd_3137950 < baseStart_3137950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3137956 : List Nat := [2, 3, 1, 2, 1, 1, 3, 5, 5]
def baseStart_3137956 : Nat := 118140960795 + 3137956 * 2 ^ 59
def prefixEnd_3137956 : Nat := 4983230072969 + 3 ^ 40 * 3137956 * 2
def baseEnd_3137956 : Nat := 179031077851114440713201

theorem tailTrace_3137956 : CollatzResearch.WordTrace tailWord_3137956 prefixEnd_3137956 179031077851114440713201 := by
  unfold tailWord_3137956
  simp only [CollatzResearch.WordTrace]
  refine ⟨57225328909864403531560861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76300438546485871375414481 57225328909864403531560861)
  ·
    refine ⟨21459498341199151324335323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57225328909864403531560861 21459498341199151324335323)
    ·
      refine ⟨32189247511798726986502985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21459498341199151324335323 32189247511798726986502985)
      ·
        refine ⟨24141935633849045239877239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32189247511798726986502985 24141935633849045239877239)
        ·
          refine ⟨36212903450773567859815859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24141935633849045239877239 36212903450773567859815859)
          ·
            refine ⟨54319355176160351789723789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36212903450773567859815859 54319355176160351789723789)
            ·
              refine ⟨20369758191060131921146421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54319355176160351789723789 20369758191060131921146421)
              ·
                refine ⟨1909664830411887367607477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20369758191060131921146421 1909664830411887367607477)
                ·
                  refine ⟨179031077851114440713201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1909664830411887367607477 179031077851114440713201)
                  ·
                    rfl

theorem cell23_3137956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_3137956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3137956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3137956 prefixEnd_3137956 := by exact prefixLift 3137956
  have htrace : WordTrace (prefixWord ++ tailWord_3137956) baseStart_3137956 baseEnd_3137956 := by
    simpa [prefixWord, tailWord_3137956, baseEnd_3137956] using wordTrace_append hprefix tailTrace_3137956
  have hstable : (prefixWord ++ tailWord_3137956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3137956).length < 2 ^ (prefixWord ++ tailWord_3137956).sum := by decide
  have hdescent : baseEnd_3137956 < baseStart_3137956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3137956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138096 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_3138096 : Nat := 118140960795 + 3138096 * 2 ^ 59
def prefixEnd_3138096 : Nat := 4983230072969 + 3 ^ 40 * 3138096 * 2
def baseEnd_3138096 : Nat := 1611351587951659418668165

theorem tailTrace_3138096 : CollatzResearch.WordTrace tailWord_3138096 prefixEnd_3138096 1611351587951659418668165 := by
  unfold tailWord_3138096
  simp only [CollatzResearch.WordTrace]
  refine ⟨57227882019610805486609071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76303842692814407315478761 57227882019610805486609071)
  ·
    refine ⟨85841823029416208229913607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57227882019610805486609071 85841823029416208229913607)
    ·
      refine ⟨128762734544124312344870411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85841823029416208229913607 128762734544124312344870411)
      ·
        refine ⟨193144101816186468517305617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128762734544124312344870411 193144101816186468517305617)
        ·
          refine ⟨144858076362139851387979213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193144101816186468517305617 144858076362139851387979213)
          ·
            refine ⟨54321778635802444270492205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144858076362139851387979213 54321778635802444270492205)
            ·
              refine ⟨20370666988425916601434577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54321778635802444270492205 20370666988425916601434577)
              ·
                refine ⟨15278000241319437451075933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20370666988425916601434577 15278000241319437451075933)
                ·
                  refine ⟨5729250090494789044153475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15278000241319437451075933 5729250090494789044153475)
                  ·
                    refine ⟨8593875135742183566230213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5729250090494789044153475 8593875135742183566230213)
                    ·
                      refine ⟨1611351587951659418668165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8593875135742183566230213 1611351587951659418668165)
                      ·
                        rfl

theorem cell23_3138096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_3138096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138096 prefixEnd_3138096 := by exact prefixLift 3138096
  have htrace : WordTrace (prefixWord ++ tailWord_3138096) baseStart_3138096 baseEnd_3138096 := by
    simpa [prefixWord, tailWord_3138096, baseEnd_3138096] using wordTrace_append hprefix tailTrace_3138096
  have hstable : (prefixWord ++ tailWord_3138096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138096).length < 2 ^ (prefixWord ++ tailWord_3138096).sum := by decide
  have hdescent : baseEnd_3138096 < baseStart_3138096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138106 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_3138106 : Nat := 118140960795 + 3138106 * 2 ^ 59
def prefixEnd_3138106 : Nat := 4983230072969 + 3 ^ 40 * 3138106 * 2
def baseEnd_3138106 : Nat := 537118907586068126514373

theorem tailTrace_3138106 : CollatzResearch.WordTrace tailWord_3138106 prefixEnd_3138106 537118907586068126514373 := by
  unfold tailWord_3138106
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614032192296345670270543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76304085846123588454054781 28614032192296345670270543)
  ·
    refine ⟨42921048288444518505405815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28614032192296345670270543 42921048288444518505405815)
    ·
      refine ⟨64381572432666777758108723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42921048288444518505405815 64381572432666777758108723)
      ·
        refine ⟨96572358649000166637163085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64381572432666777758108723 96572358649000166637163085)
        ·
          refine ⟨36214634493375062488936157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96572358649000166637163085 36214634493375062488936157)
          ·
            refine ⟨13580487935015648433351059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36214634493375062488936157 13580487935015648433351059)
            ·
              refine ⟨20370731902523472650026589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13580487935015648433351059 20370731902523472650026589)
              ·
                refine ⟨7639024463446302243759971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20370731902523472650026589 7639024463446302243759971)
                ·
                  refine ⟨11458536695169453365639957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7639024463446302243759971 11458536695169453365639957)
                  ·
                    refine ⟨537118907586068126514373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11458536695169453365639957 537118907586068126514373)
                    ·
                      rfl

theorem cell23_3138106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_3138106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138106 prefixEnd_3138106 := by exact prefixLift 3138106
  have htrace : WordTrace (prefixWord ++ tailWord_3138106) baseStart_3138106 baseEnd_3138106 := by
    simpa [prefixWord, tailWord_3138106, baseEnd_3138106] using wordTrace_append hprefix tailTrace_3138106
  have hstable : (prefixWord ++ tailWord_3138106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138106).length < 2 ^ (prefixWord ++ tailWord_3138106).sum := by decide
  have hdescent : baseEnd_3138106 < baseStart_3138106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138113 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3138113 : Nat := 118140960795 + 3138113 * 2 ^ 59
def prefixEnd_3138113 : Nat := 4983230072969 + 3 ^ 40 * 3138113 * 2
def baseEnd_3138113 : Nat := 1611360317122785852155587

theorem tailTrace_3138113 : CollatzResearch.WordTrace tailWord_3138113 prefixEnd_3138113 1611360317122785852155587 := by
  unfold tailWord_3138113
  simp only [CollatzResearch.WordTrace]
  refine ⟨114456384080160022876586993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76304256053440015251057995 114456384080160022876586993)
  ·
    refine ⟨85842288060120017157440245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114456384080160022876586993 85842288060120017157440245)
    ·
      refine ⟨8047714505636251608510023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85842288060120017157440245 8047714505636251608510023)
      ·
        refine ⟨12071571758454377412765035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8047714505636251608510023 12071571758454377412765035)
        ·
          refine ⟨18107357637681566119147553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12071571758454377412765035 18107357637681566119147553)
          ·
            refine ⟨13580518228261174589360665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18107357637681566119147553 13580518228261174589360665)
            ·
              refine ⟨10185388671195880942020499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13580518228261174589360665 10185388671195880942020499)
              ·
                refine ⟨15278083006793821413030749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10185388671195880942020499 15278083006793821413030749)
                ·
                  refine ⟨5729281127547683029886531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15278083006793821413030749 5729281127547683029886531)
                  ·
                    refine ⟨8593921691321524544829797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5729281127547683029886531 8593921691321524544829797)
                    ·
                      refine ⟨1611360317122785852155587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8593921691321524544829797 1611360317122785852155587)
                      ·
                        rfl

theorem cell23_3138113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3138113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138113 prefixEnd_3138113 := by exact prefixLift 3138113
  have htrace : WordTrace (prefixWord ++ tailWord_3138113) baseStart_3138113 baseEnd_3138113 := by
    simpa [prefixWord, tailWord_3138113, baseEnd_3138113] using wordTrace_append hprefix tailTrace_3138113
  have hstable : (prefixWord ++ tailWord_3138113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138113).length < 2 ^ (prefixWord ++ tailWord_3138113).sum := by decide
  have hdescent : baseEnd_3138113 < baseStart_3138113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138130 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_3138130 : Nat := 118140960795 + 3138130 * 2 ^ 59
def prefixEnd_3138130 : Nat := 4983230072969 + 3 ^ 40 * 3138130 * 2
def baseEnd_3138130 : Nat := 1611369046293912285643009

theorem tailTrace_3138130 : CollatzResearch.WordTrace tailWord_3138130 prefixEnd_3138130 1611369046293912285643009 := by
  unfold tailWord_3138130
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614251030274608694988961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76304669414065623186637229 28614251030274608694988961)
  ·
    refine ⟨21460688272705956521241721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28614251030274608694988961 21460688272705956521241721)
    ·
      refine ⟨16095516204529467390931291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21460688272705956521241721 16095516204529467390931291)
      ·
        refine ⟨24143274306794201086396937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16095516204529467390931291 24143274306794201086396937)
        ·
          refine ⟨18107455730095650814797703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24143274306794201086396937 18107455730095650814797703)
          ·
            refine ⟨27161183595143476222196555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18107455730095650814797703 27161183595143476222196555)
            ·
              refine ⟨40741775392715214333294833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27161183595143476222196555 40741775392715214333294833)
              ·
                refine ⟨30556331544536410749971125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40741775392715214333294833 30556331544536410749971125)
                ·
                  refine ⟨2864656082300288507809793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30556331544536410749971125 2864656082300288507809793)
                  ·
                    refine ⟨2148492061725216380857345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2864656082300288507809793 2148492061725216380857345)
                    ·
                      refine ⟨1611369046293912285643009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148492061725216380857345 1611369046293912285643009)
                      ·
                        rfl

theorem cell23_3138130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_3138130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138130 prefixEnd_3138130 := by exact prefixLift 3138130
  have htrace : WordTrace (prefixWord ++ tailWord_3138130) baseStart_3138130 baseEnd_3138130 := by
    simpa [prefixWord, tailWord_3138130, baseEnd_3138130] using wordTrace_append hprefix tailTrace_3138130
  have hstable : (prefixWord ++ tailWord_3138130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138130).length < 2 ^ (prefixWord ++ tailWord_3138130).sum := by decide
  have hdescent : baseEnd_3138130 < baseStart_3138130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138140 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3138140 : Nat := 118140960795 + 3138140 * 2 ^ 59
def prefixEnd_3138140 : Nat := 4983230072969 + 3 ^ 40 * 3138140 * 2
def baseEnd_3138140 : Nat := 537124727033485748839321

theorem tailTrace_3138140 : CollatzResearch.WordTrace tailWord_3138140 prefixEnd_3138140 537124727033485748839321 := by
  unfold tailWord_3138140
  simp only [CollatzResearch.WordTrace]
  refine ⟨57228684425531103243909937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76304912567374804325213249 57228684425531103243909937)
  ·
    refine ⟨42921513319148327432932453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57228684425531103243909937 42921513319148327432932453)
    ·
      refine ⟨8047783747340311393674835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42921513319148327432932453 8047783747340311393674835)
      ·
        refine ⟨12071675621010467090512253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8047783747340311393674835 12071675621010467090512253)
        ·
          refine ⟨4526878357878925158942095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12071675621010467090512253 4526878357878925158942095)
          ·
            refine ⟨6790317536818387738413143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526878357878925158942095 6790317536818387738413143)
            ·
              refine ⟨10185476305227581607619715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6790317536818387738413143 10185476305227581607619715)
              ·
                refine ⟨15278214457841372411429573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10185476305227581607619715 15278214457841372411429573)
                ·
                  refine ⟨2864665210845257327143045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15278214457841372411429573 2864665210845257327143045)
                  ·
                    refine ⟨537124727033485748839321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864665210845257327143045 537124727033485748839321)
                    ·
                      rfl

theorem cell23_3138140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3138140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138140 prefixEnd_3138140 := by exact prefixLift 3138140
  have htrace : WordTrace (prefixWord ++ tailWord_3138140) baseStart_3138140 baseEnd_3138140 := by
    simpa [prefixWord, tailWord_3138140, baseEnd_3138140] using wordTrace_append hprefix tailTrace_3138140
  have hstable : (prefixWord ++ tailWord_3138140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138140).length < 2 ^ (prefixWord ++ tailWord_3138140).sum := by decide
  have hdescent : baseEnd_3138140 < baseStart_3138140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138147 : List Nat := [1, 1, 1, 5, 1, 2, 1, 6, 1, 2, 2]
def baseStart_3138147 : Nat := 118140960795 + 3138147 * 2 ^ 59
def prefixEnd_3138147 : Nat := 4983230072969 + 3 ^ 40 * 3138147 * 2
def baseEnd_3138147 : Nat := 1611377775465038719130431

theorem tailTrace_3138147 : CollatzResearch.WordTrace tailWord_3138147 prefixEnd_3138147 1611377775465038719130431 := by
  unfold tailWord_3138147
  simp only [CollatzResearch.WordTrace]
  refine ⟨114457624162036846683324695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76305082774691231122216463 114457624162036846683324695)
  ·
    refine ⟨171686436243055270024987043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114457624162036846683324695 171686436243055270024987043)
    ·
      refine ⟨257529654364582905037480565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171686436243055270024987043 257529654364582905037480565)
      ·
        refine ⟨24143405096679647347263803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257529654364582905037480565 24143405096679647347263803)
        ·
          refine ⟨36215107645019471020895705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24143405096679647347263803 36215107645019471020895705)
          ·
            refine ⟨27161330733764603265671779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36215107645019471020895705 27161330733764603265671779)
            ·
              refine ⟨40741996100646904898507669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27161330733764603265671779 40741996100646904898507669)
              ·
                refine ⟨1909781067217823667117547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40741996100646904898507669 1909781067217823667117547)
                ·
                  refine ⟨2864671600826735500676321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909781067217823667117547 2864671600826735500676321)
                  ·
                    refine ⟨2148503700620051625507241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2864671600826735500676321 2148503700620051625507241)
                    ·
                      refine ⟨1611377775465038719130431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148503700620051625507241 1611377775465038719130431)
                      ·
                        rfl

theorem cell23_3138147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_3138147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138147 prefixEnd_3138147 := by exact prefixLift 3138147
  have htrace : WordTrace (prefixWord ++ tailWord_3138147) baseStart_3138147 baseEnd_3138147 := by
    simpa [prefixWord, tailWord_3138147, baseEnd_3138147] using wordTrace_append hprefix tailTrace_3138147
  have hstable : (prefixWord ++ tailWord_3138147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138147).length < 2 ^ (prefixWord ++ tailWord_3138147).sum := by decide
  have hdescent : baseEnd_3138147 < baseStart_3138147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138157 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_3138157 : Nat := 118140960795 + 3138157 * 2 ^ 59
def prefixEnd_3138157 : Nat := 4983230072969 + 3 ^ 40 * 3138157 * 2
def baseEnd_3138157 : Nat := 537127636757194560001795

theorem tailTrace_3138157 : CollatzResearch.WordTrace tailWord_3138157 prefixEnd_3138157 537127636757194560001795 := by
  unfold tailWord_3138157
  simp only [CollatzResearch.WordTrace]
  refine ⟨114457988892000618391188725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76305325928000412260792483 114457988892000618391188725)
  ·
    refine ⟨10730436458625057974173943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114457988892000618391188725 10730436458625057974173943)
    ·
      refine ⟨16095654687937586961260915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10730436458625057974173943 16095654687937586961260915)
      ·
        refine ⟨24143482031906380441891373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16095654687937586961260915 24143482031906380441891373)
        ·
          refine ⟨9053805761964892665709265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24143482031906380441891373 9053805761964892665709265)
          ·
            refine ⟨6790354321473669499281949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9053805761964892665709265 6790354321473669499281949)
            ·
              refine ⟨2546382870552626062230731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6790354321473669499281949 2546382870552626062230731)
              ·
                refine ⟨3819574305828939093346097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546382870552626062230731 3819574305828939093346097)
                ·
                  refine ⟨2864680729371704320009573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819574305828939093346097 2864680729371704320009573)
                  ·
                    refine ⟨537127636757194560001795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864680729371704320009573 537127636757194560001795)
                    ·
                      rfl

theorem cell23_3138157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_3138157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138157 prefixEnd_3138157 := by exact prefixLift 3138157
  have htrace : WordTrace (prefixWord ++ tailWord_3138157) baseStart_3138157 baseEnd_3138157 := by
    simpa [prefixWord, tailWord_3138157, baseEnd_3138157] using wordTrace_append hprefix tailTrace_3138157
  have hstable : (prefixWord ++ tailWord_3138157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138157).length < 2 ^ (prefixWord ++ tailWord_3138157).sum := by decide
  have hdescent : baseEnd_3138157 < baseStart_3138157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138160 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 4]
def baseStart_3138160 : Nat := 118140960795 + 3138160 * 2 ^ 59
def prefixEnd_3138160 : Nat := 4983230072969 + 3 ^ 40 * 3138160 * 2
def baseEnd_3138160 : Nat := 1611384450713547168267871

theorem tailTrace_3138160 : CollatzResearch.WordTrace tailWord_3138160 prefixEnd_3138160 1611384450713547168267871 := by
  unfold tailWord_3138160
  simp only [CollatzResearch.WordTrace]
  refine ⟨57229049155494874951773967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76305398873993166602365289 57229049155494874951773967)
  ·
    refine ⟨85843573733242312427660951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57229049155494874951773967 85843573733242312427660951)
    ·
      refine ⟨128765360599863468641491427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85843573733242312427660951 128765360599863468641491427)
      ·
        refine ⟨193148040899795202962237141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128765360599863468641491427 193148040899795202962237141)
        ·
          refine ⟨4526907208588950069427433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 193148040899795202962237141 4526907208588950069427433)
          ·
            refine ⟨3395180406441712552070575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4526907208588950069427433 3395180406441712552070575)
            ·
              refine ⟨5092770609662568828105863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395180406441712552070575 5092770609662568828105863)
              ·
                refine ⟨7639155914493853242158795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092770609662568828105863 7639155914493853242158795)
                ·
                  refine ⟨11458733871740779863238193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7639155914493853242158795 11458733871740779863238193)
                  ·
                    refine ⟨8594050403805584897428645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11458733871740779863238193 8594050403805584897428645)
                    ·
                      refine ⟨1611384450713547168267871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8594050403805584897428645 1611384450713547168267871)
                      ·
                        rfl

theorem cell23_3138160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 4].length) (baseStart_3138160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138160 prefixEnd_3138160 := by exact prefixLift 3138160
  have htrace : WordTrace (prefixWord ++ tailWord_3138160) baseStart_3138160 baseEnd_3138160 := by
    simpa [prefixWord, tailWord_3138160, baseEnd_3138160] using wordTrace_append hprefix tailTrace_3138160
  have hstable : (prefixWord ++ tailWord_3138160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138160).length < 2 ^ (prefixWord ++ tailWord_3138160).sum := by decide
  have hdescent : baseEnd_3138160 < baseStart_3138160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138176 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_3138176 : Nat := 118140960795 + 3138176 * 2 ^ 59
def prefixEnd_3138176 : Nat := 4983230072969 + 3 ^ 40 * 3138176 * 2
def baseEnd_3138176 : Nat := 1611392666404019105667797

theorem tailTrace_3138176 : CollatzResearch.WordTrace tailWord_3138176 prefixEnd_3138176 1611392666404019105667797 := by
  unfold tailWord_3138176
  simp only [CollatzResearch.WordTrace]
  refine ⟨57229340939465892318065191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76305787919287856424086921 57229340939465892318065191)
  ·
    refine ⟨85844011409198838477097787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57229340939465892318065191 85844011409198838477097787)
    ·
      refine ⟨128766017113798257715646681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85844011409198838477097787 128766017113798257715646681)
      ·
        refine ⟨96574512835348693286735011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128766017113798257715646681 96574512835348693286735011)
        ·
          refine ⟨144861769253023039930102517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96574512835348693286735011 144861769253023039930102517)
          ·
            refine ⟨13580790867470909993447111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144861769253023039930102517 13580790867470909993447111)
            ·
              refine ⟨20371186301206364990170667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13580790867470909993447111 20371186301206364990170667)
              ·
                refine ⟨30556779451809547485256001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20371186301206364990170667 30556779451809547485256001)
                ·
                  refine ⟨22917584588857160613942001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30556779451809547485256001 22917584588857160613942001)
                  ·
                    refine ⟨17188188441642870460456501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22917584588857160613942001 17188188441642870460456501)
                    ·
                      refine ⟨1611392666404019105667797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17188188441642870460456501 1611392666404019105667797)
                      ·
                        rfl

theorem cell23_3138176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_3138176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138176 prefixEnd_3138176 := by exact prefixLift 3138176
  have htrace : WordTrace (prefixWord ++ tailWord_3138176) baseStart_3138176 baseEnd_3138176 := by
    simpa [prefixWord, tailWord_3138176, baseEnd_3138176] using wordTrace_append hprefix tailTrace_3138176
  have hstable : (prefixWord ++ tailWord_3138176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138176).length < 2 ^ (prefixWord ++ tailWord_3138176).sum := by decide
  have hdescent : baseEnd_3138176 < baseStart_3138176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138180 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_3138180 : Nat := 118140960795 + 3138180 * 2 ^ 59
def prefixEnd_3138180 : Nat := 4983230072969 + 3 ^ 40 * 3138180 * 2
def baseEnd_3138180 : Nat := 1611394720326637090017779

theorem tailTrace_3138180 : CollatzResearch.WordTrace tailWord_3138180 prefixEnd_3138180 1611394720326637090017779 := by
  unfold tailWord_3138180
  simp only [CollatzResearch.WordTrace]
  refine ⟨57229413885458646659637997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76305885180611528879517329 57229413885458646659637997)
  ·
    refine ⟨21461030207046992497364249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57229413885458646659637997 21461030207046992497364249)
    ·
      refine ⟨16095772655285244373023187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21461030207046992497364249 16095772655285244373023187)
      ·
        refine ⟨24143658982927866559534781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16095772655285244373023187 24143658982927866559534781)
        ·
          refine ⟨9053872118597949959825543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24143658982927866559534781 9053872118597949959825543)
          ·
            refine ⟨13580808177896924939738315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9053872118597949959825543 13580808177896924939738315)
            ·
              refine ⟨20371212266845387409607473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13580808177896924939738315 20371212266845387409607473)
              ·
                refine ⟨15278409200134040557205605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20371212266845387409607473 15278409200134040557205605)
                ·
                  refine ⟨2864701725025132604476051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15278409200134040557205605 2864701725025132604476051)
                  ·
                    refine ⟨4297052587537698906714077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2864701725025132604476051 4297052587537698906714077)
                    ·
                      refine ⟨1611394720326637090017779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4297052587537698906714077 1611394720326637090017779)
                      ·
                        rfl

theorem cell23_3138180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_3138180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138180 prefixEnd_3138180 := by exact prefixLift 3138180
  have htrace : WordTrace (prefixWord ++ tailWord_3138180) baseStart_3138180 baseEnd_3138180 := by
    simpa [prefixWord, tailWord_3138180, baseEnd_3138180] using wordTrace_append hprefix tailTrace_3138180
  have hstable : (prefixWord ++ tailWord_3138180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138180).length < 2 ^ (prefixWord ++ tailWord_3138180).sum := by decide
  have hdescent : baseEnd_3138180 < baseStart_3138180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138226 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 9]
def baseStart_3138226 : Nat := 118140960795 + 3138226 * 2 ^ 59
def prefixEnd_3138226 : Nat := 4983230072969 + 3 ^ 40 * 3138226 * 2
def baseEnd_3138226 : Nat := 179046482270749323338063

theorem tailTrace_3138226 : CollatzResearch.WordTrace tailWord_3138226 prefixEnd_3138226 179046482270749323338063 := by
  unfold tailWord_3138226
  simp only [CollatzResearch.WordTrace]
  refine ⟨28615126382187660793862633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76307003685833762116967021 28615126382187660793862633)
  ·
    refine ⟨21461344786640745595396975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28615126382187660793862633 21461344786640745595396975)
    ·
      refine ⟨32192017179961118393095463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21461344786640745595396975 32192017179961118393095463)
      ·
        refine ⟨48288025769941677589643195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32192017179961118393095463 48288025769941677589643195)
        ·
          refine ⟨72432038654912516384464793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48288025769941677589643195 72432038654912516384464793)
          ·
            refine ⟨54324028991184387288348595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72432038654912516384464793 54324028991184387288348595)
            ·
              refine ⟨81486043486776580932522893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54324028991184387288348595 81486043486776580932522893)
              ·
                refine ⟨30557266307541217849696085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81486043486776580932522893 30557266307541217849696085)
                ·
                  refine ⟨179046482270749323338063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30557266307541217849696085 179046482270749323338063)
                  ·
                    rfl

theorem cell23_3138226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_3138226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138226 prefixEnd_3138226 := by exact prefixLift 3138226
  have htrace : WordTrace (prefixWord ++ tailWord_3138226) baseStart_3138226 baseEnd_3138226 := by
    simpa [prefixWord, tailWord_3138226, baseEnd_3138226] using wordTrace_append hprefix tailTrace_3138226
  have hstable : (prefixWord ++ tailWord_3138226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138226).length < 2 ^ (prefixWord ++ tailWord_3138226).sum := by decide
  have hdescent : baseEnd_3138226 < baseStart_3138226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138254 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_3138254 : Nat := 118140960795 + 3138254 * 2 ^ 59
def prefixEnd_3138254 : Nat := 4983230072969 + 3 ^ 40 * 3138254 * 2
def baseEnd_3138254 : Nat := 1611432717895069800492439

theorem tailTrace_3138254 : CollatzResearch.WordTrace tailWord_3138254 prefixEnd_3138254 1611432717895069800492439 := by
  unfold tailWord_3138254
  simp only [CollatzResearch.WordTrace]
  refine ⟨14307690846581150494683727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76307684515099469304979877 14307690846581150494683727)
  ·
    refine ⟨21461536269871725742025591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14307690846581150494683727 21461536269871725742025591)
    ·
      refine ⟨32192304404807588613038387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21461536269871725742025591 32192304404807588613038387)
      ·
        refine ⟨48288456607211382919557581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32192304404807588613038387 48288456607211382919557581)
        ·
          refine ⟨18108171227704268594834093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48288456607211382919557581 18108171227704268594834093)
          ·
            refine ⟨6790564210389100723062785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18108171227704268594834093 6790564210389100723062785)
            ·
              refine ⟨5092923157791825542297089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6790564210389100723062785 5092923157791825542297089)
              ·
                refine ⟨3819692368343869156722817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5092923157791825542297089 3819692368343869156722817)
                ·
                  refine ⟨2864769276257901867542113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819692368343869156722817 2864769276257901867542113)
                  ·
                    refine ⟨2148576957193426400656585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2864769276257901867542113 2148576957193426400656585)
                    ·
                      refine ⟨1611432717895069800492439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148576957193426400656585 1611432717895069800492439)
                      ·
                        rfl

theorem cell23_3138254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_3138254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138254 prefixEnd_3138254 := by exact prefixLift 3138254
  have htrace : WordTrace (prefixWord ++ tailWord_3138254) baseStart_3138254 baseEnd_3138254 := by
    simpa [prefixWord, tailWord_3138254, baseEnd_3138254] using wordTrace_append hprefix tailTrace_3138254
  have hstable : (prefixWord ++ tailWord_3138254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138254).length < 2 ^ (prefixWord ++ tailWord_3138254).sum := by decide
  have hdescent : baseEnd_3138254 < baseStart_3138254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138290 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_3138290 : Nat := 118140960795 + 3138290 * 2 ^ 59
def prefixEnd_3138290 : Nat := 4983230072969 + 3 ^ 40 * 3138290 * 2
def baseEnd_3138290 : Nat := 537150401066210553214091

theorem tailTrace_3138290 : CollatzResearch.WordTrace tailWord_3138290 prefixEnd_3138290 537150401066210553214091 := by
  unfold tailWord_3138290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28615709950129695526445081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76308559867012521403853549 28615709950129695526445081)
  ·
    refine ⟨21461782462597271644833811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28615709950129695526445081 21461782462597271644833811)
    ·
      refine ⟨32192673693895907467250717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21461782462597271644833811 32192673693895907467250717)
      ·
        refine ⟨12072252635210965300219019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32192673693895907467250717 12072252635210965300219019)
        ·
          refine ⟨18108378952816447950328529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12072252635210965300219019 18108378952816447950328529)
          ·
            refine ⟨13581284214612335962746397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18108378952816447950328529 13581284214612335962746397)
            ·
              refine ⟨5092981580479625986029899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13581284214612335962746397 5092981580479625986029899)
              ·
                refine ⟨7639472370719438979044849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092981580479625986029899 7639472370719438979044849)
                ·
                  refine ⟨5729604278039579234283637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7639472370719438979044849 5729604278039579234283637)
                  ·
                    refine ⟨537150401066210553214091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5729604278039579234283637 537150401066210553214091)
                    ·
                      rfl

theorem cell23_3138290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_3138290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138290 prefixEnd_3138290 := by exact prefixLift 3138290
  have htrace : WordTrace (prefixWord ++ tailWord_3138290) baseStart_3138290 baseEnd_3138290 := by
    simpa [prefixWord, tailWord_3138290, baseEnd_3138290] using wordTrace_append hprefix tailTrace_3138290
  have hstable : (prefixWord ++ tailWord_3138290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138290).length < 2 ^ (prefixWord ++ tailWord_3138290).sum := by decide
  have hdescent : baseEnd_3138290 < baseStart_3138290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138303 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 7, 4]
def baseStart_3138303 : Nat := 118140960795 + 3138303 * 2 ^ 59
def prefixEnd_3138303 : Nat := 4983230072969 + 3 ^ 40 * 3138303 * 2
def baseEnd_3138303 : Nat := 537152626149046702926571

theorem tailTrace_3138303 : CollatzResearch.WordTrace tailWord_3138303 prefixEnd_3138303 537152626149046702926571 := by
  unfold tailWord_3138303
  simp only [CollatzResearch.WordTrace]
  refine ⟨114463313949471685326003563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76308875966314456884002375 114463313949471685326003563)
  ·
    refine ⟨171694970924207527989005345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114463313949471685326003563 171694970924207527989005345)
    ·
      refine ⟨128771228193155645991754009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171694970924207527989005345 128771228193155645991754009)
      ·
        refine ⟨96578421144866734493815507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128771228193155645991754009 96578421144866734493815507)
        ·
          refine ⟨144867631717300101740723261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96578421144866734493815507 144867631717300101740723261)
          ·
            refine ⟨54325361893987538152771223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144867631717300101740723261 54325361893987538152771223)
            ·
              refine ⟨81488042840981307229156835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54325361893987538152771223 81488042840981307229156835)
              ·
                refine ⟨122232064261471960843735253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81488042840981307229156835 122232064261471960843735253)
                ·
                  refine ⟨2864814006128249082275045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 122232064261471960843735253 2864814006128249082275045)
                  ·
                    refine ⟨537152626149046702926571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2864814006128249082275045 537152626149046702926571)
                    ·
                      rfl

theorem cell23_3138303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 4].length) (baseStart_3138303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138303 prefixEnd_3138303 := by exact prefixLift 3138303
  have htrace : WordTrace (prefixWord ++ tailWord_3138303) baseStart_3138303 baseEnd_3138303 := by
    simpa [prefixWord, tailWord_3138303, baseEnd_3138303] using wordTrace_append hprefix tailTrace_3138303
  have hstable : (prefixWord ++ tailWord_3138303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138303).length < 2 ^ (prefixWord ++ tailWord_3138303).sum := by decide
  have hdescent : baseEnd_3138303 < baseStart_3138303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138350 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_3138350 : Nat := 118140960795 + 3138350 * 2 ^ 59
def prefixEnd_3138350 : Nat := 4983230072969 + 3 ^ 40 * 3138350 * 2
def baseEnd_3138350 : Nat := 179053556893100158321333

theorem tailTrace_3138350 : CollatzResearch.WordTrace tailWord_3138350 prefixEnd_3138350 179053556893100158321333 := by
  unfold tailWord_3138350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14308128522537676544120563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76310018786867608235309669 14308128522537676544120563)
  ·
    refine ⟨21462192783806514816180845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14308128522537676544120563 21462192783806514816180845)
    ·
      refine ⟨8048322293927443056067817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21462192783806514816180845 8048322293927443056067817)
      ·
        refine ⟨6036241720445582292050863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8048322293927443056067817 6036241720445582292050863)
        ·
          refine ⟨9054362580668373438076295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036241720445582292050863 9054362580668373438076295)
          ·
            refine ⟨13581543871002560157114443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9054362580668373438076295 13581543871002560157114443)
            ·
              refine ⟨20372315806503840235671665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13581543871002560157114443 20372315806503840235671665)
              ·
                refine ⟨15279236854877880176753749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20372315806503840235671665 15279236854877880176753749)
                ·
                  refine ⟨179053556893100158321333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15279236854877880176753749 179053556893100158321333)
                  ·
                    rfl

theorem cell23_3138350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_3138350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138350 prefixEnd_3138350 := by exact prefixLift 3138350
  have htrace : WordTrace (prefixWord ++ tailWord_3138350) baseStart_3138350 baseEnd_3138350 := by
    simpa [prefixWord, tailWord_3138350, baseEnd_3138350] using wordTrace_append hprefix tailTrace_3138350
  have hstable : (prefixWord ++ tailWord_3138350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138350).length < 2 ^ (prefixWord ++ tailWord_3138350).sum := by decide
  have hdescent : baseEnd_3138350 < baseStart_3138350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138377 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 3]
def baseStart_3138377 : Nat := 118140960795 + 3138377 * 2 ^ 59
def prefixEnd_3138377 : Nat := 4983230072969 + 3 ^ 40 * 3138377 * 2
def baseEnd_3138377 : Nat := 1611495876015572819254373

theorem tailTrace_3138377 : CollatzResearch.WordTrace tailWord_3138377 prefixEnd_3138377 1611495876015572819254373 := by
  unfold tailWord_3138377
  simp only [CollatzResearch.WordTrace]
  refine ⟨114466012951203595964197385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76310675300802397309464923 114466012951203595964197385)
  ·
    refine ⟨85849509713402696973148039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114466012951203595964197385 85849509713402696973148039)
    ·
      refine ⟨128774264570104045459722059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85849509713402696973148039 128774264570104045459722059)
      ·
        refine ⟨193161396855156068189583089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128774264570104045459722059 193161396855156068189583089)
        ·
          refine ⟨144871047641367051142187317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193161396855156068189583089 144871047641367051142187317)
          ·
            refine ⟨13581660716378161044580061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144871047641367051142187317 13581660716378161044580061)
            ·
              refine ⟨5093122768641810391717523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13581660716378161044580061 5093122768641810391717523)
              ·
                refine ⟨7639684152962715587576285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093122768641810391717523 7639684152962715587576285)
                ·
                  refine ⟨2864881557361018345341107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7639684152962715587576285 2864881557361018345341107)
                  ·
                    refine ⟨4297322336041527518011661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2864881557361018345341107 4297322336041527518011661)
                    ·
                      refine ⟨1611495876015572819254373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4297322336041527518011661 1611495876015572819254373)
                      ·
                        rfl

theorem cell23_3138377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 3].length) (baseStart_3138377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138377 prefixEnd_3138377 := by exact prefixLift 3138377
  have htrace : WordTrace (prefixWord ++ tailWord_3138377) baseStart_3138377 baseEnd_3138377 := by
    simpa [prefixWord, tailWord_3138377, baseEnd_3138377] using wordTrace_append hprefix tailTrace_3138377
  have hstable : (prefixWord ++ tailWord_3138377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138377).length < 2 ^ (prefixWord ++ tailWord_3138377).sum := by decide
  have hdescent : baseEnd_3138377 < baseStart_3138377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138400 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_3138400 : Nat := 118140960795 + 3138400 * 2 ^ 59
def prefixEnd_3138400 : Nat := 4983230072969 + 3 ^ 40 * 3138400 * 2
def baseEnd_3138400 : Nat := 1611507686070626229266767

theorem tailTrace_3138400 : CollatzResearch.WordTrace tailWord_3138400 prefixEnd_3138400 1611507686070626229266767 := by
  unfold tailWord_3138400
  simp only [CollatzResearch.WordTrace]
  refine ⟨57233425915060135446142327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76311234553413513928189769 57233425915060135446142327)
  ·
    refine ⟨85850138872590203169213491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57233425915060135446142327 85850138872590203169213491)
    ·
      refine ⟨128775208308885304753820237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85850138872590203169213491 128775208308885304753820237)
      ·
        refine ⟨48290703115831989282682589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128775208308885304753820237 48290703115831989282682589)
        ·
          refine ⟨18109013668436995981005971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48290703115831989282682589 18109013668436995981005971)
          ·
            refine ⟨27163520502655493971508957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18109013668436995981005971 27163520502655493971508957)
            ·
              refine ⟨10186320188495810239315859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27163520502655493971508957 10186320188495810239315859)
              ·
                refine ⟨15279480282743715358973789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10186320188495810239315859 15279480282743715358973789)
                ·
                  refine ⟨5729805106028893259615171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15279480282743715358973789 5729805106028893259615171)
                  ·
                    refine ⟨8594707659043339889422757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5729805106028893259615171 8594707659043339889422757)
                    ·
                      refine ⟨1611507686070626229266767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8594707659043339889422757 1611507686070626229266767)
                      ·
                        rfl

theorem cell23_3138400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_3138400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138400 prefixEnd_3138400 := by exact prefixLift 3138400
  have htrace : WordTrace (prefixWord ++ tailWord_3138400) baseStart_3138400 baseEnd_3138400 := by
    simpa [prefixWord, tailWord_3138400, baseEnd_3138400] using wordTrace_append hprefix tailTrace_3138400
  have hstable : (prefixWord ++ tailWord_3138400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138400).length < 2 ^ (prefixWord ++ tailWord_3138400).sum := by decide
  have hdescent : baseEnd_3138400 < baseStart_3138400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138404 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_3138404 : Nat := 118140960795 + 3138404 * 2 ^ 59
def prefixEnd_3138404 : Nat := 4983230072969 + 3 ^ 40 * 3138404 * 2
def baseEnd_3138404 : Nat := 1611509739993244213616749

theorem tailTrace_3138404 : CollatzResearch.WordTrace tailWord_3138404 prefixEnd_3138404 1611509739993244213616749 := by
  unfold tailWord_3138404
  simp only [CollatzResearch.WordTrace]
  refine ⟨57233498861052889787715133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76311331814737186383620177 57233498861052889787715133)
  ·
    refine ⟨21462562072894833670393175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57233498861052889787715133 21462562072894833670393175)
    ·
      refine ⟨32193843109342250505589763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21462562072894833670393175 32193843109342250505589763)
      ·
        refine ⟨48290764664013375758384645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32193843109342250505589763 48290764664013375758384645)
        ·
          refine ⟨9054518374502507954697121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48290764664013375758384645 9054518374502507954697121)
          ·
            refine ⟨6790888780876880966022841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9054518374502507954697121 6790888780876880966022841)
            ·
              refine ⟨5093166585657660724517131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6790888780876880966022841 5093166585657660724517131)
              ·
                refine ⟨7639749878486491086775697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093166585657660724517131 7639749878486491086775697)
                ·
                  refine ⟨5729812408864868315081773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7639749878486491086775697 5729812408864868315081773)
                  ·
                    refine ⟨2148679653324325618155665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5729812408864868315081773 2148679653324325618155665)
                    ·
                      refine ⟨1611509739993244213616749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148679653324325618155665 1611509739993244213616749)
                      ·
                        rfl

theorem cell23_3138404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_3138404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138404 prefixEnd_3138404 := by exact prefixLift 3138404
  have htrace : WordTrace (prefixWord ++ tailWord_3138404) baseStart_3138404 baseEnd_3138404 := by
    simpa [prefixWord, tailWord_3138404, baseEnd_3138404] using wordTrace_append hprefix tailTrace_3138404
  have hstable : (prefixWord ++ tailWord_3138404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138404).length < 2 ^ (prefixWord ++ tailWord_3138404).sum := by decide
  have hdescent : baseEnd_3138404 < baseStart_3138404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138440 : List Nat := [2, 1, 3, 3, 2, 1, 3, 8]
def baseStart_3138440 : Nat := 118140960795 + 3138440 * 2 ^ 59
def prefixEnd_3138440 : Nat := 4983230072969 + 3 ^ 40 * 3138440 * 2
def baseEnd_3138440 : Nat := 59686230566548373065429

theorem tailTrace_3138440 : CollatzResearch.WordTrace tailWord_3138440 prefixEnd_3138440 59686230566548373065429 := by
  unfold tailWord_3138440
  simp only [CollatzResearch.WordTrace]
  refine ⟨57234155374987678861870387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76312207166650238482493849 57234155374987678861870387)
  ·
    refine ⟨85851233062481518292805581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57234155374987678861870387 85851233062481518292805581)
    ·
      refine ⟨32194212398430569359802093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85851233062481518292805581 32194212398430569359802093)
      ·
        refine ⟨12072829649411463509925785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32194212398430569359802093 12072829649411463509925785)
        ·
          refine ⟨9054622237058597632444339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12072829649411463509925785 9054622237058597632444339)
          ·
            refine ⟨13581933355587896448666509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9054622237058597632444339 13581933355587896448666509)
            ·
              refine ⟨5093225008345461168249941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13581933355587896448666509 5093225008345461168249941)
              ·
                refine ⟨59686230566548373065429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5093225008345461168249941 59686230566548373065429)
                ·
                  rfl

theorem cell23_3138440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 8].length) (baseStart_3138440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138440 prefixEnd_3138440 := by exact prefixLift 3138440
  have htrace : WordTrace (prefixWord ++ tailWord_3138440) baseStart_3138440 baseEnd_3138440 := by
    simpa [prefixWord, tailWord_3138440, baseEnd_3138440] using wordTrace_append hprefix tailTrace_3138440
  have hstable : (prefixWord ++ tailWord_3138440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138440).length < 2 ^ (prefixWord ++ tailWord_3138440).sum := by decide
  have hdescent : baseEnd_3138440 < baseStart_3138440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138443 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 6]
def baseStart_3138443 : Nat := 118140960795 + 3138443 * 2 ^ 59
def prefixEnd_3138443 : Nat := 4983230072969 + 3 ^ 40 * 3138443 * 2
def baseEnd_3138443 : Nat := 1611529765738769561029069

theorem tailTrace_3138443 : CollatzResearch.WordTrace tailWord_3138443 prefixEnd_3138443 1611529765738769561029069 := by
  unfold tailWord_3138443
  simp only [CollatzResearch.WordTrace]
  refine ⟨114468420168964489236099983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76312280112642992824066655 114468420168964489236099983)
  ·
    refine ⟨171702630253446733854149975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114468420168964489236099983 171702630253446733854149975)
    ·
      refine ⟨257553945380170100781224963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171702630253446733854149975 257553945380170100781224963)
      ·
        refine ⟨386330918070255151171837445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257553945380170100781224963 386330918070255151171837445)
        ·
          refine ⟨72437047138172840844719521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386330918070255151171837445 72437047138172840844719521)
          ·
            refine ⟨54327785353629630633539641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72437047138172840844719521 54327785353629630633539641)
            ·
              refine ⟨40745839015222222975154731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54327785353629630633539641 40745839015222222975154731)
              ·
                refine ⟨61118758522833334462732097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40745839015222222975154731 61118758522833334462732097)
                ·
                  refine ⟨45839068892125000847049073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61118758522833334462732097 45839068892125000847049073)
                  ·
                    refine ⟨34379301669093750635286805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45839068892125000847049073 34379301669093750635286805)
                    ·
                      refine ⟨1611529765738769561029069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34379301669093750635286805 1611529765738769561029069)
                      ·
                        rfl

theorem cell23_3138443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_3138443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138443 prefixEnd_3138443 := by exact prefixLift 3138443
  have htrace : WordTrace (prefixWord ++ tailWord_3138443) baseStart_3138443 baseEnd_3138443 := by
    simpa [prefixWord, tailWord_3138443, baseEnd_3138443] using wordTrace_append hprefix tailTrace_3138443
  have hstable : (prefixWord ++ tailWord_3138443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138443).length < 2 ^ (prefixWord ++ tailWord_3138443).sum := by decide
  have hdescent : baseEnd_3138443 < baseStart_3138443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138527 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 5]
def baseStart_3138527 : Nat := 118140960795 + 3138527 * 2 ^ 59
def prefixEnd_3138527 : Nat := 4983230072969 + 3 ^ 40 * 3138527 * 2
def baseEnd_3138527 : Nat := 1611572898113747232378683

theorem tailTrace_3138527 : CollatzResearch.WordTrace tailWord_3138527 prefixEnd_3138527 1611572898113747232378683 := by
  unfold tailWord_3138527
  simp only [CollatzResearch.WordTrace]
  refine ⟨114471483900660171582157835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76314322600440114388105223 114471483900660171582157835)
  ·
    refine ⟨171707225850990257373236753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114471483900660171582157835 171707225850990257373236753)
    ·
      refine ⟨128780419388242693029927565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171707225850990257373236753 128780419388242693029927565)
      ·
        refine ⟨48292657270591009886222837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128780419388242693029927565 48292657270591009886222837)
        ·
          refine ⟨4527436619117907176833391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48292657270591009886222837 4527436619117907176833391)
          ·
            refine ⟨6791154928676860765250087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4527436619117907176833391 6791154928676860765250087)
            ·
              refine ⟨10186732393015291147875131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6791154928676860765250087 10186732393015291147875131)
              ·
                refine ⟨15280098589522936721812697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10186732393015291147875131 15280098589522936721812697)
                ·
                  refine ⟨11460073942142202541359523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15280098589522936721812697 11460073942142202541359523)
                  ·
                    refine ⟨17190110913213303812039285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11460073942142202541359523 17190110913213303812039285)
                    ·
                      refine ⟨1611572898113747232378683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17190110913213303812039285 1611572898113747232378683)
                      ·
                        rfl

theorem cell23_3138527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_3138527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138527 prefixEnd_3138527 := by exact prefixLift 3138527
  have htrace : WordTrace (prefixWord ++ tailWord_3138527) baseStart_3138527 baseEnd_3138527 := by
    simpa [prefixWord, tailWord_3138527, baseEnd_3138527] using wordTrace_append hprefix tailTrace_3138527
  have hstable : (prefixWord ++ tailWord_3138527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138527).length < 2 ^ (prefixWord ++ tailWord_3138527).sum := by decide
  have hdescent : baseEnd_3138527 < baseStart_3138527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138562 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3138562 : Nat := 118140960795 + 3138562 * 2 ^ 59
def prefixEnd_3138562 : Nat := 4983230072969 + 3 ^ 40 * 3138562 * 2
def baseEnd_3138562 : Nat := 1611590869936654595441023

theorem tailTrace_3138562 : CollatzResearch.WordTrace tailWord_3138562 prefixEnd_3138562 1611590869936654595441023 := by
  unfold tailWord_3138562
  simp only [CollatzResearch.WordTrace]
  refine ⟨28618190113883343139920485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76315173637022248373121293 28618190113883343139920485)
  ·
    refine ⟨5365910646353126838735091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28618190113883343139920485 5365910646353126838735091)
    ·
      refine ⟨8048865969529690258102637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5365910646353126838735091 8048865969529690258102637)
      ·
        refine ⟨3018324738573633846788489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8048865969529690258102637 3018324738573633846788489)
        ·
          refine ⟨2263743553930225385091367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3018324738573633846788489 2263743553930225385091367)
          ·
            refine ⟨3395615330895338077637051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263743553930225385091367 3395615330895338077637051)
            ·
              refine ⟨5093422996343007116455577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395615330895338077637051 5093422996343007116455577)
              ·
                refine ⟨3820067247257255337341683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093422996343007116455577 3820067247257255337341683)
                ·
                  refine ⟨5730100870885883006012525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820067247257255337341683 5730100870885883006012525)
                  ·
                    refine ⟨2148787826582206127254697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5730100870885883006012525 2148787826582206127254697)
                    ·
                      refine ⟨1611590869936654595441023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148787826582206127254697 1611590869936654595441023)
                      ·
                        rfl

theorem cell23_3138562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3138562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138562 prefixEnd_3138562 := by exact prefixLift 3138562
  have htrace : WordTrace (prefixWord ++ tailWord_3138562) baseStart_3138562 baseEnd_3138562 := by
    simpa [prefixWord, tailWord_3138562, baseEnd_3138562] using wordTrace_append hprefix tailTrace_3138562
  have hstable : (prefixWord ++ tailWord_3138562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138562).length < 2 ^ (prefixWord ++ tailWord_3138562).sum := by decide
  have hdescent : baseEnd_3138562 < baseStart_3138562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138597 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_3138597 : Nat := 118140960795 + 3138597 * 2 ^ 59
def prefixEnd_3138597 : Nat := 4983230072969 + 3 ^ 40 * 3138597 * 2
def baseEnd_3138597 : Nat := 1611608841759561958503361

theorem tailTrace_3138597 : CollatzResearch.WordTrace tailWord_3138597 prefixEnd_3138597 1611608841759561958503361 := by
  unfold tailWord_3138597
  simp only [CollatzResearch.WordTrace]
  refine ⟨114474037010406573537206045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76316024673604382358137363 114474037010406573537206045)
  ·
    refine ⟨42927763878902465076452267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114474037010406573537206045 42927763878902465076452267)
    ·
      refine ⟨64391645818353697614678401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42927763878902465076452267 64391645818353697614678401)
      ·
        refine ⟨48293734363765273211008801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64391645818353697614678401 48293734363765273211008801)
        ·
          refine ⟨36220300772823954908256601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48293734363765273211008801 36220300772823954908256601)
          ·
            refine ⟨27165225579617966181192451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36220300772823954908256601 27165225579617966181192451)
            ·
              refine ⟨40747838369426949271788677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27165225579617966181192451 40747838369426949271788677)
              ·
                refine ⟨7640219694267552988460377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40747838369426949271788677 7640219694267552988460377)
                ·
                  refine ⟨5730164770700664741345283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7640219694267552988460377 5730164770700664741345283)
                  ·
                    refine ⟨8595247156050997112017925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5730164770700664741345283 8595247156050997112017925)
                    ·
                      refine ⟨1611608841759561958503361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8595247156050997112017925 1611608841759561958503361)
                      ·
                        rfl

theorem cell23_3138597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_3138597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138597 prefixEnd_3138597 := by exact prefixLift 3138597
  have htrace : WordTrace (prefixWord ++ tailWord_3138597) baseStart_3138597 baseEnd_3138597 := by
    simpa [prefixWord, tailWord_3138597, baseEnd_3138597] using wordTrace_append hprefix tailTrace_3138597
  have hstable : (prefixWord ++ tailWord_3138597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138597).length < 2 ^ (prefixWord ++ tailWord_3138597).sum := by decide
  have hdescent : baseEnd_3138597 < baseStart_3138597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138634 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_3138634 : Nat := 118140960795 + 3138634 * 2 ^ 59
def prefixEnd_3138634 : Nat := 4983230072969 + 3 ^ 40 * 3138634 * 2
def baseEnd_3138634 : Nat := 1611627840543778313740691

theorem tailTrace_3138634 : CollatzResearch.WordTrace tailWord_3138634 prefixEnd_3138634 1611627840543778313740691 := by
  unfold tailWord_3138634
  simp only [CollatzResearch.WordTrace]
  refine ⟨28618846627818132214075739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76316924340848352570868637 28618846627818132214075739)
  ·
    refine ⟨42928269941727198321113609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28618846627818132214075739 42928269941727198321113609)
    ·
      refine ⟨32196202456295398740835207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42928269941727198321113609 32196202456295398740835207)
      ·
        refine ⟨48294303684443098111252811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32196202456295398740835207 48294303684443098111252811)
        ·
          refine ⟨72441455526664647166879217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48294303684443098111252811 72441455526664647166879217)
          ·
            refine ⟨54331091644998485375159413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72441455526664647166879217 54331091644998485375159413)
            ·
              refine ⟨5093539841718608003921195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54331091644998485375159413 5093539841718608003921195)
              ·
                refine ⟨7640309762577912005881793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093539841718608003921195 7640309762577912005881793)
                ·
                  refine ⟨5730232321933434004411345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7640309762577912005881793 5730232321933434004411345)
                  ·
                    refine ⟨4297674241450075503308509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5730232321933434004411345 4297674241450075503308509)
                    ·
                      refine ⟨1611627840543778313740691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4297674241450075503308509 1611627840543778313740691)
                      ·
                        rfl

theorem cell23_3138634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_3138634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138634 prefixEnd_3138634 := by exact prefixLift 3138634
  have htrace : WordTrace (prefixWord ++ tailWord_3138634) baseStart_3138634 baseEnd_3138634 := by
    simpa [prefixWord, tailWord_3138634, baseEnd_3138634] using wordTrace_append hprefix tailTrace_3138634
  have hstable : (prefixWord ++ tailWord_3138634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138634).length < 2 ^ (prefixWord ++ tailWord_3138634).sum := by decide
  have hdescent : baseEnd_3138634 < baseStart_3138634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138640 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_3138640 : Nat := 118140960795 + 3138640 * 2 ^ 59
def prefixEnd_3138640 : Nat := 4983230072969 + 3 ^ 40 * 3138640 * 2
def baseEnd_3138640 : Nat := 1611630921427705290265663

theorem tailTrace_3138640 : CollatzResearch.WordTrace tailWord_3138640 prefixEnd_3138640 1611630921427705290265663 := by
  unfold tailWord_3138640
  simp only [CollatzResearch.WordTrace]
  refine ⟨57237802674625395940510687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76317070232833861254014249 57237802674625395940510687)
  ·
    refine ⟨85856704011938093910766031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57237802674625395940510687 85856704011938093910766031)
    ·
      refine ⟨128785056017907140866149047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85856704011938093910766031 128785056017907140866149047)
      ·
        refine ⟨193177584026860711299223571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128785056017907140866149047 193177584026860711299223571)
        ·
          refine ⟨289766376040291066948835357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193177584026860711299223571 289766376040291066948835357)
          ·
            refine ⟨108662391015109150105813259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289766376040291066948835357 108662391015109150105813259)
            ·
              refine ⟨162993586522663725158719889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108662391015109150105813259 162993586522663725158719889)
              ·
                refine ⟨122245189891997793869039917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162993586522663725158719889 122245189891997793869039917)
                ·
                  refine ⟨45841946209499172700889969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122245189891997793869039917 45841946209499172700889969)
                  ·
                    refine ⟨34381459657124379525667477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45841946209499172700889969 34381459657124379525667477)
                    ·
                      refine ⟨1611630921427705290265663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34381459657124379525667477 1611630921427705290265663)
                      ·
                        rfl

theorem cell23_3138640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_3138640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138640 prefixEnd_3138640 := by exact prefixLift 3138640
  have htrace : WordTrace (prefixWord ++ tailWord_3138640) baseStart_3138640 baseEnd_3138640 := by
    simpa [prefixWord, tailWord_3138640, baseEnd_3138640] using wordTrace_append hprefix tailTrace_3138640
  have hstable : (prefixWord ++ tailWord_3138640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138640).length < 2 ^ (prefixWord ++ tailWord_3138640).sum := by decide
  have hdescent : baseEnd_3138640 < baseStart_3138640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138658 : List Nat := [3, 3, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3138658 : Nat := 118140960795 + 3138658 * 2 ^ 59
def prefixEnd_3138658 : Nat := 4983230072969 + 3 ^ 40 * 3138658 * 2
def baseEnd_3138658 : Nat := 537213388026495406613527

theorem tailTrace_3138658 : CollatzResearch.WordTrace tailWord_3138658 prefixEnd_3138658 537213388026495406613527 := by
  unfold tailWord_3138658
  simp only [CollatzResearch.WordTrace]
  refine ⟨28619065465796395238794157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76317507908790387303451085 28619065465796395238794157)
  ·
    refine ⟨10732149549673648214547809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28619065465796395238794157 10732149549673648214547809)
    ·
      refine ⟨8049112162255236160910857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10732149549673648214547809 8049112162255236160910857)
      ·
        refine ⟨6036834121691427120683143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8049112162255236160910857 6036834121691427120683143)
        ·
          refine ⟨9055251182537140681024715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036834121691427120683143 9055251182537140681024715)
          ·
            refine ⟨13582876773805711021537073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9055251182537140681024715 13582876773805711021537073)
            ·
              refine ⟨10187157580354283266152805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13582876773805711021537073 10187157580354283266152805)
              ·
                refine ⟨1910092046316428112403651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10187157580354283266152805 1910092046316428112403651)
                ·
                  refine ⟨2865138069474642168605477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910092046316428112403651 2865138069474642168605477)
                  ·
                    refine ⟨537213388026495406613527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2865138069474642168605477 537213388026495406613527)
                    ·
                      rfl

theorem cell23_3138658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3138658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138658 prefixEnd_3138658 := by exact prefixLift 3138658
  have htrace : WordTrace (prefixWord ++ tailWord_3138658) baseStart_3138658 baseEnd_3138658 := by
    simpa [prefixWord, tailWord_3138658, baseEnd_3138658] using wordTrace_append hprefix tailTrace_3138658
  have hstable : (prefixWord ++ tailWord_3138658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138658).length < 2 ^ (prefixWord ++ tailWord_3138658).sum := by decide
  have hdescent : baseEnd_3138658 < baseStart_3138658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138674 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_3138674 : Nat := 118140960795 + 3138674 * 2 ^ 59
def prefixEnd_3138674 : Nat := 4983230072969 + 3 ^ 40 * 3138674 * 2
def baseEnd_3138674 : Nat := 1611648379769958157240507

theorem tailTrace_3138674 : CollatzResearch.WordTrace tailWord_3138674 prefixEnd_3138674 1611648379769958157240507 := by
  unfold tailWord_3138674
  simp only [CollatzResearch.WordTrace]
  refine ⟨28619211357781903921939769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76317896954085077125172717 28619211357781903921939769)
  ·
    refine ⟨21464408518336427941454827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28619211357781903921939769 21464408518336427941454827)
    ·
      refine ⟨32196612777504641912182241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21464408518336427941454827 32196612777504641912182241)
      ·
        refine ⟨24147459583128481434136681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32196612777504641912182241 24147459583128481434136681)
        ·
          refine ⟨18110594687346361075602511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24147459583128481434136681 18110594687346361075602511)
          ·
            refine ⟨27165892031019541613403767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18110594687346361075602511 27165892031019541613403767)
            ·
              refine ⟨40748838046529312420105651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27165892031019541613403767 40748838046529312420105651)
              ·
                refine ⟨61123257069793968630158477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40748838046529312420105651 61123257069793968630158477)
                ·
                  refine ⟨22921221401172738236309429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61123257069793968630158477 22921221401172738236309429)
                  ·
                    refine ⟨2148864506359944209654009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22921221401172738236309429 2148864506359944209654009)
                    ·
                      refine ⟨1611648379769958157240507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148864506359944209654009 1611648379769958157240507)
                      ·
                        rfl

theorem cell23_3138674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_3138674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138674 prefixEnd_3138674 := by exact prefixLift 3138674
  have htrace : WordTrace (prefixWord ++ tailWord_3138674) baseStart_3138674 baseEnd_3138674 := by
    simpa [prefixWord, tailWord_3138674, baseEnd_3138674] using wordTrace_append hprefix tailTrace_3138674
  have hstable : (prefixWord ++ tailWord_3138674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138674).length < 2 ^ (prefixWord ++ tailWord_3138674).sum := by decide
  have hdescent : baseEnd_3138674 < baseStart_3138674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138684 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_3138684 : Nat := 118140960795 + 3138684 * 2 ^ 59
def prefixEnd_3138684 : Nat := 4983230072969 + 3 ^ 40 * 3138684 * 2
def baseEnd_3138684 : Nat := 537217838192167706038487

theorem tailTrace_3138684 : CollatzResearch.WordTrace tailWord_3138684 prefixEnd_3138684 537217838192167706038487 := by
  unfold tailWord_3138684
  simp only [CollatzResearch.WordTrace]
  refine ⟨57238605080545693697811553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76318140107394258263748737 57238605080545693697811553)
  ·
    refine ⟨42928953810409270273358665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57238605080545693697811553 42928953810409270273358665)
    ·
      refine ⟨32196715357806952705018999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42928953810409270273358665 32196715357806952705018999)
      ·
        refine ⟨48295073036710429057528499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32196715357806952705018999 48295073036710429057528499)
        ·
          refine ⟨72442609555065643586292749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48295073036710429057528499 72442609555065643586292749)
          ·
            refine ⟨27165978583149616344859781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72442609555065643586292749 27165978583149616344859781)
            ·
              refine ⟨5093620984340553064661209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27165978583149616344859781 5093620984340553064661209)
              ·
                refine ⟨3820215738255414798495907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093620984340553064661209 3820215738255414798495907)
                ·
                  refine ⟨5730323607383122197743861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820215738255414798495907 5730323607383122197743861)
                  ·
                    refine ⟨537217838192167706038487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5730323607383122197743861 537217838192167706038487)
                    ·
                      rfl

theorem cell23_3138684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_3138684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138684 prefixEnd_3138684 := by exact prefixLift 3138684
  have htrace : WordTrace (prefixWord ++ tailWord_3138684) baseStart_3138684 baseEnd_3138684 := by
    simpa [prefixWord, tailWord_3138684, baseEnd_3138684] using wordTrace_append hprefix tailTrace_3138684
  have hstable : (prefixWord ++ tailWord_3138684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138684).length < 2 ^ (prefixWord ++ tailWord_3138684).sum := by decide
  have hdescent : baseEnd_3138684 < baseStart_3138684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138707 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 5]
def baseStart_3138707 : Nat := 118140960795 + 3138707 * 2 ^ 59
def prefixEnd_3138707 : Nat := 4983230072969 + 3 ^ 40 * 3138707 * 2
def baseEnd_3138707 : Nat := 1611665324631556528127855

theorem tailTrace_3138707 : CollatzResearch.WordTrace tailWord_3138707 prefixEnd_3138707 1611665324631556528127855 := by
  unfold tailWord_3138707
  simp only [CollatzResearch.WordTrace]
  refine ⟨114478049040008062323710375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76318699360005374882473583 114478049040008062323710375)
  ·
    refine ⟨171717073560012093485565563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114478049040008062323710375 171717073560012093485565563)
    ·
      refine ⟨257575610340018140228348345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171717073560012093485565563 257575610340018140228348345)
      ·
        refine ⟨193181707755013605171261259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257575610340018140228348345 193181707755013605171261259)
        ·
          refine ⟨289772561632520407756891889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193181707755013605171261259 289772561632520407756891889)
          ·
            refine ⟨217329421224390305817668917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289772561632520407756891889 217329421224390305817668917)
            ·
              refine ⟨20374633239786591170406461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217329421224390305817668917 20374633239786591170406461)
              ·
                refine ⟨7640487464919971688902423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20374633239786591170406461 7640487464919971688902423)
                ·
                  refine ⟨11460731197379957533353635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7640487464919971688902423 11460731197379957533353635)
                  ·
                    refine ⟨17191096796069936300030453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11460731197379957533353635 17191096796069936300030453)
                    ·
                      refine ⟨1611665324631556528127855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17191096796069936300030453 1611665324631556528127855)
                      ·
                        rfl

theorem cell23_3138707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_3138707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138707 prefixEnd_3138707 := by exact prefixLift 3138707
  have htrace : WordTrace (prefixWord ++ tailWord_3138707) baseStart_3138707 baseEnd_3138707 := by
    simpa [prefixWord, tailWord_3138707, baseEnd_3138707] using wordTrace_append hprefix tailTrace_3138707
  have hstable : (prefixWord ++ tailWord_3138707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138707).length < 2 ^ (prefixWord ++ tailWord_3138707).sum := by decide
  have hdescent : baseEnd_3138707 < baseStart_3138707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138717 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3138717 : Nat := 118140960795 + 3138717 * 2 ^ 59
def prefixEnd_3138717 : Nat := 4983230072969 + 3 ^ 40 * 3138717 * 2
def baseEnd_3138717 : Nat := 1611670459438101489002809

theorem tailTrace_3138717 : CollatzResearch.WordTrace tailWord_3138717 prefixEnd_3138717 1611670459438101489002809 := by
  unfold tailWord_3138717
  simp only [CollatzResearch.WordTrace]
  refine ⟨114478413769971834031574405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76318942513314556021049603 114478413769971834031574405)
  ·
    refine ⟨21464702581869718880920201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114478413769971834031574405 21464702581869718880920201)
    ·
      refine ⟨16098526936402289160690151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21464702581869718880920201 16098526936402289160690151)
      ·
        refine ⟨24147790404603433741035227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16098526936402289160690151 24147790404603433741035227)
        ·
          refine ⟨36221685606905150611552841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24147790404603433741035227 36221685606905150611552841)
          ·
            refine ⟨27166264205178862958664631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36221685606905150611552841 27166264205178862958664631)
            ·
              refine ⟨40749396307768294437996947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27166264205178862958664631 40749396307768294437996947)
              ·
                refine ⟨61124094461652441656995421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40749396307768294437996947 61124094461652441656995421)
                ·
                  refine ⟨22921535423119665621373283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61124094461652441656995421 22921535423119665621373283)
                  ·
                    refine ⟨34382303134679498432059925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22921535423119665621373283 34382303134679498432059925)
                    ·
                      refine ⟨1611670459438101489002809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34382303134679498432059925 1611670459438101489002809)
                      ·
                        rfl

theorem cell23_3138717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3138717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138717 prefixEnd_3138717 := by exact prefixLift 3138717
  have htrace : WordTrace (prefixWord ++ tailWord_3138717) baseStart_3138717 baseEnd_3138717 := by
    simpa [prefixWord, tailWord_3138717, baseEnd_3138717] using wordTrace_append hprefix tailTrace_3138717
  have hstable : (prefixWord ++ tailWord_3138717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138717).length < 2 ^ (prefixWord ++ tailWord_3138717).sum := by decide
  have hdescent : baseEnd_3138717 < baseStart_3138717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138724 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_3138724 : Nat := 118140960795 + 3138724 * 2 ^ 59
def prefixEnd_3138724 : Nat := 4983230072969 + 3 ^ 40 * 3138724 * 2
def baseEnd_3138724 : Nat := 1611674053802682961615277

theorem tailTrace_3138724 : CollatzResearch.WordTrace tailWord_3138724 prefixEnd_3138724 1611674053802682961615277 := by
  unfold tailWord_3138724
  simp only [CollatzResearch.WordTrace]
  refine ⟨57239334540473237113539613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76319112720630982818052817 57239334540473237113539613)
  ·
    refine ⟨21464750452677463917577355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57239334540473237113539613 21464750452677463917577355)
    ·
      refine ⟨32197125679016195876366033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21464750452677463917577355 32197125679016195876366033)
      ·
        refine ⟨24147844259262146907274525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32197125679016195876366033 24147844259262146907274525)
        ·
          refine ⟨9055441597223305090227947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24147844259262146907274525 9055441597223305090227947)
          ·
            refine ⟨13583162395834957635341921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9055441597223305090227947 13583162395834957635341921)
            ·
              refine ⟨10187371796876218226506441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13583162395834957635341921 10187371796876218226506441)
              ·
                refine ⟨7640528847657163669879831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10187371796876218226506441 7640528847657163669879831)
                ·
                  refine ⟨11460793271485745504819747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7640528847657163669879831 11460793271485745504819747)
                  ·
                    refine ⟨17191189907228618257229621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11460793271485745504819747 17191189907228618257229621)
                    ·
                      refine ⟨1611674053802682961615277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17191189907228618257229621 1611674053802682961615277)
                      ·
                        rfl

theorem cell23_3138724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_3138724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138724 prefixEnd_3138724 := by exact prefixLift 3138724
  have htrace : WordTrace (prefixWord ++ tailWord_3138724) baseStart_3138724 baseEnd_3138724 := by
    simpa [prefixWord, tailWord_3138724, baseEnd_3138724] using wordTrace_append hprefix tailTrace_3138724
  have hstable : (prefixWord ++ tailWord_3138724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138724).length < 2 ^ (prefixWord ++ tailWord_3138724).sum := by decide
  have hdescent : baseEnd_3138724 < baseStart_3138724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138742 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3138742 : Nat := 118140960795 + 3138742 * 2 ^ 59
def prefixEnd_3138742 : Nat := 4983230072969 + 3 ^ 40 * 3138742 * 2
def baseEnd_3138742 : Nat := 1611683296454463891190195

theorem tailTrace_3138742 : CollatzResearch.WordTrace tailWord_3138742 prefixEnd_3138742 1611683296454463891190195 := by
  unfold tailWord_3138742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154957849680078956327155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76319550396587508867489653 7154957849680078956327155)
  ·
    refine ⟨10732436774520118434490733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7154957849680078956327155 10732436774520118434490733)
    ·
      refine ⟨4024663790445044412934025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10732436774520118434490733 4024663790445044412934025)
      ·
        refine ⟨3018497842833783309700519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4024663790445044412934025 3018497842833783309700519)
        ·
          refine ⟨4527746764250674964550779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3018497842833783309700519 4527746764250674964550779)
          ·
            refine ⟨6791620146376012446826169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4527746764250674964550779 6791620146376012446826169)
            ·
              refine ⟨5093715109782009335119627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6791620146376012446826169 5093715109782009335119627)
              ·
                refine ⟨7640572664673014002679441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093715109782009335119627 7640572664673014002679441)
                ·
                  refine ⟨5730429498504760502009581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7640572664673014002679441 5730429498504760502009581)
                  ·
                    refine ⟨2148911061939285188253593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5730429498504760502009581 2148911061939285188253593)
                    ·
                      refine ⟨1611683296454463891190195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148911061939285188253593 1611683296454463891190195)
                      ·
                        rfl

theorem cell23_3138742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3138742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138742 prefixEnd_3138742 := by exact prefixLift 3138742
  have htrace : WordTrace (prefixWord ++ tailWord_3138742) baseStart_3138742 baseEnd_3138742 := by
    simpa [prefixWord, tailWord_3138742, baseEnd_3138742] using wordTrace_append hprefix tailTrace_3138742
  have hstable : (prefixWord ++ tailWord_3138742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138742).length < 2 ^ (prefixWord ++ tailWord_3138742).sum := by decide
  have hdescent : baseEnd_3138742 < baseStart_3138742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138815 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 1, 3, 2]
def baseStart_3138815 : Nat := 118140960795 + 3138815 * 2 ^ 59
def prefixEnd_3138815 : Nat := 4983230072969 + 3 ^ 40 * 3138815 * 2
def baseEnd_3138815 : Nat := 1611720780542242105577359

theorem tailTrace_3138815 : CollatzResearch.WordTrace tailWord_3138815 prefixEnd_3138815 1611720780542242105577359 := by
  unfold tailWord_3138815
  simp only [CollatzResearch.WordTrace]
  refine ⟨114481988123616796768641899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76321325415744531179094599 114481988123616796768641899)
  ·
    refine ⟨171722982185425195152962849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114481988123616796768641899 171722982185425195152962849)
    ·
      refine ⟨128792236639068896364722137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171722982185425195152962849 128792236639068896364722137)
      ·
        refine ⟨96594177479301672273541603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128792236639068896364722137 96594177479301672273541603)
        ·
          refine ⟨144891266218952508410312405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96594177479301672273541603 144891266218952508410312405)
          ·
            refine ⟨3395889052006699415866697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 144891266218952508410312405 3395889052006699415866697)
            ·
              refine ⟨2546916789005024561900023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395889052006699415866697 2546916789005024561900023)
              ·
                refine ⟨3820375183507536842850035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546916789005024561900023 3820375183507536842850035)
                ·
                  refine ⟨5730562775261305264275053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820375183507536842850035 5730562775261305264275053)
                  ·
                    refine ⟨2148961040722989474103145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5730562775261305264275053 2148961040722989474103145)
                    ·
                      refine ⟨1611720780542242105577359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148961040722989474103145 1611720780542242105577359)
                      ·
                        rfl

theorem cell23_3138815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_3138815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138815 prefixEnd_3138815 := by exact prefixLift 3138815
  have htrace : WordTrace (prefixWord ++ tailWord_3138815) baseStart_3138815 baseEnd_3138815 := by
    simpa [prefixWord, tailWord_3138815, baseEnd_3138815] using wordTrace_append hprefix tailTrace_3138815
  have hstable : (prefixWord ++ tailWord_3138815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138815).length < 2 ^ (prefixWord ++ tailWord_3138815).sum := by decide
  have hdescent : baseEnd_3138815 < baseStart_3138815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138828 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 4, 2, 2]
def baseStart_3138828 : Nat := 118140960795 + 3138828 * 2 ^ 59
def prefixEnd_3138828 : Nat := 4983230072969 + 3 ^ 40 * 3138828 * 2
def baseEnd_3138828 : Nat := 1611727455790750554714799

theorem tailTrace_3138828 : CollatzResearch.WordTrace tailWord_3138828 prefixEnd_3138828 1611727455790750554714799 := by
  unfold tailWord_3138828
  simp only [CollatzResearch.WordTrace]
  refine ⟨57241231136284849994432569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76321641515046466659243425 57241231136284849994432569)
  ·
    refine ⟨42930923352213637495824427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57241231136284849994432569 42930923352213637495824427)
    ·
      refine ⟨64396385028320456243736641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42930923352213637495824427 64396385028320456243736641)
      ·
        refine ⟨48297288771240342182802481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64396385028320456243736641 48297288771240342182802481)
        ·
          refine ⟨36222966578430256637101861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48297288771240342182802481 36222966578430256637101861)
          ·
            refine ⟨6791806233455673119456599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36222966578430256637101861 6791806233455673119456599)
            ·
              refine ⟨10187709350183509679184899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6791806233455673119456599 10187709350183509679184899)
              ·
                refine ⟨15281564025275264518777349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10187709350183509679184899 15281564025275264518777349)
                ·
                  refine ⟨2865293254739112097270753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15281564025275264518777349 2865293254739112097270753)
                  ·
                    refine ⟨2148969941054334072953065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2865293254739112097270753 2148969941054334072953065)
                    ·
                      refine ⟨1611727455790750554714799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148969941054334072953065 1611727455790750554714799)
                      ·
                        rfl

theorem cell23_3138828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_3138828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138828 prefixEnd_3138828 := by exact prefixLift 3138828
  have htrace : WordTrace (prefixWord ++ tailWord_3138828) baseStart_3138828 baseEnd_3138828 := by
    simpa [prefixWord, tailWord_3138828, baseEnd_3138828] using wordTrace_append hprefix tailTrace_3138828
  have hstable : (prefixWord ++ tailWord_3138828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138828).length < 2 ^ (prefixWord ++ tailWord_3138828).sum := by decide
  have hdescent : baseEnd_3138828 < baseStart_3138828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138845 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_3138845 : Nat := 118140960795 + 3138845 * 2 ^ 59
def prefixEnd_3138845 : Nat := 4983230072969 + 3 ^ 40 * 3138845 * 2
def baseEnd_3138845 : Nat := 1611736184961876988202221

theorem tailTrace_3138845 : CollatzResearch.WordTrace tailWord_3138845 prefixEnd_3138845 1611736184961876988202221 := by
  unfold tailWord_3138845
  simp only [CollatzResearch.WordTrace]
  refine ⟨114483082313508111892233989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76322054875672074594822659 114483082313508111892233989)
  ·
    refine ⟨21465577933782770979793873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114483082313508111892233989 21465577933782770979793873)
    ·
      refine ⟨16099183450337078234845405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21465577933782770979793873 16099183450337078234845405)
      ·
        refine ⟨6037193793876404338067027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16099183450337078234845405 6037193793876404338067027)
        ·
          refine ⟨9055790690814606507100541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6037193793876404338067027 9055790690814606507100541)
          ·
            refine ⟨3395921509055477440162703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9055790690814606507100541 3395921509055477440162703)
            ·
              refine ⟨5093882263583216160244055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395921509055477440162703 5093882263583216160244055)
              ·
                refine ⟨7640823395374824240366083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5093882263583216160244055 7640823395374824240366083)
                ·
                  refine ⟨11461235093062236360549125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7640823395374824240366083 11461235093062236360549125)
                  ·
                    refine ⟨2148981579949169317602961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11461235093062236360549125 2148981579949169317602961)
                    ·
                      refine ⟨1611736184961876988202221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2148981579949169317602961 1611736184961876988202221)
                      ·
                        rfl

theorem cell23_3138845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_3138845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138845 prefixEnd_3138845 := by exact prefixLift 3138845
  have htrace : WordTrace (prefixWord ++ tailWord_3138845) baseStart_3138845 baseEnd_3138845 := by
    simpa [prefixWord, tailWord_3138845, baseEnd_3138845] using wordTrace_append hprefix tailTrace_3138845
  have hstable : (prefixWord ++ tailWord_3138845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138845).length < 2 ^ (prefixWord ++ tailWord_3138845).sum := by decide
  have hdescent : baseEnd_3138845 < baseStart_3138845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138864 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 2, 5]
def baseStart_3138864 : Nat := 118140960795 + 3138864 * 2 ^ 59
def prefixEnd_3138864 : Nat := 4983230072969 + 3 ^ 40 * 3138864 * 2
def baseEnd_3138864 : Nat := 537248647031437471288211

theorem tailTrace_3138864 : CollatzResearch.WordTrace tailWord_3138864 prefixEnd_3138864 537248647031437471288211 := by
  unfold tailWord_3138864
  simp only [CollatzResearch.WordTrace]
  refine ⟨57241887650219639068587823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76322516866959518758117097 57241887650219639068587823)
  ·
    refine ⟨85862831475329458602881735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57241887650219639068587823 85862831475329458602881735)
    ·
      refine ⟨128794247212994187904322603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85862831475329458602881735 128794247212994187904322603)
      ·
        refine ⟨193191370819491281856483905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128794247212994187904322603 193191370819491281856483905)
        ·
          refine ⟨144893528114618461392362929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193191370819491281856483905 144893528114618461392362929)
          ·
            refine ⟨108670146085963846044272197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144893528114618461392362929 108670146085963846044272197)
            ·
              refine ⟨20375652391118221133301037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108670146085963846044272197 20375652391118221133301037)
              ·
                refine ⟨7640869646669332924987889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20375652391118221133301037 7640869646669332924987889)
                ·
                  refine ⟨5730652235001999693740917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7640869646669332924987889 5730652235001999693740917)
                  ·
                    refine ⟨537248647031437471288211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5730652235001999693740917 537248647031437471288211)
                    ·
                      rfl

theorem cell23_3138864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_3138864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138864 prefixEnd_3138864 := by exact prefixLift 3138864
  have htrace : WordTrace (prefixWord ++ tailWord_3138864) baseStart_3138864 baseEnd_3138864 := by
    simpa [prefixWord, tailWord_3138864, baseEnd_3138864] using wordTrace_append hprefix tailTrace_3138864
  have hstable : (prefixWord ++ tailWord_3138864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138864).length < 2 ^ (prefixWord ++ tailWord_3138864).sum := by decide
  have hdescent : baseEnd_3138864 < baseStart_3138864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138874 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_3138874 : Nat := 118140960795 + 3138874 * 2 ^ 59
def prefixEnd_3138874 : Nat := 4983230072969 + 3 ^ 40 * 3138874 * 2
def baseEnd_3138874 : Nat := 1611751075900857374739587

theorem tailTrace_3138874 : CollatzResearch.WordTrace tailWord_3138874 prefixEnd_3138874 1611751075900857374739587 := by
  unfold tailWord_3138874
  simp only [CollatzResearch.WordTrace]
  refine ⟨28621035007600762461259919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76322760020268699896693117 28621035007600762461259919)
  ·
    refine ⟨42931552511401143691889879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28621035007600762461259919 42931552511401143691889879)
    ·
      refine ⟨64397328767101715537834819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42931552511401143691889879 64397328767101715537834819)
      ·
        refine ⟨96595993150652573306752229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64397328767101715537834819 96595993150652573306752229)
        ·
          refine ⟨18111748715747357495016043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96595993150652573306752229 18111748715747357495016043)
          ·
            refine ⟨27167623073621036242524065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18111748715747357495016043 27167623073621036242524065)
            ·
              refine ⟨20375717305215777181893049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27167623073621036242524065 20375717305215777181893049)
              ·
                refine ⟨15281787978911832886419787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20375717305215777181893049 15281787978911832886419787)
                ·
                  refine ⟨22922681968367749329629681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15281787978911832886419787 22922681968367749329629681)
                  ·
                    refine ⟨17192011476275811997222261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22922681968367749329629681 17192011476275811997222261)
                    ·
                      refine ⟨1611751075900857374739587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17192011476275811997222261 1611751075900857374739587)
                      ·
                        rfl

theorem cell23_3138874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_3138874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138874 prefixEnd_3138874 := by exact prefixLift 3138874
  have htrace : WordTrace (prefixWord ++ tailWord_3138874) baseStart_3138874 baseEnd_3138874 := by
    simpa [prefixWord, tailWord_3138874, baseEnd_3138874] using wordTrace_append hprefix tailTrace_3138874
  have hstable : (prefixWord ++ tailWord_3138874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138874).length < 2 ^ (prefixWord ++ tailWord_3138874).sum := by decide
  have hdescent : baseEnd_3138874 < baseStart_3138874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138881 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3138881 : Nat := 118140960795 + 3138881 * 2 ^ 59
def prefixEnd_3138881 : Nat := 4983230072969 + 3 ^ 40 * 3138881 * 2
def baseEnd_3138881 : Nat := 537251556755146282450685

theorem tailTrace_3138881 : CollatzResearch.WordTrace tailWord_3138881 prefixEnd_3138881 537251556755146282450685 := by
  unfold tailWord_3138881
  simp only [CollatzResearch.WordTrace]
  refine ⟨114484395341377690040544497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76322930227585126693696331 114484395341377690040544497)
  ·
    refine ⟨85863296506033267530408373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114484395341377690040544497 85863296506033267530408373)
    ·
      refine ⟨8049684047440618830975785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85863296506033267530408373 8049684047440618830975785)
      ·
        refine ⟨6037263035580464123231839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8049684047440618830975785 6037263035580464123231839)
        ·
          refine ⟨9055894553370696184847759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6037263035580464123231839 9055894553370696184847759)
          ·
            refine ⟨13583841830056044277271639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9055894553370696184847759 13583841830056044277271639)
            ·
              refine ⟨20375762745084066415907459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13583841830056044277271639 20375762745084066415907459)
              ·
                refine ⟨30563644117626099623861189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20375762745084066415907459 30563644117626099623861189)
                ·
                  refine ⟨5730683272054893679473973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30563644117626099623861189 5730683272054893679473973)
                  ·
                    refine ⟨537251556755146282450685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5730683272054893679473973 537251556755146282450685)
                    ·
                      rfl

theorem cell23_3138881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3138881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138881 prefixEnd_3138881 := by exact prefixLift 3138881
  have htrace : WordTrace (prefixWord ++ tailWord_3138881) baseStart_3138881 baseEnd_3138881 := by
    simpa [prefixWord, tailWord_3138881, baseEnd_3138881] using wordTrace_append hprefix tailTrace_3138881
  have hstable : (prefixWord ++ tailWord_3138881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138881).length < 2 ^ (prefixWord ++ tailWord_3138881).sum := by decide
  have hdescent : baseEnd_3138881 < baseStart_3138881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138928 : List Nat := [2, 1, 1, 1, 4, 2, 2, 5, 1, 4]
def baseStart_3138928 : Nat := 118140960795 + 3138928 * 2 ^ 59
def prefixEnd_3138928 : Nat := 4983230072969 + 3 ^ 40 * 3138928 * 2
def baseEnd_3138928 : Nat := 537259601285400054488113

theorem tailTrace_3138928 : CollatzResearch.WordTrace tailWord_3138928 prefixEnd_3138928 537259601285400054488113 := by
  unfold tailWord_3138928
  simp only [CollatzResearch.WordTrace]
  refine ⟨57243054786103708533752719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76324073048138278045003625 57243054786103708533752719)
  ·
    refine ⟨85864582179155562800629079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57243054786103708533752719 85864582179155562800629079)
    ·
      refine ⟨128796873268733344200943619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85864582179155562800629079 128796873268733344200943619)
      ·
        refine ⟨193195309903100016301415429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128796873268733344200943619 193195309903100016301415429)
        ·
          refine ⟨36224120606831253056515393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193195309903100016301415429 36224120606831253056515393)
          ·
            refine ⟨27168090455123439792386545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36224120606831253056515393 27168090455123439792386545)
            ·
              refine ⟨20376067841342579844289909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27168090455123439792386545 20376067841342579844289909)
              ·
                refine ⟨1910256360125866860402179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20376067841342579844289909 1910256360125866860402179)
                ·
                  refine ⟨2865384540188800290603269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910256360125866860402179 2865384540188800290603269)
                  ·
                    refine ⟨537259601285400054488113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2865384540188800290603269 537259601285400054488113)
                    ·
                      rfl

theorem cell23_3138928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 4].length) (baseStart_3138928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138928 prefixEnd_3138928 := by exact prefixLift 3138928
  have htrace : WordTrace (prefixWord ++ tailWord_3138928) baseStart_3138928 baseEnd_3138928 := by
    simpa [prefixWord, tailWord_3138928, baseEnd_3138928] using wordTrace_append hprefix tailTrace_3138928
  have hstable : (prefixWord ++ tailWord_3138928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138928).length < 2 ^ (prefixWord ++ tailWord_3138928).sum := by decide
  have hdescent : baseEnd_3138928 < baseStart_3138928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138941 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 6]
def baseStart_3138941 : Nat := 118140960795 + 3138941 * 2 ^ 59
def prefixEnd_3138941 : Nat := 4983230072969 + 3 ^ 40 * 3138941 * 2
def baseEnd_3138941 : Nat := 179087275456078734733531

theorem tailTrace_3138941 : CollatzResearch.WordTrace tailWord_3138941 prefixEnd_3138941 179087275456078734733531 := by
  unfold tailWord_3138941
  simp only [CollatzResearch.WordTrace]
  refine ⟨114486583721160320287728677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76324389147440213525152451 114486583721160320287728677)
  ·
    refine ⟨21466234447717560053949127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114486583721160320287728677 21466234447717560053949127)
    ·
      refine ⟨32199351671576340080923691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21466234447717560053949127 32199351671576340080923691)
      ·
        refine ⟨48299027507364510121385537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32199351671576340080923691 48299027507364510121385537)
        ·
          refine ⟨36224270630523382591039153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48299027507364510121385537 36224270630523382591039153)
          ·
            refine ⟨27168202972892536943279365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36224270630523382591039153 27168202972892536943279365)
            ·
              refine ⟨5094038057417350676864881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27168202972892536943279365 5094038057417350676864881)
              ·
                refine ⟨3820528543063013007648661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5094038057417350676864881 3820528543063013007648661)
                ·
                  refine ⟨179087275456078734733531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3820528543063013007648661 179087275456078734733531)
                  ·
                    rfl

theorem cell23_3138941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_3138941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138941 prefixEnd_3138941 := by exact prefixLift 3138941
  have htrace : WordTrace (prefixWord ++ tailWord_3138941) baseStart_3138941 baseEnd_3138941 := by
    simpa [prefixWord, tailWord_3138941, baseEnd_3138941] using wordTrace_append hprefix tailTrace_3138941
  have hstable : (prefixWord ++ tailWord_3138941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138941).length < 2 ^ (prefixWord ++ tailWord_3138941).sum := by decide
  have hdescent : baseEnd_3138941 < baseStart_3138941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138961 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 3, 5, 2]
def baseStart_3138961 : Nat := 118140960795 + 3138961 * 2 ^ 59
def prefixEnd_3138961 : Nat := 4983230072969 + 3 ^ 40 * 3138961 * 2
def baseEnd_3138961 : Nat := 1611795748717798534351687

theorem tailTrace_3138961 : CollatzResearch.WordTrace tailWord_3138961 prefixEnd_3138961 1611795748717798534351687 := by
  unfold tailWord_3138961
  simp only [CollatzResearch.WordTrace]
  refine ⟨114487313181087863703456737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76324875454058575802304491 114487313181087863703456737)
  ·
    refine ⟨85865484885815897777592553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114487313181087863703456737 85865484885815897777592553)
    ·
      refine ⟨64399113664361923333194415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85865484885815897777592553 64399113664361923333194415)
      ·
        refine ⟨96598670496542884999791623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64399113664361923333194415 96598670496542884999791623)
        ·
          refine ⟨144898005744814327499687435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96598670496542884999791623 144898005744814327499687435)
          ·
            refine ⟨217347008617221491249531153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144898005744814327499687435 217347008617221491249531153)
            ·
              refine ⟨163010256462916118437148365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217347008617221491249531153 163010256462916118437148365)
              ·
                refine ⟨61128846173593544413930637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163010256462916118437148365 61128846173593544413930637)
                ·
                  refine ⟨22923317315097579155223989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61128846173593544413930637 22923317315097579155223989)
                  ·
                    refine ⟨2149060998290398045802249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22923317315097579155223989 2149060998290398045802249)
                    ·
                      refine ⟨1611795748717798534351687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149060998290398045802249 1611795748717798534351687)
                      ·
                        rfl

theorem cell23_3138961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_3138961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138961 prefixEnd_3138961 := by exact prefixLift 3138961
  have htrace : WordTrace (prefixWord ++ tailWord_3138961) baseStart_3138961 baseEnd_3138961 := by
    simpa [prefixWord, tailWord_3138961, baseEnd_3138961] using wordTrace_append hprefix tailTrace_3138961
  have hstable : (prefixWord ++ tailWord_3138961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138961).length < 2 ^ (prefixWord ++ tailWord_3138961).sum := by decide
  have hdescent : baseEnd_3138961 < baseStart_3138961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138972 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3138972 : Nat := 118140960795 + 3138972 * 2 ^ 59
def prefixEnd_3138972 : Nat := 4983230072969 + 3 ^ 40 * 3138972 * 2
def baseEnd_3138972 : Nat := 1611801397004997991314137

theorem tailTrace_3138972 : CollatzResearch.WordTrace tailWord_3138972 prefixEnd_3138972 1611801397004997991314137 := by
  unfold tailWord_3138972
  simp only [CollatzResearch.WordTrace]
  refine ⟨57243857192024006291053585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76325142922698675054738113 57243857192024006291053585)
  ·
    refine ⟨42932892894018004718290189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57243857192024006291053585 42932892894018004718290189)
    ·
      refine ⟨16099834835256751769358821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42932892894018004718290189 16099834835256751769358821)
      ·
        refine ⟨3018719031610640956754779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16099834835256751769358821 3018719031610640956754779)
        ·
          refine ⟨4528078547415961435132169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3018719031610640956754779 4528078547415961435132169)
          ·
            refine ⟨3396058910561971076349127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4528078547415961435132169 3396058910561971076349127)
            ·
              refine ⟨5094088365842956614523691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396058910561971076349127 5094088365842956614523691)
              ·
                refine ⟨7641132548764434921785537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5094088365842956614523691 7641132548764434921785537)
                ·
                  refine ⟨5730849411573326191339153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7641132548764434921785537 5730849411573326191339153)
                  ·
                    refine ⟨4298137058679994643504365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5730849411573326191339153 4298137058679994643504365)
                    ·
                      refine ⟨1611801397004997991314137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4298137058679994643504365 1611801397004997991314137)
                      ·
                        rfl

theorem cell23_3138972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3138972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138972 prefixEnd_3138972 := by exact prefixLift 3138972
  have htrace : WordTrace (prefixWord ++ tailWord_3138972) baseStart_3138972 baseEnd_3138972 := by
    simpa [prefixWord, tailWord_3138972, baseEnd_3138972] using wordTrace_append hprefix tailTrace_3138972
  have hstable : (prefixWord ++ tailWord_3138972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138972).length < 2 ^ (prefixWord ++ tailWord_3138972).sum := by decide
  have hdescent : baseEnd_3138972 < baseStart_3138972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138988 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_3138988 : Nat := 118140960795 + 3138988 * 2 ^ 59
def prefixEnd_3138988 : Nat := 4983230072969 + 3 ^ 40 * 3138988 * 2
def baseEnd_3138988 : Nat := 537269870898489976238021

theorem tailTrace_3138988 : CollatzResearch.WordTrace tailWord_3138988 prefixEnd_3138988 537269870898489976238021 := by
  unfold tailWord_3138988
  simp only [CollatzResearch.WordTrace]
  refine ⟨57244148975995023657344809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76325531967993364876459745 57244148975995023657344809)
  ·
    refine ⟨42933111731996267743008607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57244148975995023657344809 42933111731996267743008607)
    ·
      refine ⟨64399667597994401614512911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42933111731996267743008607 64399667597994401614512911)
      ·
        refine ⟨96599501396991602421769367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64399667597994401614512911 96599501396991602421769367)
        ·
          refine ⟨144899252095487403632654051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96599501396991602421769367 144899252095487403632654051)
          ·
            refine ⟨217348878143231105448981077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144899252095487403632654051 217348878143231105448981077)
            ·
              refine ⟨2547057165740989516980247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 217348878143231105448981077 2547057165740989516980247)
              ·
                refine ⟨3820585748611484275470371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547057165740989516980247 3820585748611484275470371)
                ·
                  refine ⟨5730878622917226413205557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820585748611484275470371 5730878622917226413205557)
                  ·
                    refine ⟨537269870898489976238021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5730878622917226413205557 537269870898489976238021)
                    ·
                      rfl

theorem cell23_3138988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_3138988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138988 prefixEnd_3138988 := by exact prefixLift 3138988
  have htrace : WordTrace (prefixWord ++ tailWord_3138988) baseStart_3138988 baseEnd_3138988 := by
    simpa [prefixWord, tailWord_3138988, baseEnd_3138988] using wordTrace_append hprefix tailTrace_3138988
  have hstable : (prefixWord ++ tailWord_3138988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138988).length < 2 ^ (prefixWord ++ tailWord_3138988).sum := by decide
  have hdescent : baseEnd_3138988 < baseStart_3138988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3138991 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 8, 2]
def baseStart_3138991 : Nat := 118140960795 + 3138991 * 2 ^ 59
def prefixEnd_3138991 : Nat := 4983230072969 + 3 ^ 40 * 3138991 * 2
def baseEnd_3138991 : Nat := 1611811153137433416976549

theorem tailTrace_3138991 : CollatzResearch.WordTrace tailWord_3138991 prefixEnd_3138991 1611811153137433416976549 := by
  unfold tailWord_3138991
  simp only [CollatzResearch.WordTrace]
  refine ⟨114488407370979178827048827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76325604913986119218032551 114488407370979178827048827)
  ·
    refine ⟨171732611056468768240573241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114488407370979178827048827 171732611056468768240573241)
    ·
      refine ⟨128799458292351576180429931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171732611056468768240573241 128799458292351576180429931)
      ·
        refine ⟨193199187438527364270644897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128799458292351576180429931 193199187438527364270644897)
        ·
          refine ⟨144899390578895523202983673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193199187438527364270644897 144899390578895523202983673)
          ·
            refine ⟨108674542934171642402237755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144899390578895523202983673 108674542934171642402237755)
            ·
              refine ⟨163011814401257463603356633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108674542934171642402237755 163011814401257463603356633)
              ·
                refine ⟨122258860800943097702517475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163011814401257463603356633 122258860800943097702517475)
                ·
                  refine ⟨183388291201414646553776213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122258860800943097702517475 183388291201414646553776213)
                  ·
                    refine ⟨2149081537516577889302065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 183388291201414646553776213 2149081537516577889302065)
                    ·
                      refine ⟨1611811153137433416976549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149081537516577889302065 1611811153137433416976549)
                      ·
                        rfl

theorem cell23_3138991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 8, 2].length) (baseStart_3138991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3138991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3138991 prefixEnd_3138991 := by exact prefixLift 3138991
  have htrace : WordTrace (prefixWord ++ tailWord_3138991) baseStart_3138991 baseEnd_3138991 := by
    simpa [prefixWord, tailWord_3138991, baseEnd_3138991] using wordTrace_append hprefix tailTrace_3138991
  have hstable : (prefixWord ++ tailWord_3138991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3138991).length < 2 ^ (prefixWord ++ tailWord_3138991).sum := by decide
  have hdescent : baseEnd_3138991 < baseStart_3138991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3138991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139011 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 3]
def baseStart_3139011 : Nat := 118140960795 + 3139011 * 2 ^ 59
def prefixEnd_3139011 : Nat := 4983230072969 + 3 ^ 40 * 3139011 * 2
def baseEnd_3139011 : Nat := 1611821422750523338726457

theorem tailTrace_3139011 : CollatzResearch.WordTrace tailWord_3139011 prefixEnd_3139011 1611821422750523338726457 := by
  unfold tailWord_3139011
  simp only [CollatzResearch.WordTrace]
  refine ⟨114489136830906722242776887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76326091220604481495184591 114489136830906722242776887)
  ·
    refine ⟨171733705246360083364165331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114489136830906722242776887 171733705246360083364165331)
    ·
      refine ⟨257600557869540125046247997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171733705246360083364165331 257600557869540125046247997)
      ·
        refine ⟨96600209201077546892342999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257600557869540125046247997 96600209201077546892342999)
        ·
          refine ⟨144900313801616320338514499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96600209201077546892342999 144900313801616320338514499)
          ·
            refine ⟨217350470702424480507771749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144900313801616320338514499 217350470702424480507771749)
            ·
              refine ⟨40753213256704590095207203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217350470702424480507771749 40753213256704590095207203)
              ·
                refine ⟨61129819885056885142810805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40753213256704590095207203 61129819885056885142810805)
                ·
                  refine ⟨5730920614224082982138513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61129819885056885142810805 5730920614224082982138513)
                  ·
                    refine ⟨4298190460668062236603885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5730920614224082982138513 4298190460668062236603885)
                    ·
                      refine ⟨1611821422750523338726457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4298190460668062236603885 1611821422750523338726457)
                      ·
                        rfl

theorem cell23_3139011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_3139011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139011 prefixEnd_3139011 := by exact prefixLift 3139011
  have htrace : WordTrace (prefixWord ++ tailWord_3139011) baseStart_3139011 baseEnd_3139011 := by
    simpa [prefixWord, tailWord_3139011, baseEnd_3139011] using wordTrace_append hprefix tailTrace_3139011
  have hstable : (prefixWord ++ tailWord_3139011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139011).length < 2 ^ (prefixWord ++ tailWord_3139011).sum := by decide
  have hdescent : baseEnd_3139011 < baseStart_3139011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139018 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3139018 : Nat := 118140960795 + 3139018 * 2 ^ 59
def prefixEnd_3139018 : Nat := 4983230072969 + 3 ^ 40 * 3139018 * 2
def baseEnd_3139018 : Nat := 537275005705034937112975

theorem tailTrace_3139018 : CollatzResearch.WordTrace tailWord_3139018 prefixEnd_3139018 537275005705034937112975 := by
  unfold tailWord_3139018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28622348035470340609570427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76326261427920908292187805 28622348035470340609570427)
  ·
    refine ⟨42933522053205510914355641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28622348035470340609570427 42933522053205510914355641)
    ·
      refine ⟨32200141539904133185766731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42933522053205510914355641 32200141539904133185766731)
      ·
        refine ⟨48300212309856199778650097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32200141539904133185766731 48300212309856199778650097)
        ·
          refine ⟨36225159232392149833987573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48300212309856199778650097 36225159232392149833987573)
          ·
            refine ⟨3396108678036764046936335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36225159232392149833987573 3396108678036764046936335)
            ·
              refine ⟨5094163017055146070404503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396108678036764046936335 5094163017055146070404503)
              ·
                refine ⟨7641244525582719105606755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5094163017055146070404503 7641244525582719105606755)
                ·
                  refine ⟨11461866788374078658410133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7641244525582719105606755 11461866788374078658410133)
                  ·
                    refine ⟨537275005705034937112975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11461866788374078658410133 537275005705034937112975)
                    ·
                      rfl

theorem cell23_3139018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3139018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139018 prefixEnd_3139018 := by exact prefixLift 3139018
  have htrace : WordTrace (prefixWord ++ tailWord_3139018) baseStart_3139018 baseEnd_3139018 := by
    simpa [prefixWord, tailWord_3139018, baseEnd_3139018] using wordTrace_append hprefix tailTrace_3139018
  have hstable : (prefixWord ++ tailWord_3139018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139018).length < 2 ^ (prefixWord ++ tailWord_3139018).sum := by decide
  have hdescent : baseEnd_3139018 < baseStart_3139018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139024 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_3139024 : Nat := 118140960795 + 3139024 * 2 ^ 59
def prefixEnd_3139024 : Nat := 4983230072969 + 3 ^ 40 * 3139024 * 2
def baseEnd_3139024 : Nat := 1611828097999031787863897

theorem tailTrace_3139024 : CollatzResearch.WordTrace tailWord_3139024 prefixEnd_3139024 1611828097999031787863897 := by
  unfold tailWord_3139024
  simp only [CollatzResearch.WordTrace]
  refine ⟨57244805489929812731500063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76326407319906416975333417 57244805489929812731500063)
  ·
    refine ⟨85867208234894719097250095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57244805489929812731500063 85867208234894719097250095)
    ·
      refine ⟨128800812352342078645875143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85867208234894719097250095 128800812352342078645875143)
      ·
        refine ⟨193201218528513117968812715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128800812352342078645875143 193201218528513117968812715)
        ·
          refine ⟨289801827792769676953219073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193201218528513117968812715 289801827792769676953219073)
          ·
            refine ⟨217351370844577257714914305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289801827792769676953219073 217351370844577257714914305)
            ·
              refine ⟨163013528133432943286185729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217351370844577257714914305 163013528133432943286185729)
              ·
                refine ⟨122260146100074707464639297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163013528133432943286185729 122260146100074707464639297)
                ·
                  refine ⟨91695109575056030598479473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122260146100074707464639297 91695109575056030598479473)
                  ·
                    refine ⟨68771332181292022948859605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91695109575056030598479473 68771332181292022948859605)
                    ·
                      refine ⟨1611828097999031787863897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 68771332181292022948859605 1611828097999031787863897)
                      ·
                        rfl

theorem cell23_3139024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_3139024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139024 prefixEnd_3139024 := by exact prefixLift 3139024
  have htrace : WordTrace (prefixWord ++ tailWord_3139024) baseStart_3139024 baseEnd_3139024 := by
    simpa [prefixWord, tailWord_3139024, baseEnd_3139024] using wordTrace_append hprefix tailTrace_3139024
  have hstable : (prefixWord ++ tailWord_3139024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139024).length < 2 ^ (prefixWord ++ tailWord_3139024).sum := by decide
  have hdescent : baseEnd_3139024 < baseStart_3139024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139045 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_3139045 : Nat := 118140960795 + 3139045 * 2 ^ 59
def prefixEnd_3139045 : Nat := 4983230072969 + 3 ^ 40 * 3139045 * 2
def baseEnd_3139045 : Nat := 1611838881092776205701301

theorem tailTrace_3139045 : CollatzResearch.WordTrace tailWord_3139045 prefixEnd_3139045 1611838881092776205701301 := by
  unfold tailWord_3139045
  simp only [CollatzResearch.WordTrace]
  refine ⟨114490376912783546049514589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76326917941855697366343059 114490376912783546049514589)
  ·
    refine ⟨42933891342293829768567971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114490376912783546049514589 42933891342293829768567971)
    ·
      refine ⟨64400837013440744652851957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42933891342293829768567971 64400837013440744652851957)
      ·
        refine ⟨6037578470010069811204871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64400837013440744652851957 6037578470010069811204871)
        ·
          refine ⟨9056367705015104716807307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6037578470010069811204871 9056367705015104716807307)
          ·
            refine ⟨13584551557522657075210961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9056367705015104716807307 13584551557522657075210961)
            ·
              refine ⟨10188413668141992806408221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13584551557522657075210961 10188413668141992806408221)
              ·
                refine ⟨3820655125553247302403083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10188413668141992806408221 3820655125553247302403083)
                ·
                  refine ⟨5730982688329870953604625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820655125553247302403083 5730982688329870953604625)
                  ·
                    refine ⟨4298237016247403215203469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5730982688329870953604625 4298237016247403215203469)
                    ·
                      refine ⟨1611838881092776205701301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4298237016247403215203469 1611838881092776205701301)
                      ·
                        rfl

theorem cell23_3139045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_3139045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139045 prefixEnd_3139045 := by exact prefixLift 3139045
  have htrace : WordTrace (prefixWord ++ tailWord_3139045) baseStart_3139045 baseEnd_3139045 := by
    simpa [prefixWord, tailWord_3139045, baseEnd_3139045] using wordTrace_append hprefix tailTrace_3139045
  have hstable : (prefixWord ++ tailWord_3139045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139045).length < 2 ^ (prefixWord ++ tailWord_3139045).sum := by decide
  have hdescent : baseEnd_3139045 < baseStart_3139045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139092 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3139092 : Nat := 118140960795 + 3139092 * 2 ^ 59
def prefixEnd_3139092 : Nat := 4983230072969 + 3 ^ 40 * 3139092 * 2
def baseEnd_3139092 : Nat := 1611863014683537521813585

theorem tailTrace_3139092 : CollatzResearch.WordTrace tailWord_3139092 prefixEnd_3139092 1611863014683537521813585 := by
  unfold tailWord_3139092
  simp only [CollatzResearch.WordTrace]
  refine ⟨57246045571806636538237765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76328060762408848717650353 57246045571806636538237765)
  ·
    refine ⟨10733633544713744350919581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57246045571806636538237765 10733633544713744350919581)
    ·
      refine ⟨4025112579267654131594843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10733633544713744350919581 4025112579267654131594843)
      ·
        refine ⟨6037668868901481197392265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025112579267654131594843 6037668868901481197392265)
        ·
          refine ⟨4528251651676110898044199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6037668868901481197392265 4528251651676110898044199)
          ·
            refine ⟨6792377477514166347066299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528251651676110898044199 6792377477514166347066299)
            ·
              refine ⟨10188566216271249520599449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792377477514166347066299 10188566216271249520599449)
              ·
                refine ⟨7641424662203437140449587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10188566216271249520599449 7641424662203437140449587)
                ·
                  refine ⟨11462136993305155710674381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7641424662203437140449587 11462136993305155710674381)
                  ·
                    refine ⟨4298301372489433391502893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11462136993305155710674381 4298301372489433391502893)
                    ·
                      refine ⟨1611863014683537521813585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4298301372489433391502893 1611863014683537521813585)
                      ·
                        rfl

theorem cell23_3139092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3139092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139092 prefixEnd_3139092 := by exact prefixLift 3139092
  have htrace : WordTrace (prefixWord ++ tailWord_3139092) baseStart_3139092 baseEnd_3139092 := by
    simpa [prefixWord, tailWord_3139092, baseEnd_3139092] using wordTrace_append hprefix tailTrace_3139092
  have hstable : (prefixWord ++ tailWord_3139092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139092).length < 2 ^ (prefixWord ++ tailWord_3139092).sum := by decide
  have hdescent : baseEnd_3139092 < baseStart_3139092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139121 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 7]
def baseStart_3139121 : Nat := 118140960795 + 3139121 * 2 ^ 59
def prefixEnd_3139121 : Nat := 4983230072969 + 3 ^ 40 * 3139121 * 2
def baseEnd_3139121 : Nat := 179097545069168656483439

theorem tailTrace_3139121 : CollatzResearch.WordTrace tailWord_3139121 prefixEnd_3139121 179097545069168656483439 := by
  unfold tailWord_3139121
  simp only [CollatzResearch.WordTrace]
  refine ⟨114493148860508211029281217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76328765907005474019520811 114493148860508211029281217)
  ·
    refine ⟨85869861645381158271960913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114493148860508211029281217 85869861645381158271960913)
    ·
      refine ⟨64402396234035868703970685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85869861645381158271960913 64402396234035868703970685)
      ·
        refine ⟨24150898587763450763989007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64402396234035868703970685 24150898587763450763989007)
        ·
          refine ⟨36226347881645176145983511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24150898587763450763989007 36226347881645176145983511)
          ·
            refine ⟨54339521822467764218975267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36226347881645176145983511 54339521822467764218975267)
            ·
              refine ⟨81509282733701646328462901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54339521822467764218975267 81509282733701646328462901)
              ·
                refine ⟨7641495256284529343293397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81509282733701646328462901 7641495256284529343293397)
                ·
                  refine ⟨179097545069168656483439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7641495256284529343293397 179097545069168656483439)
                  ·
                    rfl

theorem cell23_3139121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 7].length) (baseStart_3139121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139121 prefixEnd_3139121 := by exact prefixLift 3139121
  have htrace : WordTrace (prefixWord ++ tailWord_3139121) baseStart_3139121 baseEnd_3139121 := by
    simpa [prefixWord, tailWord_3139121, baseEnd_3139121] using wordTrace_append hprefix tailTrace_3139121
  have hstable : (prefixWord ++ tailWord_3139121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139121).length < 2 ^ (prefixWord ++ tailWord_3139121).sum := by decide
  have hdescent : baseEnd_3139121 < baseStart_3139121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139128 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_3139128 : Nat := 118140960795 + 3139128 * 2 ^ 59
def prefixEnd_3139128 : Nat := 4983230072969 + 3 ^ 40 * 3139128 * 2
def baseEnd_3139128 : Nat := 1611881499987099380963419

theorem tailTrace_3139128 : CollatzResearch.WordTrace tailWord_3139128 prefixEnd_3139128 1611881499987099380963419 := by
  unfold tailWord_3139128
  simp only [CollatzResearch.WordTrace]
  refine ⟨57246702085741425612393019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76328936114321900816524025 57246702085741425612393019)
  ·
    refine ⟨85870053128612138418589529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57246702085741425612393019 85870053128612138418589529)
    ·
      refine ⟨64402539846459103813942147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85870053128612138418589529 64402539846459103813942147)
      ·
        refine ⟨96603809769688655720913221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64402539846459103813942147 96603809769688655720913221)
        ·
          refine ⟨18113214331816622947671229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96603809769688655720913221 18113214331816622947671229)
          ·
            refine ⟨6792455374431233605376711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18113214331816622947671229 6792455374431233605376711)
            ·
              refine ⟨10188683061646850408065067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792455374431233605376711 10188683061646850408065067)
              ·
                refine ⟨15283024592470275612097601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10188683061646850408065067 15283024592470275612097601)
                ·
                  refine ⟨11462268444352706709073201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15283024592470275612097601 11462268444352706709073201)
                  ·
                    refine ⟨8596701333264530031804901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11462268444352706709073201 8596701333264530031804901)
                    ·
                      refine ⟨1611881499987099380963419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8596701333264530031804901 1611881499987099380963419)
                      ·
                        rfl

theorem cell23_3139128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_3139128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139128 prefixEnd_3139128 := by exact prefixLift 3139128
  have htrace : WordTrace (prefixWord ++ tailWord_3139128) baseStart_3139128 baseEnd_3139128 := by
    simpa [prefixWord, tailWord_3139128, baseEnd_3139128] using wordTrace_append hprefix tailTrace_3139128
  have hstable : (prefixWord ++ tailWord_3139128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139128).length < 2 ^ (prefixWord ++ tailWord_3139128).sum := by decide
  have hdescent : baseEnd_3139128 < baseStart_3139128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139132 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_3139132 : Nat := 118140960795 + 3139132 * 2 ^ 59
def prefixEnd_3139132 : Nat := 4983230072969 + 3 ^ 40 * 3139132 * 2
def baseEnd_3139132 : Nat := 1611883553909717365313401

theorem tailTrace_3139132 : CollatzResearch.WordTrace tailWord_3139132 prefixEnd_3139132 1611883553909717365313401 := by
  unfold tailWord_3139132
  simp only [CollatzResearch.WordTrace]
  refine ⟨57246775031734179953965825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76329033375645573271954433 57246775031734179953965825)
  ·
    refine ⟨42935081273800634965474369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57246775031734179953965825 42935081273800634965474369)
    ·
      refine ⟨32201310955350476224105777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42935081273800634965474369 32201310955350476224105777)
      ·
        refine ⟨24150983216512857168079333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32201310955350476224105777 24150983216512857168079333)
        ·
          refine ⟨4528309353096160719014875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24150983216512857168079333 4528309353096160719014875)
          ·
            refine ⟨6792464029644241078522313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528309353096160719014875 6792464029644241078522313)
            ·
              refine ⟨5094348022233180808891735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6792464029644241078522313 5094348022233180808891735)
              ·
                refine ⟨7641522033349771213337603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5094348022233180808891735 7641522033349771213337603)
                ·
                  refine ⟨11462283050024656820006405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7641522033349771213337603 11462283050024656820006405)
                  ·
                    refine ⟨2149178071879623153751201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11462283050024656820006405 2149178071879623153751201)
                    ·
                      refine ⟨1611883553909717365313401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149178071879623153751201 1611883553909717365313401)
                      ·
                        rfl

theorem cell23_3139132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_3139132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139132 prefixEnd_3139132 := by exact prefixLift 3139132
  have htrace : WordTrace (prefixWord ++ tailWord_3139132) baseStart_3139132 baseEnd_3139132 := by
    simpa [prefixWord, tailWord_3139132, baseEnd_3139132] using wordTrace_append hprefix tailTrace_3139132
  have hstable : (prefixWord ++ tailWord_3139132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139132).length < 2 ^ (prefixWord ++ tailWord_3139132).sum := by decide
  have hdescent : baseEnd_3139132 < baseStart_3139132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139161 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_3139161 : Nat := 118140960795 + 3139161 * 2 ^ 59
def prefixEnd_3139161 : Nat := 4983230072969 + 3 ^ 40 * 3139161 * 2
def baseEnd_3139161 : Nat := 1611898444848697751850767

theorem tailTrace_3139161 : CollatzResearch.WordTrace tailWord_3139161 prefixEnd_3139161 1611898444848697751850767 := by
  unfold tailWord_3139161
  simp only [CollatzResearch.WordTrace]
  refine ⟨114494607780363297860737337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76329738520242198573824891 114494607780363297860737337)
  ·
    refine ⟨85870955835272473395553003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114494607780363297860737337 85870955835272473395553003)
    ·
      refine ⟨128806433752908710093329505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85870955835272473395553003 128806433752908710093329505)
      ·
        refine ⟨96604825314681532569997129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128806433752908710093329505 96604825314681532569997129)
        ·
          refine ⟨72453618986011149427497847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96604825314681532569997129 72453618986011149427497847)
          ·
            refine ⟨108680428479016724141246771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72453618986011149427497847 108680428479016724141246771)
            ·
              refine ⟨163020642718525086211870157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108680428479016724141246771 163020642718525086211870157)
              ·
                refine ⟨61132741019446907329451309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163020642718525086211870157 61132741019446907329451309)
                ·
                  refine ⟨22924777882292590248544241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61132741019446907329451309 22924777882292590248544241)
                  ·
                    refine ⟨17193583411719442686408181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22924777882292590248544241 17193583411719442686408181)
                    ·
                      refine ⟨1611898444848697751850767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17193583411719442686408181 1611898444848697751850767)
                      ·
                        rfl

theorem cell23_3139161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_3139161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139161 prefixEnd_3139161 := by exact prefixLift 3139161
  have htrace : WordTrace (prefixWord ++ tailWord_3139161) baseStart_3139161 baseEnd_3139161 := by
    simpa [prefixWord, tailWord_3139161, baseEnd_3139161] using wordTrace_append hprefix tailTrace_3139161
  have hstable : (prefixWord ++ tailWord_3139161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139161).length < 2 ^ (prefixWord ++ tailWord_3139161).sum := by decide
  have hdescent : baseEnd_3139161 < baseStart_3139161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139211 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 10]
def baseStart_3139211 : Nat := 118140960795 + 3139211 * 2 ^ 59
def prefixEnd_3139211 : Nat := 4983230072969 + 3 ^ 40 * 3139211 * 2
def baseEnd_3139211 : Nat := 179102679875713617358393

theorem tailTrace_3139211 : CollatzResearch.WordTrace tailWord_3139211 prefixEnd_3139211 179102679875713617358393 := by
  unfold tailWord_3139211
  simp only [CollatzResearch.WordTrace]
  refine ⟨114496431430182156400057487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76330954286788104266704991 114496431430182156400057487)
  ·
    refine ⟨171744647145273234600086231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114496431430182156400057487 171744647145273234600086231)
    ·
      refine ⟨257616970717909851900129347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171744647145273234600086231 257616970717909851900129347)
      ·
        refine ⟨386425456076864777850194021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257616970717909851900129347 386425456076864777850194021)
        ·
          refine ⟨72454773014412145846911379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386425456076864777850194021 72454773014412145846911379)
          ·
            refine ⟨108682159521618218770367069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72454773014412145846911379 108682159521618218770367069)
            ·
              refine ⟨40755809820606832038887651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108682159521618218770367069 40755809820606832038887651)
              ·
                refine ⟨61133714730910248058331477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40755809820606832038887651 61133714730910248058331477)
                ·
                  refine ⟨179102679875713617358393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 61133714730910248058331477 179102679875713617358393)
                  ·
                    rfl

theorem cell23_3139211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 10].length) (baseStart_3139211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139211 prefixEnd_3139211 := by exact prefixLift 3139211
  have htrace : WordTrace (prefixWord ++ tailWord_3139211) baseStart_3139211 baseEnd_3139211 := by
    simpa [prefixWord, tailWord_3139211, baseEnd_3139211] using wordTrace_append hprefix tailTrace_3139211
  have hstable : (prefixWord ++ tailWord_3139211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139211).length < 2 ^ (prefixWord ++ tailWord_3139211).sum := by decide
  have hdescent : baseEnd_3139211 < baseStart_3139211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139232 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 3, 4]
def baseStart_3139232 : Nat := 118140960795 + 3139232 * 2 ^ 59
def prefixEnd_3139232 : Nat := 4983230072969 + 3 ^ 40 * 3139232 * 2
def baseEnd_3139232 : Nat := 537311633991722324687647

theorem tailTrace_3139232 : CollatzResearch.WordTrace tailWord_3139232 prefixEnd_3139232 537311633991722324687647 := by
  unfold tailWord_3139232
  simp only [CollatzResearch.WordTrace]
  refine ⟨57248598681553038493285975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76331464908737384657714633 57248598681553038493285975)
  ·
    refine ⟨85872898022329557739928963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57248598681553038493285975 85872898022329557739928963)
    ·
      refine ⟨128809347033494336609893445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85872898022329557739928963 128809347033494336609893445)
      ·
        refine ⟨24151752568780188114355021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128809347033494336609893445 24151752568780188114355021)
        ·
          refine ⟨9056907213292570542883133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24151752568780188114355021 9056907213292570542883133)
          ·
            refine ⟨3396340204984713953581175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9056907213292570542883133 3396340204984713953581175)
            ·
              refine ⟨5094510307477070930371763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396340204984713953581175 5094510307477070930371763)
              ·
                refine ⟨7641765461215606395557645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5094510307477070930371763 7641765461215606395557645)
                ·
                  refine ⟨2865662047955852398334117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7641765461215606395557645 2865662047955852398334117)
                  ·
                    refine ⟨537311633991722324687647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2865662047955852398334117 537311633991722324687647)
                    ·
                      rfl

theorem cell23_3139232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 4].length) (baseStart_3139232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139232 prefixEnd_3139232 := by exact prefixLift 3139232
  have htrace : WordTrace (prefixWord ++ tailWord_3139232) baseStart_3139232 baseEnd_3139232 := by
    simpa [prefixWord, tailWord_3139232, baseEnd_3139232] using wordTrace_append hprefix tailTrace_3139232
  have hstable : (prefixWord ++ tailWord_3139232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139232).length < 2 ^ (prefixWord ++ tailWord_3139232).sum := by decide
  have hdescent : baseEnd_3139232 < baseStart_3139232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139245 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 6]
def baseStart_3139245 : Nat := 118140960795 + 3139245 * 2 ^ 59
def prefixEnd_3139245 : Nat := 4983230072969 + 3 ^ 40 * 3139245 * 2
def baseEnd_3139245 : Nat := 179104619691519491466709

theorem tailTrace_3139245 : CollatzResearch.WordTrace tailWord_3139245 prefixEnd_3139245 179104619691519491466709 := by
  unfold tailWord_3139245
  simp only [CollatzResearch.WordTrace]
  refine ⟨114497671512058980206795189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76331781008039320137863459 114497671512058980206795189)
  ·
    refine ⟨10734156704255529394387049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114497671512058980206795189 10734156704255529394387049)
    ·
      refine ⟨8050617528191647045790287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10734156704255529394387049 8050617528191647045790287)
      ·
        refine ⟨12075926292287470568685431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050617528191647045790287 12075926292287470568685431)
        ·
          refine ⟨18113889438431205853028147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12075926292287470568685431 18113889438431205853028147)
          ·
            refine ⟨27170834157646808779542221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18113889438431205853028147 27170834157646808779542221)
            ·
              refine ⟨10189062809117553292328333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27170834157646808779542221 10189062809117553292328333)
              ·
                refine ⟨3820898553419082484623125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10189062809117553292328333 3820898553419082484623125)
                ·
                  refine ⟨179104619691519491466709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3820898553419082484623125 179104619691519491466709)
                  ·
                    rfl

theorem cell23_3139245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_3139245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139245 prefixEnd_3139245 := by exact prefixLift 3139245
  have htrace : WordTrace (prefixWord ++ tailWord_3139245) baseStart_3139245 baseEnd_3139245 := by
    simpa [prefixWord, tailWord_3139245, baseEnd_3139245] using wordTrace_append hprefix tailTrace_3139245
  have hstable : (prefixWord ++ tailWord_3139245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139245).length < 2 ^ (prefixWord ++ tailWord_3139245).sum := by decide
  have hdescent : baseEnd_3139245 < baseStart_3139245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139288 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 3, 6]
def baseStart_3139288 : Nat := 118140960795 + 3139288 * 2 ^ 59
def prefixEnd_3139288 : Nat := 4983230072969 + 3 ^ 40 * 3139288 * 2
def baseEnd_3139288 : Nat := 537321218963939584987561

theorem tailTrace_3139288 : CollatzResearch.WordTrace tailWord_3139288 prefixEnd_3139288 537321218963939584987561 := by
  unfold tailWord_3139288
  simp only [CollatzResearch.WordTrace]
  refine ⟨57249619925451599275305259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76332826567268799033740345 57249619925451599275305259)
  ·
    refine ⟨85874429888177398912957889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57249619925451599275305259 85874429888177398912957889)
    ·
      refine ⟨64405822416133049184718417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85874429888177398912957889 64405822416133049184718417)
      ·
        refine ⟨48304366812099786888538813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64405822416133049184718417 48304366812099786888538813)
        ·
          refine ⟨18114137554537420083202055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48304366812099786888538813 18114137554537420083202055)
          ·
            refine ⟨27171206331806130124803083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18114137554537420083202055 27171206331806130124803083)
            ·
              refine ⟨40756809497709195187204625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27171206331806130124803083 40756809497709195187204625)
              ·
                refine ⟨30567607123281896390403469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40756809497709195187204625 30567607123281896390403469)
                ·
                  refine ⟨11462852671230711146401301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30567607123281896390403469 11462852671230711146401301)
                  ·
                    refine ⟨537321218963939584987561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11462852671230711146401301 537321218963939584987561)
                    ·
                      rfl

theorem cell23_3139288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_3139288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139288 prefixEnd_3139288 := by exact prefixLift 3139288
  have htrace : WordTrace (prefixWord ++ tailWord_3139288) baseStart_3139288 baseEnd_3139288 := by
    simpa [prefixWord, tailWord_3139288, baseEnd_3139288] using wordTrace_append hprefix tailTrace_3139288
  have hstable : (prefixWord ++ tailWord_3139288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139288).length < 2 ^ (prefixWord ++ tailWord_3139288).sum := by decide
  have hdescent : baseEnd_3139288 < baseStart_3139288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139289 : List Nat := [1, 2, 1, 2, 3, 4, 1, 4, 1, 1, 3]
def baseStart_3139289 : Nat := 118140960795 + 3139289 * 2 ^ 59
def prefixEnd_3139289 : Nat := 4983230072969 + 3 ^ 40 * 3139289 * 2
def baseEnd_3139289 : Nat := 1611964170372473251050179

theorem tailTrace_3139289 : CollatzResearch.WordTrace tailWord_3139289 prefixEnd_3139289 1611964170372473251050179 := by
  unfold tailWord_3139289
  simp only [CollatzResearch.WordTrace]
  refine ⟨114499276323899575721396921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76332850882599717147597947 114499276323899575721396921)
  ·
    refine ⟨85874457242924681791047691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114499276323899575721396921 85874457242924681791047691)
    ·
      refine ⟨128811685864387022686571537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85874457242924681791047691 128811685864387022686571537)
      ·
        refine ⟨96608764398290267014928653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128811685864387022686571537 96608764398290267014928653)
        ·
          refine ⟨36228286649358850130598245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96608764398290267014928653 36228286649358850130598245)
          ·
            refine ⟨6792803746754784399487171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36228286649358850130598245 6792803746754784399487171)
            ·
              refine ⟨10189205620132176599230757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792803746754784399487171 10189205620132176599230757)
              ·
                refine ⟨1910476053774783112355767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10189205620132176599230757 1910476053774783112355767)
                ·
                  refine ⟨2865714080662174668533651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910476053774783112355767 2865714080662174668533651)
                  ·
                    refine ⟨4298571120993262002800477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2865714080662174668533651 4298571120993262002800477)
                    ·
                      refine ⟨1611964170372473251050179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4298571120993262002800477 1611964170372473251050179)
                      ·
                        rfl

theorem cell23_3139289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_3139289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139289 prefixEnd_3139289 := by exact prefixLift 3139289
  have htrace : WordTrace (prefixWord ++ tailWord_3139289) baseStart_3139289 baseEnd_3139289 := by
    simpa [prefixWord, tailWord_3139289, baseEnd_3139289] using wordTrace_append hprefix tailTrace_3139289
  have hstable : (prefixWord ++ tailWord_3139289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139289).length < 2 ^ (prefixWord ++ tailWord_3139289).sum := by decide
  have hdescent : baseEnd_3139289 < baseStart_3139289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139308 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_3139308 : Nat := 118140960795 + 3139308 * 2 ^ 59
def prefixEnd_3139308 : Nat := 4983230072969 + 3 ^ 40 * 3139308 * 2
def baseEnd_3139308 : Nat := 1611973926504908676712591

theorem tailTrace_3139308 : CollatzResearch.WordTrace tailWord_3139308 prefixEnd_3139308 1611973926504908676712591 := by
  unfold tailWord_3139308
  simp only [CollatzResearch.WordTrace]
  refine ⟨57249984655415370983169289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76333312873887161310892385 57249984655415370983169289)
  ·
    refine ⟨42937488491561528237376967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57249984655415370983169289 42937488491561528237376967)
    ·
      refine ⟨64406232737342292356065451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42937488491561528237376967 64406232737342292356065451)
      ·
        refine ⟨96609349106013438534098177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64406232737342292356065451 96609349106013438534098177)
        ·
          refine ⟨72457011829510078900573633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96609349106013438534098177 72457011829510078900573633)
          ·
            refine ⟨54342758872132559175430225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72457011829510078900573633 54342758872132559175430225)
            ·
              refine ⟨40757069154099419381572669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54342758872132559175430225 40757069154099419381572669)
              ·
                refine ⟨15283900932787282268089751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40757069154099419381572669 15283900932787282268089751)
                ·
                  refine ⟨22925851399180923402134627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15283900932787282268089751 22925851399180923402134627)
                  ·
                    refine ⟨34388777098771385103201941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22925851399180923402134627 34388777098771385103201941)
                    ·
                      refine ⟨1611973926504908676712591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34388777098771385103201941 1611973926504908676712591)
                      ·
                        rfl

theorem cell23_3139308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_3139308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139308 prefixEnd_3139308 := by exact prefixLift 3139308
  have htrace : WordTrace (prefixWord ++ tailWord_3139308) baseStart_3139308 baseEnd_3139308 := by
    simpa [prefixWord, tailWord_3139308, baseEnd_3139308] using wordTrace_append hprefix tailTrace_3139308
  have hstable : (prefixWord ++ tailWord_3139308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139308).length < 2 ^ (prefixWord ++ tailWord_3139308).sum := by decide
  have hdescent : baseEnd_3139308 < baseStart_3139308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139315 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 3]
def baseStart_3139315 : Nat := 118140960795 + 3139315 * 2 ^ 59
def prefixEnd_3139315 : Nat := 4983230072969 + 3 ^ 40 * 3139315 * 2
def baseEnd_3139315 : Nat := 1611977520869490149325059

theorem tailTrace_3139315 : CollatzResearch.WordTrace tailWord_3139315 prefixEnd_3139315 1611977520869490149325059 := by
  unfold tailWord_3139315
  simp only [CollatzResearch.WordTrace]
  refine ⟨114500224621805382161843399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76333483081203588107895599 114500224621805382161843399)
  ·
    refine ⟨171750336932708073242765099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114500224621805382161843399 171750336932708073242765099)
    ·
      refine ⟨257625505399062109864147649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171750336932708073242765099 257625505399062109864147649)
      ·
        refine ⟨193219129049296582398110737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257625505399062109864147649 193219129049296582398110737)
        ·
          refine ⟨144914346786972436798583053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193219129049296582398110737 144914346786972436798583053)
          ·
            refine ⟨54342880045114663799468645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144914346786972436798583053 54342880045114663799468645)
            ·
              refine ⟨10189290008458999462400371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54342880045114663799468645 10189290008458999462400371)
              ·
                refine ⟨15283935012688499193600557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189290008458999462400371 15283935012688499193600557)
                ·
                  refine ⟨5731475629758187197600209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15283935012688499193600557 5731475629758187197600209)
                  ·
                    refine ⟨4298606722318640398200157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5731475629758187197600209 4298606722318640398200157)
                    ·
                      refine ⟨1611977520869490149325059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4298606722318640398200157 1611977520869490149325059)
                      ·
                        rfl

theorem cell23_3139315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 3].length) (baseStart_3139315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139315 prefixEnd_3139315 := by exact prefixLift 3139315
  have htrace : WordTrace (prefixWord ++ tailWord_3139315) baseStart_3139315 baseEnd_3139315 := by
    simpa [prefixWord, tailWord_3139315, baseEnd_3139315] using wordTrace_append hprefix tailTrace_3139315
  have hstable : (prefixWord ++ tailWord_3139315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139315).length < 2 ^ (prefixWord ++ tailWord_3139315).sum := by decide
  have hdescent : baseEnd_3139315 < baseStart_3139315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139316 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3139316 : Nat := 118140960795 + 3139316 * 2 ^ 59
def prefixEnd_3139316 : Nat := 4983230072969 + 3 ^ 40 * 3139316 * 2
def baseEnd_3139316 : Nat := 1611978034350144645412555

theorem tailTrace_3139316 : CollatzResearch.WordTrace tailWord_3139316 prefixEnd_3139316 1611978034350144645412555 := by
  unfold tailWord_3139316
  simp only [CollatzResearch.WordTrace]
  refine ⟨57250130547400879666314901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76333507396534506221753201 57250130547400879666314901)
  ·
    refine ⟨2683599869409416234358511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57250130547400879666314901 2683599869409416234358511)
    ·
      refine ⟨4025399804114124351537767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683599869409416234358511 4025399804114124351537767)
      ·
        refine ⟨6038099706171186527306651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025399804114124351537767 6038099706171186527306651)
        ·
          refine ⟨9057149559256779790959977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038099706171186527306651 9057149559256779790959977)
          ·
            refine ⟨6792862169442584843219983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9057149559256779790959977 6792862169442584843219983)
            ·
              refine ⟨10189293254163877264829975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792862169442584843219983 10189293254163877264829975)
              ·
                refine ⟨15283939881245815897244963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189293254163877264829975 15283939881245815897244963)
                ·
                  refine ⟨22925909821868723845867445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15283939881245815897244963 22925909821868723845867445)
                  ·
                    refine ⟨2149304045800192860550073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22925909821868723845867445 2149304045800192860550073)
                    ·
                      refine ⟨1611978034350144645412555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149304045800192860550073 1611978034350144645412555)
                      ·
                        rfl

theorem cell23_3139316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3139316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139316 prefixEnd_3139316 := by exact prefixLift 3139316
  have htrace : WordTrace (prefixWord ++ tailWord_3139316) baseStart_3139316 baseEnd_3139316 := by
    simpa [prefixWord, tailWord_3139316, baseEnd_3139316] using wordTrace_append hprefix tailTrace_3139316
  have hstable : (prefixWord ++ tailWord_3139316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139316).length < 2 ^ (prefixWord ++ tailWord_3139316).sum := by decide
  have hdescent : baseEnd_3139316 < baseStart_3139316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139326 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_3139326 : Nat := 118140960795 + 3139326 * 2 ^ 59
def prefixEnd_3139326 : Nat := 4983230072969 + 3 ^ 40 * 3139326 * 2
def baseEnd_3139326 : Nat := 537327723052229868762503

theorem tailTrace_3139326 : CollatzResearch.WordTrace tailWord_3139326 prefixEnd_3139326 537327723052229868762503 := by
  unfold tailWord_3139326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14312578228095691380061729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76333750549843687360329221 14312578228095691380061729)
  ·
    refine ⟨10734433671071768535046297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14312578228095691380061729 10734433671071768535046297)
    ·
      refine ⟨8050825253303826401284723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10734433671071768535046297 8050825253303826401284723)
      ·
        refine ⟨12076237879955739601927085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050825253303826401284723 12076237879955739601927085)
        ·
          refine ⟨4528589204983402350722657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12076237879955739601927085 4528589204983402350722657)
          ·
            refine ⟨3396441903737551763041993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4528589204983402350722657 3396441903737551763041993)
            ·
              refine ⟨2547331427803163822281495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396441903737551763041993 2547331427803163822281495)
              ·
                refine ⟨3820997141704745733422243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547331427803163822281495 3820997141704745733422243)
                ·
                  refine ⟨5731495712557118600133365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820997141704745733422243 5731495712557118600133365)
                  ·
                    refine ⟨537327723052229868762503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5731495712557118600133365 537327723052229868762503)
                    ·
                      rfl

theorem cell23_3139326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_3139326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139326 prefixEnd_3139326 := by exact prefixLift 3139326
  have htrace : WordTrace (prefixWord ++ tailWord_3139326) baseStart_3139326 baseEnd_3139326 := by
    simpa [prefixWord, tailWord_3139326, baseEnd_3139326] using wordTrace_append hprefix tailTrace_3139326
  have hstable : (prefixWord ++ tailWord_3139326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139326).length < 2 ^ (prefixWord ++ tailWord_3139326).sum := by decide
  have hdescent : baseEnd_3139326 < baseStart_3139326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139335 : List Nat := [1, 1, 4, 4, 2, 1, 10]
def baseStart_3139335 : Nat := 118140960795 + 3139335 * 2 ^ 59
def prefixEnd_3139335 : Nat := 4983230072969 + 3 ^ 40 * 3139335 * 2
def baseEnd_3139335 : Nat := 19901083833118272482407

theorem tailTrace_3139335 : CollatzResearch.WordTrace tailWord_3139335 prefixEnd_3139335 19901083833118272482407 := by
  unfold tailWord_3139335
  simp only [CollatzResearch.WordTrace]
  refine ⟨114500954081732925577571459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76333969387821950385047639 114500954081732925577571459)
  ·
    refine ⟨171751431122599388366357189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114500954081732925577571459 171751431122599388366357189)
    ·
      refine ⟨32203393335487385318691973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171751431122599388366357189 32203393335487385318691973)
      ·
        refine ⟨6038136250403884747254745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32203393335487385318691973 6038136250403884747254745)
        ·
          refine ⟨4528602187802913560441059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6038136250403884747254745 4528602187802913560441059)
          ·
            refine ⟨6792903281704370340661589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528602187802913560441059 6792903281704370340661589)
            ·
              refine ⟨19901083833118272482407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6792903281704370340661589 19901083833118272482407)
              ·
                rfl

theorem cell23_3139335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 10].length) (baseStart_3139335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139335 prefixEnd_3139335 := by exact prefixLift 3139335
  have htrace : WordTrace (prefixWord ++ tailWord_3139335) baseStart_3139335 baseEnd_3139335 := by
    simpa [prefixWord, tailWord_3139335, baseEnd_3139335] using wordTrace_append hprefix tailTrace_3139335
  have hstable : (prefixWord ++ tailWord_3139335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139335).length < 2 ^ (prefixWord ++ tailWord_3139335).sum := by decide
  have hdescent : baseEnd_3139335 < baseStart_3139335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139346 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_3139346 : Nat := 118140960795 + 3139346 * 2 ^ 59
def prefixEnd_3139346 : Nat := 4983230072969 + 3 ^ 40 * 3139346 * 2
def baseEnd_3139346 : Nat := 1611993438769779528037417

theorem tailTrace_3139346 : CollatzResearch.WordTrace tailWord_3139346 prefixEnd_3139346 1611993438769779528037417 := by
  unfold tailWord_3139346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28625338821173268614055473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76334236856462049637481261 28625338821173268614055473)
  ·
    refine ⟨21469004115879951460541605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28625338821173268614055473 21469004115879951460541605)
    ·
      refine ⟨4025438271727490898851551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21469004115879951460541605 4025438271727490898851551)
      ·
        refine ⟨6038157407591236348277327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025438271727490898851551 6038157407591236348277327)
        ·
          refine ⟨9057236111386854522415991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038157407591236348277327 9057236111386854522415991)
          ·
            refine ⟨13585854167080281783623987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9057236111386854522415991 13585854167080281783623987)
            ·
              refine ⟨20378781250620422675435981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13585854167080281783623987 20378781250620422675435981)
              ·
                refine ⟨7642042968982658503288493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20378781250620422675435981 7642042968982658503288493)
                ·
                  refine ⟨2865766113368496938733185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7642042968982658503288493 2865766113368496938733185)
                  ·
                    refine ⟨2149324585026372704049889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2865766113368496938733185 2149324585026372704049889)
                    ·
                      refine ⟨1611993438769779528037417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149324585026372704049889 1611993438769779528037417)
                      ·
                        rfl

theorem cell23_3139346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_3139346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139346 prefixEnd_3139346 := by exact prefixLift 3139346
  have htrace : WordTrace (prefixWord ++ tailWord_3139346) baseStart_3139346 baseEnd_3139346 := by
    simpa [prefixWord, tailWord_3139346, baseEnd_3139346] using wordTrace_append hprefix tailTrace_3139346
  have hstable : (prefixWord ++ tailWord_3139346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139346).length < 2 ^ (prefixWord ++ tailWord_3139346).sum := by decide
  have hdescent : baseEnd_3139346 < baseStart_3139346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139380 : List Nat := [2, 5, 1, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_3139380 : Nat := 118140960795 + 3139380 * 2 ^ 59
def prefixEnd_3139380 : Nat := 4983230072969 + 3 ^ 40 * 3139380 * 2
def baseEnd_3139380 : Nat := 1612010897112032395012261

theorem tailTrace_3139380 : CollatzResearch.WordTrace tailWord_3139380 prefixEnd_3139380 1612010897112032395012261 := by
  unfold tailWord_3139380
  simp only [CollatzResearch.WordTrace]
  refine ⟨57251297683284949131479797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76335063577713265508639729 57251297683284949131479797)
  ·
    refine ⟨5367309157807963981076231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57251297683284949131479797 5367309157807963981076231)
    ·
      refine ⟨8050963736711945971614347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5367309157807963981076231 8050963736711945971614347)
      ·
        refine ⟨12076445605067918957421521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050963736711945971614347 12076445605067918957421521)
        ·
          refine ⟨9057334203800939218066141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12076445605067918957421521 9057334203800939218066141)
          ·
            refine ⟨3396500326425352206774803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9057334203800939218066141 3396500326425352206774803)
            ·
              refine ⟨5094750489638028310162205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396500326425352206774803 5094750489638028310162205)
              ·
                refine ⟨1910531433614260616310827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5094750489638028310162205 1910531433614260616310827)
                ·
                  refine ⟨2865797150421390924466241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910531433614260616310827 2865797150421390924466241)
                  ·
                    refine ⟨2149347862816043193349681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2865797150421390924466241 2149347862816043193349681)
                    ·
                      refine ⟨1612010897112032395012261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149347862816043193349681 1612010897112032395012261)
                      ·
                        rfl

theorem cell23_3139380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_3139380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139380 prefixEnd_3139380 := by exact prefixLift 3139380
  have htrace : WordTrace (prefixWord ++ tailWord_3139380) baseStart_3139380 baseEnd_3139380 := by
    simpa [prefixWord, tailWord_3139380, baseEnd_3139380] using wordTrace_append hprefix tailTrace_3139380
  have hstable : (prefixWord ++ tailWord_3139380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139380).length < 2 ^ (prefixWord ++ tailWord_3139380).sum := by decide
  have hdescent : baseEnd_3139380 < baseStart_3139380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139435 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 3]
def baseStart_3139435 : Nat := 118140960795 + 3139435 * 2 ^ 59
def prefixEnd_3139435 : Nat := 4983230072969 + 3 ^ 40 * 3139435 * 2
def baseEnd_3139435 : Nat := 1612039138548029679824507

theorem tailTrace_3139435 : CollatzResearch.WordTrace tailWord_3139435 prefixEnd_3139435 1612039138548029679824507 := by
  unfold tailWord_3139435
  simp only [CollatzResearch.WordTrace]
  refine ⟨114504601381370642656211759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76336400920913761770807839 114504601381370642656211759)
  ·
    refine ⟨171756902072055963984317639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114504601381370642656211759 171756902072055963984317639)
    ·
      refine ⟨257635353108083945976476459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171756902072055963984317639 257635353108083945976476459)
      ·
        refine ⟨386453029662125918964714689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257635353108083945976476459 386453029662125918964714689)
        ·
          refine ⟨289839772246594439223536017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386453029662125918964714689 289839772246594439223536017)
          ·
            refine ⟨217379829184945829417652013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289839772246594439223536017 217379829184945829417652013)
            ·
              refine ⟨81517435944354686031619505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217379829184945829417652013 81517435944354686031619505)
              ·
                refine ⟨61138076958266014523714629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81517435944354686031619505 61138076958266014523714629)
                ·
                  refine ⟨11463389429674877723196493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61138076958266014523714629 11463389429674877723196493)
                  ·
                    refine ⟨4298771036128079146198685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11463389429674877723196493 4298771036128079146198685)
                    ·
                      refine ⟨1612039138548029679824507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4298771036128079146198685 1612039138548029679824507)
                      ·
                        rfl

theorem cell23_3139435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 3].length) (baseStart_3139435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139435 prefixEnd_3139435 := by exact prefixLift 3139435
  have htrace : WordTrace (prefixWord ++ tailWord_3139435) baseStart_3139435 baseEnd_3139435 := by
    simpa [prefixWord, tailWord_3139435, baseEnd_3139435] using wordTrace_append hprefix tailTrace_3139435
  have hstable : (prefixWord ++ tailWord_3139435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139435).length < 2 ^ (prefixWord ++ tailWord_3139435).sum := by decide
  have hdescent : baseEnd_3139435 < baseStart_3139435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139442 : List Nat := [3, 2, 1, 2, 1, 1, 1, 7, 5]
def baseStart_3139442 : Nat := 118140960795 + 3139442 * 2 ^ 59
def prefixEnd_3139442 : Nat := 4983230072969 + 3 ^ 40 * 3139442 * 2
def baseEnd_3139442 : Nat := 179115859212512350270775

theorem tailTrace_3139442 : CollatzResearch.WordTrace tailWord_3139442 prefixEnd_3139442 179115859212512350270775 := by
  unfold tailWord_3139442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28626214173086320712929145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76336571128230188567811053 28626214173086320712929145)
  ·
    refine ⟨21469660629814740534696859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28626214173086320712929145 21469660629814740534696859)
    ·
      refine ⟨32204490944722110802045289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21469660629814740534696859 32204490944722110802045289)
      ·
        refine ⟨24153368208541583101533967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32204490944722110802045289 24153368208541583101533967)
        ·
          refine ⟨36230052312812374652300951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24153368208541583101533967 36230052312812374652300951)
          ·
            refine ⟨54345078469218561978451427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36230052312812374652300951 54345078469218561978451427)
            ·
              refine ⟨81517617703827842967677141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54345078469218561978451427 81517617703827842967677141)
              ·
                refine ⟨1910569164933465069554933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81517617703827842967677141 1910569164933465069554933)
                ·
                  refine ⟨179115859212512350270775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910569164933465069554933 179115859212512350270775)
                  ·
                    rfl

theorem cell23_3139442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_3139442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139442 prefixEnd_3139442 := by exact prefixLift 3139442
  have htrace : WordTrace (prefixWord ++ tailWord_3139442) baseStart_3139442 baseEnd_3139442 := by
    simpa [prefixWord, tailWord_3139442, baseEnd_3139442] using wordTrace_append hprefix tailTrace_3139442
  have hstable : (prefixWord ++ tailWord_3139442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139442).length < 2 ^ (prefixWord ++ tailWord_3139442).sum := by decide
  have hdescent : baseEnd_3139442 < baseStart_3139442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139459 : List Nat := [1, 1, 1, 3, 4, 2, 4, 2, 5]
def baseStart_3139459 : Nat := 118140960795 + 3139459 * 2 ^ 59
def prefixEnd_3139459 : Nat := 4983230072969 + 3 ^ 40 * 3139459 * 2
def baseEnd_3139459 : Nat := 179116829120415287324933

theorem tailTrace_3139459 : CollatzResearch.WordTrace tailWord_3139459 prefixEnd_3139459 179116829120415287324933 := by
  unfold tailWord_3139459
  simp only [CollatzResearch.WordTrace]
  refine ⟨114505476733283694755085431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76336984488855796503390287 114505476733283694755085431)
  ·
    refine ⟨171758215099925542132628147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114505476733283694755085431 171758215099925542132628147)
    ·
      refine ⟨257637322649888313198942221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171758215099925542132628147 257637322649888313198942221)
      ·
        refine ⟨96613995993708117449603333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257637322649888313198942221 96613995993708117449603333)
        ·
          refine ⟨18115124248820272021800625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96613995993708117449603333 18115124248820272021800625)
          ·
            refine ⟨13586343186615204016350469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18115124248820272021800625 13586343186615204016350469)
            ·
              refine ⟨2547439347490350753065713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13586343186615204016350469 2547439347490350753065713)
              ·
                refine ⟨1910579510617763064799285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2547439347490350753065713 1910579510617763064799285)
                ·
                  refine ⟨179116829120415287324933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910579510617763064799285 179116829120415287324933)
                  ·
                    rfl

theorem cell23_3139459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 5].length) (baseStart_3139459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139459 prefixEnd_3139459 := by exact prefixLift 3139459
  have htrace : WordTrace (prefixWord ++ tailWord_3139459) baseStart_3139459 baseEnd_3139459 := by
    simpa [prefixWord, tailWord_3139459, baseEnd_3139459] using wordTrace_append hprefix tailTrace_3139459
  have hstable : (prefixWord ++ tailWord_3139459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139459).length < 2 ^ (prefixWord ++ tailWord_3139459).sum := by decide
  have hdescent : baseEnd_3139459 < baseStart_3139459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139465 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_3139465 : Nat := 118140960795 + 3139465 * 2 ^ 59
def prefixEnd_3139465 : Nat := 4983230072969 + 3 ^ 40 * 3139465 * 2
def baseEnd_3139465 : Nat := 1612054542967664562449369

theorem tailTrace_3139465 : CollatzResearch.WordTrace tailWord_3139465 prefixEnd_3139465 1612054542967664562449369 := by
  unfold tailWord_3139465
  simp only [CollatzResearch.WordTrace]
  refine ⟨114505695571261957779803849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76337130380841305186535899 114505695571261957779803849)
  ·
    refine ⟨85879271678446468334852887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114505695571261957779803849 85879271678446468334852887)
    ·
      refine ⟨128818907517669702502279331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85879271678446468334852887 128818907517669702502279331)
      ·
        refine ⟨193228361276504553753418997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128818907517669702502279331 193228361276504553753418997)
        ·
          refine ⟨18115158869672301914383031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193228361276504553753418997 18115158869672301914383031)
          ·
            refine ⟨27172738304508452871574547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18115158869672301914383031 27172738304508452871574547)
            ·
              refine ⟨40759107456762679307361821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27172738304508452871574547 40759107456762679307361821)
              ·
                refine ⟨15284665296286004740260683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40759107456762679307361821 15284665296286004740260683)
                ·
                  refine ⟨22926997944429007110391025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15284665296286004740260683 22926997944429007110391025)
                  ·
                    refine ⟨17195248458321755332793269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22926997944429007110391025 17195248458321755332793269)
                    ·
                      refine ⟨1612054542967664562449369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17195248458321755332793269 1612054542967664562449369)
                      ·
                        rfl

theorem cell23_3139465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_3139465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139465 prefixEnd_3139465 := by exact prefixLift 3139465
  have htrace : WordTrace (prefixWord ++ tailWord_3139465) baseStart_3139465 baseEnd_3139465 := by
    simpa [prefixWord, tailWord_3139465, baseEnd_3139465] using wordTrace_append hprefix tailTrace_3139465
  have hstable : (prefixWord ++ tailWord_3139465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139465).length < 2 ^ (prefixWord ++ tailWord_3139465).sum := by decide
  have hdescent : baseEnd_3139465 < baseStart_3139465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139492 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_3139492 : Nat := 118140960795 + 3139492 * 2 ^ 59
def prefixEnd_3139492 : Nat := 4983230072969 + 3 ^ 40 * 3139492 * 2
def baseEnd_3139492 : Nat := 1612068406945335956811745

theorem tailTrace_3139492 : CollatzResearch.WordTrace tailWord_3139492 prefixEnd_3139492 1612068406945335956811745 := by
  unfold tailWord_3139492
  simp only [CollatzResearch.WordTrace]
  refine ⟨57253340171082070695518365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76337786894776094260691153 57253340171082070695518365)
  ·
    refine ⟨21470002564155776510819387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57253340171082070695518365 21470002564155776510819387)
    ·
      refine ⟨32205003846233664766229081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21470002564155776510819387 32205003846233664766229081)
      ·
        refine ⟨24153752884675248574671811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32205003846233664766229081 24153752884675248574671811)
        ·
          refine ⟨36230629327012872862007717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24153752884675248574671811 36230629327012872862007717)
          ·
            refine ⟨6793242998814913661626447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36230629327012872862007717 6793242998814913661626447)
            ·
              refine ⟨10189864498222370492439671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6793242998814913661626447 10189864498222370492439671)
              ·
                refine ⟨15284796747333555738659507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189864498222370492439671 15284796747333555738659507)
                ·
                  refine ⟨22927195121000333607989261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15284796747333555738659507 22927195121000333607989261)
                  ·
                    refine ⟨8597698170375125102995973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22927195121000333607989261 8597698170375125102995973)
                    ·
                      refine ⟨1612068406945335956811745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8597698170375125102995973 1612068406945335956811745)
                      ·
                        rfl

theorem cell23_3139492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_3139492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139492 prefixEnd_3139492 := by exact prefixLift 3139492
  have htrace : WordTrace (prefixWord ++ tailWord_3139492) baseStart_3139492 baseEnd_3139492 := by
    simpa [prefixWord, tailWord_3139492, baseEnd_3139492] using wordTrace_append hprefix tailTrace_3139492
  have hstable : (prefixWord ++ tailWord_3139492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139492).length < 2 ^ (prefixWord ++ tailWord_3139492).sum := by decide
  have hdescent : baseEnd_3139492 < baseStart_3139492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139509 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_3139509 : Nat := 118140960795 + 3139509 * 2 ^ 59
def prefixEnd_3139509 : Nat := 4983230072969 + 3 ^ 40 * 3139509 * 2
def baseEnd_3139509 : Nat := 1612077136116462390299167

theorem tailTrace_3139509 : CollatzResearch.WordTrace tailWord_3139509 prefixEnd_3139509 1612077136116462390299167 := by
  unfold tailWord_3139509
  simp only [CollatzResearch.WordTrace]
  refine ⟨114507300383102553294405581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76338200255401702196270387 114507300383102553294405581)
  ·
    refine ⟨42940237643663457485402093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114507300383102553294405581 42940237643663457485402093)
    ·
      refine ⟨16102589116373796557025785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42940237643663457485402093 16102589116373796557025785)
      ·
        refine ⟨12076941837280347417769339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16102589116373796557025785 12076941837280347417769339)
        ·
          refine ⟨18115412755920521126654009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12076941837280347417769339 18115412755920521126654009)
          ·
            refine ⟨13586559566940390844990507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18115412755920521126654009 13586559566940390844990507)
            ·
              refine ⟨20379839350410586267485761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13586559566940390844990507 20379839350410586267485761)
              ·
                refine ⟨15284879512807939700614321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20379839350410586267485761 15284879512807939700614321)
                ·
                  refine ⟨11463659634605954775460741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15284879512807939700614321 11463659634605954775460741)
                  ·
                    refine ⟨2149436181488616520398889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11463659634605954775460741 2149436181488616520398889)
                    ·
                      refine ⟨1612077136116462390299167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2149436181488616520398889 1612077136116462390299167)
                      ·
                        rfl

theorem cell23_3139509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_3139509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139509 prefixEnd_3139509 := by exact prefixLift 3139509
  have htrace : WordTrace (prefixWord ++ tailWord_3139509) baseStart_3139509 baseEnd_3139509 := by
    simpa [prefixWord, tailWord_3139509, baseEnd_3139509] using wordTrace_append hprefix tailTrace_3139509
  have hstable : (prefixWord ++ tailWord_3139509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139509).length < 2 ^ (prefixWord ++ tailWord_3139509).sum := by decide
  have hdescent : baseEnd_3139509 < baseStart_3139509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3139512 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_3139512 : Nat := 118140960795 + 3139512 * 2 ^ 59
def prefixEnd_3139512 : Nat := 4983230072969 + 3 ^ 40 * 3139512 * 2
def baseEnd_3139512 : Nat := 1612078676558425878561653

theorem tailTrace_3139512 : CollatzResearch.WordTrace tailWord_3139512 prefixEnd_3139512 1612078676558425878561653 := by
  unfold tailWord_3139512
  simp only [CollatzResearch.WordTrace]
  refine ⟨57253704901045842403382395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76338273201394456537843193 57253704901045842403382395)
  ·
    refine ⟨85880557351568763605073593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57253704901045842403382395 85880557351568763605073593)
    ·
      refine ⟨64410418013676572703805195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85880557351568763605073593 64410418013676572703805195)
      ·
        refine ⟨96615627020514859055707793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64410418013676572703805195 96615627020514859055707793)
        ·
          refine ⟨72461720265386144291780845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96615627020514859055707793 72461720265386144291780845)
          ·
            refine ⟨27173145099519804109417817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72461720265386144291780845 27173145099519804109417817)
            ·
              refine ⟨20379858824639853082063363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27173145099519804109417817 20379858824639853082063363)
              ·
                refine ⟨30569788236959779623095045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20379858824639853082063363 30569788236959779623095045)
                ·
                  refine ⟨5731835294429958679330321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30569788236959779623095045 5731835294429958679330321)
                  ·
                    refine ⟨4298876470822469009497741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5731835294429958679330321 4298876470822469009497741)
                    ·
                      refine ⟨1612078676558425878561653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4298876470822469009497741 1612078676558425878561653)
                      ·
                        rfl

theorem cell23_3139512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_3139512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3139512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3139512 prefixEnd_3139512 := by exact prefixLift 3139512
  have htrace : WordTrace (prefixWord ++ tailWord_3139512) baseStart_3139512 baseEnd_3139512 := by
    simpa [prefixWord, tailWord_3139512, baseEnd_3139512] using wordTrace_append hprefix tailTrace_3139512
  have hstable : (prefixWord ++ tailWord_3139512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3139512).length < 2 ^ (prefixWord ++ tailWord_3139512).sum := by decide
  have hdescent : baseEnd_3139512 < baseStart_3139512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3139512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
