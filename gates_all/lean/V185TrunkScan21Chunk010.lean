import V185TrunkScan21Chunk009

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_119870 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_119870 : Nat := 118140960795 + 119870 * 2 ^ 59
def prefixEnd_119870 : Nat := 4983230072969 + 3 ^ 40 * 119870 * 2
def baseEnd_119870 : Nat := 27355967135356107454993

theorem tailTrace_119870 : CollatzResearch.WordTrace tailWord_119870 prefixEnd_119870 27355967135356107454993 := by
  unfold tailWord_119870
  simp only [CollatzResearch.WordTrace]
  refine ⟨546502259467367126404633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2914678717159291340824709 546502259467367126404633)
  ·
    refine ⟨409876694600525344803475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 546502259467367126404633 409876694600525344803475)
    ·
      refine ⟨614815041900788017205213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409876694600525344803475 614815041900788017205213)
      ·
        refine ⟨230555640712795506451955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614815041900788017205213 230555640712795506451955)
        ·
          refine ⟨345833461069193259677933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230555640712795506451955 345833461069193259677933)
          ·
            refine ⟨129687547900947472379225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345833461069193259677933 129687547900947472379225)
            ·
              refine ⟨97265660925710604284419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129687547900947472379225 97265660925710604284419)
              ·
                refine ⟨145898491388565906426629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97265660925710604284419 145898491388565906426629)
                ·
                  refine ⟨27355967135356107454993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145898491388565906426629 27355967135356107454993)
                  ·
                    rfl

theorem cell21_119870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_119870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119870 prefixEnd_119870 := by exact prefixLift 119870
  have htrace : WordTrace (prefixWord ++ tailWord_119870) baseStart_119870 baseEnd_119870 := by
    simpa [prefixWord, tailWord_119870, baseEnd_119870] using wordTrace_append hprefix tailTrace_119870
  have hstable : (prefixWord ++ tailWord_119870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119870).length < 2 ^ (prefixWord ++ tailWord_119870).sum := by decide
  have hdescent : baseEnd_119870 < baseStart_119870 := by decide
  rcases family_descends (prefixWord ++ tailWord_119870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119923 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 11]
def baseStart_119923 : Nat := 118140960795 + 119923 * 2 ^ 59
def prefixEnd_119923 : Nat := 4983230072969 + 3 ^ 40 * 119923 * 2
def baseEnd_119923 : Nat := 27368062457439793071551

theorem tailTrace_119923 : CollatzResearch.WordTrace tailWord_119923 prefixEnd_119923 27368062457439793071551 := by
  unfold tailWord_119923
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373951144546927062916423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2915967429697951375277615 4373951144546927062916423)
  ·
    refine ⟨6560926716820390594374635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373951144546927062916423 6560926716820390594374635)
    ·
      refine ⟨9841390075230585891561953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6560926716820390594374635 9841390075230585891561953)
      ·
        refine ⟨7381042556422939418671465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9841390075230585891561953 7381042556422939418671465)
        ·
          refine ⟨5535781917317204564003599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7381042556422939418671465 5535781917317204564003599)
          ·
            refine ⟨8303672875975806846005399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535781917317204564003599 8303672875975806846005399)
            ·
              refine ⟨12455509313963710269008099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303672875975806846005399 12455509313963710269008099)
              ·
                refine ⟨18683263970945565403512149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12455509313963710269008099 18683263970945565403512149)
                ·
                  refine ⟨27368062457439793071551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 18683263970945565403512149 27368062457439793071551)
                  ·
                    rfl

theorem cell21_119923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_119923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119923 prefixEnd_119923 := by exact prefixLift 119923
  have htrace : WordTrace (prefixWord ++ tailWord_119923) baseStart_119923 baseEnd_119923 := by
    simpa [prefixWord, tailWord_119923, baseEnd_119923] using wordTrace_append hprefix tailTrace_119923
  have hstable : (prefixWord ++ tailWord_119923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119923).length < 2 ^ (prefixWord ++ tailWord_119923).sum := by decide
  have hdescent : baseEnd_119923 < baseStart_119923 := by decide
  rcases family_descends (prefixWord ++ tailWord_119923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119940 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_119940 : Nat := 118140960795 + 119940 * 2 ^ 59
def prefixEnd_119940 : Nat := 4983230072969 + 3 ^ 40 * 119940 * 2
def baseEnd_119940 : Nat := 27371942089051541288183

theorem tailTrace_119940 : CollatzResearch.WordTrace tailWord_119940 prefixEnd_119940 27371942089051541288183 := by
  unfold tailWord_119940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187285592742669483142637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2916380790323559310856849 2187285592742669483142637)
  ·
    refine ⟨820232097278501056178489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2187285592742669483142637 820232097278501056178489)
    ·
      refine ⟨615174072958875792133867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 820232097278501056178489 615174072958875792133867)
      ·
        refine ⟨922761109438313688200801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615174072958875792133867 922761109438313688200801)
        ·
          refine ⟨692070832078735266150601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922761109438313688200801 692070832078735266150601)
          ·
            refine ⟨519053124059051449612951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692070832078735266150601 519053124059051449612951)
            ·
              refine ⟨778579686088577174419427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519053124059051449612951 778579686088577174419427)
              ·
                refine ⟨1167869529132865761629141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 778579686088577174419427 1167869529132865761629141)
                ·
                  refine ⟨27371942089051541288183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1167869529132865761629141 27371942089051541288183)
                  ·
                    rfl

theorem cell21_119940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_119940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119940 prefixEnd_119940 := by exact prefixLift 119940
  have htrace : WordTrace (prefixWord ++ tailWord_119940) baseStart_119940 baseEnd_119940 := by
    simpa [prefixWord, tailWord_119940, baseEnd_119940] using wordTrace_append hprefix tailTrace_119940
  have hstable : (prefixWord ++ tailWord_119940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119940).length < 2 ^ (prefixWord ++ tailWord_119940).sum := by decide
  have hdescent : baseEnd_119940 < baseStart_119940 := by decide
  rcases family_descends (prefixWord ++ tailWord_119940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120033 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 5]
def baseStart_120033 : Nat := 118140960795 + 120033 * 2 ^ 59
def prefixEnd_120033 : Nat := 4983230072969 + 3 ^ 40 * 120033 * 2
def baseEnd_120033 : Nat := 27393165956104046237993

theorem tailTrace_120033 : CollatzResearch.WordTrace tailWord_120033 prefixEnd_120033 27393165956104046237993 := by
  unfold tailWord_120033
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377963174148415849420753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2918642116098943899613835 4377963174148415849420753)
  ·
    refine ⟨3283472380611311887065565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4377963174148415849420753 3283472380611311887065565)
    ·
      refine ⟨1231302142729241957649587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3283472380611311887065565 1231302142729241957649587)
      ·
        refine ⟨1846953214093862936474381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231302142729241957649587 1846953214093862936474381)
        ·
          refine ⟨692607455285198601177893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1846953214093862936474381 692607455285198601177893)
          ·
            refine ⟨129863897865974737720855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 692607455285198601177893 129863897865974737720855)
            ·
              refine ⟨194795846798962106581283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129863897865974737720855 194795846798962106581283)
              ·
                refine ⟨292193770198443159871925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194795846798962106581283 292193770198443159871925)
                ·
                  refine ⟨27393165956104046237993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292193770198443159871925 27393165956104046237993)
                  ·
                    rfl

theorem cell21_120033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_120033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120033 prefixEnd_120033 := by exact prefixLift 120033
  have htrace : WordTrace (prefixWord ++ tailWord_120033) baseStart_120033 baseEnd_120033 := by
    simpa [prefixWord, tailWord_120033, baseEnd_120033] using wordTrace_append hprefix tailTrace_120033
  have hstable : (prefixWord ++ tailWord_120033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120033).length < 2 ^ (prefixWord ++ tailWord_120033).sum := by decide
  have hdescent : baseEnd_120033 < baseStart_120033 := by decide
  rcases family_descends (prefixWord ++ tailWord_120033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120095 : List Nat := [1, 1, 2, 4, 5, 1, 1, 6]
def baseStart_120095 : Nat := 118140960795 + 120095 * 2 ^ 59
def prefixEnd_120095 : Nat := 4983230072969 + 3 ^ 40 * 120095 * 2
def baseEnd_120095 : Nat := 9135771733601905401511

theorem tailTrace_120095 : CollatzResearch.WordTrace tailWord_120095 prefixEnd_120095 9135771733601905401511 := by
  unfold tailWord_120095
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380224499923800438177739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2920149666615866958785159 4380224499923800438177739)
  ·
    refine ⟨6570336749885700657266609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4380224499923800438177739 6570336749885700657266609)
    ·
      refine ⟨4927752562414275492949957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6570336749885700657266609 4927752562414275492949957)
      ·
        refine ⟨923953605452676654928117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4927752562414275492949957 923953605452676654928117)
        ·
          refine ⟨86620650511188436399511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 923953605452676654928117 86620650511188436399511)
          ·
            refine ⟨129930975766782654599267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86620650511188436399511 129930975766782654599267)
            ·
              refine ⟨194896463650173981898901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129930975766782654599267 194896463650173981898901)
              ·
                refine ⟨9135771733601905401511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194896463650173981898901 9135771733601905401511)
                ·
                  rfl

theorem cell21_120095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 6].length) (baseStart_120095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120095 prefixEnd_120095 := by exact prefixLift 120095
  have htrace : WordTrace (prefixWord ++ tailWord_120095) baseStart_120095 baseEnd_120095 := by
    simpa [prefixWord, tailWord_120095, baseEnd_120095] using wordTrace_append hprefix tailTrace_120095
  have hstable : (prefixWord ++ tailWord_120095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120095).length < 2 ^ (prefixWord ++ tailWord_120095).sum := by decide
  have hdescent : baseEnd_120095 < baseStart_120095 := by decide
  rcases family_descends (prefixWord ++ tailWord_120095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120109 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 7]
def baseStart_120109 : Nat := 118140960795 + 120109 * 2 ^ 59
def prefixEnd_120109 : Nat := 4983230072969 + 3 ^ 40 * 120109 * 2
def baseEnd_120109 : Nat := 27410510191544802971171

theorem tailTrace_120109 : CollatzResearch.WordTrace tailWord_120109 prefixEnd_120109 27410510191544802971171 := by
  unfold tailWord_120109
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380735121873080829187381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2920490081248720552791587 4380735121873080829187381)
  ·
    refine ⟨410693917675601327736317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4380735121873080829187381 410693917675601327736317)
    ·
      refine ⟨154010219128350497901119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410693917675601327736317 154010219128350497901119)
      ·
        refine ⟨231015328692525746851679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154010219128350497901119 231015328692525746851679)
        ·
          refine ⟨346522993038788620277519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231015328692525746851679 346522993038788620277519)
          ·
            refine ⟨519784489558182930416279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346522993038788620277519 519784489558182930416279)
            ·
              refine ⟨779676734337274395624419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519784489558182930416279 779676734337274395624419)
              ·
                refine ⟨1169515101505911593436629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779676734337274395624419 1169515101505911593436629)
                ·
                  refine ⟨27410510191544802971171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1169515101505911593436629 27410510191544802971171)
                  ·
                    rfl

theorem cell21_120109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_120109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120109 prefixEnd_120109 := by exact prefixLift 120109
  have htrace : WordTrace (prefixWord ++ tailWord_120109) baseStart_120109 baseEnd_120109 := by
    simpa [prefixWord, tailWord_120109, baseEnd_120109] using wordTrace_append hprefix tailTrace_120109
  have hstable : (prefixWord ++ tailWord_120109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120109).length < 2 ^ (prefixWord ++ tailWord_120109).sum := by decide
  have hdescent : baseEnd_120109 < baseStart_120109 := by decide
  rcases family_descends (prefixWord ++ tailWord_120109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120126 : List Nat := [4, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_120126 : Nat := 118140960795 + 120126 * 2 ^ 59
def prefixEnd_120126 : Nat := 4983230072969 + 3 ^ 40 * 120126 * 2
def baseEnd_120126 : Nat := 27414389823156551187803

theorem tailTrace_120126 : CollatzResearch.WordTrace tailWord_120126 prefixEnd_120126 27414389823156551187803 := by
  unfold tailWord_120126
  simp only [CollatzResearch.WordTrace]
  refine ⟨547669395351436591569529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2920903441874328488370821 547669395351436591569529)
  ·
    refine ⟨410752046513577443677147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 547669395351436591569529 410752046513577443677147)
    ·
      refine ⟨616128069770366165515721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410752046513577443677147 616128069770366165515721)
      ·
        refine ⟨462096052327774624136791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616128069770366165515721 462096052327774624136791)
        ·
          refine ⟨693144078491661936205187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462096052327774624136791 693144078491661936205187)
          ·
            refine ⟨1039716117737492904307781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693144078491661936205187 1039716117737492904307781)
            ·
              refine ⟨194946772075779919557709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1039716117737492904307781 194946772075779919557709)
              ·
                refine ⟨73105039528417469834141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194946772075779919557709 73105039528417469834141)
                ·
                  refine ⟨27414389823156551187803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73105039528417469834141 27414389823156551187803)
                  ·
                    rfl

theorem cell21_120126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_120126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120126 prefixEnd_120126 := by exact prefixLift 120126
  have htrace : WordTrace (prefixWord ++ tailWord_120126) baseStart_120126 baseEnd_120126 := by
    simpa [prefixWord, tailWord_120126, baseEnd_120126] using wordTrace_append hprefix tailTrace_120126
  have hstable : (prefixWord ++ tailWord_120126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120126).length < 2 ^ (prefixWord ++ tailWord_120126).sum := by decide
  have hdescent : baseEnd_120126 < baseStart_120126 := by decide
  rcases family_descends (prefixWord ++ tailWord_120126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120140 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_120140 : Nat := 118140960795 + 120140 * 2 ^ 59
def prefixEnd_120140 : Nat := 4983230072969 + 3 ^ 40 * 120140 * 2
def baseEnd_120140 : Nat := 27417584813895637954441

theorem tailTrace_120140 : CollatzResearch.WordTrace tailWord_120140 prefixEnd_120140 27417584813895637954441 := by
  unfold tailWord_120140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190932892380386561782937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2921243856507182082377249 2190932892380386561782937)
  ·
    refine ⟨1643199669285289921337203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2190932892380386561782937 1643199669285289921337203)
    ·
      refine ⟨2464799503927934882005805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643199669285289921337203 2464799503927934882005805)
      ·
        refine ⟨924299813972975580752177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2464799503927934882005805 924299813972975580752177)
        ·
          refine ⟨693224860479731685564133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924299813972975580752177 693224860479731685564133)
          ·
            refine ⟨129979661339949691043275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 693224860479731685564133 129979661339949691043275)
            ·
              refine ⟨194969492009924536564913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129979661339949691043275 194969492009924536564913)
              ·
                refine ⟨146227119007443402423685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194969492009924536564913 146227119007443402423685)
                ·
                  refine ⟨27417584813895637954441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146227119007443402423685 27417584813895637954441)
                  ·
                    rfl

theorem cell21_120140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_120140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120140 prefixEnd_120140 := by exact prefixLift 120140
  have htrace : WordTrace (prefixWord ++ tailWord_120140) baseStart_120140 baseEnd_120140 := by
    simpa [prefixWord, tailWord_120140, baseEnd_120140] using wordTrace_append hprefix tailTrace_120140
  have hstable : (prefixWord ++ tailWord_120140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120140).length < 2 ^ (prefixWord ++ tailWord_120140).sum := by decide
  have hdescent : baseEnd_120140 < baseStart_120140 := by decide
  rcases family_descends (prefixWord ++ tailWord_120140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120185 : List Nat := [1, 2, 1, 3, 2, 1, 5, 3, 3]
def baseStart_120185 : Nat := 118140960795 + 120185 * 2 ^ 59
def prefixEnd_120185 : Nat := 4983230072969 + 3 ^ 40 * 120185 * 2
def baseEnd_120185 : Nat := 27427854426985559704349

theorem tailTrace_120185 : CollatzResearch.WordTrace tailWord_120185 prefixEnd_120185 27427854426985559704349 := by
  unfold tailWord_120185
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383507069597745808954009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2922338046398497205969339 4383507069597745808954009)
  ·
    refine ⟨3287630302198309356715507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4383507069597745808954009 3287630302198309356715507)
    ·
      refine ⟨4931445453297464035073261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287630302198309356715507 4931445453297464035073261)
      ·
        refine ⟨1849292044986549013152473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4931445453297464035073261 1849292044986549013152473)
        ·
          refine ⟨1386969033739911759864355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1849292044986549013152473 1386969033739911759864355)
          ·
            refine ⟨2080453550609867639796533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386969033739911759864355 2080453550609867639796533)
            ·
              refine ⟨195042520369675091230925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2080453550609867639796533 195042520369675091230925)
              ·
                refine ⟨73140945138628159211597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195042520369675091230925 73140945138628159211597)
                ·
                  refine ⟨27427854426985559704349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73140945138628159211597 27427854426985559704349)
                  ·
                    rfl

theorem cell21_120185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_120185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120185 prefixEnd_120185 := by exact prefixLift 120185
  have htrace : WordTrace (prefixWord ++ tailWord_120185) baseStart_120185 baseEnd_120185 := by
    simpa [prefixWord, tailWord_120185, baseEnd_120185] using wordTrace_append hprefix tailTrace_120185
  have hstable : (prefixWord ++ tailWord_120185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120185).length < 2 ^ (prefixWord ++ tailWord_120185).sum := by decide
  have hdescent : baseEnd_120185 < baseStart_120185 := by decide
  rcases family_descends (prefixWord ++ tailWord_120185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120216 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_120216 : Nat := 118140960795 + 120216 * 2 ^ 59
def prefixEnd_120216 : Nat := 4983230072969 + 3 ^ 40 * 120216 * 2
def baseEnd_120216 : Nat := 27434929049336394687619

theorem tailTrace_120216 : CollatzResearch.WordTrace tailWord_120216 prefixEnd_120216 27434929049336394687619 := by
  unfold tailWord_120216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192318866242719051666251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2923091821656958735555001 2192318866242719051666251)
  ·
    refine ⟨3288478299364078577499377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2192318866242719051666251 3288478299364078577499377)
    ·
      refine ⟨2466358724523058933124533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3288478299364078577499377 2466358724523058933124533)
      ·
        refine ⟨231221130424036774980425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2466358724523058933124533 231221130424036774980425)
        ·
          refine ⟨173415847818027581235319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231221130424036774980425 173415847818027581235319)
          ·
            refine ⟨260123771727041371852979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173415847818027581235319 260123771727041371852979)
            ·
              refine ⟨390185657590562057779469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260123771727041371852979 390185657590562057779469)
              ·
                refine ⟨146319621596460771667301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390185657590562057779469 146319621596460771667301)
                ·
                  refine ⟨27434929049336394687619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146319621596460771667301 27434929049336394687619)
                  ·
                    rfl

theorem cell21_120216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_120216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120216 prefixEnd_120216 := by exact prefixLift 120216
  have htrace : WordTrace (prefixWord ++ tailWord_120216) baseStart_120216 baseEnd_120216 := by
    simpa [prefixWord, tailWord_120216, baseEnd_120216] using wordTrace_append hprefix tailTrace_120216
  have hstable : (prefixWord ++ tailWord_120216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120216).length < 2 ^ (prefixWord ++ tailWord_120216).sum := by decide
  have hdescent : baseEnd_120216 < baseStart_120216 := by decide
  rcases family_descends (prefixWord ++ tailWord_120216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120227 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 7]
def baseStart_120227 : Nat := 118140960795 + 120227 * 2 ^ 59
def prefixEnd_120227 : Nat := 4983230072969 + 3 ^ 40 * 120227 * 2
def baseEnd_120227 : Nat := 27437439399202820004263

theorem tailTrace_120227 : CollatzResearch.WordTrace tailWord_120227 prefixEnd_120227 27437439399202820004263 := by
  unfold tailWord_120227
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385038935445586981982935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2923359290297057987988623 4385038935445586981982935)
  ·
    refine ⟨6577558403168380472974403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4385038935445586981982935 6577558403168380472974403)
    ·
      refine ⟨9866337604752570709461605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6577558403168380472974403 9866337604752570709461605)
      ·
        refine ⟨1849938300891107008024051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9866337604752570709461605 1849938300891107008024051)
        ·
          refine ⟨2774907451336660512036077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849938300891107008024051 2774907451336660512036077)
          ·
            refine ⟨1040590294251247692013529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2774907451336660512036077 1040590294251247692013529)
            ·
              refine ⟨780442720688435769010147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040590294251247692013529 780442720688435769010147)
              ·
                refine ⟨1170664081032653653515221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780442720688435769010147 1170664081032653653515221)
                ·
                  refine ⟨27437439399202820004263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1170664081032653653515221 27437439399202820004263)
                  ·
                    rfl

theorem cell21_120227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_120227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120227 prefixEnd_120227 := by exact prefixLift 120227
  have htrace : WordTrace (prefixWord ++ tailWord_120227) baseStart_120227 baseEnd_120227 := by
    simpa [prefixWord, tailWord_120227, baseEnd_120227] using wordTrace_append hprefix tailTrace_120227
  have hstable : (prefixWord ++ tailWord_120227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120227).length < 2 ^ (prefixWord ++ tailWord_120227).sum := by decide
  have hdescent : baseEnd_120227 < baseStart_120227 := by decide
  rcases family_descends (prefixWord ++ tailWord_120227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120309 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 4]
def baseStart_120309 : Nat := 118140960795 + 120309 * 2 ^ 59
def prefixEnd_120309 : Nat := 4983230072969 + 3 ^ 40 * 120309 * 2
def baseEnd_120309 : Nat := 27456152916388899637429

theorem tailTrace_120309 : CollatzResearch.WordTrace tailWord_120309 prefixEnd_120309 27456152916388899637429 := by
  unfold tailWord_120309
  simp only [CollatzResearch.WordTrace]
  refine ⟨4388029721148514986467981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2925353147432343324311987 4388029721148514986467981)
  ·
    refine ⟨1645511145430693119925493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4388029721148514986467981 1645511145430693119925493)
    ·
      refine ⟨154266669884127479993015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1645511145430693119925493 154266669884127479993015)
      ·
        refine ⟨231400004826191219989523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154266669884127479993015 231400004826191219989523)
        ·
          refine ⟨347100007239286829984285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231400004826191219989523 347100007239286829984285)
          ·
            refine ⟨130162502714732561244107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347100007239286829984285 130162502714732561244107)
            ·
              refine ⟨195243754072098841866161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130162502714732561244107 195243754072098841866161)
              ·
                refine ⟨146432815554074131399621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195243754072098841866161 146432815554074131399621)
                ·
                  refine ⟨27456152916388899637429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146432815554074131399621 27456152916388899637429)
                  ·
                    rfl

theorem cell21_120309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_120309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120309 prefixEnd_120309 := by exact prefixLift 120309
  have htrace : WordTrace (prefixWord ++ tailWord_120309) baseStart_120309 baseEnd_120309 := by
    simpa [prefixWord, tailWord_120309, baseEnd_120309] using wordTrace_append hprefix tailTrace_120309
  have hstable : (prefixWord ++ tailWord_120309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120309).length < 2 ^ (prefixWord ++ tailWord_120309).sum := by decide
  have hdescent : baseEnd_120309 < baseStart_120309 := by decide
  rcases family_descends (prefixWord ++ tailWord_120309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120340 : List Nat := [2, 4, 3, 1, 2, 2, 2, 5]
def baseStart_120340 : Nat := 118140960795 + 120340 * 2 ^ 59
def prefixEnd_120340 : Nat := 4983230072969 + 3 ^ 40 * 120340 * 2
def baseEnd_120340 : Nat := 9154409179579911540233

theorem tailTrace_120340 : CollatzResearch.WordTrace tailWord_120340 prefixEnd_120340 9154409179579911540233 := by
  unfold tailWord_120340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194580192018103640423237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2926106922690804853897649 2194580192018103640423237)
  ·
    refine ⟨411483786003394432579357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2194580192018103640423237 411483786003394432579357)
    ·
      refine ⟨154306419751272912217259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411483786003394432579357 154306419751272912217259)
      ·
        refine ⟨231459629626909368325889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154306419751272912217259 231459629626909368325889)
        ·
          refine ⟨173594722220182026244417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231459629626909368325889 173594722220182026244417)
          ·
            refine ⟨130196041665136519683313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173594722220182026244417 130196041665136519683313)
            ·
              refine ⟨97647031248852389762485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130196041665136519683313 97647031248852389762485)
              ·
                refine ⟨9154409179579911540233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97647031248852389762485 9154409179579911540233)
                ·
                  rfl

theorem cell21_120340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_120340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120340 prefixEnd_120340 := by exact prefixLift 120340
  have htrace : WordTrace (prefixWord ++ tailWord_120340) baseStart_120340 baseEnd_120340 := by
    simpa [prefixWord, tailWord_120340, baseEnd_120340] using wordTrace_append hprefix tailTrace_120340
  have hstable : (prefixWord ++ tailWord_120340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120340).length < 2 ^ (prefixWord ++ tailWord_120340).sum := by decide
  have hdescent : baseEnd_120340 < baseStart_120340 := by decide
  rcases family_descends (prefixWord ++ tailWord_120340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120430 : List Nat := [4, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_120430 : Nat := 118140960795 + 120430 * 2 ^ 59
def prefixEnd_120430 : Nat := 4983230072969 + 3 ^ 40 * 120430 * 2
def baseEnd_120430 : Nat := 27483766764919578120515

theorem tailTrace_120430 : CollatzResearch.WordTrace tailWord_120430 prefixEnd_120430 27483766764919578120515 := by
  unfold tailWord_120430
  simp only [CollatzResearch.WordTrace]
  refine ⟨549055369213769081452843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2928295302473435101081829 549055369213769081452843)
  ·
    refine ⟨823583053820653622179265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 549055369213769081452843 823583053820653622179265)
    ·
      refine ⟨617687290365490216634449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 823583053820653622179265 617687290365490216634449)
      ·
        refine ⟨463265467774117662475837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617687290365490216634449 463265467774117662475837)
        ·
          refine ⟨173724550415294123428439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463265467774117662475837 173724550415294123428439)
          ·
            refine ⟨260586825622941185142659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173724550415294123428439 260586825622941185142659)
            ·
              refine ⟨390880238434411777713989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260586825622941185142659 390880238434411777713989)
              ·
                refine ⟨73290044706452208321373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390880238434411777713989 73290044706452208321373)
                ·
                  refine ⟨27483766764919578120515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73290044706452208321373 27483766764919578120515)
                  ·
                    rfl

theorem cell21_120430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_120430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120430 prefixEnd_120430 := by exact prefixLift 120430
  have htrace : WordTrace (prefixWord ++ tailWord_120430) baseStart_120430 baseEnd_120430 := by
    simpa [prefixWord, tailWord_120430, baseEnd_120430] using wordTrace_append hprefix tailTrace_120430
  have hstable : (prefixWord ++ tailWord_120430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120430).length < 2 ^ (prefixWord ++ tailWord_120430).sum := by decide
  have hdescent : baseEnd_120430 < baseStart_120430 := by decide
  rcases family_descends (prefixWord ++ tailWord_120430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120455 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 7]
def baseStart_120455 : Nat := 118140960795 + 120455 * 2 ^ 59
def prefixEnd_120455 : Nat := 4983230072969 + 3 ^ 40 * 120455 * 2
def baseEnd_120455 : Nat := 27489472105525090203797

theorem tailTrace_120455 : CollatzResearch.WordTrace tailWord_120455 prefixEnd_120455 27489472105525090203797 := by
  unfold tailWord_120455
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393354778619581921282819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2928903185746387947521879 4393354778619581921282819)
  ·
    refine ⟨6590032167929372881924229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4393354778619581921282819 6590032167929372881924229)
    ·
      refine ⟨1235631031486757415360793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6590032167929372881924229 1235631031486757415360793)
      ·
        refine ⟨926723273615068061520595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1235631031486757415360793 926723273615068061520595)
        ·
          refine ⟨1390084910422602092280893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926723273615068061520595 1390084910422602092280893)
          ·
            refine ⟨521281841408475784605335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1390084910422602092280893 521281841408475784605335)
            ·
              refine ⟨781922762112713676908003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521281841408475784605335 781922762112713676908003)
              ·
                refine ⟨1172884143169070515362005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781922762112713676908003 1172884143169070515362005)
                ·
                  refine ⟨27489472105525090203797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1172884143169070515362005 27489472105525090203797)
                  ·
                    rfl

theorem cell21_120455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_120455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120455 prefixEnd_120455 := by exact prefixLift 120455
  have htrace : WordTrace (prefixWord ++ tailWord_120455) baseStart_120455 baseEnd_120455 := by
    simpa [prefixWord, tailWord_120455, baseEnd_120455] using wordTrace_append hprefix tailTrace_120455
  have hstable : (prefixWord ++ tailWord_120455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120455).length < 2 ^ (prefixWord ++ tailWord_120455).sum := by decide
  have hdescent : baseEnd_120455 < baseStart_120455 := by decide
  rcases family_descends (prefixWord ++ tailWord_120455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120458 : List Nat := [3, 1, 2, 3, 2, 2, 3, 5]
def baseStart_120458 : Nat := 118140960795 + 120458 * 2 ^ 59
def prefixEnd_120458 : Nat := 4983230072969 + 3 ^ 40 * 120458 * 2
def baseEnd_120458 : Nat := 9163385582132583884597

theorem tailTrace_120458 : CollatzResearch.WordTrace tailWord_120458 prefixEnd_120458 9163385582132583884597 := by
  unfold tailWord_120458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098366049402178358410507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2928976131739142289094685 1098366049402178358410507)
  ·
    refine ⟨1647549074103267537615761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1098366049402178358410507 1647549074103267537615761)
    ·
      refine ⟨1235661805577450653211821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1647549074103267537615761 1235661805577450653211821)
      ·
        refine ⟨463373177091543994954433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1235661805577450653211821 463373177091543994954433)
        ·
          refine ⟨347529882818657996215825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463373177091543994954433 347529882818657996215825)
          ·
            refine ⟨260647412113993497161869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347529882818657996215825 260647412113993497161869)
            ·
              refine ⟨97742779542747561435701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260647412113993497161869 97742779542747561435701)
              ·
                refine ⟨9163385582132583884597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97742779542747561435701 9163385582132583884597)
                ·
                  rfl

theorem cell21_120458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_120458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120458 prefixEnd_120458 := by exact prefixLift 120458
  have htrace : WordTrace (prefixWord ++ tailWord_120458) baseStart_120458 baseEnd_120458 := by
    simpa [prefixWord, tailWord_120458, baseEnd_120458] using wordTrace_append hprefix tailTrace_120458
  have hstable : (prefixWord ++ tailWord_120458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120458).length < 2 ^ (prefixWord ++ tailWord_120458).sum := by decide
  have hdescent : baseEnd_120458 < baseStart_120458 := by decide
  rcases family_descends (prefixWord ++ tailWord_120458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120607 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 5]
def baseStart_120607 : Nat := 118140960795 + 120607 * 2 ^ 59
def prefixEnd_120607 : Nat := 4983230072969 + 3 ^ 40 * 120607 * 2
def baseEnd_120607 : Nat := 27524160576406603670153

theorem tailTrace_120607 : CollatzResearch.WordTrace tailWord_120607 prefixEnd_120607 27524160576406603670153 := by
  unfold tailWord_120607
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398898674068911880816075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2932599116045941253877383 4398898674068911880816075)
  ·
    refine ⟨6598348011103367821224113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4398898674068911880816075 6598348011103367821224113)
    ·
      refine ⟨4948761008327525865918085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6598348011103367821224113 4948761008327525865918085)
      ·
        refine ⟨927892689061411099859641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4948761008327525865918085 927892689061411099859641)
        ·
          refine ⟨695919516796058324894731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927892689061411099859641 695919516796058324894731)
          ·
            refine ⟨1043879275194087487342097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695919516796058324894731 1043879275194087487342097)
            ·
              refine ⟨782909456395565615506573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043879275194087487342097 782909456395565615506573)
              ·
                refine ⟨293591046148337105814965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 782909456395565615506573 293591046148337105814965)
                ·
                  refine ⟨27524160576406603670153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293591046148337105814965 27524160576406603670153)
                  ·
                    rfl

theorem cell21_120607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_120607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120607 prefixEnd_120607 := by exact prefixLift 120607
  have htrace : WordTrace (prefixWord ++ tailWord_120607) baseStart_120607 baseEnd_120607 := by
    simpa [prefixWord, tailWord_120607, baseEnd_120607] using wordTrace_append hprefix tailTrace_120607
  have hstable : (prefixWord ++ tailWord_120607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120607).length < 2 ^ (prefixWord ++ tailWord_120607).sum := by decide
  have hdescent : baseEnd_120607 < baseStart_120607 := by decide
  rcases family_descends (prefixWord ++ tailWord_120607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120686 : List Nat := [4, 1, 2, 3, 1, 1, 4, 5]
def baseStart_120686 : Nat := 118140960795 + 120686 * 2 ^ 59
def prefixEnd_120686 : Nat := 4983230072969 + 3 ^ 40 * 120686 * 2
def baseEnd_120686 : Nat := 9180729817573340617775

theorem tailTrace_120686 : CollatzResearch.WordTrace tailWord_120686 prefixEnd_120686 9180729817573340617775 := by
  unfold tailWord_120686
  simp only [CollatzResearch.WordTrace]
  refine ⟨550222505097838546617739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2934520027188472248627941 550222505097838546617739)
  ·
    refine ⟨825333757646757819926609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 550222505097838546617739 825333757646757819926609)
    ·
      refine ⟨619000318235068364944957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 825333757646757819926609 619000318235068364944957)
      ·
        refine ⟨232125119338150636854359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 619000318235068364944957 232125119338150636854359)
        ·
          refine ⟨348187679007225955281539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232125119338150636854359 348187679007225955281539)
          ·
            refine ⟨522281518510838932922309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348187679007225955281539 522281518510838932922309)
            ·
              refine ⟨97927784720782299922933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 522281518510838932922309 97927784720782299922933)
              ·
                refine ⟨9180729817573340617775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97927784720782299922933 9180729817573340617775)
                ·
                  rfl

theorem cell21_120686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_120686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120686 prefixEnd_120686 := by exact prefixLift 120686
  have htrace : WordTrace (prefixWord ++ tailWord_120686) baseStart_120686 baseEnd_120686 := by
    simpa [prefixWord, tailWord_120686, baseEnd_120686] using wordTrace_append hprefix tailTrace_120686
  have hstable : (prefixWord ++ tailWord_120686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120686).length < 2 ^ (prefixWord ++ tailWord_120686).sum := by decide
  have hdescent : baseEnd_120686 < baseStart_120686 := by decide
  rcases family_descends (prefixWord ++ tailWord_120686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120697 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 8]
def baseStart_120697 : Nat := 118140960795 + 120697 * 2 ^ 59
def prefixEnd_120697 : Nat := 4983230072969 + 3 ^ 40 * 120697 * 2
def baseEnd_120697 : Nat := 27544699802586447169969

theorem tailTrace_120697 : CollatzResearch.WordTrace tailWord_120697 prefixEnd_120697 27544699802586447169969 := by
  unfold tailWord_120697
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402181243742857251592345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2934787495828571501061563 4402181243742857251592345)
  ·
    refine ⟨3301635932807142938694259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4402181243742857251592345 3301635932807142938694259)
    ·
      refine ⟨4952453899210714408041389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301635932807142938694259 4952453899210714408041389)
      ·
        refine ⟨1857170212204017903015521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4952453899210714408041389 1857170212204017903015521)
        ·
          refine ⟨1392877659153013427261641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1857170212204017903015521 1392877659153013427261641)
          ·
            refine ⟨1044658244364760070446231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392877659153013427261641 1044658244364760070446231)
            ·
              refine ⟨1566987366547140105669347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044658244364760070446231 1566987366547140105669347)
              ·
                refine ⟨2350481049820710158504021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1566987366547140105669347 2350481049820710158504021)
                ·
                  refine ⟨27544699802586447169969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2350481049820710158504021 27544699802586447169969)
                  ·
                    rfl

theorem cell21_120697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_120697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120697 prefixEnd_120697 := by exact prefixLift 120697
  have htrace : WordTrace (prefixWord ++ tailWord_120697) baseStart_120697 baseEnd_120697 := by
    simpa [prefixWord, tailWord_120697, baseEnd_120697] using wordTrace_append hprefix tailTrace_120697
  have hstable : (prefixWord ++ tailWord_120697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120697).length < 2 ^ (prefixWord ++ tailWord_120697).sum := by decide
  have hdescent : baseEnd_120697 < baseStart_120697 := by decide
  rcases family_descends (prefixWord ++ tailWord_120697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120796 : List Nat := [2, 2, 6, 1, 1, 1, 3, 5]
def baseStart_120796 : Nat := 118140960795 + 120796 * 2 ^ 59
def prefixEnd_120796 : Nat := 4983230072969 + 3 ^ 40 * 120796 * 2
def baseEnd_120796 : Nat := 9189097650461425006589

theorem tailTrace_120796 : CollatzResearch.WordTrace tailWord_120796 prefixEnd_120796 9189097650461425006589 := by
  unfold tailWord_120796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202896035192098579723121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2937194713589464772964161 2202896035192098579723121)
  ·
    refine ⟨1652172026394073934792341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2202896035192098579723121 1652172026394073934792341)
    ·
      refine ⟨77445563737222215693391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1652172026394073934792341 77445563737222215693391)
      ·
        refine ⟨116168345605833323540087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77445563737222215693391 116168345605833323540087)
        ·
          refine ⟨174252518408749985310131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116168345605833323540087 174252518408749985310131)
          ·
            refine ⟨261378777613124977965197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174252518408749985310131 261378777613124977965197)
            ·
              refine ⟨98017041604921866736949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261378777613124977965197 98017041604921866736949)
              ·
                refine ⟨9189097650461425006589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98017041604921866736949 9189097650461425006589)
                ·
                  rfl

theorem cell21_120796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_120796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120796 prefixEnd_120796 := by exact prefixLift 120796
  have htrace : WordTrace (prefixWord ++ tailWord_120796) baseStart_120796 baseEnd_120796 := by
    simpa [prefixWord, tailWord_120796, baseEnd_120796] using wordTrace_append hprefix tailTrace_120796
  have hstable : (prefixWord ++ tailWord_120796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120796).length < 2 ^ (prefixWord ++ tailWord_120796).sum := by decide
  have hdescent : baseEnd_120796 < baseStart_120796 := by decide
  rcases family_descends (prefixWord ++ tailWord_120796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120855 : List Nat := [1, 1, 3, 5, 3, 1, 2, 5]
def baseStart_120855 : Nat := 118140960795 + 120855 * 2 ^ 59
def prefixEnd_120855 : Nat := 4983230072969 + 3 ^ 40 * 120855 * 2
def baseEnd_120855 : Nat := 9193585851737761178771

theorem tailTrace_120855 : CollatzResearch.WordTrace tailWord_120855 prefixEnd_120855 9193585851737761178771 := by
  unfold tailWord_120855
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407943977170450235844019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2938629318113633490562679 4407943977170450235844019)
  ·
    refine ⟨6611915965755675353766029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4407943977170450235844019 6611915965755675353766029)
    ·
      refine ⟨2479468487158378257662261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6611915965755675353766029 2479468487158378257662261)
      ·
        refine ⟨232450170671097961655837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2479468487158378257662261 232450170671097961655837)
        ·
          refine ⟨87168814001661735620939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232450170671097961655837 87168814001661735620939)
          ·
            refine ⟨130753221002492603431409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87168814001661735620939 130753221002492603431409)
            ·
              refine ⟨98064915751869452573557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130753221002492603431409 98064915751869452573557)
              ·
                refine ⟨9193585851737761178771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98064915751869452573557 9193585851737761178771)
                ·
                  rfl

theorem cell21_120855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 5].length) (baseStart_120855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120855 prefixEnd_120855 := by exact prefixLift 120855
  have htrace : WordTrace (prefixWord ++ tailWord_120855) baseStart_120855 baseEnd_120855 := by
    simpa [prefixWord, tailWord_120855, baseEnd_120855] using wordTrace_append hprefix tailTrace_120855
  have hstable : (prefixWord ++ tailWord_120855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120855).length < 2 ^ (prefixWord ++ tailWord_120855).sum := by decide
  have hdescent : baseEnd_120855 < baseStart_120855 := by decide
  rcases family_descends (prefixWord ++ tailWord_120855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120869 : List Nat := [1, 3, 1, 2, 2, 5, 1, 3, 3]
def baseStart_120869 : Nat := 118140960795 + 120869 * 2 ^ 59
def prefixEnd_120869 : Nat := 4983230072969 + 3 ^ 40 * 120869 * 2
def baseEnd_120869 : Nat := 27583952545952370302951

theorem tailTrace_120869 : CollatzResearch.WordTrace tailWord_120869 prefixEnd_120869 27583952545952370302951 := by
  unfold tailWord_120869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4408454599119730626853661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2938969732746487084569107 4408454599119730626853661)
  ·
    refine ⟨1653170474669898985070123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4408454599119730626853661 1653170474669898985070123)
    ·
      refine ⟨2479755712004848477605185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653170474669898985070123 2479755712004848477605185)
      ·
        refine ⟨1859816784003636358203889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479755712004848477605185 1859816784003636358203889)
        ·
          refine ⟨1394862588002727268652917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859816784003636358203889 1394862588002727268652917)
          ·
            refine ⟨130768367625255681436211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1394862588002727268652917 130768367625255681436211)
            ·
              refine ⟨196152551437883522154317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130768367625255681436211 196152551437883522154317)
              ·
                refine ⟨73557206789206320807869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196152551437883522154317 73557206789206320807869)
                ·
                  refine ⟨27583952545952370302951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73557206789206320807869 27583952545952370302951)
                  ·
                    rfl

theorem cell21_120869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_120869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120869 prefixEnd_120869 := by exact prefixLift 120869
  have htrace : WordTrace (prefixWord ++ tailWord_120869) baseStart_120869 baseEnd_120869 := by
    simpa [prefixWord, tailWord_120869, baseEnd_120869] using wordTrace_append hprefix tailTrace_120869
  have hstable : (prefixWord ++ tailWord_120869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120869).length < 2 ^ (prefixWord ++ tailWord_120869).sum := by decide
  have hdescent : baseEnd_120869 < baseStart_120869 := by decide
  rcases family_descends (prefixWord ++ tailWord_120869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120880 : List Nat := [2, 1, 1, 1, 2, 7, 7]
def baseStart_120880 : Nat := 118140960795 + 120880 * 2 ^ 59
def prefixEnd_120880 : Nat := 4983230072969 + 3 ^ 40 * 120880 * 2
def baseEnd_120880 : Nat := 3065162543979866179955

theorem tailTrace_120880 : CollatzResearch.WordTrace tailWord_120880 prefixEnd_120880 3065162543979866179955 := by
  unfold tailWord_120880
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204427901039939752752047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2939237201386586337002729 2204427901039939752752047)
  ·
    refine ⟨3306641851559909629128071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2204427901039939752752047 3306641851559909629128071)
    ·
      refine ⟨4959962777339864443692107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3306641851559909629128071 4959962777339864443692107)
      ·
        refine ⟨7439944166009796665538161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959962777339864443692107 7439944166009796665538161)
        ·
          refine ⟨5579958124507347499153621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7439944166009796665538161 5579958124507347499153621)
          ·
            refine ⟨130780268543140957011413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5579958124507347499153621 130780268543140957011413)
            ·
              refine ⟨3065162543979866179955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130780268543140957011413 3065162543979866179955)
              ·
                rfl

theorem cell21_120880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 7].length) (baseStart_120880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120880 prefixEnd_120880 := by exact prefixLift 120880
  have htrace : WordTrace (prefixWord ++ tailWord_120880) baseStart_120880 baseEnd_120880 := by
    simpa [prefixWord, tailWord_120880, baseEnd_120880] using wordTrace_append hprefix tailTrace_120880
  have hstable : (prefixWord ++ tailWord_120880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120880).length < 2 ^ (prefixWord ++ tailWord_120880).sum := by decide
  have hdescent : baseEnd_120880 < baseStart_120880 := by decide
  rcases family_descends (prefixWord ++ tailWord_120880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120886 : List Nat := [5, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_120886 : Nat := 118140960795 + 120886 * 2 ^ 59
def prefixEnd_120886 : Nat := 4983230072969 + 3 ^ 40 * 120886 * 2
def baseEnd_120886 : Nat := 27587832177564118519583

theorem tailTrace_120886 : CollatzResearch.WordTrace tailWord_120886 prefixEnd_120886 27587832177564118519583 := by
  unfold tailWord_120886
  simp only [CollatzResearch.WordTrace]
  refine ⟨275567165003633908138907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2939383093372095020148341 275567165003633908138907)
  ·
    refine ⟨413350747505450862208361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275567165003633908138907 413350747505450862208361)
    ·
      refine ⟨310013060629088146656271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413350747505450862208361 310013060629088146656271)
      ·
        refine ⟨465019590943632219984407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310013060629088146656271 465019590943632219984407)
        ·
          refine ⟨697529386415448329976611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465019590943632219984407 697529386415448329976611)
          ·
            refine ⟨1046294079623172494964917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697529386415448329976611 1046294079623172494964917)
            ·
              refine ⟨98090069964672421402961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1046294079623172494964917 98090069964672421402961)
              ·
                refine ⟨73567552473504316052221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98090069964672421402961 73567552473504316052221)
                ·
                  refine ⟨27587832177564118519583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73567552473504316052221 27587832177564118519583)
                  ·
                    rfl

theorem cell21_120886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_120886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120886 prefixEnd_120886 := by exact prefixLift 120886
  have htrace : WordTrace (prefixWord ++ tailWord_120886) baseStart_120886 baseEnd_120886 := by
    simpa [prefixWord, tailWord_120886, baseEnd_120886] using wordTrace_append hprefix tailTrace_120886
  have hstable : (prefixWord ++ tailWord_120886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120886).length < 2 ^ (prefixWord ++ tailWord_120886).sum := by decide
  have hdescent : baseEnd_120886 < baseStart_120886 := by decide
  rcases family_descends (prefixWord ++ tailWord_120886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120897 : List Nat := [1, 2, 5, 1, 2, 2, 2, 6]
def baseStart_120897 : Nat := 118140960795 + 120897 * 2 ^ 59
def prefixEnd_120897 : Nat := 4983230072969 + 3 ^ 40 * 120897 * 2
def baseEnd_120897 : Nat := 9196780842476847945409

theorem tailTrace_120897 : CollatzResearch.WordTrace tailWord_120897 prefixEnd_120897 9196780842476847945409 := by
  unfold tailWord_120897
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409475843018291408872945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2939650562012194272581963 4409475843018291408872945)
  ·
    refine ⟨3307106882263718556654709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4409475843018291408872945 3307106882263718556654709)
    ·
      refine ⟨310041270212223614686379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3307106882263718556654709 310041270212223614686379)
      ·
        refine ⟨465061905318335422029569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310041270212223614686379 465061905318335422029569)
        ·
          refine ⟨348796428988751566522177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465061905318335422029569 348796428988751566522177)
          ·
            refine ⟨261597321741563674891633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348796428988751566522177 261597321741563674891633)
            ·
              refine ⟨196197991306172756168725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261597321741563674891633 196197991306172756168725)
              ·
                refine ⟨9196780842476847945409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196197991306172756168725 9196780842476847945409)
                ·
                  rfl

theorem cell21_120897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 6].length) (baseStart_120897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120897 prefixEnd_120897 := by exact prefixLift 120897
  have htrace : WordTrace (prefixWord ++ tailWord_120897) baseStart_120897 baseEnd_120897 := by
    simpa [prefixWord, tailWord_120897, baseEnd_120897] using wordTrace_append hprefix tailTrace_120897
  have hstable : (prefixWord ++ tailWord_120897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120897).length < 2 ^ (prefixWord ++ tailWord_120897).sum := by decide
  have hdescent : baseEnd_120897 < baseStart_120897 := by decide
  rcases family_descends (prefixWord ++ tailWord_120897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120956 : List Nat := [2, 2, 2, 1, 1, 4, 3, 6]
def baseStart_120956 : Nat := 118140960795 + 120956 * 2 ^ 59
def prefixEnd_120956 : Nat := 4983230072969 + 3 ^ 40 * 120956 * 2
def baseEnd_120956 : Nat := 9201269043753184117591

theorem tailTrace_120956 : CollatzResearch.WordTrace tailWord_120956 prefixEnd_120956 9201269043753184117591 := by
  unfold tailWord_120956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205813874902272242635361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2941085166536362990180481 2205813874902272242635361)
  ·
    refine ⟨1654360406176704181976521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2205813874902272242635361 1654360406176704181976521)
    ·
      refine ⟨1240770304632528136482391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1654360406176704181976521 1240770304632528136482391)
      ·
        refine ⟨1861155456948792204723587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240770304632528136482391 1861155456948792204723587)
        ·
          refine ⟨2791733185423188307085381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861155456948792204723587 2791733185423188307085381)
          ·
            refine ⟨523449972266847807578509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2791733185423188307085381 523449972266847807578509)
            ·
              refine ⟨196293739600067927841941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523449972266847807578509 196293739600067927841941)
              ·
                refine ⟨9201269043753184117591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196293739600067927841941 9201269043753184117591)
                ·
                  rfl

theorem cell21_120956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_120956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_120956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_120956 prefixEnd_120956 := by exact prefixLift 120956
  have htrace : WordTrace (prefixWord ++ tailWord_120956) baseStart_120956 baseEnd_120956 := by
    simpa [prefixWord, tailWord_120956, baseEnd_120956] using wordTrace_append hprefix tailTrace_120956
  have hstable : (prefixWord ++ tailWord_120956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120956).length < 2 ^ (prefixWord ++ tailWord_120956).sum := by decide
  have hdescent : baseEnd_120956 < baseStart_120956 := by decide
  rcases family_descends (prefixWord ++ tailWord_120956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121069 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 4]
def baseStart_121069 : Nat := 118140960795 + 121069 * 2 ^ 59
def prefixEnd_121069 : Nat := 4983230072969 + 3 ^ 40 * 121069 * 2
def baseEnd_121069 : Nat := 27629595270796466969209

theorem tailTrace_121069 : CollatzResearch.WordTrace tailWord_121069 prefixEnd_121069 27629595270796466969209 := by
  unfold tailWord_121069
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415749198395164784134261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2943832798930109856089507 4415749198395164784134261)
  ·
    refine ⟨413976487349546698512587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4415749198395164784134261 413976487349546698512587)
    ·
      refine ⟨620964731024320047768881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413976487349546698512587 620964731024320047768881)
      ·
        refine ⟨465723548268240035826661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620964731024320047768881 465723548268240035826661)
        ·
          refine ⟨87323165300295006717499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 465723548268240035826661 87323165300295006717499)
          ·
            refine ⟨130984747950442510076249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87323165300295006717499 130984747950442510076249)
            ·
              refine ⟨98238560962831882557187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130984747950442510076249 98238560962831882557187)
              ·
                refine ⟨147357841444247823835781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98238560962831882557187 147357841444247823835781)
                ·
                  refine ⟨27629595270796466969209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147357841444247823835781 27629595270796466969209)
                  ·
                    rfl

theorem cell21_121069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_121069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121069 prefixEnd_121069 := by exact prefixLift 121069
  have htrace : WordTrace (prefixWord ++ tailWord_121069) baseStart_121069 baseEnd_121069 := by
    simpa [prefixWord, tailWord_121069, baseEnd_121069] using wordTrace_append hprefix tailTrace_121069
  have hstable : (prefixWord ++ tailWord_121069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121069).length < 2 ^ (prefixWord ++ tailWord_121069).sum := by decide
  have hdescent : baseEnd_121069 < baseStart_121069 := by decide
  rcases family_descends (prefixWord ++ tailWord_121069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121091 : List Nat := [1, 1, 1, 3, 2, 3, 1, 9]
def baseStart_121091 : Nat := 118140960795 + 121091 * 2 ^ 59
def prefixEnd_121091 : Nat := 4983230072969 + 3 ^ 40 * 121091 * 2
def baseEnd_121091 : Nat := 9211538656843105867499

theorem tailTrace_121091 : CollatzResearch.WordTrace tailWord_121091 prefixEnd_121091 9211538656843105867499 := by
  unfold tailWord_121091
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416551604315462541435127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2944367736210308360956751 4416551604315462541435127)
  ·
    refine ⟨6624827406473193812152691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4416551604315462541435127 6624827406473193812152691)
    ·
      refine ⟨9937241109709790718229037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6624827406473193812152691 9937241109709790718229037)
      ·
        refine ⟨3726465416141171519335889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9937241109709790718229037 3726465416141171519335889)
        ·
          refine ⟨2794849062105878639501917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726465416141171519335889 2794849062105878639501917)
          ·
            refine ⟨1048068398289704489813219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2794849062105878639501917 1048068398289704489813219)
            ·
              refine ⟨1572102597434556734719829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048068398289704489813219 1572102597434556734719829)
              ·
                refine ⟨9211538656843105867499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1572102597434556734719829 9211538656843105867499)
                ·
                  rfl

theorem cell21_121091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 9].length) (baseStart_121091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121091 prefixEnd_121091 := by exact prefixLift 121091
  have htrace : WordTrace (prefixWord ++ tailWord_121091) baseStart_121091 baseEnd_121091 := by
    simpa [prefixWord, tailWord_121091, baseEnd_121091] using wordTrace_append hprefix tailTrace_121091
  have hstable : (prefixWord ++ tailWord_121091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121091).length < 2 ^ (prefixWord ++ tailWord_121091).sum := by decide
  have hdescent : baseEnd_121091 < baseStart_121091 := by decide
  rcases family_descends (prefixWord ++ tailWord_121091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121114 : List Nat := [3, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_121114 : Nat := 118140960795 + 121114 * 2 ^ 59
def prefixEnd_121114 : Nat := 4983230072969 + 3 ^ 40 * 121114 * 2
def baseEnd_121114 : Nat := 27639864883886388719117

theorem tailTrace_121114 : CollatzResearch.WordTrace tailWord_121114 prefixEnd_121114 27639864883886388719117 := by
  unfold tailWord_121114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104347620808034367380599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2944926988821424979681597 1104347620808034367380599)
  ·
    refine ⟨1656521431212051551070899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104347620808034367380599 1656521431212051551070899)
    ·
      refine ⟨2484782146818077326606349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656521431212051551070899 2484782146818077326606349)
      ·
        refine ⟨931793305056778997477381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2484782146818077326606349 931793305056778997477381)
        ·
          refine ⟨174711244698146062027009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 931793305056778997477381 174711244698146062027009)
          ·
            refine ⟨131033433523609546520257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174711244698146062027009 131033433523609546520257)
            ·
              refine ⟨98275075142707159890193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131033433523609546520257 98275075142707159890193)
              ·
                refine ⟨73706306357030369917645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98275075142707159890193 73706306357030369917645)
                ·
                  refine ⟨27639864883886388719117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73706306357030369917645 27639864883886388719117)
                  ·
                    rfl

theorem cell21_121114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_121114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121114 prefixEnd_121114 := by exact prefixLift 121114
  have htrace : WordTrace (prefixWord ++ tailWord_121114) baseStart_121114 baseEnd_121114 := by
    simpa [prefixWord, tailWord_121114, baseEnd_121114] using wordTrace_append hprefix tailTrace_121114
  have hstable : (prefixWord ++ tailWord_121114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121114).length < 2 ^ (prefixWord ++ tailWord_121114).sum := by decide
  have hdescent : baseEnd_121114 < baseStart_121114 := by decide
  rcases family_descends (prefixWord ++ tailWord_121114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121125 : List Nat := [1, 3, 1, 2, 5, 2, 1, 6]
def baseStart_121125 : Nat := 118140960795 + 121125 * 2 ^ 59
def prefixEnd_121125 : Nat := 4983230072969 + 3 ^ 40 * 121125 * 2
def baseEnd_121125 : Nat := 9214125077917604678587

theorem tailTrace_121125 : CollatzResearch.WordTrace tailWord_121125 prefixEnd_121125 9214125077917604678587 := by
  unfold tailWord_121125
  simp only [CollatzResearch.WordTrace]
  refine ⟨4417791686192286348172829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2945194457461524232115219 4417791686192286348172829)
  ·
    refine ⟨1656671882322107380564811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4417791686192286348172829 1656671882322107380564811)
    ·
      refine ⟨2485007823483161070847217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656671882322107380564811 2485007823483161070847217)
      ·
        refine ⟨1863755867612370803135413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2485007823483161070847217 1863755867612370803135413)
        ·
          refine ⟨174727112588659762793945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1863755867612370803135413 174727112588659762793945)
          ·
            refine ⟨131045334441494822095459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174727112588659762793945 131045334441494822095459)
            ·
              refine ⟨196568001662242233143189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131045334441494822095459 196568001662242233143189)
              ·
                refine ⟨9214125077917604678587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196568001662242233143189 9214125077917604678587)
                ·
                  rfl

theorem cell21_121125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 6].length) (baseStart_121125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121125 prefixEnd_121125 := by exact prefixLift 121125
  have htrace : WordTrace (prefixWord ++ tailWord_121125) baseStart_121125 baseEnd_121125 := by
    simpa [prefixWord, tailWord_121125, baseEnd_121125] using wordTrace_append hprefix tailTrace_121125
  have hstable : (prefixWord ++ tailWord_121125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121125).length < 2 ^ (prefixWord ++ tailWord_121125).sum := by decide
  have hdescent : baseEnd_121125 < baseStart_121125 := by decide
  rcases family_descends (prefixWord ++ tailWord_121125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121170 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_121170 : Nat := 118140960795 + 121170 * 2 ^ 59
def prefixEnd_121170 : Nat := 4983230072969 + 3 ^ 40 * 121170 * 2
def baseEnd_121170 : Nat := 27652644846842735785669

theorem tailTrace_121170 : CollatzResearch.WordTrace tailWord_121170 prefixEnd_121170 27652644846842735785669 := by
  unfold tailWord_121170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104858242757314758390241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2946288647352839355707309 1104858242757314758390241)
  ·
    refine ⟨828643682067986068792681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1104858242757314758390241 828643682067986068792681)
    ·
      refine ⟨621482761550989551594511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 828643682067986068792681 621482761550989551594511)
      ·
        refine ⟨932224142326484327391767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621482761550989551594511 932224142326484327391767)
        ·
          refine ⟨1398336213489726491087651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932224142326484327391767 1398336213489726491087651)
          ·
            refine ⟨2097504320234589736631477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398336213489726491087651 2097504320234589736631477)
            ·
              refine ⟨196641030021992787809201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2097504320234589736631477 196641030021992787809201)
              ·
                refine ⟨147480772516494590856901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196641030021992787809201 147480772516494590856901)
                ·
                  refine ⟨27652644846842735785669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147480772516494590856901 27652644846842735785669)
                  ·
                    rfl

theorem cell21_121170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_121170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121170 prefixEnd_121170 := by exact prefixLift 121170
  have htrace : WordTrace (prefixWord ++ tailWord_121170) baseStart_121170 baseEnd_121170 := by
    simpa [prefixWord, tailWord_121170, baseEnd_121170] using wordTrace_append hprefix tailTrace_121170
  have hstable : (prefixWord ++ tailWord_121170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121170).length < 2 ^ (prefixWord ++ tailWord_121170).sum := by decide
  have hdescent : baseEnd_121170 < baseStart_121170 := by decide
  rcases family_descends (prefixWord ++ tailWord_121170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121218 : List Nat := [3, 4, 2, 1, 2, 2, 7]
def baseStart_121218 : Nat := 118140960795 + 121218 * 2 ^ 59
def prefixEnd_121218 : Nat := 4983230072969 + 3 ^ 40 * 121218 * 2
def baseEnd_121218 : Nat := 3073733233422813220619

theorem tailTrace_121218 : CollatzResearch.WordTrace tailWord_121218 prefixEnd_121218 3073733233422813220619 := by
  unfold tailWord_121218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105295918713840807827077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2947455783236908820872205 1105295918713840807827077)
  ·
    refine ⟨207242984758845151467577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1105295918713840807827077 207242984758845151467577)
    ·
      refine ⟨155432238569133863600683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207242984758845151467577 155432238569133863600683)
      ·
        refine ⟨233148357853700795401025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155432238569133863600683 233148357853700795401025)
        ·
          refine ⟨174861268390275596550769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233148357853700795401025 174861268390275596550769)
          ·
            refine ⟨131145951292706697413077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174861268390275596550769 131145951292706697413077)
            ·
              refine ⟨3073733233422813220619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131145951292706697413077 3073733233422813220619)
              ·
                rfl

theorem cell21_121218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 7].length) (baseStart_121218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121218 prefixEnd_121218 := by exact prefixLift 121218
  have htrace : WordTrace (prefixWord ++ tailWord_121218) baseStart_121218 baseEnd_121218 := by
    simpa [prefixWord, tailWord_121218, baseEnd_121218] using wordTrace_append hprefix tailTrace_121218
  have hstable : (prefixWord ++ tailWord_121218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121218).length < 2 ^ (prefixWord ++ tailWord_121218).sum := by decide
  have hdescent : baseEnd_121218 < baseStart_121218 := by decide
  rcases family_descends (prefixWord ++ tailWord_121218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121305 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 4]
def baseStart_121305 : Nat := 118140960795 + 121305 * 2 ^ 59
def prefixEnd_121305 : Nat := 4983230072969 + 3 ^ 40 * 121305 * 2
def baseEnd_121305 : Nat := 27683453686112501035393

theorem tailTrace_121305 : CollatzResearch.WordTrace tailWord_121305 prefixEnd_121305 27683453686112501035393 := by
  unfold tailWord_121305
  simp only [CollatzResearch.WordTrace]
  refine ⟨4424356825540177089725369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2949571217026784726483579 4424356825540177089725369)
  ·
    refine ⟨3318267619155132817294027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4424356825540177089725369 3318267619155132817294027)
    ·
      refine ⟨4977401428732699225941041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3318267619155132817294027 4977401428732699225941041)
      ·
        refine ⟨3733051071549524419455781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4977401428732699225941041 3733051071549524419455781)
        ·
          refine ⟨699947075915535828647959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3733051071549524419455781 699947075915535828647959)
          ·
            refine ⟨1049920613873303742971939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699947075915535828647959 1049920613873303742971939)
            ·
              refine ⟨1574880920809955614457909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049920613873303742971939 1574880920809955614457909)
              ·
                refine ⟨147645086325933338855429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1574880920809955614457909 147645086325933338855429)
                ·
                  refine ⟨27683453686112501035393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147645086325933338855429 27683453686112501035393)
                  ·
                    rfl

theorem cell21_121305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_121305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121305 prefixEnd_121305 := by exact prefixLift 121305
  have htrace : WordTrace (prefixWord ++ tailWord_121305) baseStart_121305 baseEnd_121305 := by
    simpa [prefixWord, tailWord_121305, baseEnd_121305] using wordTrace_append hprefix tailTrace_121305
  have hstable : (prefixWord ++ tailWord_121305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121305).length < 2 ^ (prefixWord ++ tailWord_121305).sum := by decide
  have hdescent : baseEnd_121305 < baseStart_121305 := by decide
  rcases family_descends (prefixWord ++ tailWord_121305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121325 : List Nat := [1, 5, 1, 3, 1, 2, 2, 3, 3]
def baseStart_121325 : Nat := 118140960795 + 121325 * 2 ^ 59
def prefixEnd_121325 : Nat := 4983230072969 + 3 ^ 40 * 121325 * 2
def baseEnd_121325 : Nat := 27688017958596910702019

theorem tailTrace_121325 : CollatzResearch.WordTrace tailWord_121325 prefixEnd_121325 27688017958596910702019 := by
  unfold tailWord_121325
  simp only [CollatzResearch.WordTrace]
  refine ⟨4425086285467720505453429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2950057523645147003635619 4425086285467720505453429)
  ·
    refine ⟨414851839262598797386259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4425086285467720505453429 414851839262598797386259)
    ·
      refine ⟨622277758893898196079389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414851839262598797386259 622277758893898196079389)
      ·
        refine ⟨233354159585211823529771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622277758893898196079389 233354159585211823529771)
        ·
          refine ⟨350031239377817735294657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233354159585211823529771 350031239377817735294657)
          ·
            refine ⟨262523429533363301470993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350031239377817735294657 262523429533363301470993)
            ·
              refine ⟨196892572150022476103245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262523429533363301470993 196892572150022476103245)
              ·
                refine ⟨73834714556258428538717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196892572150022476103245 73834714556258428538717)
                ·
                  refine ⟨27688017958596910702019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73834714556258428538717 27688017958596910702019)
                  ·
                    rfl

theorem cell21_121325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_121325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121325 prefixEnd_121325 := by exact prefixLift 121325
  have htrace : WordTrace (prefixWord ++ tailWord_121325) baseStart_121325 baseEnd_121325 := by
    simpa [prefixWord, tailWord_121325, baseEnd_121325] using wordTrace_append hprefix tailTrace_121325
  have hstable : (prefixWord ++ tailWord_121325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121325).length < 2 ^ (prefixWord ++ tailWord_121325).sum := by decide
  have hdescent : baseEnd_121325 < baseStart_121325 := by decide
  rcases family_descends (prefixWord ++ tailWord_121325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121398 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_121398 : Nat := 118140960795 + 121398 * 2 ^ 59
def prefixEnd_121398 : Nat := 4983230072969 + 3 ^ 40 * 121398 * 2
def baseEnd_121398 : Nat := 27704677553165005985203

theorem tailTrace_121398 : CollatzResearch.WordTrace tailWord_121398 prefixEnd_121398 27704677553165005985203 := by
  unfold tailWord_121398
  simp only [CollatzResearch.WordTrace]
  refine ⟨276734300887703373303803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2951832542802169315240565 276734300887703373303803)
  ·
    refine ⟨415101451331555059955705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276734300887703373303803 415101451331555059955705)
    ·
      refine ⟨311326088498666294966779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415101451331555059955705 311326088498666294966779)
      ·
        refine ⟨466989132747999442450169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311326088498666294966779 466989132747999442450169)
        ·
          refine ⟨350241849560999581837627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466989132747999442450169 350241849560999581837627)
          ·
            refine ⟨525362774341499372756441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350241849560999581837627 525362774341499372756441)
            ·
              refine ⟨394022080756124529567331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525362774341499372756441 394022080756124529567331)
              ·
                refine ⟨591033121134186794350997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394022080756124529567331 591033121134186794350997)
                ·
                  refine ⟨27704677553165005985203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 591033121134186794350997 27704677553165005985203)
                  ·
                    rfl

theorem cell21_121398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_121398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121398 prefixEnd_121398 := by exact prefixLift 121398
  have htrace : WordTrace (prefixWord ++ tailWord_121398) baseStart_121398 baseEnd_121398 := by
    simpa [prefixWord, tailWord_121398, baseEnd_121398] using wordTrace_append hprefix tailTrace_121398
  have hstable : (prefixWord ++ tailWord_121398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121398).length < 2 ^ (prefixWord ++ tailWord_121398).sum := by decide
  have hdescent : baseEnd_121398 < baseStart_121398 := by decide
  rcases family_descends (prefixWord ++ tailWord_121398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121415 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 4]
def baseStart_121415 : Nat := 118140960795 + 121415 * 2 ^ 59
def prefixEnd_121415 : Nat := 4983230072969 + 3 ^ 40 * 121415 * 2
def baseEnd_121415 : Nat := 27708557184776754201835

theorem tailTrace_121415 : CollatzResearch.WordTrace tailWord_121415 prefixEnd_121415 27708557184776754201835 := by
  unfold tailWord_121415
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428368855141665876229699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2952245903427777250819799 4428368855141665876229699)
  ·
    refine ⟨6642553282712498814344549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4428368855141665876229699 6642553282712498814344549)
    ·
      refine ⟨1245478740508593527689603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6642553282712498814344549 1245478740508593527689603)
      ·
        refine ⟨1868218110762890291534405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245478740508593527689603 1868218110762890291534405)
        ·
          refine ⟨350290895768041929662701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1868218110762890291534405 350290895768041929662701)
          ·
            refine ⟨131359085913015723623513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350290895768041929662701 131359085913015723623513)
            ·
              refine ⟨98519314434761792717635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131359085913015723623513 98519314434761792717635)
              ·
                refine ⟨147778971652142689076453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98519314434761792717635 147778971652142689076453)
                ·
                  refine ⟨27708557184776754201835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147778971652142689076453 27708557184776754201835)
                  ·
                    rfl

theorem cell21_121415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 4].length) (baseStart_121415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121415 prefixEnd_121415 := by exact prefixLift 121415
  have htrace : WordTrace (prefixWord ++ tailWord_121415) baseStart_121415 baseEnd_121415 := by
    simpa [prefixWord, tailWord_121415, baseEnd_121415] using wordTrace_append hprefix tailTrace_121415
  have hstable : (prefixWord ++ tailWord_121415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121415).length < 2 ^ (prefixWord ++ tailWord_121415).sum := by decide
  have hdescent : baseEnd_121415 < baseStart_121415 := by decide
  rcases family_descends (prefixWord ++ tailWord_121415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121426 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_121426 : Nat := 118140960795 + 121426 * 2 ^ 59
def prefixEnd_121426 : Nat := 4983230072969 + 3 ^ 40 * 121426 * 2
def baseEnd_121426 : Nat := 27711067534643179518479

theorem tailTrace_121426 : CollatzResearch.WordTrace tailWord_121426 prefixEnd_121426 27711067534643179518479 := by
  unfold tailWord_121426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107192514525453688720033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2952513372067876503253421 1107192514525453688720033)
  ·
    refine ⟨830394385894090266540025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1107192514525453688720033 830394385894090266540025)
    ·
      refine ⟨622795789420567699905019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 830394385894090266540025 622795789420567699905019)
      ·
        refine ⟨934193684130851549857529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 622795789420567699905019 934193684130851549857529)
        ·
          refine ⟨700645263098138662393147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 934193684130851549857529 700645263098138662393147)
          ·
            refine ⟨1050967894647207993589721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700645263098138662393147 1050967894647207993589721)
            ·
              refine ⟨788225920985405995192291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1050967894647207993589721 788225920985405995192291)
              ·
                refine ⟨1182338881478108992788437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 788225920985405995192291 1182338881478108992788437)
                ·
                  refine ⟨27711067534643179518479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1182338881478108992788437 27711067534643179518479)
                  ·
                    rfl

theorem cell21_121426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_121426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121426 prefixEnd_121426 := by exact prefixLift 121426
  have htrace : WordTrace (prefixWord ++ tailWord_121426) baseStart_121426 baseEnd_121426 := by
    simpa [prefixWord, tailWord_121426, baseEnd_121426] using wordTrace_append hprefix tailTrace_121426
  have hstable : (prefixWord ++ tailWord_121426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121426).length < 2 ^ (prefixWord ++ tailWord_121426).sum := by decide
  have hdescent : baseEnd_121426 < baseStart_121426 := by decide
  rcases family_descends (prefixWord ++ tailWord_121426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121440 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_121440 : Nat := 118140960795 + 121440 * 2 ^ 59
def prefixEnd_121440 : Nat := 4983230072969 + 3 ^ 40 * 121440 * 2
def baseEnd_121440 : Nat := 27714262525382266285117

theorem tailTrace_121440 : CollatzResearch.WordTrace tailWord_121440 prefixEnd_121440 27714262525382266285117 := by
  unfold tailWord_121440
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214640340025547572944887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2952853786700730097259849 2214640340025547572944887)
  ·
    refine ⟨3321960510038321359417331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2214640340025547572944887 3321960510038321359417331)
    ·
      refine ⟨4982940765057482039125997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3321960510038321359417331 4982940765057482039125997)
      ·
        refine ⟨1868602786896555764672249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4982940765057482039125997 1868602786896555764672249)
        ·
          refine ⟨1401452090172416823504187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1868602786896555764672249 1401452090172416823504187)
          ·
            refine ⟨2102178135258625235256281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1401452090172416823504187 2102178135258625235256281)
            ·
              refine ⟨1576633601443968926442211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2102178135258625235256281 1576633601443968926442211)
              ·
                refine ⟨2364950402165953389663317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1576633601443968926442211 2364950402165953389663317)
                ·
                  refine ⟨27714262525382266285117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2364950402165953389663317 27714262525382266285117)
                  ·
                    rfl

theorem cell21_121440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_121440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121440 prefixEnd_121440 := by exact prefixLift 121440
  have htrace : WordTrace (prefixWord ++ tailWord_121440) baseStart_121440 baseEnd_121440 := by
    simpa [prefixWord, tailWord_121440, baseEnd_121440] using wordTrace_append hprefix tailTrace_121440
  have hstable : (prefixWord ++ tailWord_121440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121440).length < 2 ^ (prefixWord ++ tailWord_121440).sum := by decide
  have hdescent : baseEnd_121440 < baseStart_121440 := by decide
  rcases family_descends (prefixWord ++ tailWord_121440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121443 : List Nat := [1, 1, 1, 5, 1, 2, 2, 5, 3]
def baseStart_121443 : Nat := 118140960795 + 121443 * 2 ^ 59
def prefixEnd_121443 : Nat := 4983230072969 + 3 ^ 40 * 121443 * 2
def baseEnd_121443 : Nat := 27714947166254927735111

theorem tailTrace_121443 : CollatzResearch.WordTrace tailWord_121443 prefixEnd_121443 27714947166254927735111 := by
  unfold tailWord_121443
  simp only [CollatzResearch.WordTrace]
  refine ⟨4429390099040226658248983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2952926732693484438832655 4429390099040226658248983)
  ·
    refine ⟨6644085148560339987373475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4429390099040226658248983 6644085148560339987373475)
    ·
      refine ⟨9966127722840509981060213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6644085148560339987373475 9966127722840509981060213)
      ·
        refine ⟨934324474016297810724395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9966127722840509981060213 934324474016297810724395)
        ·
          refine ⟨1401486711024446716086593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934324474016297810724395 1401486711024446716086593)
          ·
            refine ⟨1051115033268335037064945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1401486711024446716086593 1051115033268335037064945)
            ·
              refine ⟨788336274951251277798709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1051115033268335037064945 788336274951251277798709)
              ·
                refine ⟨73906525776679807293629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788336274951251277798709 73906525776679807293629)
                ·
                  refine ⟨27714947166254927735111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73906525776679807293629 27714947166254927735111)
                  ·
                    rfl

theorem cell21_121443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 3].length) (baseStart_121443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121443 prefixEnd_121443 := by exact prefixLift 121443
  have htrace : WordTrace (prefixWord ++ tailWord_121443) baseStart_121443 baseEnd_121443 := by
    simpa [prefixWord, tailWord_121443, baseEnd_121443] using wordTrace_append hprefix tailTrace_121443
  have hstable : (prefixWord ++ tailWord_121443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121443).length < 2 ^ (prefixWord ++ tailWord_121443).sum := by decide
  have hdescent : baseEnd_121443 < baseStart_121443 := by decide
  rcases family_descends (prefixWord ++ tailWord_121443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121519 : List Nat := [1, 1, 2, 1, 2, 5, 2, 4, 3]
def baseStart_121519 : Nat := 118140960795 + 121519 * 2 ^ 59
def prefixEnd_121519 : Nat := 4983230072969 + 3 ^ 40 * 121519 * 2
def baseEnd_121519 : Nat := 27732291401695684468289

theorem tailTrace_121519 : CollatzResearch.WordTrace tailWord_121519 prefixEnd_121519 27732291401695684468289 := by
  unfold tailWord_121519
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432162046764891638015611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2954774697843261092010407 4432162046764891638015611)
  ·
    refine ⟨6648243070147337457023417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4432162046764891638015611 6648243070147337457023417)
    ·
      refine ⟨4986182302610503092767563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6648243070147337457023417 4986182302610503092767563)
      ·
        refine ⟨7479273453915754639151345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986182302610503092767563 7479273453915754639151345)
        ·
          refine ⟨5609455090436815979363509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7479273453915754639151345 5609455090436815979363509)
          ·
            refine ⟨525886414728451498065329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5609455090436815979363509 525886414728451498065329)
            ·
              refine ⟨394414811046338623548997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525886414728451498065329 394414811046338623548997)
              ·
                refine ⟨73952777071188491915437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394414811046338623548997 73952777071188491915437)
                ·
                  refine ⟨27732291401695684468289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73952777071188491915437 27732291401695684468289)
                  ·
                    rfl

theorem cell21_121519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 3].length) (baseStart_121519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121519 prefixEnd_121519 := by exact prefixLift 121519
  have htrace : WordTrace (prefixWord ++ tailWord_121519) baseStart_121519 baseEnd_121519 := by
    simpa [prefixWord, tailWord_121519, baseEnd_121519] using wordTrace_append hprefix tailTrace_121519
  have hstable : (prefixWord ++ tailWord_121519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121519).length < 2 ^ (prefixWord ++ tailWord_121519).sum := by decide
  have hdescent : baseEnd_121519 < baseStart_121519 := by decide
  rcases family_descends (prefixWord ++ tailWord_121519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121564 : List Nat := [2, 2, 5, 1, 1, 1, 9]
def baseStart_121564 : Nat := 118140960795 + 121564 * 2 ^ 59
def prefixEnd_121564 : Nat := 4983230072969 + 3 ^ 40 * 121564 * 2
def baseEnd_121564 : Nat := 3082506779420622913133

theorem tailTrace_121564 : CollatzResearch.WordTrace tailWord_121564 prefixEnd_121564 3082506779420622913133 := by
  unfold tailWord_121564
  simp only [CollatzResearch.WordTrace]
  refine ⟨2216901665800932161701873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2955868887734576215602497 2216901665800932161701873)
  ·
    refine ⟨1662676249350699121276405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2216901665800932161701873 1662676249350699121276405)
    ·
      refine ⟨155875898376628042619663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1662676249350699121276405 155875898376628042619663)
      ·
        refine ⟨233813847564942063929495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155875898376628042619663 233813847564942063929495)
        ·
          refine ⟨350720771347413095894243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233813847564942063929495 350720771347413095894243)
          ·
            refine ⟨526081157021119643841365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350720771347413095894243 526081157021119643841365)
            ·
              refine ⟨3082506779420622913133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 526081157021119643841365 3082506779420622913133)
              ·
                rfl

theorem cell21_121564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 9].length) (baseStart_121564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121564 prefixEnd_121564 := by exact prefixLift 121564
  have htrace : WordTrace (prefixWord ++ tailWord_121564) baseStart_121564 baseEnd_121564 := by
    simpa [prefixWord, tailWord_121564, baseEnd_121564] using wordTrace_append hprefix tailTrace_121564
  have hstable : (prefixWord ++ tailWord_121564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121564).length < 2 ^ (prefixWord ++ tailWord_121564).sum := by decide
  have hdescent : baseEnd_121564 < baseStart_121564 := by decide
  rcases family_descends (prefixWord ++ tailWord_121564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121623 : List Nat := [1, 1, 3, 4, 3, 9]
def baseStart_121623 : Nat := 118140960795 + 121623 * 2 ^ 59
def prefixEnd_121623 : Nat := 4983230072969 + 3 ^ 40 * 121623 * 2
def baseEnd_121623 : Nat := 1028000948837578323509

theorem tailTrace_121623 : CollatzResearch.WordTrace tailWord_121623 prefixEnd_121623 1028000948837578323509 := by
  unfold tailWord_121623
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435955238388117399801523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2957303492258744933201015 4435955238388117399801523)
  ·
    refine ⟨6653932857582176099702285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4435955238388117399801523 6653932857582176099702285)
    ·
      refine ⟨2495224821593316037388357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6653932857582176099702285 2495224821593316037388357)
      ·
        refine ⟨467854654048746757010317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2495224821593316037388357 467854654048746757010317)
        ·
          refine ⟨175445495268280033878869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467854654048746757010317 175445495268280033878869)
          ·
            refine ⟨1028000948837578323509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 175445495268280033878869 1028000948837578323509)
            ·
              rfl

theorem cell21_121623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 9].length) (baseStart_121623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121623 prefixEnd_121623 := by exact prefixLift 121623
  have htrace : WordTrace (prefixWord ++ tailWord_121623) baseStart_121623 baseEnd_121623 := by
    simpa [prefixWord, tailWord_121623, baseEnd_121623] using wordTrace_append hprefix tailTrace_121623
  have hstable : (prefixWord ++ tailWord_121623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121623).length < 2 ^ (prefixWord ++ tailWord_121623).sum := by decide
  have hdescent : baseEnd_121623 < baseStart_121623 := by decide
  rcases family_descends (prefixWord ++ tailWord_121623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121629 : List Nat := [1, 4, 2, 4, 1, 1, 1, 4, 3]
def baseStart_121629 : Nat := 118140960795 + 121629 * 2 ^ 59
def prefixEnd_121629 : Nat := 4983230072969 + 3 ^ 40 * 121629 * 2
def baseEnd_121629 : Nat := 27757394900359937634731

theorem tailTrace_121629 : CollatzResearch.WordTrace tailWord_121629 prefixEnd_121629 27757394900359937634731 := by
  unfold tailWord_121629
  simp only [CollatzResearch.WordTrace]
  refine ⟨4436174076366380424519941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2957449384244253616346627 4436174076366380424519941)
  ·
    refine ⟨831782639318696329597489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4436174076366380424519941 831782639318696329597489)
    ·
      refine ⟨623836979489022247198117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 831782639318696329597489 623836979489022247198117)
      ·
        refine ⟨116969433654191671349647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623836979489022247198117 116969433654191671349647)
        ·
          refine ⟨175454150481287507024471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116969433654191671349647 175454150481287507024471)
          ·
            refine ⟨263181225721931260536707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175454150481287507024471 263181225721931260536707)
            ·
              refine ⟨394771838582896890805061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263181225721931260536707 394771838582896890805061)
              ·
                refine ⟨74019719734293167025949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394771838582896890805061 74019719734293167025949)
                ·
                  refine ⟨27757394900359937634731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74019719734293167025949 27757394900359937634731)
                  ·
                    rfl

theorem cell21_121629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_121629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121629 prefixEnd_121629 := by exact prefixLift 121629
  have htrace : WordTrace (prefixWord ++ tailWord_121629) baseStart_121629 baseEnd_121629 := by
    simpa [prefixWord, tailWord_121629, baseEnd_121629] using wordTrace_append hprefix tailTrace_121629
  have hstable : (prefixWord ++ tailWord_121629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121629).length < 2 ^ (prefixWord ++ tailWord_121629).sum := by decide
  have hdescent : baseEnd_121629 < baseStart_121629 := by decide
  rcases family_descends (prefixWord ++ tailWord_121629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121750 : List Nat := [5, 3, 1, 1, 1, 2, 2, 6]
def baseStart_121750 : Nat := 118140960795 + 121750 * 2 ^ 59
def prefixEnd_121750 : Nat := 4983230072969 + 3 ^ 40 * 121750 * 2
def baseEnd_121750 : Nat := 9261669582963538705939

theorem tailTrace_121750 : CollatzResearch.WordTrace tailWord_121750 prefixEnd_121750 9261669582963538705939 := by
  unfold tailWord_121750
  simp only [CollatzResearch.WordTrace]
  refine ⟨277536706808001130604669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2960391539285345393116469 277536706808001130604669)
  ·
    refine ⟨104076265053000423976751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277536706808001130604669 104076265053000423976751)
    ·
      refine ⟨156114397579500635965127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104076265053000423976751 156114397579500635965127)
      ·
        refine ⟨234171596369250953947691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156114397579500635965127 234171596369250953947691)
        ·
          refine ⟨351257394553876430921537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234171596369250953947691 351257394553876430921537)
          ·
            refine ⟨263443045915407323191153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351257394553876430921537 263443045915407323191153)
            ·
              refine ⟨197582284436555492393365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263443045915407323191153 197582284436555492393365)
              ·
                refine ⟨9261669582963538705939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197582284436555492393365 9261669582963538705939)
                ·
                  rfl

theorem cell21_121750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_121750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121750 prefixEnd_121750 := by exact prefixLift 121750
  have htrace : WordTrace (prefixWord ++ tailWord_121750) baseStart_121750 baseEnd_121750 := by
    simpa [prefixWord, tailWord_121750, baseEnd_121750] using wordTrace_append hprefix tailTrace_121750
  have hstable : (prefixWord ++ tailWord_121750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121750).length < 2 ^ (prefixWord ++ tailWord_121750).sum := by decide
  have hdescent : baseEnd_121750 < baseStart_121750 := by decide
  rcases family_descends (prefixWord ++ tailWord_121750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121854 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_121854 : Nat := 118140960795 + 121854 * 2 ^ 59
def prefixEnd_121854 : Nat := 4983230072969 + 3 ^ 40 * 121854 * 2
def baseEnd_121854 : Nat := 27808742965809546384271

theorem tailTrace_121854 : CollatzResearch.WordTrace tailWord_121854 prefixEnd_121854 27808742965809546384271 := by
  unfold tailWord_121854
  simp only [CollatzResearch.WordTrace]
  refine ⟨555547562568905481432577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2962920333700829234307077 555547562568905481432577)
  ·
    refine ⟨416660671926679111074433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 555547562568905481432577 416660671926679111074433)
    ·
      refine ⟨312495503945009333305825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416660671926679111074433 312495503945009333305825)
      ·
        refine ⟨234371627958756999979369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312495503945009333305825 234371627958756999979369)
        ·
          refine ⟨175778720969067749984527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234371627958756999979369 175778720969067749984527)
          ·
            refine ⟨263668081453601624976791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175778720969067749984527 263668081453601624976791)
            ·
              refine ⟨395502122180402437465187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263668081453601624976791 395502122180402437465187)
              ·
                refine ⟨593253183270603656197781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395502122180402437465187 593253183270603656197781)
                ·
                  refine ⟨27808742965809546384271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 593253183270603656197781 27808742965809546384271)
                  ·
                    rfl

theorem cell21_121854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_121854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121854 prefixEnd_121854 := by exact prefixLift 121854
  have htrace : WordTrace (prefixWord ++ tailWord_121854) baseStart_121854 baseEnd_121854 := by
    simpa [prefixWord, tailWord_121854, baseEnd_121854] using wordTrace_append hprefix tailTrace_121854
  have hstable : (prefixWord ++ tailWord_121854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121854).length < 2 ^ (prefixWord ++ tailWord_121854).sum := by decide
  have hdescent : baseEnd_121854 < baseStart_121854 := by decide
  rcases family_descends (prefixWord ++ tailWord_121854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121885 : List Nat := [1, 4, 2, 2, 3, 2, 2, 5]
def baseStart_121885 : Nat := 118140960795 + 121885 * 2 ^ 59
def prefixEnd_121885 : Nat := 4983230072969 + 3 ^ 40 * 121885 * 2
def baseEnd_121885 : Nat := 9271939196053460455847

theorem tailTrace_121885 : CollatzResearch.WordTrace tailWord_121885 prefixEnd_121885 9271939196053460455847 := by
  unfold tailWord_121885
  simp only [CollatzResearch.WordTrace]
  refine ⟨4445511163438936145839109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2963674108959290763892739 4445511163438936145839109)
  ·
    refine ⟨833533343144800527344833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4445511163438936145839109 833533343144800527344833)
    ·
      refine ⟨625150007358600395508625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 833533343144800527344833 625150007358600395508625)
      ·
        refine ⟨468862505518950296631469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625150007358600395508625 468862505518950296631469)
        ·
          refine ⟨175823439569606361236801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468862505518950296631469 175823439569606361236801)
          ·
            refine ⟨131867579677204770927601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175823439569606361236801 131867579677204770927601)
            ·
              refine ⟨98900684757903578195701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131867579677204770927601 98900684757903578195701)
              ·
                refine ⟨9271939196053460455847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98900684757903578195701 9271939196053460455847)
                ·
                  rfl

theorem cell21_121885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 5].length) (baseStart_121885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121885 prefixEnd_121885 := by exact prefixLift 121885
  have htrace : WordTrace (prefixWord ++ tailWord_121885) baseStart_121885 baseEnd_121885 := by
    simpa [prefixWord, tailWord_121885, baseEnd_121885] using wordTrace_append hprefix tailTrace_121885
  have hstable : (prefixWord ++ tailWord_121885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121885).length < 2 ^ (prefixWord ++ tailWord_121885).sum := by decide
  have hdescent : baseEnd_121885 < baseStart_121885 := by decide
  rcases family_descends (prefixWord ++ tailWord_121885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121916 : List Nat := [2, 2, 2, 2, 2, 3, 3, 2, 3]
def baseStart_121916 : Nat := 118140960795 + 121916 * 2 ^ 59
def prefixEnd_121916 : Nat := 4983230072969 + 3 ^ 40 * 121916 * 2
def baseEnd_121916 : Nat := 27822892210511216350811

theorem tailTrace_121916 : CollatzResearch.WordTrace tailWord_121916 prefixEnd_121916 27822892210511216350811 := by
  unfold tailWord_121916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223320913163314220108801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2964427884217752293478401 2223320913163314220108801)
  ·
    refine ⟨1667490684872485665081601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2223320913163314220108801 1667490684872485665081601)
    ·
      refine ⟨1250618013654364248811201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1667490684872485665081601 1250618013654364248811201)
      ·
        refine ⟨937963510240773186608401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1250618013654364248811201 937963510240773186608401)
        ·
          refine ⟨703472632680579889956301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937963510240773186608401 703472632680579889956301)
          ·
            refine ⟨263802237255217458733613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 703472632680579889956301 263802237255217458733613)
            ·
              refine ⟨98925838970706547025105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263802237255217458733613 98925838970706547025105)
              ·
                refine ⟨74194379228029910268829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98925838970706547025105 74194379228029910268829)
                ·
                  refine ⟨27822892210511216350811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74194379228029910268829 27822892210511216350811)
                  ·
                    rfl

theorem cell21_121916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_121916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121916 prefixEnd_121916 := by exact prefixLift 121916
  have htrace : WordTrace (prefixWord ++ tailWord_121916) baseStart_121916 baseEnd_121916 := by
    simpa [prefixWord, tailWord_121916, baseEnd_121916] using wordTrace_append hprefix tailTrace_121916
  have hstable : (prefixWord ++ tailWord_121916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121916).length < 2 ^ (prefixWord ++ tailWord_121916).sum := by decide
  have hdescent : baseEnd_121916 < baseStart_121916 := by decide
  rcases family_descends (prefixWord ++ tailWord_121916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121927 : List Nat := [1, 1, 4, 1, 3, 3, 2, 6]
def baseStart_121927 : Nat := 118140960795 + 121927 * 2 ^ 59
def prefixEnd_121927 : Nat := 4983230072969 + 3 ^ 40 * 121927 * 2
def baseEnd_121927 : Nat := 9275134186792547222485

theorem tailTrace_121927 : CollatzResearch.WordTrace tailWord_121927 prefixEnd_121927 9275134186792547222485 := by
  unfold tailWord_121927
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447043029286777318868035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2964695352857851545912023 4447043029286777318868035)
  ·
    refine ⟨6670564543930165978302053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4447043029286777318868035 6670564543930165978302053)
    ·
      refine ⟨1250730851986906120931635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6670564543930165978302053 1250730851986906120931635)
      ·
        refine ⟨1876096277980359181397453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250730851986906120931635 1876096277980359181397453)
        ·
          refine ⟨703536104242634693024045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1876096277980359181397453 703536104242634693024045)
          ·
            refine ⟨263826039090988009884017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 703536104242634693024045 263826039090988009884017)
            ·
              refine ⟨197869529318241007413013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263826039090988009884017 197869529318241007413013)
              ·
                refine ⟨9275134186792547222485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197869529318241007413013 9275134186792547222485)
                ·
                  rfl

theorem cell21_121927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 6].length) (baseStart_121927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121927 prefixEnd_121927 := by exact prefixLift 121927
  have htrace : WordTrace (prefixWord ++ tailWord_121927) baseStart_121927 baseEnd_121927 := by
    simpa [prefixWord, tailWord_121927, baseEnd_121927] using wordTrace_append hprefix tailTrace_121927
  have hstable : (prefixWord ++ tailWord_121927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121927).length < 2 ^ (prefixWord ++ tailWord_121927).sum := by decide
  have hdescent : baseEnd_121927 < baseStart_121927 := by decide
  rcases family_descends (prefixWord ++ tailWord_121927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121941 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 7]
def baseStart_121941 : Nat := 118140960795 + 121941 * 2 ^ 59
def prefixEnd_121941 : Nat := 4983230072969 + 3 ^ 40 * 121941 * 2
def baseEnd_121941 : Nat := 27828597551116728434093

theorem tailTrace_121941 : CollatzResearch.WordTrace tailWord_121941 prefixEnd_121941 27828597551116728434093 := by
  unfold tailWord_121941
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447553651236057709877677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2965035767490705139918451 4447553651236057709877677)
  ·
    refine ⟨1667832619213521641204129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4447553651236057709877677 1667832619213521641204129)
    ·
      refine ⟨1250874464410141230903097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1667832619213521641204129 1250874464410141230903097)
      ·
        refine ⟨938155848307605923177323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1250874464410141230903097 938155848307605923177323)
        ·
          refine ⟨1407233772461408884765985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938155848307605923177323 1407233772461408884765985)
          ·
            refine ⟨1055425329346056663574489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1407233772461408884765985 1055425329346056663574489)
            ·
              refine ⟨791568997009542497680867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055425329346056663574489 791568997009542497680867)
              ·
                refine ⟨1187353495514313746521301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791568997009542497680867 1187353495514313746521301)
                ·
                  refine ⟨27828597551116728434093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1187353495514313746521301 27828597551116728434093)
                  ·
                    rfl

theorem cell21_121941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_121941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_121941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_121941 prefixEnd_121941 := by exact prefixLift 121941
  have htrace : WordTrace (prefixWord ++ tailWord_121941) baseStart_121941 baseEnd_121941 := by
    simpa [prefixWord, tailWord_121941, baseEnd_121941] using wordTrace_append hprefix tailTrace_121941
  have hstable : (prefixWord ++ tailWord_121941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121941).length < 2 ^ (prefixWord ++ tailWord_121941).sum := by decide
  have hdescent : baseEnd_121941 < baseStart_121941 := by decide
  rcases family_descends (prefixWord ++ tailWord_121941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122017 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 7]
def baseStart_122017 : Nat := 118140960795 + 122017 * 2 ^ 59
def prefixEnd_122017 : Nat := 4983230072969 + 3 ^ 40 * 122017 * 2
def baseEnd_122017 : Nat := 27845941786557485167271

theorem tailTrace_122017 : CollatzResearch.WordTrace tailWord_122017 prefixEnd_122017 27845941786557485167271 := by
  unfold tailWord_122017
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450325598960722689644305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2966883732640481793096203 4450325598960722689644305)
  ·
    refine ⟨3337744199220542017233229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4450325598960722689644305 3337744199220542017233229)
    ·
      refine ⟨1251654074707703256462461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3337744199220542017233229 1251654074707703256462461)
      ·
        refine ⟨469370278015388721173423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1251654074707703256462461 469370278015388721173423)
        ·
          refine ⟨704055417023083081760135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469370278015388721173423 704055417023083081760135)
          ·
            refine ⟨1056083125534624622640203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704055417023083081760135 1056083125534624622640203)
            ·
              refine ⟨1584124688301936933960305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056083125534624622640203 1584124688301936933960305)
              ·
                refine ⟨1188093516226452700470229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584124688301936933960305 1188093516226452700470229)
                ·
                  refine ⟨27845941786557485167271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1188093516226452700470229 27845941786557485167271)
                  ·
                    rfl

theorem cell21_122017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_122017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122017 prefixEnd_122017 := by exact prefixLift 122017
  have htrace : WordTrace (prefixWord ++ tailWord_122017) baseStart_122017 baseEnd_122017 := by
    simpa [prefixWord, tailWord_122017, baseEnd_122017] using wordTrace_append hprefix tailTrace_122017
  have hstable : (prefixWord ++ tailWord_122017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122017).length < 2 ^ (prefixWord ++ tailWord_122017).sum := by decide
  have hdescent : baseEnd_122017 < baseStart_122017 := by decide
  rcases family_descends (prefixWord ++ tailWord_122017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122034 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_122034 : Nat := 118140960795 + 122034 * 2 ^ 59
def prefixEnd_122034 : Nat := 4983230072969 + 3 ^ 40 * 122034 * 2
def baseEnd_122034 : Nat := 27849821418169233383903

theorem tailTrace_122034 : CollatzResearch.WordTrace tailWord_122034 prefixEnd_122034 27849821418169233383903 := by
  unfold tailWord_122034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112736409974783648253289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2967297093266089728675437 1112736409974783648253289)
  ·
    refine ⟨834552307481087736189967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1112736409974783648253289 834552307481087736189967)
    ·
      refine ⟨1251828461221631604284951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834552307481087736189967 1251828461221631604284951)
      ·
        refine ⟨1877742691832447406427427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251828461221631604284951 1877742691832447406427427)
        ·
          refine ⟨2816614037748671109641141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877742691832447406427427 2816614037748671109641141)
          ·
            refine ⟨264057566038937916528857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2816614037748671109641141 264057566038937916528857)
            ·
              refine ⟨198043174529203437396643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264057566038937916528857 198043174529203437396643)
              ·
                refine ⟨297064761793805156094965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198043174529203437396643 297064761793805156094965)
                ·
                  refine ⟨27849821418169233383903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 297064761793805156094965 27849821418169233383903)
                  ·
                    rfl

theorem cell21_122034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_122034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122034 prefixEnd_122034 := by exact prefixLift 122034
  have htrace : WordTrace (prefixWord ++ tailWord_122034) baseStart_122034 baseEnd_122034 := by
    simpa [prefixWord, tailWord_122034, baseEnd_122034] using wordTrace_append hprefix tailTrace_122034
  have hstable : (prefixWord ++ tailWord_122034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122034).length < 2 ^ (prefixWord ++ tailWord_122034).sum := by decide
  have hdescent : baseEnd_122034 < baseStart_122034 := by decide
  rcases family_descends (prefixWord ++ tailWord_122034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122054 : List Nat := [6, 1, 2, 2, 1, 1, 1, 7]
def baseStart_122054 : Nat := 118140960795 + 122054 * 2 ^ 59
def prefixEnd_122054 : Nat := 4983230072969 + 3 ^ 40 * 122054 * 2
def baseEnd_122054 : Nat := 9284795230217881016843

theorem tailTrace_122054 : CollatzResearch.WordTrace tailWord_122054 prefixEnd_122054 9284795230217881016843 := by
  unfold tailWord_122054
  simp only [CollatzResearch.WordTrace]
  refine ⟨139114846869583687773163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2967783399884452005827477 139114846869583687773163)
  ·
    refine ⟨208672270304375531659745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139114846869583687773163 208672270304375531659745)
    ·
      refine ⟨156504202728281648744809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208672270304375531659745 156504202728281648744809)
      ·
        refine ⟨117378152046211236558607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156504202728281648744809 117378152046211236558607)
        ·
          refine ⟨176067228069316854837911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117378152046211236558607 176067228069316854837911)
          ·
            refine ⟨264100842103975282256867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176067228069316854837911 264100842103975282256867)
            ·
              refine ⟨396151263155962923385301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264100842103975282256867 396151263155962923385301)
              ·
                refine ⟨9284795230217881016843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 396151263155962923385301 9284795230217881016843)
                ·
                  rfl

theorem cell21_122054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_122054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122054 prefixEnd_122054 := by exact prefixLift 122054
  have htrace : WordTrace (prefixWord ++ tailWord_122054) baseStart_122054 baseEnd_122054 := by
    simpa [prefixWord, tailWord_122054, baseEnd_122054] using wordTrace_append hprefix tailTrace_122054
  have hstable : (prefixWord ++ tailWord_122054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122054).length < 2 ^ (prefixWord ++ tailWord_122054).sum := by decide
  have hdescent : baseEnd_122054 < baseStart_122054 := by decide
  rcases family_descends (prefixWord ++ tailWord_122054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122138 : List Nat := [3, 1, 1, 3, 3, 10]
def baseStart_122138 : Nat := 118140960795 + 122138 * 2 ^ 59
def prefixEnd_122138 : Nat := 4983230072969 + 3 ^ 40 * 122138 * 2
def baseEnd_122138 : Nat := 1032353912410672727791

theorem tailTrace_122138 : CollatzResearch.WordTrace tailWord_122138 prefixEnd_122138 1032353912410672727791 := by
  unfold tailWord_122138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113684707880590088699767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2969825887681573569866045 1113684707880590088699767)
  ·
    refine ⟨1670527061820885133049651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1113684707880590088699767 1670527061820885133049651)
    ·
      refine ⟨2505790592731327699574477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670527061820885133049651 2505790592731327699574477)
      ·
        refine ⟨939671472274247887340429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2505790592731327699574477 939671472274247887340429)
        ·
          refine ⟨352376802102842957752661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 939671472274247887340429 352376802102842957752661)
          ·
            refine ⟨1032353912410672727791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 352376802102842957752661 1032353912410672727791)
            ·
              rfl

theorem cell21_122138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 10].length) (baseStart_122138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122138 prefixEnd_122138 := by exact prefixLift 122138
  have htrace : WordTrace (prefixWord ++ tailWord_122138) baseStart_122138 baseEnd_122138 := by
    simpa [prefixWord, tailWord_122138, baseEnd_122138] using wordTrace_append hprefix tailTrace_122138
  have hstable : (prefixWord ++ tailWord_122138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122138).length < 2 ^ (prefixWord ++ tailWord_122138).sum := by decide
  have hdescent : baseEnd_122138 < baseStart_122138 := by decide
  rcases family_descends (prefixWord ++ tailWord_122138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122141 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 4]
def baseStart_122141 : Nat := 118140960795 + 122141 * 2 ^ 59
def prefixEnd_122141 : Nat := 4983230072969 + 3 ^ 40 * 122141 * 2
def baseEnd_122141 : Nat := 27874240275960825100351

theorem tailTrace_122141 : CollatzResearch.WordTrace tailWord_122141 prefixEnd_122141 27874240275960825100351 := by
  unfold tailWord_122141
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454848250511491867158277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2969898833674327911438851 4454848250511491867158277)
  ·
    refine ⟨835284046970904725092177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4454848250511491867158277 835284046970904725092177)
    ·
      refine ⟨626463035228178543819133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 835284046970904725092177 626463035228178543819133)
      ·
        refine ⟨234923638210566953932175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 626463035228178543819133 234923638210566953932175)
        ·
          refine ⟨352385457315850430898263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234923638210566953932175 352385457315850430898263)
          ·
            refine ⟨528578185973775646347395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352385457315850430898263 528578185973775646347395)
            ·
              refine ⟨792867278960663469521093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528578185973775646347395 792867278960663469521093)
              ·
                refine ⟨148662614805124400535205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 792867278960663469521093 148662614805124400535205)
                ·
                  refine ⟨27874240275960825100351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148662614805124400535205 27874240275960825100351)
                  ·
                    rfl

theorem cell21_122141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_122141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122141 prefixEnd_122141 := by exact prefixLift 122141
  have htrace : WordTrace (prefixWord ++ tailWord_122141) baseStart_122141 baseEnd_122141 := by
    simpa [prefixWord, tailWord_122141, baseEnd_122141] using wordTrace_append hprefix tailTrace_122141
  have hstable : (prefixWord ++ tailWord_122141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122141).length < 2 ^ (prefixWord ++ tailWord_122141).sum := by decide
  have hdescent : baseEnd_122141 < baseStart_122141 := by decide
  rcases family_descends (prefixWord ++ tailWord_122141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122268 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 4]
def baseStart_122268 : Nat := 118140960795 + 122268 * 2 ^ 59
def prefixEnd_122268 : Nat := 4983230072969 + 3 ^ 40 * 122268 * 2
def baseEnd_122268 : Nat := 27903223406236826483425

theorem tailTrace_122268 : CollatzResearch.WordTrace tailWord_122268 prefixEnd_122268 27903223406236826483425 := by
  unfold tailWord_122268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229740160525696278515729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2972986880700928371354305 2229740160525696278515729)
  ·
    refine ⟨1672305120394272208886797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2229740160525696278515729 1672305120394272208886797)
    ·
      refine ⟨627114420147852078332549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1672305120394272208886797 627114420147852078332549)
      ·
        refine ⟨117583953777722264687353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 627114420147852078332549 117583953777722264687353)
        ·
          refine ⟨88187965333291698515515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117583953777722264687353 88187965333291698515515)
          ·
            refine ⟨132281947999937547773273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88187965333291698515515 132281947999937547773273)
            ·
              refine ⟨99211460999953160829955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132281947999937547773273 99211460999953160829955)
              ·
                refine ⟨148817191499929741244933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99211460999953160829955 148817191499929741244933)
                ·
                  refine ⟨27903223406236826483425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148817191499929741244933 27903223406236826483425)
                  ·
                    rfl

theorem cell21_122268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_122268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122268 prefixEnd_122268 := by exact prefixLift 122268
  have htrace : WordTrace (prefixWord ++ tailWord_122268) baseStart_122268 baseEnd_122268 := by
    simpa [prefixWord, tailWord_122268, baseEnd_122268] using wordTrace_append hprefix tailTrace_122268
  have hstable : (prefixWord ++ tailWord_122268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122268).length < 2 ^ (prefixWord ++ tailWord_122268).sum := by decide
  have hdescent : baseEnd_122268 < baseStart_122268 := by decide
  rcases family_descends (prefixWord ++ tailWord_122268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122324 : List Nat := [2, 4, 1, 2, 3, 2, 1, 6]
def baseStart_122324 : Nat := 118140960795 + 122324 * 2 ^ 59
def prefixEnd_122324 : Nat := 4983230072969 + 3 ^ 40 * 122324 * 2
def baseEnd_122324 : Nat := 9305334456397724516659

theorem tailTrace_122324 : CollatzResearch.WordTrace tailWord_122324 prefixEnd_122324 9305334456397724516659 := by
  unfold tailWord_122324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230761404424257060535013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2974348539232342747380017 2230761404424257060535013)
  ·
    refine ⟨418267763329548198850315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2230761404424257060535013 418267763329548198850315)
    ·
      refine ⟨627401644994322298275473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418267763329548198850315 627401644994322298275473)
      ·
        refine ⟨470551233745741723706605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627401644994322298275473 470551233745741723706605)
        ·
          refine ⟨176456712654653146389977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470551233745741723706605 176456712654653146389977)
          ·
            refine ⟨132342534490989859792483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176456712654653146389977 132342534490989859792483)
            ·
              refine ⟨198513801736484789688725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132342534490989859792483 198513801736484789688725)
              ·
                refine ⟨9305334456397724516659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198513801736484789688725 9305334456397724516659)
                ·
                  rfl

theorem cell21_122324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_122324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122324 prefixEnd_122324 := by exact prefixLift 122324
  have htrace : WordTrace (prefixWord ++ tailWord_122324) baseStart_122324 baseEnd_122324 := by
    simpa [prefixWord, tailWord_122324, baseEnd_122324] using wordTrace_append hprefix tailTrace_122324
  have hstable : (prefixWord ++ tailWord_122324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122324).length < 2 ^ (prefixWord ++ tailWord_122324).sum := by decide
  have hdescent : baseEnd_122324 < baseStart_122324 := by decide
  rcases family_descends (prefixWord ++ tailWord_122324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122397 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 5]
def baseStart_122397 : Nat := 118140960795 + 122397 * 2 ^ 59
def prefixEnd_122397 : Nat := 4983230072969 + 3 ^ 40 * 122397 * 2
def baseEnd_122397 : Nat := 27932662963761268833161

theorem tailTrace_122397 : CollatzResearch.WordTrace tailWord_122397 prefixEnd_122397 27932662963761268833161 := by
  unfold tailWord_122397
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464185337584047588477445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2976123558389365058984963 4464185337584047588477445)
  ·
    refine ⟨837034750797008922839521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4464185337584047588477445 837034750797008922839521)
    ·
      refine ⟨627776063097756692129641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 837034750797008922839521 627776063097756692129641)
      ·
        refine ⟨470832047323317519097231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627776063097756692129641 470832047323317519097231)
        ·
          refine ⟨706248070984976278645847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470832047323317519097231 706248070984976278645847)
          ·
            refine ⟨1059372106477464417968771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706248070984976278645847 1059372106477464417968771)
            ·
              refine ⟨1589058159716196626953157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059372106477464417968771 1589058159716196626953157)
              ·
                refine ⟨297948404946786867553717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1589058159716196626953157 297948404946786867553717)
                ·
                  refine ⟨27932662963761268833161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 297948404946786867553717 27932662963761268833161)
                  ·
                    rfl

theorem cell21_122397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_122397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122397 prefixEnd_122397 := by exact prefixLift 122397
  have htrace : WordTrace (prefixWord ++ tailWord_122397) baseStart_122397 baseEnd_122397 := by
    simpa [prefixWord, tailWord_122397, baseEnd_122397] using wordTrace_append hprefix tailTrace_122397
  have hstable : (prefixWord ++ tailWord_122397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122397).length < 2 ^ (prefixWord ++ tailWord_122397).sum := by decide
  have hdescent : baseEnd_122397 < baseStart_122397 := by decide
  rcases family_descends (prefixWord ++ tailWord_122397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122400 : List Nat := [2, 1, 1, 6, 1, 3, 2, 5]
def baseStart_122400 : Nat := 118140960795 + 122400 * 2 ^ 59
def prefixEnd_122400 : Nat := 4983230072969 + 3 ^ 40 * 122400 * 2
def baseEnd_122400 : Nat := 9311115868211310094385

theorem tailTrace_122400 : CollatzResearch.WordTrace tailWord_122400 prefixEnd_122400 9311115868211310094385 := by
  unfold tailWord_122400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232147378286589550418327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2976196504382119400557769 2232147378286589550418327)
  ·
    refine ⟨3348221067429884325627491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2232147378286589550418327 3348221067429884325627491)
    ·
      refine ⟨5022331601144826488441237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348221067429884325627491 5022331601144826488441237)
      ·
        refine ⟨235421793803663741645683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5022331601144826488441237 235421793803663741645683)
        ·
          refine ⟨353132690705495612468525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235421793803663741645683 353132690705495612468525)
          ·
            refine ⟨132424759014560854675697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353132690705495612468525 132424759014560854675697)
            ·
              refine ⟨99318569260920641006773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132424759014560854675697 99318569260920641006773)
              ·
                refine ⟨9311115868211310094385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99318569260920641006773 9311115868211310094385)
                ·
                  rfl

theorem cell21_122400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_122400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122400 prefixEnd_122400 := by exact prefixLift 122400
  have htrace : WordTrace (prefixWord ++ tailWord_122400) baseStart_122400 baseEnd_122400 := by
    simpa [prefixWord, tailWord_122400, baseEnd_122400] using wordTrace_append hprefix tailTrace_122400
  have hstable : (prefixWord ++ tailWord_122400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122400).length < 2 ^ (prefixWord ++ tailWord_122400).sum := by decide
  have hdescent : baseEnd_122400 < baseStart_122400 := by decide
  rcases family_descends (prefixWord ++ tailWord_122400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122431 : List Nat := [1, 1, 2, 2, 3, 4, 3, 2, 3]
def baseStart_122431 : Nat := 118140960795 + 122431 * 2 ^ 59
def prefixEnd_122431 : Nat := 4983230072969 + 3 ^ 40 * 122431 * 2
def baseEnd_122431 : Nat := 27940422226984765266425

theorem tailTrace_122431 : CollatzResearch.WordTrace tailWord_122431 prefixEnd_122431 27940422226984765266425 := by
  unfold tailWord_122431
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465425419460871395215147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2976950279640580930143431 4465425419460871395215147)
  ·
    refine ⟨6698138129191307092822721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4465425419460871395215147 6698138129191307092822721)
    ·
      refine ⟨5023603596893480319617041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6698138129191307092822721 5023603596893480319617041)
      ·
        refine ⟨3767702697670110239712781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5023603596893480319617041 3767702697670110239712781)
        ·
          refine ⟨1412888511626291339892293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3767702697670110239712781 1412888511626291339892293)
          ·
            refine ⟨264916595929929626229805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1412888511626291339892293 264916595929929626229805)
            ·
              refine ⟨99343723473723609836177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264916595929929626229805 99343723473723609836177)
              ·
                refine ⟨74507792605292707377133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99343723473723609836177 74507792605292707377133)
                ·
                  refine ⟨27940422226984765266425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74507792605292707377133 27940422226984765266425)
                  ·
                    rfl

theorem cell21_122431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 3].length) (baseStart_122431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122431 prefixEnd_122431 := by exact prefixLift 122431
  have htrace : WordTrace (prefixWord ++ tailWord_122431) baseStart_122431 baseEnd_122431 := by
    simpa [prefixWord, tailWord_122431, baseEnd_122431] using wordTrace_append hprefix tailTrace_122431
  have hstable : (prefixWord ++ tailWord_122431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122431).length < 2 ^ (prefixWord ++ tailWord_122431).sum := by decide
  have hdescent : baseEnd_122431 < baseStart_122431 := by decide
  rcases family_descends (prefixWord ++ tailWord_122431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122442 : List Nat := [3, 1, 2, 1, 1, 3, 4, 6]
def baseStart_122442 : Nat := 118140960795 + 122442 * 2 ^ 59
def prefixEnd_122442 : Nat := 4983230072969 + 3 ^ 40 * 122442 * 2
def baseEnd_122442 : Nat := 9314310858950396861023

theorem tailTrace_122442 : CollatzResearch.WordTrace tailWord_122442 prefixEnd_122442 9314310858950396861023 := by
  unfold tailWord_122442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116456655605255068466395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2977217748280680182577053 1116456655605255068466395)
  ·
    refine ⟨1674684983407882602699593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1116456655605255068466395 1674684983407882602699593)
    ·
      refine ⟨1256013737555911952024695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1674684983407882602699593 1256013737555911952024695)
      ·
        refine ⟨1884020606333867928037043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256013737555911952024695 1884020606333867928037043)
        ·
          refine ⟨2826030909500801892055565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884020606333867928037043 2826030909500801892055565)
          ·
            refine ⟨1059761591062800709520837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2826030909500801892055565 1059761591062800709520837)
            ·
              refine ⟨198705298324275133035157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1059761591062800709520837 198705298324275133035157)
              ·
                refine ⟨9314310858950396861023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198705298324275133035157 9314310858950396861023)
                ·
                  rfl

theorem cell21_122442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_122442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122442 prefixEnd_122442 := by exact prefixLift 122442
  have htrace : WordTrace (prefixWord ++ tailWord_122442) baseStart_122442 baseEnd_122442 := by
    simpa [prefixWord, tailWord_122442, baseEnd_122442] using wordTrace_append hprefix tailTrace_122442
  have hstable : (prefixWord ++ tailWord_122442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122442).length < 2 ^ (prefixWord ++ tailWord_122442).sum := by decide
  have hdescent : baseEnd_122442 < baseStart_122442 := by decide
  rcases family_descends (prefixWord ++ tailWord_122442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122456 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_122456 : Nat := 118140960795 + 122456 * 2 ^ 59
def prefixEnd_122456 : Nat := 4983230072969 + 3 ^ 40 * 122456 * 2
def baseEnd_122456 : Nat := 27946127567590277349707

theorem tailTrace_122456 : CollatzResearch.WordTrace tailWord_122456 prefixEnd_122456 27946127567590277349707 := by
  unfold tailWord_122456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233168622185150332437611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2977558162913533776583481 2233168622185150332437611)
  ·
    refine ⟨3349752933277725498656417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2233168622185150332437611 3349752933277725498656417)
    ·
      refine ⟨2512314699958294123992313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3349752933277725498656417 2512314699958294123992313)
      ·
        refine ⟨1884236024968720592994235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2512314699958294123992313 1884236024968720592994235)
        ·
          refine ⟨2826354037453080889491353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884236024968720592994235 2826354037453080889491353)
          ·
            refine ⟨2119765528089810667118515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826354037453080889491353 2119765528089810667118515)
            ·
              refine ⟨3179648292134716000677773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119765528089810667118515 3179648292134716000677773)
              ·
                refine ⟨1192368109550518500254165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3179648292134716000677773 1192368109550518500254165)
                ·
                  refine ⟨27946127567590277349707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1192368109550518500254165 27946127567590277349707)
                  ·
                    rfl

theorem cell21_122456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_122456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122456 prefixEnd_122456 := by exact prefixLift 122456
  have htrace : WordTrace (prefixWord ++ tailWord_122456) baseStart_122456 baseEnd_122456 := by
    simpa [prefixWord, tailWord_122456, baseEnd_122456] using wordTrace_append hprefix tailTrace_122456
  have hstable : (prefixWord ++ tailWord_122456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122456).length < 2 ^ (prefixWord ++ tailWord_122456).sum := by decide
  have hdescent : baseEnd_122456 < baseStart_122456 := by decide
  rcases family_descends (prefixWord ++ tailWord_122456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122580 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_122580 : Nat := 118140960795 + 122580 * 2 ^ 59
def prefixEnd_122580 : Nat := 4983230072969 + 3 ^ 40 * 122580 * 2
def baseEnd_122580 : Nat := 27974426056993617282787

theorem tailTrace_122580 : CollatzResearch.WordTrace tailWord_122580 prefixEnd_122580 27974426056993617282787 := by
  unfold tailWord_122580
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235429947960534921194597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2980573263947379894926129 2235429947960534921194597)
  ·
    refine ⟨419143115242600297723987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2235429947960534921194597 419143115242600297723987)
    ·
      refine ⟨628714672863900446585981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419143115242600297723987 628714672863900446585981)
      ·
        refine ⟨235768002323962667469743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628714672863900446585981 235768002323962667469743)
        ·
          refine ⟨353652003485944001204615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235768002323962667469743 353652003485944001204615)
          ·
            refine ⟨530478005228916001806923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353652003485944001204615 530478005228916001806923)
            ·
              refine ⟨795717007843374002710385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530478005228916001806923 795717007843374002710385)
              ·
                refine ⟨596787755882530502032789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795717007843374002710385 596787755882530502032789)
                ·
                  refine ⟨27974426056993617282787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 596787755882530502032789 27974426056993617282787)
                  ·
                    rfl

theorem cell21_122580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_122580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122580 prefixEnd_122580 := by exact prefixLift 122580
  have htrace : WordTrace (prefixWord ++ tailWord_122580) baseStart_122580 baseEnd_122580 := by
    simpa [prefixWord, tailWord_122580, baseEnd_122580] using wordTrace_append hprefix tailTrace_122580
  have hstable : (prefixWord ++ tailWord_122580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122580).length < 2 ^ (prefixWord ++ tailWord_122580).sum := by decide
  have hdescent : baseEnd_122580 < baseStart_122580 := by decide
  rcases family_descends (prefixWord ++ tailWord_122580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122608 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_122608 : Nat := 118140960795 + 122608 * 2 ^ 59
def prefixEnd_122608 : Nat := 4983230072969 + 3 ^ 40 * 122608 * 2
def baseEnd_122608 : Nat := 27980816038471790816063

theorem tailTrace_122608 : CollatzResearch.WordTrace tailWord_122608 prefixEnd_122608 27980816038471790816063 := by
  unfold tailWord_122608
  simp only [CollatzResearch.WordTrace]
  refine ⟨2235940569909815312204239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2981254093213087082938985 2235940569909815312204239)
  ·
    refine ⟨3353910854864722968306359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2235940569909815312204239 3353910854864722968306359)
    ·
      refine ⟨5030866282297084452459539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353910854864722968306359 5030866282297084452459539)
      ·
        refine ⟨7546299423445626678689309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5030866282297084452459539 7546299423445626678689309)
        ·
          refine ⟨2829862283792110004508491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7546299423445626678689309 2829862283792110004508491)
          ·
            refine ⟨4244793425688165006762737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829862283792110004508491 4244793425688165006762737)
            ·
              refine ⟨3183595069266123755072053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244793425688165006762737 3183595069266123755072053)
              ·
                refine ⟨298462037743699102038005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3183595069266123755072053 298462037743699102038005)
                ·
                  refine ⟨27980816038471790816063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 298462037743699102038005 27980816038471790816063)
                  ·
                    rfl

theorem cell21_122608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_122608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122608 prefixEnd_122608 := by exact prefixLift 122608
  have htrace : WordTrace (prefixWord ++ tailWord_122608) baseStart_122608 baseEnd_122608 := by
    simpa [prefixWord, tailWord_122608, baseEnd_122608] using wordTrace_append hprefix tailTrace_122608
  have hstable : (prefixWord ++ tailWord_122608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122608).length < 2 ^ (prefixWord ++ tailWord_122608).sum := by decide
  have hdescent : baseEnd_122608 < baseStart_122608 := by decide
  rcases family_descends (prefixWord ++ tailWord_122608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122614 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_122614 : Nat := 118140960795 + 122614 * 2 ^ 59
def prefixEnd_122614 : Nat := 4983230072969 + 3 ^ 40 * 122614 * 2
def baseEnd_122614 : Nat := 27982185320217113716051

theorem tailTrace_122614 : CollatzResearch.WordTrace tailWord_122614 prefixEnd_122614 27982185320217113716051 := by
  unfold tailWord_122614
  simp only [CollatzResearch.WordTrace]
  refine ⟨279506248612368353070431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2981399985198595766084597 279506248612368353070431)
  ·
    refine ⟨419259372918552529605647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279506248612368353070431 419259372918552529605647)
    ·
      refine ⟨628889059377828794408471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419259372918552529605647 628889059377828794408471)
      ·
        refine ⟨943333589066743191612707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628889059377828794408471 943333589066743191612707)
        ·
          refine ⟨1415000383600114787419061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943333589066743191612707 1415000383600114787419061)
          ·
            refine ⟨132656285962510761320537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1415000383600114787419061 132656285962510761320537)
            ·
              refine ⟨99492214471883070990403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132656285962510761320537 99492214471883070990403)
              ·
                refine ⟨149238321707824606485605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99492214471883070990403 149238321707824606485605)
                ·
                  refine ⟨27982185320217113716051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149238321707824606485605 27982185320217113716051)
                  ·
                    rfl

theorem cell21_122614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_122614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122614 prefixEnd_122614 := by exact prefixLift 122614
  have htrace : WordTrace (prefixWord ++ tailWord_122614) baseStart_122614 baseEnd_122614 := by
    simpa [prefixWord, tailWord_122614, baseEnd_122614] using wordTrace_append hprefix tailTrace_122614
  have hstable : (prefixWord ++ tailWord_122614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122614).length < 2 ^ (prefixWord ++ tailWord_122614).sum := by decide
  have hdescent : baseEnd_122614 < baseStart_122614 := by decide
  rcases family_descends (prefixWord ++ tailWord_122614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122653 : List Nat := [1, 4, 2, 14]
def baseStart_122653 : Nat := 118140960795 + 122653 * 2 ^ 59
def prefixEnd_122653 : Nat := 4983230072969 + 3 ^ 40 * 122653 * 2
def baseEnd_122653 : Nat := 115189652887085236897

theorem tailTrace_122653 : CollatzResearch.WordTrace tailWord_122653 prefixEnd_122653 115189652887085236897 := by
  unfold tailWord_122653
  simp only [CollatzResearch.WordTrace]
  refine ⟨4473522424656603309796613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2982348283104402206531075 4473522424656603309796613)
  ·
    refine ⟨838785454623113120586865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4473522424656603309796613 838785454623113120586865)
    ·
      refine ⟨629089090967334840440149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 838785454623113120586865 629089090967334840440149)
      ·
        refine ⟨115189652887085236897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 629089090967334840440149 115189652887085236897)
        ·
          rfl

theorem cell21_122653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 14].length) (baseStart_122653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122653 prefixEnd_122653 := by exact prefixLift 122653
  have htrace : WordTrace (prefixWord ++ tailWord_122653) baseStart_122653 baseEnd_122653 := by
    simpa [prefixWord, tailWord_122653, baseEnd_122653] using wordTrace_append hprefix tailTrace_122653
  have hstable : (prefixWord ++ tailWord_122653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122653).length < 2 ^ (prefixWord ++ tailWord_122653).sum := by decide
  have hdescent : baseEnd_122653 < baseStart_122653 := by decide
  rcases family_descends (prefixWord ++ tailWord_122653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122656 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_122656 : Nat := 118140960795 + 122656 * 2 ^ 59
def prefixEnd_122656 : Nat := 4983230072969 + 3 ^ 40 * 122656 * 2
def baseEnd_122656 : Nat := 27991770292434374015965

theorem tailTrace_122656 : CollatzResearch.WordTrace tailWord_122656 prefixEnd_122656 27991770292434374015965 := by
  unfold tailWord_122656
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236815921822867411077911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2982421229097156548103881 2236815921822867411077911)
  ·
    refine ⟨3355223882734301116616867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2236815921822867411077911 3355223882734301116616867)
    ·
      refine ⟨5032835824101451674925301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3355223882734301116616867 5032835824101451674925301)
      ·
        refine ⟨471828358509511094524247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5032835824101451674925301 471828358509511094524247)
        ·
          refine ⟨707742537764266641786371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471828358509511094524247 707742537764266641786371)
          ·
            refine ⟨1061613806646399962679557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707742537764266641786371 1061613806646399962679557)
            ·
              refine ⟨199052588746199993002417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1061613806646399962679557 199052588746199993002417)
              ·
                refine ⟨149289441559649994751813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199052588746199993002417 149289441559649994751813)
                ·
                  refine ⟨27991770292434374015965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149289441559649994751813 27991770292434374015965)
                  ·
                    rfl

theorem cell21_122656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_122656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122656 prefixEnd_122656 := by exact prefixLift 122656
  have htrace : WordTrace (prefixWord ++ tailWord_122656) baseStart_122656 baseEnd_122656 := by
    simpa [prefixWord, tailWord_122656, baseEnd_122656] using wordTrace_append hprefix tailTrace_122656
  have hstable : (prefixWord ++ tailWord_122656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122656).length < 2 ^ (prefixWord ++ tailWord_122656).sum := by decide
  have hdescent : baseEnd_122656 < baseStart_122656 := by decide
  rcases family_descends (prefixWord ++ tailWord_122656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122684 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_122684 : Nat := 118140960795 + 122684 * 2 ^ 59
def prefixEnd_122684 : Nat := 4983230072969 + 3 ^ 40 * 122684 * 2
def baseEnd_122684 : Nat := 27998160273912547549241

theorem tailTrace_122684 : CollatzResearch.WordTrace tailWord_122684 prefixEnd_122684 27998160273912547549241 := by
  unfold tailWord_122684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237326543772147802087553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2983102058362863736116737 2237326543772147802087553)
  ·
    refine ⟨1677994907829110851565665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2237326543772147802087553 1677994907829110851565665)
    ·
      refine ⟨1258496180871833138674249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1677994907829110851565665 1258496180871833138674249)
      ·
        refine ⟨943872135653874854005687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1258496180871833138674249 943872135653874854005687)
        ·
          refine ⟨1415808203480812281008531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943872135653874854005687 1415808203480812281008531)
          ·
            refine ⟨2123712305221218421512797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415808203480812281008531 2123712305221218421512797)
            ·
              refine ⟨796392114457956908067299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2123712305221218421512797 796392114457956908067299)
              ·
                refine ⟨1194588171686935362100949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796392114457956908067299 1194588171686935362100949)
                ·
                  refine ⟨27998160273912547549241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1194588171686935362100949 27998160273912547549241)
                  ·
                    rfl

theorem cell21_122684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_122684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122684 prefixEnd_122684 := by exact prefixLift 122684
  have htrace : WordTrace (prefixWord ++ tailWord_122684) baseStart_122684 baseEnd_122684 := by
    simpa [prefixWord, tailWord_122684, baseEnd_122684] using wordTrace_append hprefix tailTrace_122684
  have hstable : (prefixWord ++ tailWord_122684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122684).length < 2 ^ (prefixWord ++ tailWord_122684).sum := by decide
  have hdescent : baseEnd_122684 < baseStart_122684 := by decide
  rcases family_descends (prefixWord ++ tailWord_122684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122687 : List Nat := [1, 1, 2, 2, 6, 1, 3, 5]
def baseStart_122687 : Nat := 118140960795 + 122687 * 2 ^ 59
def prefixEnd_122687 : Nat := 4983230072969 + 3 ^ 40 * 122687 * 2
def baseEnd_122687 : Nat := 9332948304928402999745

theorem tailTrace_122687 : CollatzResearch.WordTrace tailWord_122687 prefixEnd_122687 9332948304928402999745 := by
  unfold tailWord_122687
  simp only [CollatzResearch.WordTrace]
  refine ⟨4474762506533427116534315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2983175004355618077689543 4474762506533427116534315)
  ·
    refine ⟨6712143759800140674801473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4474762506533427116534315 6712143759800140674801473)
    ·
      refine ⟨5034107819850105506101105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6712143759800140674801473 5034107819850105506101105)
      ·
        refine ⟨3775580864887579129575829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5034107819850105506101105 3775580864887579129575829)
        ·
          refine ⟨176980353041605271698867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3775580864887579129575829 176980353041605271698867)
          ·
            refine ⟨265470529562407907548301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176980353041605271698867 265470529562407907548301)
            ·
              refine ⟨99551448585902965330613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265470529562407907548301 99551448585902965330613)
              ·
                refine ⟨9332948304928402999745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99551448585902965330613 9332948304928402999745)
                ·
                  rfl

theorem cell21_122687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 5].length) (baseStart_122687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122687 prefixEnd_122687 := by exact prefixLift 122687
  have htrace : WordTrace (prefixWord ++ tailWord_122687) baseStart_122687 baseEnd_122687 := by
    simpa [prefixWord, tailWord_122687, baseEnd_122687] using wordTrace_append hprefix tailTrace_122687
  have hstable : (prefixWord ++ tailWord_122687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122687).length < 2 ^ (prefixWord ++ tailWord_122687).sum := by decide
  have hdescent : baseEnd_122687 < baseStart_122687 := by decide
  rcases family_descends (prefixWord ++ tailWord_122687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122746 : List Nat := [3, 1, 1, 1, 1, 1, 8, 5]
def baseStart_122746 : Nat := 118140960795 + 122746 * 2 ^ 59
def prefixEnd_122746 : Nat := 4983230072969 + 3 ^ 40 * 122746 * 2
def baseEnd_122746 : Nat := 9337436506204739171927

theorem tailTrace_122746 : CollatzResearch.WordTrace tailWord_122746 prefixEnd_122746 9337436506204739171927 := by
  unfold tailWord_122746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119228603329920048233023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2984609608879786795288061 1119228603329920048233023)
  ·
    refine ⟨1678842904994880072349535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1119228603329920048233023 1678842904994880072349535)
    ·
      refine ⟨2518264357492320108524303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1678842904994880072349535 2518264357492320108524303)
      ·
        refine ⟨3777396536238480162786455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2518264357492320108524303 3777396536238480162786455)
        ·
          refine ⟨5666094804357720244179683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777396536238480162786455 5666094804357720244179683)
          ·
            refine ⟨8499142206536580366269525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666094804357720244179683 8499142206536580366269525)
            ·
              refine ⟨99599322732850551167221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 8499142206536580366269525 99599322732850551167221)
              ·
                refine ⟨9337436506204739171927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99599322732850551167221 9337436506204739171927)
                ·
                  rfl

theorem cell21_122746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_122746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122746 prefixEnd_122746 := by exact prefixLift 122746
  have htrace : WordTrace (prefixWord ++ tailWord_122746) baseStart_122746 baseEnd_122746 := by
    simpa [prefixWord, tailWord_122746, baseEnd_122746] using wordTrace_append hprefix tailTrace_122746
  have hstable : (prefixWord ++ tailWord_122746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122746).length < 2 ^ (prefixWord ++ tailWord_122746).sum := by decide
  have hdescent : baseEnd_122746 < baseStart_122746 := by decide
  rcases family_descends (prefixWord ++ tailWord_122746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122777 : List Nat := [1, 2, 1, 2, 1, 3, 2, 6, 3]
def baseStart_122777 : Nat := 118140960795 + 122777 * 2 ^ 59
def prefixEnd_122777 : Nat := 4983230072969 + 3 ^ 40 * 122777 * 2
def baseEnd_122777 : Nat := 28019384140965052499051

theorem tailTrace_122777 : CollatzResearch.WordTrace tailWord_122777 prefixEnd_122777 28019384140965052499051 := by
  unfold tailWord_122777
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478045076207372487310585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2985363384138248324873723 4478045076207372487310585)
  ·
    refine ⟨3358533807155529365482939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4478045076207372487310585 3358533807155529365482939)
    ·
      refine ⟨5037800710733294048224409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358533807155529365482939 5037800710733294048224409)
      ·
        refine ⟨3778350533049970536168307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5037800710733294048224409 3778350533049970536168307)
        ·
          refine ⟨5667525799574955804252461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778350533049970536168307 5667525799574955804252461)
          ·
            refine ⟨2125322174840608426594673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5667525799574955804252461 2125322174840608426594673)
            ·
              refine ⟨1593991631130456319946005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125322174840608426594673 1593991631130456319946005)
              ·
                refine ⟨74718357709240139997469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1593991631130456319946005 74718357709240139997469)
                ·
                  refine ⟨28019384140965052499051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74718357709240139997469 28019384140965052499051)
                  ·
                    rfl

theorem cell21_122777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_122777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122777 prefixEnd_122777 := by exact prefixLift 122777
  have htrace : WordTrace (prefixWord ++ tailWord_122777) baseStart_122777 baseEnd_122777 := by
    simpa [prefixWord, tailWord_122777, baseEnd_122777] using wordTrace_append hprefix tailTrace_122777
  have hstable : (prefixWord ++ tailWord_122777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122777).length < 2 ^ (prefixWord ++ tailWord_122777).sum := by decide
  have hdescent : baseEnd_122777 < baseStart_122777 := by decide
  rcases family_descends (prefixWord ++ tailWord_122777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122881 : List Nat := [1, 2, 4, 1, 2, 1, 10]
def baseStart_122881 : Nat := 118140960795 + 122881 * 2 ^ 59
def prefixEnd_122881 : Nat := 4983230072969 + 3 ^ 40 * 122881 * 2
def baseEnd_122881 : Nat := 3115902039764886973945

theorem tailTrace_122881 : CollatzResearch.WordTrace tailWord_122881 prefixEnd_122881 3115902039764886973945 := by
  unfold tailWord_122881
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481838267830598249096497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2987892178553732166064331 4481838267830598249096497)
  ·
    refine ⟨3361378700872948686822373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4481838267830598249096497 3361378700872948686822373)
    ·
      refine ⟨630258506413677878779195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3361378700872948686822373 630258506413677878779195)
      ·
        refine ⟨945387759620516818168793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630258506413677878779195 945387759620516818168793)
        ·
          refine ⟨709040819715387613626595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945387759620516818168793 709040819715387613626595)
          ·
            refine ⟨1063561229573081420439893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709040819715387613626595 1063561229573081420439893)
            ·
              refine ⟨3115902039764886973945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1063561229573081420439893 3115902039764886973945)
              ·
                rfl

theorem cell21_122881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 10].length) (baseStart_122881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122881 prefixEnd_122881 := by exact prefixLift 122881
  have htrace : WordTrace (prefixWord ++ tailWord_122881) baseStart_122881 baseEnd_122881 := by
    simpa [prefixWord, tailWord_122881, baseEnd_122881] using wordTrace_append hprefix tailTrace_122881
  have hstable : (prefixWord ++ tailWord_122881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122881).length < 2 ^ (prefixWord ++ tailWord_122881).sum := by decide
  have hdescent : baseEnd_122881 < baseStart_122881 := by decide
  rcases family_descends (prefixWord ++ tailWord_122881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122901 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 4]
def baseStart_122901 : Nat := 118140960795 + 122901 * 2 ^ 59
def prefixEnd_122901 : Nat := 4983230072969 + 3 ^ 40 * 122901 * 2
def baseEnd_122901 : Nat := 28047682630368392432131

theorem tailTrace_122901 : CollatzResearch.WordTrace tailWord_122901 prefixEnd_122901 28047682630368392432131 := by
  unfold tailWord_122901
  simp only [CollatzResearch.WordTrace]
  refine ⟨4482567727758141664824557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2988378485172094443216371 4482567727758141664824557)
  ·
    refine ⟨1680962897909303124309209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4482567727758141664824557 1680962897909303124309209)
    ·
      refine ⟨1260722173431977343231907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1680962897909303124309209 1260722173431977343231907)
      ·
        refine ⟨1891083260147966014847861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260722173431977343231907 1891083260147966014847861)
        ·
          refine ⟨177289055638871813891987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1891083260147966014847861 177289055638871813891987)
          ·
            refine ⟨265933583458307720837981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177289055638871813891987 265933583458307720837981)
            ·
              refine ⟨99725093796865395314243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265933583458307720837981 99725093796865395314243)
              ·
                refine ⟨149587640695298092971365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99725093796865395314243 149587640695298092971365)
                ·
                  refine ⟨28047682630368392432131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149587640695298092971365 28047682630368392432131)
                  ·
                    rfl

theorem cell21_122901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_122901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122901 prefixEnd_122901 := by exact prefixLift 122901
  have htrace : WordTrace (prefixWord ++ tailWord_122901) baseStart_122901 baseEnd_122901 := by
    simpa [prefixWord, tailWord_122901, baseEnd_122901] using wordTrace_append hprefix tailTrace_122901
  have hstable : (prefixWord ++ tailWord_122901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122901).length < 2 ^ (prefixWord ++ tailWord_122901).sum := by decide
  have hdescent : baseEnd_122901 < baseStart_122901 := by decide
  rcases family_descends (prefixWord ++ tailWord_122901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_122932 : List Nat := [2, 5, 1, 2, 3, 1, 7]
def baseStart_122932 : Nat := 118140960795 + 122932 * 2 ^ 59
def prefixEnd_122932 : Nat := 4983230072969 + 3 ^ 40 * 122932 * 2
def baseEnd_122932 : Nat := 3117195250302136379489

theorem tailTrace_122932 : CollatzResearch.WordTrace tailWord_122932 prefixEnd_122932 3117195250302136379489 := by
  unfold tailWord_122932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2241849195322916979601525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2989132260430555972802033 2241849195322916979601525)
  ·
    refine ⟨210173362061523466837643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2241849195322916979601525 210173362061523466837643)
    ·
      refine ⟨315260043092285200256465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210173362061523466837643 315260043092285200256465)
      ·
        refine ⟨236445032319213900192349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315260043092285200256465 236445032319213900192349)
        ·
          refine ⟨88666887119705212572131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236445032319213900192349 88666887119705212572131)
          ·
            refine ⟨133000330679557818858197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88666887119705212572131 133000330679557818858197)
            ·
              refine ⟨3117195250302136379489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133000330679557818858197 3117195250302136379489)
              ·
                rfl

theorem cell21_122932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 7].length) (baseStart_122932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_122932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_122932 prefixEnd_122932 := by exact prefixLift 122932
  have htrace : WordTrace (prefixWord ++ tailWord_122932) baseStart_122932 baseEnd_122932 := by
    simpa [prefixWord, tailWord_122932, baseEnd_122932] using wordTrace_append hprefix tailTrace_122932
  have hstable : (prefixWord ++ tailWord_122932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_122932).length < 2 ^ (prefixWord ++ tailWord_122932).sum := by decide
  have hdescent : baseEnd_122932 < baseStart_122932 := by decide
  rcases family_descends (prefixWord ++ tailWord_122932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123053 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 4]
def baseStart_123053 : Nat := 118140960795 + 123053 * 2 ^ 59
def prefixEnd_123053 : Nat := 4983230072969 + 3 ^ 40 * 123053 * 2
def baseEnd_123053 : Nat := 28082371101249905898487

theorem tailTrace_123053 : CollatzResearch.WordTrace tailWord_123053 prefixEnd_123053 28082371101249905898487 := by
  unfold tailWord_123053
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488111623207471624357813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2992074415471647749571875 4488111623207471624357813)
  ·
    refine ⟨420760464675700464783545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4488111623207471624357813 420760464675700464783545)
    ·
      refine ⟨315570348506775348587659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420760464675700464783545 315570348506775348587659)
      ·
        refine ⟨473355522760163022881489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315570348506775348587659 473355522760163022881489)
        ·
          refine ⟨355016642070122267161117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473355522760163022881489 355016642070122267161117)
          ·
            refine ⟨133131240776295850185419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355016642070122267161117 133131240776295850185419)
            ·
              refine ⟨199696861164443775278129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133131240776295850185419 199696861164443775278129)
              ·
                refine ⟨149772645873332831458597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199696861164443775278129 149772645873332831458597)
                ·
                  refine ⟨28082371101249905898487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149772645873332831458597 28082371101249905898487)
                  ·
                    rfl

theorem cell21_123053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_123053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123053 prefixEnd_123053 := by exact prefixLift 123053
  have htrace : WordTrace (prefixWord ++ tailWord_123053) baseStart_123053 baseEnd_123053 := by
    simpa [prefixWord, tailWord_123053, baseEnd_123053] using wordTrace_append hprefix tailTrace_123053
  have hstable : (prefixWord ++ tailWord_123053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123053).length < 2 ^ (prefixWord ++ tailWord_123053).sum := by decide
  have hdescent : baseEnd_123053 < baseStart_123053 := by decide
  rcases family_descends (prefixWord ++ tailWord_123053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123064 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_123064 : Nat := 118140960795 + 123064 * 2 ^ 59
def prefixEnd_123064 : Nat := 4983230072969 + 3 ^ 40 * 123064 * 2
def baseEnd_123064 : Nat := 28084881451116331215131

theorem tailTrace_123064 : CollatzResearch.WordTrace tailWord_123064 prefixEnd_123064 28084881451116331215131 := by
  unfold tailWord_123064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244256413083810251504123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2992341884111747002005497 2244256413083810251504123)
  ·
    refine ⟨3366384619625715377256185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244256413083810251504123 3366384619625715377256185)
    ·
      refine ⟨2524788464719286532942139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3366384619625715377256185 2524788464719286532942139)
      ·
        refine ⟨3787182697078929799413209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524788464719286532942139 3787182697078929799413209)
        ·
          refine ⟨2840387022809197349559907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3787182697078929799413209 2840387022809197349559907)
          ·
            refine ⟨4260580534213796024339861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840387022809197349559907 4260580534213796024339861)
            ·
              refine ⟨199714712541271688640931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4260580534213796024339861 199714712541271688640931)
              ·
                refine ⟨299572068811907532961397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199714712541271688640931 299572068811907532961397)
                ·
                  refine ⟨28084881451116331215131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 299572068811907532961397 28084881451116331215131)
                  ·
                    rfl

theorem cell21_123064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_123064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123064 prefixEnd_123064 := by exact prefixLift 123064
  have htrace : WordTrace (prefixWord ++ tailWord_123064) baseStart_123064 baseEnd_123064 := by
    simpa [prefixWord, tailWord_123064, baseEnd_123064] using wordTrace_append hprefix tailTrace_123064
  have hstable : (prefixWord ++ tailWord_123064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123064).length < 2 ^ (prefixWord ++ tailWord_123064).sum := by decide
  have hdescent : baseEnd_123064 < baseStart_123064 := by decide
  rcases family_descends (prefixWord ++ tailWord_123064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123084 : List Nat := [2, 2, 1, 6, 1, 2, 2, 5]
def baseStart_123084 : Nat := 118140960795 + 123084 * 2 ^ 59
def prefixEnd_123084 : Nat := 4983230072969 + 3 ^ 40 * 123084 * 2
def baseEnd_123084 : Nat := 9363148574533580293919

theorem tailTrace_123084 : CollatzResearch.WordTrace tailWord_123084 prefixEnd_123084 9363148574533580293919 := by
  unfold tailWord_123084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244621143047581959368153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2992828190730109279157537 2244621143047581959368153)
  ·
    refine ⟨1683465857285686469526115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2244621143047581959368153 1683465857285686469526115)
    ·
      refine ⟨2525198785928529704289173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683465857285686469526115 2525198785928529704289173)
      ·
        refine ⟨118368693090399829888555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2525198785928529704289173 118368693090399829888555)
        ·
          refine ⟨177553039635599744832833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118368693090399829888555 177553039635599744832833)
          ·
            refine ⟨133164779726699808624625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177553039635599744832833 133164779726699808624625)
            ·
              refine ⟨99873584795024856468469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133164779726699808624625 99873584795024856468469)
              ·
                refine ⟨9363148574533580293919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99873584795024856468469 9363148574533580293919)
                ·
                  rfl

theorem cell21_123084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_123084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123084 prefixEnd_123084 := by exact prefixLift 123084
  have htrace : WordTrace (prefixWord ++ tailWord_123084) baseStart_123084 baseEnd_123084 := by
    simpa [prefixWord, tailWord_123084, baseEnd_123084] using wordTrace_append hprefix tailTrace_123084
  have hstable : (prefixWord ++ tailWord_123084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123084).length < 2 ^ (prefixWord ++ tailWord_123084).sum := by decide
  have hdescent : baseEnd_123084 < baseStart_123084 := by decide
  rcases family_descends (prefixWord ++ tailWord_123084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123109 : List Nat := [1, 3, 1, 4, 2, 1, 9]
def baseStart_123109 : Nat := 118140960795 + 123109 * 2 ^ 59
def prefixEnd_123109 : Nat := 4983230072969 + 3 ^ 40 * 123109 * 2
def baseEnd_123109 : Nat := 3121683451578472551671

theorem tailTrace_123109 : CollatzResearch.WordTrace tailWord_123109 prefixEnd_123109 3121683451578472551671 := by
  unfold tailWord_123109
  simp only [CollatzResearch.WordTrace]
  refine ⟨4490154111004593188396381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2993436074003062125597587 4490154111004593188396381)
  ·
    refine ⟨1683807791626722445648643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4490154111004593188396381 1683807791626722445648643)
    ·
      refine ⟨2525711687440083668472965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683807791626722445648643 2525711687440083668472965)
      ·
        refine ⟨473570941395015687838681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2525711687440083668472965 473570941395015687838681)
        ·
          refine ⟨355178206046261765879011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473570941395015687838681 355178206046261765879011)
          ·
            refine ⟨532767309069392648818517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355178206046261765879011 532767309069392648818517)
            ·
              refine ⟨3121683451578472551671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 532767309069392648818517 3121683451578472551671)
              ·
                rfl

theorem cell21_123109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 9].length) (baseStart_123109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123109 prefixEnd_123109 := by exact prefixLift 123109
  have htrace : WordTrace (prefixWord ++ tailWord_123109) baseStart_123109 baseEnd_123109 := by
    simpa [prefixWord, tailWord_123109, baseEnd_123109] using wordTrace_append hprefix tailTrace_123109
  have hstable : (prefixWord ++ tailWord_123109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123109).length < 2 ^ (prefixWord ++ tailWord_123109).sum := by decide
  have hdescent : baseEnd_123109 < baseStart_123109 := by decide
  rcases family_descends (prefixWord ++ tailWord_123109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123171 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 4]
def baseStart_123171 : Nat := 118140960795 + 123171 * 2 ^ 59
def prefixEnd_123171 : Nat := 4983230072969 + 3 ^ 40 * 123171 * 2
def baseEnd_123171 : Nat := 28109300308907922931579

theorem tailTrace_123171 : CollatzResearch.WordTrace tailWord_123171 prefixEnd_123171 28109300308907922931579 := by
  unfold tailWord_123171
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492415436779977777153367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2994943624519985184768911 4492415436779977777153367)
  ·
    refine ⟨6738623155169966665730051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4492415436779977777153367 6738623155169966665730051)
    ·
      refine ⟨10107934732754949998595077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738623155169966665730051 10107934732754949998595077)
      ·
        refine ⟨1895237762391553124736577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10107934732754949998595077 1895237762391553124736577)
        ·
          refine ⟨1421428321793664843552433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1895237762391553124736577 1421428321793664843552433)
          ·
            refine ⟨1066071241345248632664325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421428321793664843552433 1066071241345248632664325)
            ·
              refine ⟨199888357752234118624561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1066071241345248632664325 199888357752234118624561)
              ·
                refine ⟨149916268314175588968421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199888357752234118624561 149916268314175588968421)
                ·
                  refine ⟨28109300308907922931579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149916268314175588968421 28109300308907922931579)
                  ·
                    rfl

theorem cell21_123171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 4].length) (baseStart_123171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123171 prefixEnd_123171 := by exact prefixLift 123171
  have htrace : WordTrace (prefixWord ++ tailWord_123171) baseStart_123171 baseEnd_123171 := by
    simpa [prefixWord, tailWord_123171, baseEnd_123171] using wordTrace_append hprefix tailTrace_123171
  have hstable : (prefixWord ++ tailWord_123171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123171).length < 2 ^ (prefixWord ++ tailWord_123171).sum := by decide
  have hdescent : baseEnd_123171 < baseStart_123171 := by decide
  rcases family_descends (prefixWord ++ tailWord_123171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123188 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_123188 : Nat := 118140960795 + 123188 * 2 ^ 59
def prefixEnd_123188 : Nat := 4983230072969 + 3 ^ 40 * 123188 * 2
def baseEnd_123188 : Nat := 28113179940519671148211

theorem tailTrace_123188 : CollatzResearch.WordTrace tailWord_123188 prefixEnd_123188 28113179940519671148211 := by
  unfold tailWord_123188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246517738859194840261109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2995356985145593120348145 2246517738859194840261109)
  ·
    refine ⟨210611038018049516274479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2246517738859194840261109 210611038018049516274479)
    ·
      refine ⟨315916557027074274411719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210611038018049516274479 315916557027074274411719)
      ·
        refine ⟨473874835540611411617579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315916557027074274411719 473874835540611411617579)
        ·
          refine ⟨710812253310917117426369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473874835540611411617579 710812253310917117426369)
          ·
            refine ⟨533109189983187838069777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710812253310917117426369 533109189983187838069777)
            ·
              refine ⟨399831892487390878552333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533109189983187838069777 399831892487390878552333)
              ·
                refine ⟨149936959682771579457125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399831892487390878552333 149936959682771579457125)
                ·
                  refine ⟨28113179940519671148211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149936959682771579457125 28113179940519671148211)
                  ·
                    rfl

theorem cell21_123188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_123188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123188 prefixEnd_123188 := by exact prefixLift 123188
  have htrace : WordTrace (prefixWord ++ tailWord_123188) baseStart_123188 baseEnd_123188 := by
    simpa [prefixWord, tailWord_123188, baseEnd_123188] using wordTrace_append hprefix tailTrace_123188
  have hstable : (prefixWord ++ tailWord_123188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123188).length < 2 ^ (prefixWord ++ tailWord_123188).sum := by decide
  have hdescent : baseEnd_123188 < baseStart_123188 := by decide
  rcases family_descends (prefixWord ++ tailWord_123188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123261 : List Nat := [1, 4, 1, 1, 2, 4, 1, 7]
def baseStart_123261 : Nat := 118140960795 + 123261 * 2 ^ 59
def prefixEnd_123261 : Nat := 4983230072969 + 3 ^ 40 * 123261 * 2
def baseEnd_123261 : Nat := 9376613178362588810465

theorem tailTrace_123261 : CollatzResearch.WordTrace tailWord_123261 prefixEnd_123261 9376613178362588810465 := by
  unfold tailWord_123261
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495698006453923147929637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2997132004302615431953091 4495698006453923147929637)
  ·
    refine ⟨842943376210110590236807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4495698006453923147929637 842943376210110590236807)
    ·
      refine ⟨1264415064315165885355211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842943376210110590236807 1264415064315165885355211)
      ·
        refine ⟨1896622596472748828032817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264415064315165885355211 1896622596472748828032817)
        ·
          refine ⟨1422466947354561621024613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1896622596472748828032817 1422466947354561621024613)
          ·
            refine ⟨266712552628980303942115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1422466947354561621024613 266712552628980303942115)
            ·
              refine ⟨400068828943470455913173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266712552628980303942115 400068828943470455913173)
              ·
                refine ⟨9376613178362588810465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 400068828943470455913173 9376613178362588810465)
                ·
                  rfl

theorem cell21_123261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 7].length) (baseStart_123261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123261 prefixEnd_123261 := by exact prefixLift 123261
  have htrace : WordTrace (prefixWord ++ tailWord_123261) baseStart_123261 baseEnd_123261 := by
    simpa [prefixWord, tailWord_123261, baseEnd_123261] using wordTrace_append hprefix tailTrace_123261
  have hstable : (prefixWord ++ tailWord_123261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123261).length < 2 ^ (prefixWord ++ tailWord_123261).sum := by decide
  have hdescent : baseEnd_123261 < baseStart_123261 := by decide
  rcases family_descends (prefixWord ++ tailWord_123261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123267 : List Nat := [1, 1, 1, 3, 7, 1, 1, 3, 3]
def baseStart_123267 : Nat := 118140960795 + 123267 * 2 ^ 59
def prefixEnd_123267 : Nat := 4983230072969 + 3 ^ 40 * 123267 * 2
def baseEnd_123267 : Nat := 28131208816833089331383

theorem tailTrace_123267 : CollatzResearch.WordTrace tailWord_123267 prefixEnd_123267 28131208816833089331383 := by
  unfold tailWord_123267
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495916844432186172648055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2997277896288124115098703 4495916844432186172648055)
  ·
    refine ⟨6743875266648279258972083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4495916844432186172648055 6743875266648279258972083)
    ·
      refine ⟨10115812899972418888458125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6743875266648279258972083 10115812899972418888458125)
      ·
        refine ⟨3793429837489657083171797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10115812899972418888458125 3793429837489657083171797)
        ·
          refine ⟨88908511816163837886839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3793429837489657083171797 88908511816163837886839)
          ·
            refine ⟨133362767724245756830259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88908511816163837886839 133362767724245756830259)
            ·
              refine ⟨200044151586368635245389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133362767724245756830259 200044151586368635245389)
              ·
                refine ⟨75016556844888238217021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200044151586368635245389 75016556844888238217021)
                ·
                  refine ⟨28131208816833089331383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75016556844888238217021 28131208816833089331383)
                  ·
                    rfl

theorem cell21_123267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3, 3].length) (baseStart_123267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123267 prefixEnd_123267 := by exact prefixLift 123267
  have htrace : WordTrace (prefixWord ++ tailWord_123267) baseStart_123267 baseEnd_123267 := by
    simpa [prefixWord, tailWord_123267, baseEnd_123267] using wordTrace_append hprefix tailTrace_123267
  have hstable : (prefixWord ++ tailWord_123267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123267).length < 2 ^ (prefixWord ++ tailWord_123267).sum := by decide
  have hdescent : baseEnd_123267 < baseStart_123267 := by decide
  rcases family_descends (prefixWord ++ tailWord_123267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123278 : List Nat := [4, 1, 1, 4, 1, 3, 7]
def baseStart_123278 : Nat := 118140960795 + 123278 * 2 ^ 59
def prefixEnd_123278 : Nat := 4983230072969 + 3 ^ 40 * 123278 * 2
def baseEnd_123278 : Nat := 3125968796299946072003

theorem tailTrace_123278 : CollatzResearch.WordTrace tailWord_123278 prefixEnd_123278 3125968796299946072003 := by
  unfold tailWord_123278
  simp only [CollatzResearch.WordTrace]
  refine ⟨562039755924041881412311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2997545364928223367532325 562039755924041881412311)
  ·
    refine ⟨843059633886062822118467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 562039755924041881412311 843059633886062822118467)
    ·
      refine ⟨1264589450829094233177701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843059633886062822118467 1264589450829094233177701)
      ·
        refine ⟨237110522030455168720819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1264589450829094233177701 237110522030455168720819)
        ·
          refine ⟨355665783045682753081229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237110522030455168720819 355665783045682753081229)
          ·
            refine ⟨133374668642131032405461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355665783045682753081229 133374668642131032405461)
            ·
              refine ⟨3125968796299946072003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133374668642131032405461 3125968796299946072003)
              ·
                rfl

theorem cell21_123278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 7].length) (baseStart_123278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123278 prefixEnd_123278 := by exact prefixLift 123278
  have htrace : WordTrace (prefixWord ++ tailWord_123278) baseStart_123278 baseEnd_123278 := by
    simpa [prefixWord, tailWord_123278, baseEnd_123278] using wordTrace_append hprefix tailTrace_123278
  have hstable : (prefixWord ++ tailWord_123278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123278).length < 2 ^ (prefixWord ++ tailWord_123278).sum := by decide
  have hdescent : baseEnd_123278 < baseStart_123278 := by decide
  rcases family_descends (prefixWord ++ tailWord_123278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123340 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_123340 : Nat := 118140960795 + 123340 * 2 ^ 59
def prefixEnd_123340 : Nat := 4983230072969 + 3 ^ 40 * 123340 * 2
def baseEnd_123340 : Nat := 28147868411401184614567

theorem tailTrace_123340 : CollatzResearch.WordTrace tailWord_123340 prefixEnd_123340 28147868411401184614567 := by
  unfold tailWord_123340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249289686583859820027737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2999052915445146426703649 2249289686583859820027737)
  ·
    refine ⟨1686967264937894865020803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2249289686583859820027737 1686967264937894865020803)
    ·
      refine ⟨2530450897406842297531205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686967264937894865020803 2530450897406842297531205)
      ·
        refine ⟨474459543263782930787101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2530450897406842297531205 474459543263782930787101)
        ·
          refine ⟨177922328723918599045163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474459543263782930787101 177922328723918599045163)
          ·
            refine ⟨266883493085877898567745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177922328723918599045163 266883493085877898567745)
            ·
              refine ⟨200162619814408423925809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266883493085877898567745 200162619814408423925809)
              ·
                refine ⟨150121964860806317944357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200162619814408423925809 150121964860806317944357)
                ·
                  refine ⟨28147868411401184614567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150121964860806317944357 28147868411401184614567)
                  ·
                    rfl

theorem cell21_123340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_123340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123340 prefixEnd_123340 := by exact prefixLift 123340
  have htrace : WordTrace (prefixWord ++ tailWord_123340) baseStart_123340 baseEnd_123340 := by
    simpa [prefixWord, tailWord_123340, baseEnd_123340] using wordTrace_append hprefix tailTrace_123340
  have hstable : (prefixWord ++ tailWord_123340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123340).length < 2 ^ (prefixWord ++ tailWord_123340).sum := by decide
  have hdescent : baseEnd_123340 < baseStart_123340 := by decide
  rcases family_descends (prefixWord ++ tailWord_123340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123368 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_123368 : Nat := 118140960795 + 123368 * 2 ^ 59
def prefixEnd_123368 : Nat := 4983230072969 + 3 ^ 40 * 123368 * 2
def baseEnd_123368 : Nat := 28154258392879358147843

theorem tailTrace_123368 : CollatzResearch.WordTrace tailWord_123368 prefixEnd_123368 28154258392879358147843 := by
  unfold tailWord_123368
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249800308533140211037379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2999733744710853614716505 2249800308533140211037379)
  ·
    refine ⟨3374700462799710316556069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2249800308533140211037379 3374700462799710316556069)
    ·
      refine ⟨632756336774945684354263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3374700462799710316556069 632756336774945684354263)
      ·
        refine ⟨949134505162418526531395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632756336774945684354263 949134505162418526531395)
        ·
          refine ⟨1423701757743627789797093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949134505162418526531395 1423701757743627789797093)
          ·
            refine ⟨266944079576930210586955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1423701757743627789797093 266944079576930210586955)
            ·
              refine ⟨400416119365395315880433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266944079576930210586955 400416119365395315880433)
              ·
                refine ⟨300312089524046486910325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400416119365395315880433 300312089524046486910325)
                ·
                  refine ⟨28154258392879358147843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300312089524046486910325 28154258392879358147843)
                  ·
                    rfl

theorem cell21_123368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_123368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123368 prefixEnd_123368 := by exact prefixLift 123368
  have htrace : WordTrace (prefixWord ++ tailWord_123368) baseStart_123368 baseEnd_123368 := by
    simpa [prefixWord, tailWord_123368, baseEnd_123368] using wordTrace_append hprefix tailTrace_123368
  have hstable : (prefixWord ++ tailWord_123368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123368).length < 2 ^ (prefixWord ++ tailWord_123368).sum := by decide
  have hdescent : baseEnd_123368 < baseStart_123368 := by decide
  rcases family_descends (prefixWord ++ tailWord_123368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123399 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 6]
def baseStart_123399 : Nat := 118140960795 + 123399 * 2 ^ 59
def prefixEnd_123399 : Nat := 4983230072969 + 3 ^ 40 * 123399 * 2
def baseEnd_123399 : Nat := 28161333015230193131113

theorem tailTrace_123399 : CollatzResearch.WordTrace tailWord_123399 prefixEnd_123399 28161333015230193131113 := by
  unfold tailWord_123399
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500731279953972716453251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3000487519969315144302167 4500731279953972716453251)
  ·
    refine ⟨6751096919930959074679877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4500731279953972716453251 6751096919930959074679877)
    ·
      refine ⟨1265830672487054826502477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6751096919930959074679877 1265830672487054826502477)
      ·
        refine ⟨474686502182645559938429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1265830672487054826502477 474686502182645559938429)
        ·
          refine ⟨178007438318492084976911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474686502182645559938429 178007438318492084976911)
          ·
            refine ⟨267011157477738127465367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178007438318492084976911 267011157477738127465367)
            ·
              refine ⟨400516736216607191198051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267011157477738127465367 400516736216607191198051)
              ·
                refine ⟨600775104324910786797077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400516736216607191198051 600775104324910786797077)
                ·
                  refine ⟨28161333015230193131113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 600775104324910786797077 28161333015230193131113)
                  ·
                    rfl

theorem cell21_123399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_123399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123399 prefixEnd_123399 := by exact prefixLift 123399
  have htrace : WordTrace (prefixWord ++ tailWord_123399) baseStart_123399 baseEnd_123399 := by
    simpa [prefixWord, tailWord_123399, baseEnd_123399] using wordTrace_append hprefix tailTrace_123399
  have hstable : (prefixWord ++ tailWord_123399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123399).length < 2 ^ (prefixWord ++ tailWord_123399).sum := by decide
  have hdescent : baseEnd_123399 < baseStart_123399 := by decide
  rcases family_descends (prefixWord ++ tailWord_123399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123416 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_123416 : Nat := 118140960795 + 123416 * 2 ^ 59
def prefixEnd_123416 : Nat := 4983230072969 + 3 ^ 40 * 123416 * 2
def baseEnd_123416 : Nat := 28165212646841941347745

theorem tailTrace_123416 : CollatzResearch.WordTrace tailWord_123416 prefixEnd_123416 28165212646841941347745 := by
  unfold tailWord_123416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250675660446192309911051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3000900880594923079881401 2250675660446192309911051)
  ·
    refine ⟨3376013490669288464866577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2250675660446192309911051 3376013490669288464866577)
    ·
      refine ⟨2532010118001966348649933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3376013490669288464866577 2532010118001966348649933)
      ·
        refine ⟨949503794250737380743725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2532010118001966348649933 949503794250737380743725)
        ·
          refine ⟨356063922844026517778897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 949503794250737380743725 356063922844026517778897)
          ·
            refine ⟨267047942133019888334173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356063922844026517778897 267047942133019888334173)
            ·
              refine ⟨100142978299882458125315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267047942133019888334173 100142978299882458125315)
              ·
                refine ⟨150214467449823687187973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100142978299882458125315 150214467449823687187973)
                ·
                  refine ⟨28165212646841941347745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150214467449823687187973 28165212646841941347745)
                  ·
                    rfl

theorem cell21_123416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_123416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123416 prefixEnd_123416 := by exact prefixLift 123416
  have htrace : WordTrace (prefixWord ++ tailWord_123416) baseStart_123416 baseEnd_123416 := by
    simpa [prefixWord, tailWord_123416, baseEnd_123416] using wordTrace_append hprefix tailTrace_123416
  have hstable : (prefixWord ++ tailWord_123416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123416).length < 2 ^ (prefixWord ++ tailWord_123416).sum := by decide
  have hdescent : baseEnd_123416 < baseStart_123416 := by decide
  rcases family_descends (prefixWord ++ tailWord_123416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123565 : List Nat := [1, 5, 2, 1, 1, 3, 8]
def baseStart_123565 : Nat := 118140960795 + 123565 * 2 ^ 59
def prefixEnd_123565 : Nat := 4983230072969 + 3 ^ 40 * 123565 * 2
def baseEnd_123565 : Nat := 3133246275205643707123

theorem tailTrace_123565 : CollatzResearch.WordTrace tailWord_123565 prefixEnd_123565 3133246275205643707123 := by
  unfold tailWord_123565
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506785797352583066996149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3004523864901722044664099 4506785797352583066996149)
  ·
    refine ⟨422511168501804662530889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4506785797352583066996149 422511168501804662530889)
    ·
      refine ⟨316883376376353496898167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422511168501804662530889 316883376376353496898167)
      ·
        refine ⟨475325064564530245347251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316883376376353496898167 475325064564530245347251)
        ·
          refine ⟨712987596846795368020877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475325064564530245347251 712987596846795368020877)
          ·
            refine ⟨267370348817548263007829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 712987596846795368020877 267370348817548263007829)
            ·
              refine ⟨3133246275205643707123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 267370348817548263007829 3133246275205643707123)
              ·
                rfl

theorem cell21_123565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 8].length) (baseStart_123565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123565 prefixEnd_123565 := by exact prefixLift 123565
  have htrace : WordTrace (prefixWord ++ tailWord_123565) baseStart_123565 baseEnd_123565 := by
    simpa [prefixWord, tailWord_123565, baseEnd_123565] using wordTrace_append hprefix tailTrace_123565
  have hstable : (prefixWord ++ tailWord_123565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123565).length < 2 ^ (prefixWord ++ tailWord_123565).sum := by decide
  have hdescent : baseEnd_123565 < baseStart_123565 := by decide
  rcases family_descends (prefixWord ++ tailWord_123565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123596 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_123596 : Nat := 118140960795 + 123596 * 2 ^ 59
def prefixEnd_123596 : Nat := 4983230072969 + 3 ^ 40 * 123596 * 2
def baseEnd_123596 : Nat := 28206291099201628347377

theorem tailTrace_123596 : CollatzResearch.WordTrace tailWord_123596 prefixEnd_123596 28206291099201628347377 := by
  unfold tailWord_123596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253958230120137680687321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3005277640160183574249761 2253958230120137680687321)
  ·
    refine ⟨1690468672590103260515491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2253958230120137680687321 1690468672590103260515491)
    ·
      refine ⟨2535703008885154890773237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1690468672590103260515491 2535703008885154890773237)
      ·
        refine ⟨237722157082983271009991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2535703008885154890773237 237722157082983271009991)
        ·
          refine ⟨356583235624474906514987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237722157082983271009991 356583235624474906514987)
          ·
            refine ⟨534874853436712359772481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356583235624474906514987 534874853436712359772481)
            ·
              refine ⟨401156140077534269829361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534874853436712359772481 401156140077534269829361)
              ·
                refine ⟨300867105058150702372021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401156140077534269829361 300867105058150702372021)
                ·
                  refine ⟨28206291099201628347377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300867105058150702372021 28206291099201628347377)
                  ·
                    rfl

theorem cell21_123596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_123596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123596 prefixEnd_123596 := by exact prefixLift 123596
  have htrace : WordTrace (prefixWord ++ tailWord_123596) baseStart_123596 baseEnd_123596 := by
    simpa [prefixWord, tailWord_123596, baseEnd_123596] using wordTrace_append hprefix tailTrace_123596
  have hstable : (prefixWord ++ tailWord_123596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123596).length < 2 ^ (prefixWord ++ tailWord_123596).sum := by decide
  have hdescent : baseEnd_123596 < baseStart_123596 := by decide
  rcases family_descends (prefixWord ++ tailWord_123596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123630 : List Nat := [4, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_123630 : Nat := 118140960795 + 123630 * 2 ^ 59
def prefixEnd_123630 : Nat := 4983230072969 + 3 ^ 40 * 123630 * 2
def baseEnd_123630 : Nat := 28214050362425124780641

theorem tailTrace_123630 : CollatzResearch.WordTrace tailWord_123630 prefixEnd_123630 28214050362425124780641 := by
  unfold tailWord_123630
  simp only [CollatzResearch.WordTrace]
  refine ⟨563644567764637396014043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3006104361411399445408229 563644567764637396014043)
  ·
    refine ⟨845466851646956094021065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 563644567764637396014043 845466851646956094021065)
    ·
      refine ⟨634100138735217070515799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 845466851646956094021065 634100138735217070515799)
      ·
        refine ⟨951150208102825605773699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634100138735217070515799 951150208102825605773699)
        ·
          refine ⟨1426725312154238408660549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951150208102825605773699 1426725312154238408660549)
          ·
            refine ⟨267510996028919701623853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1426725312154238408660549 267510996028919701623853)
            ·
              refine ⟨100316623510844888108945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267510996028919701623853 100316623510844888108945)
              ·
                refine ⟨75237467633133666081709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100316623510844888108945 75237467633133666081709)
                ·
                  refine ⟨28214050362425124780641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75237467633133666081709 28214050362425124780641)
                  ·
                    rfl

theorem cell21_123630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_123630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123630 prefixEnd_123630 := by exact prefixLift 123630
  have htrace : WordTrace (prefixWord ++ tailWord_123630) baseStart_123630 baseEnd_123630 := by
    simpa [prefixWord, tailWord_123630, baseEnd_123630] using wordTrace_append hprefix tailTrace_123630
  have hstable : (prefixWord ++ tailWord_123630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123630).length < 2 ^ (prefixWord ++ tailWord_123630).sum := by decide
  have hdescent : baseEnd_123630 < baseStart_123630 := by decide
  rcases family_descends (prefixWord ++ tailWord_123630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123644 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_123644 : Nat := 118140960795 + 123644 * 2 ^ 59
def prefixEnd_123644 : Nat := 4983230072969 + 3 ^ 40 * 123644 * 2
def baseEnd_123644 : Nat := 28217245353164211547279

theorem tailTrace_123644 : CollatzResearch.WordTrace tailWord_123644 prefixEnd_123644 28217245353164211547279 := by
  unfold tailWord_123644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2254833582033189779560993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3006444776044253039414657 2254833582033189779560993)
  ·
    refine ⟨1691125186524892334670745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2254833582033189779560993 1691125186524892334670745)
    ·
      refine ⟨1268343889893669251003059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1691125186524892334670745 1268343889893669251003059)
      ·
        refine ⟨1902515834840503876504589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268343889893669251003059 1902515834840503876504589)
        ·
          refine ⟨713443438065188953689221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1902515834840503876504589 713443438065188953689221)
          ·
            refine ⟨133770644637222928816729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 713443438065188953689221 133770644637222928816729)
            ·
              refine ⟨100327983477917196612547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133770644637222928816729 100327983477917196612547)
              ·
                refine ⟨150491975216875794918821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100327983477917196612547 150491975216875794918821)
                ·
                  refine ⟨28217245353164211547279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150491975216875794918821 28217245353164211547279)
                  ·
                    rfl

theorem cell21_123644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_123644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123644 prefixEnd_123644 := by exact prefixLift 123644
  have htrace : WordTrace (prefixWord ++ tailWord_123644) baseStart_123644 baseEnd_123644 := by
    simpa [prefixWord, tailWord_123644, baseEnd_123644] using wordTrace_append hprefix tailTrace_123644
  have hstable : (prefixWord ++ tailWord_123644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123644).length < 2 ^ (prefixWord ++ tailWord_123644).sum := by decide
  have hdescent : baseEnd_123644 < baseStart_123644 := by decide
  rcases family_descends (prefixWord ++ tailWord_123644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123672 : List Nat := [2, 1, 2, 3, 1, 1, 1, 7, 3]
def baseStart_123672 : Nat := 118140960795 + 123672 * 2 ^ 59
def prefixEnd_123672 : Nat := 4983230072969 + 3 ^ 40 * 123672 * 2
def baseEnd_123672 : Nat := 28223635334642385080555

theorem tailTrace_123672 : CollatzResearch.WordTrace tailWord_123672 prefixEnd_123672 28223635334642385080555 := by
  unfold tailWord_123672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2255344203982470170570635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3007125605309960227427513 2255344203982470170570635)
  ·
    refine ⟨3383016305973705255855953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2255344203982470170570635 3383016305973705255855953)
    ·
      refine ⟨2537262229480278941891965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3383016305973705255855953 2537262229480278941891965)
      ·
        refine ⟨951473336055104603209487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2537262229480278941891965 951473336055104603209487)
        ·
          refine ⟨1427210004082656904814231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951473336055104603209487 1427210004082656904814231)
          ·
            refine ⟨2140815006123985357221347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427210004082656904814231 2140815006123985357221347)
            ·
              refine ⟨3211222509185978035832021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140815006123985357221347 3211222509185978035832021)
              ·
                refine ⟨75263027559046360214813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3211222509185978035832021 75263027559046360214813)
                ·
                  refine ⟨28223635334642385080555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75263027559046360214813 28223635334642385080555)
                  ·
                    rfl

theorem cell21_123672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_123672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123672 prefixEnd_123672 := by exact prefixLift 123672
  have htrace : WordTrace (prefixWord ++ tailWord_123672) baseStart_123672 baseEnd_123672 := by
    simpa [prefixWord, tailWord_123672, baseEnd_123672] using wordTrace_append hprefix tailTrace_123672
  have hstable : (prefixWord ++ tailWord_123672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123672).length < 2 ^ (prefixWord ++ tailWord_123672).sum := by decide
  have hdescent : baseEnd_123672 < baseStart_123672 := by decide
  rcases family_descends (prefixWord ++ tailWord_123672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123748 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_123748 : Nat := 118140960795 + 123748 * 2 ^ 59
def prefixEnd_123748 : Nat := 4983230072969 + 3 ^ 40 * 123748 * 2
def baseEnd_123748 : Nat := 28240979570083141813733

theorem tailTrace_123748 : CollatzResearch.WordTrace tailWord_123748 prefixEnd_123748 28240979570083141813733 := by
  unfold tailWord_123748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256730177844802660453949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3008973570459736880605265 2256730177844802660453949)
  ·
    refine ⟨846273816691800997670231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2256730177844802660453949 846273816691800997670231)
    ·
      refine ⟨1269410725037701496505347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846273816691800997670231 1269410725037701496505347)
      ·
        refine ⟨1904116087556552244758021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269410725037701496505347 1904116087556552244758021)
        ·
          refine ⟨357021766416853545892129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1904116087556552244758021 357021766416853545892129)
          ·
            refine ⟨267766324812640159419097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357021766416853545892129 267766324812640159419097)
            ·
              refine ⟨200824743609480119564323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267766324812640159419097 200824743609480119564323)
              ·
                refine ⟨301237115414220179346485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200824743609480119564323 301237115414220179346485)
                ·
                  refine ⟨28240979570083141813733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301237115414220179346485 28240979570083141813733)
                  ·
                    rfl

theorem cell21_123748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_123748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123748 prefixEnd_123748 := by exact prefixLift 123748
  have htrace : WordTrace (prefixWord ++ tailWord_123748) baseStart_123748 baseEnd_123748 := by
    simpa [prefixWord, tailWord_123748, baseEnd_123748] using wordTrace_append hprefix tailTrace_123748
  have hstable : (prefixWord ++ tailWord_123748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123748).length < 2 ^ (prefixWord ++ tailWord_123748).sum := by decide
  have hdescent : baseEnd_123748 < baseStart_123748 := by decide
  rcases family_descends (prefixWord ++ tailWord_123748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123762 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_123762 : Nat := 118140960795 + 123762 * 2 ^ 59
def prefixEnd_123762 : Nat := 4983230072969 + 3 ^ 40 * 123762 * 2
def baseEnd_123762 : Nat := 28244174560822228580371

theorem tailTrace_123762 : CollatzResearch.WordTrace tailWord_123762 prefixEnd_123762 28244174560822228580371 := by
  unfold tailWord_123762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128492744409721427979385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3009313985092590474611693 1128492744409721427979385)
  ·
    refine ⟨846369558307291070984539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1128492744409721427979385 846369558307291070984539)
    ·
      refine ⟨1269554337460936606476809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846369558307291070984539 1269554337460936606476809)
      ·
        refine ⟨952165753095702454857607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1269554337460936606476809 952165753095702454857607)
        ·
          refine ⟨1428248629643553682286411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952165753095702454857607 1428248629643553682286411)
          ·
            refine ⟨2142372944465330523429617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428248629643553682286411 2142372944465330523429617)
            ·
              refine ⟨1606779708348997892572213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142372944465330523429617 1606779708348997892572213)
              ·
                refine ⟨150635597657718552428645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1606779708348997892572213 150635597657718552428645)
                ·
                  refine ⟨28244174560822228580371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150635597657718552428645 28244174560822228580371)
                  ·
                    rfl

theorem cell21_123762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_123762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123762 prefixEnd_123762 := by exact prefixLift 123762
  have htrace : WordTrace (prefixWord ++ tailWord_123762) baseStart_123762 baseEnd_123762 := by
    simpa [prefixWord, tailWord_123762, baseEnd_123762] using wordTrace_append hprefix tailTrace_123762
  have hstable : (prefixWord ++ tailWord_123762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123762).length < 2 ^ (prefixWord ++ tailWord_123762).sum := by decide
  have hdescent : baseEnd_123762 < baseStart_123762 := by decide
  rcases family_descends (prefixWord ++ tailWord_123762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123858 : List Nat := [3, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_123858 : Nat := 118140960795 + 123858 * 2 ^ 59
def prefixEnd_123858 : Nat := 4983230072969 + 3 ^ 40 * 123858 * 2
def baseEnd_123858 : Nat := 28266083068747394980175

theorem tailTrace_123858 : CollatzResearch.WordTrace tailWord_123858 prefixEnd_123858 28266083068747394980175 := by
  unfold tailWord_123858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129368096322773526853057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3011648256860729404941485 1129368096322773526853057)
  ·
    refine ⟨847026072242080145139793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1129368096322773526853057 847026072242080145139793)
    ·
      refine ⟨635269554181560108854845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 847026072242080145139793 635269554181560108854845)
      ·
        refine ⟨238226082818085040820567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635269554181560108854845 238226082818085040820567)
        ·
          refine ⟨357339124227127561230851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238226082818085040820567 357339124227127561230851)
          ·
            refine ⟨536008686340691341846277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357339124227127561230851 536008686340691341846277)
            ·
              refine ⟨100501628688879626596177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 536008686340691341846277 100501628688879626596177)
              ·
                refine ⟨75376221516659719947133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100501628688879626596177 75376221516659719947133)
                ·
                  refine ⟨28266083068747394980175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75376221516659719947133 28266083068747394980175)
                  ·
                    rfl

theorem cell21_123858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_123858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123858 prefixEnd_123858 := by exact prefixLift 123858
  have htrace : WordTrace (prefixWord ++ tailWord_123858) baseStart_123858 baseEnd_123858 := by
    simpa [prefixWord, tailWord_123858, baseEnd_123858] using wordTrace_append hprefix tailTrace_123858
  have hstable : (prefixWord ++ tailWord_123858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123858).length < 2 ^ (prefixWord ++ tailWord_123858).sum := by decide
  have hdescent : baseEnd_123858 < baseStart_123858 := by decide
  rcases family_descends (prefixWord ++ tailWord_123858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123869 : List Nat := [1, 4, 3, 1, 2, 1, 3, 6]
def baseStart_123869 : Nat := 118140960795 + 123869 * 2 ^ 59
def prefixEnd_123869 : Nat := 4983230072969 + 3 ^ 40 * 123869 * 2
def baseEnd_123869 : Nat := 9422864472871273432273

theorem tailTrace_123869 : CollatzResearch.WordTrace tailWord_123869 prefixEnd_123869 9422864472871273432273 := by
  unfold tailWord_123869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4517873588251242986062661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3011915725500828657375107 4517873588251242986062661)
  ·
    refine ⟨847101297797108059886749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4517873588251242986062661 847101297797108059886749)
    ·
      refine ⟨317662986673915522457531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 847101297797108059886749 317662986673915522457531)
      ·
        refine ⟨476494480010873283686297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317662986673915522457531 476494480010873283686297)
        ·
          refine ⟨357370860008154962764723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476494480010873283686297 357370860008154962764723)
          ·
            refine ⟨536056290012232444147085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357370860008154962764723 536056290012232444147085)
            ·
              refine ⟨201021108754587166555157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536056290012232444147085 201021108754587166555157)
              ·
                refine ⟨9422864472871273432273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201021108754587166555157 9422864472871273432273)
                ·
                  rfl

theorem cell21_123869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 6].length) (baseStart_123869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123869 prefixEnd_123869 := by exact prefixLift 123869
  have htrace : WordTrace (prefixWord ++ tailWord_123869) baseStart_123869 baseEnd_123869 := by
    simpa [prefixWord, tailWord_123869, baseEnd_123869] using wordTrace_append hprefix tailTrace_123869
  have hstable : (prefixWord ++ tailWord_123869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123869).length < 2 ^ (prefixWord ++ tailWord_123869).sum := by decide
  have hdescent : baseEnd_123869 < baseStart_123869 := by decide
  rcases family_descends (prefixWord ++ tailWord_123869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123886 : List Nat := [4, 1, 2, 1, 4, 1, 3, 5]
def baseStart_123886 : Nat := 118140960795 + 123886 * 2 ^ 59
def prefixEnd_123886 : Nat := 4983230072969 + 3 ^ 40 * 123886 * 2
def baseEnd_123886 : Nat := 9424157683408522837817

theorem tailTrace_123886 : CollatzResearch.WordTrace tailWord_123886 prefixEnd_123886 9424157683408522837817 := by
  unfold tailWord_123886
  simp only [CollatzResearch.WordTrace]
  refine ⟨564811703648706861178939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3012329086126436592954341 564811703648706861178939)
  ·
    refine ⟨847217555473060291768409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 564811703648706861178939 847217555473060291768409)
    ·
      refine ⟨635413166604795218826307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 847217555473060291768409 635413166604795218826307)
      ·
        refine ⟨953119749907192828239461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635413166604795218826307 953119749907192828239461)
        ·
          refine ⟨178709953107598655294899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 953119749907192828239461 178709953107598655294899)
          ·
            refine ⟨268064929661397982942349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178709953107598655294899 268064929661397982942349)
            ·
              refine ⟨100524348623024243603381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268064929661397982942349 100524348623024243603381)
              ·
                refine ⟨9424157683408522837817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100524348623024243603381 9424157683408522837817)
                ·
                  rfl

theorem cell21_123886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_123886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123886 prefixEnd_123886 := by exact prefixLift 123886
  have htrace : WordTrace (prefixWord ++ tailWord_123886) baseStart_123886 baseEnd_123886 := by
    simpa [prefixWord, tailWord_123886, baseEnd_123886] using wordTrace_append hprefix tailTrace_123886
  have hstable : (prefixWord ++ tailWord_123886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123886).length < 2 ^ (prefixWord ++ tailWord_123886).sum := by decide
  have hdescent : baseEnd_123886 < baseStart_123886 := by decide
  rcases family_descends (prefixWord ++ tailWord_123886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123897 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 6]
def baseStart_123897 : Nat := 118140960795 + 123897 * 2 ^ 59
def prefixEnd_123897 : Nat := 4983230072969 + 3 ^ 40 * 123897 * 2
def baseEnd_123897 : Nat := 28274983400091993830095

theorem tailTrace_123897 : CollatzResearch.WordTrace tailWord_123897 prefixEnd_123897 28274983400091993830095 := by
  unfold tailWord_123897
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518894832149803768081945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3012596554766535845387963 4518894832149803768081945)
  ·
    refine ⟨3389171124112352826061459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4518894832149803768081945 3389171124112352826061459)
    ·
      refine ⟨5083756686168529239092189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389171124112352826061459 5083756686168529239092189)
      ·
        refine ⟨1906408757313198464659571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5083756686168529239092189 1906408757313198464659571)
        ·
          refine ⟨2859613135969797696989357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906408757313198464659571 2859613135969797696989357)
          ·
            refine ⟨1072354925988674136371009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2859613135969797696989357 1072354925988674136371009)
            ·
              refine ⟨804266194491505602278257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072354925988674136371009 804266194491505602278257)
              ·
                refine ⟨603199645868629201708693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804266194491505602278257 603199645868629201708693)
                ·
                  refine ⟨28274983400091993830095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 603199645868629201708693 28274983400091993830095)
                  ·
                    rfl

theorem cell21_123897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_123897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123897 prefixEnd_123897 := by exact prefixLift 123897
  have htrace : WordTrace (prefixWord ++ tailWord_123897) baseStart_123897 baseEnd_123897 := by
    simpa [prefixWord, tailWord_123897, baseEnd_123897] using wordTrace_append hprefix tailTrace_123897
  have hstable : (prefixWord ++ tailWord_123897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123897).length < 2 ^ (prefixWord ++ tailWord_123897).sum := by decide
  have hdescent : baseEnd_123897 < baseStart_123897 := by decide
  rcases family_descends (prefixWord ++ tailWord_123897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123900 : List Nat := [2, 2, 2, 1, 2, 3, 1, 5, 3]
def baseStart_123900 : Nat := 118140960795 + 123900 * 2 ^ 59
def prefixEnd_123900 : Nat := 4983230072969 + 3 ^ 40 * 123900 * 2
def baseEnd_123900 : Nat := 28275668040964655280089

theorem tailTrace_123900 : CollatzResearch.WordTrace tailWord_123900 prefixEnd_123900 28275668040964655280089 := by
  unfold tailWord_123900
  simp only [CollatzResearch.WordTrace]
  refine ⟨2259502125569467640220577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3012669500759290186960769 2259502125569467640220577)
  ·
    refine ⟨1694626594177100730165433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2259502125569467640220577 1694626594177100730165433)
    ·
      refine ⟨1270969945632825547624075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1694626594177100730165433 1270969945632825547624075)
      ·
        refine ⟨1906454918449238321436113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1270969945632825547624075 1906454918449238321436113)
        ·
          refine ⟨1429841188836928741077085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1906454918449238321436113 1429841188836928741077085)
          ·
            refine ⟨536190445813848277903907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1429841188836928741077085 536190445813848277903907)
            ·
              refine ⟨804285668720772416855861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536190445813848277903907 804285668720772416855861)
              ·
                refine ⟨75401781442572414080237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804285668720772416855861 75401781442572414080237)
                ·
                  refine ⟨28275668040964655280089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75401781442572414080237 28275668040964655280089)
                  ·
                    rfl

theorem cell21_123900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_123900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123900 prefixEnd_123900 := by exact prefixLift 123900
  have htrace : WordTrace (prefixWord ++ tailWord_123900) baseStart_123900 baseEnd_123900 := by
    simpa [prefixWord, tailWord_123900, baseEnd_123900] using wordTrace_append hprefix tailTrace_123900
  have hstable : (prefixWord ++ tailWord_123900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123900).length < 2 ^ (prefixWord ++ tailWord_123900).sum := by decide
  have hdescent : baseEnd_123900 < baseStart_123900 := by decide
  rcases family_descends (prefixWord ++ tailWord_123900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123906 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_123906 : Nat := 118140960795 + 123906 * 2 ^ 59
def prefixEnd_123906 : Nat := 4983230072969 + 3 ^ 40 * 123906 * 2
def baseEnd_123906 : Nat := 28277037322709978180077

theorem tailTrace_123906 : CollatzResearch.WordTrace tailWord_123906 prefixEnd_123906 28277037322709978180077 := by
  unfold tailWord_123906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129805772279299576289893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3012815392744798870106381 1129805772279299576289893)
  ·
    refine ⟨211838582302368670554355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1129805772279299576289893 211838582302368670554355)
    ·
      refine ⟨317757873453553005831533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211838582302368670554355 317757873453553005831533)
      ·
        refine ⟨119159202545082377186825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317757873453553005831533 119159202545082377186825)
        ·
          refine ⟨89369401908811782890119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119159202545082377186825 89369401908811782890119)
          ·
            refine ⟨134054102863217674335179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89369401908811782890119 134054102863217674335179)
            ·
              refine ⟨201081154294826511502769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134054102863217674335179 201081154294826511502769)
              ·
                refine ⟨150810865721119883627077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201081154294826511502769 150810865721119883627077)
                ·
                  refine ⟨28277037322709978180077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150810865721119883627077 28277037322709978180077)
                  ·
                    rfl

theorem cell21_123906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_123906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123906 prefixEnd_123906 := by exact prefixLift 123906
  have htrace : WordTrace (prefixWord ++ tailWord_123906) baseStart_123906 baseEnd_123906 := by
    simpa [prefixWord, tailWord_123906, baseEnd_123906] using wordTrace_append hprefix tailTrace_123906
  have hstable : (prefixWord ++ tailWord_123906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123906).length < 2 ^ (prefixWord ++ tailWord_123906).sum := by decide
  have hdescent : baseEnd_123906 < baseStart_123906 := by decide
  rcases family_descends (prefixWord ++ tailWord_123906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123914 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_123914 : Nat := 118140960795 + 123914 * 2 ^ 59
def prefixEnd_123914 : Nat := 4983230072969 + 3 ^ 40 * 123914 * 2
def baseEnd_123914 : Nat := 28278863031703742046727

theorem tailTrace_123914 : CollatzResearch.WordTrace tailWord_123914 prefixEnd_123914 28278863031703742046727 := by
  unfold tailWord_123914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129878718272053917862699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3013009915392143780967197 1129878718272053917862699)
  ·
    refine ⟨1694818077408080876794049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129878718272053917862699 1694818077408080876794049)
    ·
      refine ⟨1271113558056060657595537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1694818077408080876794049 1271113558056060657595537)
      ·
        refine ⟨953335168542045493196653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1271113558056060657595537 953335168542045493196653)
        ·
          refine ⟨357500688203267059948745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953335168542045493196653 357500688203267059948745)
          ·
            refine ⟨268125516152450294961559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357500688203267059948745 268125516152450294961559)
            ·
              refine ⟨402188274228675442442339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268125516152450294961559 402188274228675442442339)
              ·
                refine ⟨603282411343013163663509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402188274228675442442339 603282411343013163663509)
                ·
                  refine ⟨28278863031703742046727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 603282411343013163663509 28278863031703742046727)
                  ·
                    rfl

theorem cell21_123914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_123914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123914 prefixEnd_123914 := by exact prefixLift 123914
  have htrace : WordTrace (prefixWord ++ tailWord_123914) baseStart_123914 baseEnd_123914 := by
    simpa [prefixWord, tailWord_123914, baseEnd_123914] using wordTrace_append hprefix tailTrace_123914
  have hstable : (prefixWord ++ tailWord_123914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123914).length < 2 ^ (prefixWord ++ tailWord_123914).sum := by decide
  have hdescent : baseEnd_123914 < baseStart_123914 := by decide
  rcases family_descends (prefixWord ++ tailWord_123914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123973 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 6]
def baseStart_123973 : Nat := 118140960795 + 123973 * 2 ^ 59
def prefixEnd_123973 : Nat := 4983230072969 + 3 ^ 40 * 123973 * 2
def baseEnd_123973 : Nat := 28292327635532750563273

theorem tailTrace_123973 : CollatzResearch.WordTrace tailWord_123973 prefixEnd_123973 28292327635532750563273 := by
  unfold tailWord_123973
  simp only [CollatzResearch.WordTrace]
  refine ⟨4521666779874468747848573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3014444519916312498565715 4521666779874468747848573)
  ·
    refine ⟨1695625042452925780443215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4521666779874468747848573 1695625042452925780443215)
    ·
      refine ⟨2543437563679388670664823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695625042452925780443215 2543437563679388670664823)
      ·
        refine ⟨3815156345519083005997235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543437563679388670664823 3815156345519083005997235)
        ·
          refine ⟨5722734518278624508995853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815156345519083005997235 5722734518278624508995853)
          ·
            refine ⟨2146025444354484190873445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5722734518278624508995853 2146025444354484190873445)
            ·
              refine ⟨402379770816465785788771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2146025444354484190873445 402379770816465785788771)
              ·
                refine ⟨603569656224698678683157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402379770816465785788771 603569656224698678683157)
                ·
                  refine ⟨28292327635532750563273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 603569656224698678683157 28292327635532750563273)
                  ·
                    rfl

theorem cell21_123973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_123973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123973 prefixEnd_123973 := by exact prefixLift 123973
  have htrace : WordTrace (prefixWord ++ tailWord_123973) baseStart_123973 baseEnd_123973 := by
    simpa [prefixWord, tailWord_123973, baseEnd_123973] using wordTrace_append hprefix tailTrace_123973
  have hstable : (prefixWord ++ tailWord_123973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123973).length < 2 ^ (prefixWord ++ tailWord_123973).sum := by decide
  have hdescent : baseEnd_123973 < baseStart_123973 := by decide
  rcases family_descends (prefixWord ++ tailWord_123973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_123987 : List Nat := [1, 1, 1, 2, 1, 1, 2, 12]
def baseStart_123987 : Nat := 118140960795 + 123987 * 2 ^ 59
def prefixEnd_123987 : Nat := 4983230072969 + 3 ^ 40 * 123987 * 2
def baseEnd_123987 : Nat := 9431840875423945776637

theorem tailTrace_123987 : CollatzResearch.WordTrace tailWord_123987 prefixEnd_123987 9431840875423945776637 := by
  unfold tailWord_123987
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522177401823749138858215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3014784934549166092572143 4522177401823749138858215)
  ·
    refine ⟨6783266102735623708287323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4522177401823749138858215 6783266102735623708287323)
    ·
      refine ⟨10174899154103435562430985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783266102735623708287323 10174899154103435562430985)
      ·
        refine ⟨7631174365577576671823239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10174899154103435562430985 7631174365577576671823239)
        ·
          refine ⟨11446761548366365007734859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7631174365577576671823239 11446761548366365007734859)
          ·
            refine ⟨17170142322549547511602289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11446761548366365007734859 17170142322549547511602289)
            ·
              refine ⟨12877606741912160633701717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17170142322549547511602289 12877606741912160633701717)
              ·
                refine ⟨9431840875423945776637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 12877606741912160633701717 9431840875423945776637)
                ·
                  rfl

theorem cell21_123987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 12].length) (baseStart_123987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_123987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_123987 prefixEnd_123987 := by exact prefixLift 123987
  have htrace : WordTrace (prefixWord ++ tailWord_123987) baseStart_123987 baseEnd_123987 := by
    simpa [prefixWord, tailWord_123987, baseEnd_123987] using wordTrace_append hprefix tailTrace_123987
  have hstable : (prefixWord ++ tailWord_123987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_123987).length < 2 ^ (prefixWord ++ tailWord_123987).sum := by decide
  have hdescent : baseEnd_123987 < baseStart_123987 := by decide
  rcases family_descends (prefixWord ++ tailWord_123987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124021 : List Nat := [1, 3, 4, 3, 1, 9]
def baseStart_124021 : Nat := 118140960795 + 124021 * 2 ^ 59
def prefixEnd_124021 : Nat := 4983230072969 + 3 ^ 40 * 124021 * 2
def baseEnd_124021 : Nat := 1048269699610938287525

theorem tailTrace_124021 : CollatzResearch.WordTrace tailWord_124021 prefixEnd_124021 1048269699610938287525 := by
  unfold tailWord_124021
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523417483700572945595917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3015611655800381963730611 4523417483700572945595917)
  ·
    refine ⟨1696281556387714854598469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4523417483700572945595917 1696281556387714854598469)
    ·
      refine ⟨318052791822696535237213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1696281556387714854598469 318052791822696535237213)
      ·
        refine ⟨119269796933511200713955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318052791822696535237213 119269796933511200713955)
        ·
          refine ⟨178904695400266801070933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119269796933511200713955 178904695400266801070933)
          ·
            refine ⟨1048269699610938287525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 178904695400266801070933 1048269699610938287525)
            ·
              rfl

theorem cell21_124021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 9].length) (baseStart_124021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124021 prefixEnd_124021 := by exact prefixLift 124021
  have htrace : WordTrace (prefixWord ++ tailWord_124021) baseStart_124021 baseEnd_124021 := by
    simpa [prefixWord, tailWord_124021, baseEnd_124021] using wordTrace_append hprefix tailTrace_124021
  have hstable : (prefixWord ++ tailWord_124021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124021).length < 2 ^ (prefixWord ++ tailWord_124021).sum := by decide
  have hdescent : baseEnd_124021 < baseStart_124021 := by decide
  rcases family_descends (prefixWord ++ tailWord_124021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124086 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_124086 : Nat := 118140960795 + 124086 * 2 ^ 59
def prefixEnd_124086 : Nat := 4983230072969 + 3 ^ 40 * 124086 * 2
def baseEnd_124086 : Nat := 28318115775069665179709

theorem tailTrace_124086 : CollatzResearch.WordTrace tailWord_124086 prefixEnd_124086 28318115775069665179709 := by
  unfold tailWord_124086
  simp only [CollatzResearch.WordTrace]
  refine ⟨282861764279068065419507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3017192152310059364474741 282861764279068065419507)
  ·
    refine ⟨424292646418602098129261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282861764279068065419507 424292646418602098129261)
    ·
      refine ⟨159109742406975786798473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424292646418602098129261 159109742406975786798473)
      ·
        refine ⟨119332306805231840098855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159109742406975786798473 119332306805231840098855)
        ·
          refine ⟨178998460207847760148283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119332306805231840098855 178998460207847760148283)
          ·
            refine ⟨268497690311771640222425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178998460207847760148283 268497690311771640222425)
            ·
              refine ⟨201373267733828730166819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268497690311771640222425 201373267733828730166819)
              ·
                refine ⟨302059901600743095250229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201373267733828730166819 302059901600743095250229)
                ·
                  refine ⟨28318115775069665179709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 302059901600743095250229 28318115775069665179709)
                  ·
                    rfl

theorem cell21_124086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_124086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124086 prefixEnd_124086 := by exact prefixLift 124086
  have htrace : WordTrace (prefixWord ++ tailWord_124086) baseStart_124086 baseEnd_124086 := by
    simpa [prefixWord, tailWord_124086, baseEnd_124086] using wordTrace_append hprefix tailTrace_124086
  have hstable : (prefixWord ++ tailWord_124086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124086).length < 2 ^ (prefixWord ++ tailWord_124086).sum := by decide
  have hdescent : baseEnd_124086 < baseStart_124086 := by decide
  rcases family_descends (prefixWord ++ tailWord_124086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124100 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_124100 : Nat := 118140960795 + 124100 * 2 ^ 59
def prefixEnd_124100 : Nat := 4983230072969 + 3 ^ 40 * 124100 * 2
def baseEnd_124100 : Nat := 28321310765808751946347

theorem tailTrace_124100 : CollatzResearch.WordTrace tailWord_124100 prefixEnd_124100 28321310765808751946347 := by
  unfold tailWord_124100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263149425207184718860877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3017532566942912958481169 2263149425207184718860877)
  ·
    refine ⟨848681034452694269572829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2263149425207184718860877 848681034452694269572829)
    ·
      refine ⟨318255387919760351089811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 848681034452694269572829 318255387919760351089811)
      ·
        refine ⟨477383081879640526634717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318255387919760351089811 477383081879640526634717)
        ·
          refine ⟨179018655704865197488019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477383081879640526634717 179018655704865197488019)
          ·
            refine ⟨268527983557297796232029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179018655704865197488019 268527983557297796232029)
            ·
              refine ⟨100697993833986673587011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268527983557297796232029 100697993833986673587011)
              ·
                refine ⟨151046990750980010380517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100697993833986673587011 151046990750980010380517)
                ·
                  refine ⟨28321310765808751946347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151046990750980010380517 28321310765808751946347)
                  ·
                    rfl

theorem cell21_124100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_124100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124100 prefixEnd_124100 := by exact prefixLift 124100
  have htrace : WordTrace (prefixWord ++ tailWord_124100) baseStart_124100 baseEnd_124100 := by
    simpa [prefixWord, tailWord_124100, baseEnd_124100] using wordTrace_append hprefix tailTrace_124100
  have hstable : (prefixWord ++ tailWord_124100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124100).length < 2 ^ (prefixWord ++ tailWord_124100).sum := by decide
  have hdescent : baseEnd_124100 < baseStart_124100 := by decide
  rcases family_descends (prefixWord ++ tailWord_124100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124128 : List Nat := [2, 1, 1, 3, 1, 4, 3, 3, 3]
def baseStart_124128 : Nat := 118140960795 + 124128 * 2 ^ 59
def prefixEnd_124128 : Nat := 4983230072969 + 3 ^ 40 * 124128 * 2
def baseEnd_124128 : Nat := 28327700747286925479623

theorem tailTrace_124128 : CollatzResearch.WordTrace tailWord_124128 prefixEnd_124128 28327700747286925479623 := by
  unfold tailWord_124128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263660047156465109870519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3018213396208620146494025 2263660047156465109870519)
  ·
    refine ⟨3395490070734697664805779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263660047156465109870519 3395490070734697664805779)
    ·
      refine ⟨5093235106102046497208669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395490070734697664805779 5093235106102046497208669)
      ·
        refine ⟨1909963164788267436453251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5093235106102046497208669 1909963164788267436453251)
        ·
          refine ⟨2864944747182401154679877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909963164788267436453251 2864944747182401154679877)
          ·
            refine ⟨537177140096700216502477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2864944747182401154679877 537177140096700216502477)
            ·
              refine ⟨201441427536262581188429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537177140096700216502477 201441427536262581188429)
              ·
                refine ⟨75540535326098467945661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201441427536262581188429 75540535326098467945661)
                ·
                  refine ⟨28327700747286925479623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75540535326098467945661 28327700747286925479623)
                  ·
                    rfl

theorem cell21_124128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_124128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124128 prefixEnd_124128 := by exact prefixLift 124128
  have htrace : WordTrace (prefixWord ++ tailWord_124128) baseStart_124128 baseEnd_124128 := by
    simpa [prefixWord, tailWord_124128, baseEnd_124128] using wordTrace_append hprefix tailTrace_124128
  have hstable : (prefixWord ++ tailWord_124128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124128).length < 2 ^ (prefixWord ++ tailWord_124128).sum := by decide
  have hdescent : baseEnd_124128 < baseStart_124128 := by decide
  rcases family_descends (prefixWord ++ tailWord_124128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124139 : List Nat := [1, 1, 1, 1, 2, 6, 9]
def baseStart_124139 : Nat := 118140960795 + 124139 * 2 ^ 59
def prefixEnd_124139 : Nat := 4983230072969 + 3 ^ 40 * 124139 * 2
def baseEnd_124139 : Nat := 3147801233017038977363

theorem tailTrace_124139 : CollatzResearch.WordTrace tailWord_124139 prefixEnd_124139 3147801233017038977363 := by
  unfold tailWord_124139
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527721297273079098391471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3018480864848719398927647 4527721297273079098391471)
  ·
    refine ⟨6791581945909618647587207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4527721297273079098391471 6791581945909618647587207)
    ·
      refine ⟨10187372918864427971380811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791581945909618647587207 10187372918864427971380811)
      ·
        refine ⟨15281059378296641957071217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187372918864427971380811 15281059378296641957071217)
        ·
          refine ⟨11460794533722481467803413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15281059378296641957071217 11460794533722481467803413)
          ·
            refine ⟨537224743768241318803285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11460794533722481467803413 537224743768241318803285)
            ·
              refine ⟨3147801233017038977363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 537224743768241318803285 3147801233017038977363)
              ·
                rfl

theorem cell21_124139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 9].length) (baseStart_124139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124139 prefixEnd_124139 := by exact prefixLift 124139
  have htrace : WordTrace (prefixWord ++ tailWord_124139) baseStart_124139 baseEnd_124139 := by
    simpa [prefixWord, tailWord_124139, baseEnd_124139] using wordTrace_append hprefix tailTrace_124139
  have hstable : (prefixWord ++ tailWord_124139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124139).length < 2 ^ (prefixWord ++ tailWord_124139).sum := by decide
  have hdescent : baseEnd_124139 < baseStart_124139 := by decide
  rcases family_descends (prefixWord ++ tailWord_124139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124159 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 4]
def baseStart_124159 : Nat := 118140960795 + 124159 * 2 ^ 59
def prefixEnd_124159 : Nat := 4983230072969 + 3 ^ 40 * 124159 * 2
def baseEnd_124159 : Nat := 28334775369637760462893

theorem tailTrace_124159 : CollatzResearch.WordTrace tailWord_124159 prefixEnd_124159 28334775369637760462893 := by
  unfold tailWord_124159
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528450757200622514119531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3018967171467081676079687 4528450757200622514119531)
  ·
    refine ⟨6792676135800933771179297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4528450757200622514119531 6792676135800933771179297)
    ·
      refine ⟨5094507101850700328384473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6792676135800933771179297 5094507101850700328384473)
      ·
        refine ⟨3820880326388025246288355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5094507101850700328384473 3820880326388025246288355)
        ·
          refine ⟨5731320489582037869432533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3820880326388025246288355 5731320489582037869432533)
          ·
            refine ⟨134327823974579012564825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5731320489582037869432533 134327823974579012564825)
            ·
              refine ⟨100745867980934259423619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134327823974579012564825 100745867980934259423619)
              ·
                refine ⟨151118801971401389135429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100745867980934259423619 151118801971401389135429)
                ·
                  refine ⟨28334775369637760462893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151118801971401389135429 28334775369637760462893)
                  ·
                    rfl

theorem cell21_124159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 4].length) (baseStart_124159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124159 prefixEnd_124159 := by exact prefixLift 124159
  have htrace : WordTrace (prefixWord ++ tailWord_124159) baseStart_124159 baseEnd_124159 := by
    simpa [prefixWord, tailWord_124159, baseEnd_124159] using wordTrace_append hprefix tailTrace_124159
  have hstable : (prefixWord ++ tailWord_124159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124159).length < 2 ^ (prefixWord ++ tailWord_124159).sum := by decide
  have hdescent : baseEnd_124159 < baseStart_124159 := by decide
  rcases family_descends (prefixWord ++ tailWord_124159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124170 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_124170 : Nat := 118140960795 + 124170 * 2 ^ 59
def prefixEnd_124170 : Nat := 4983230072969 + 3 ^ 40 * 124170 * 2
def baseEnd_124170 : Nat := 28337285719504185779537

theorem tailTrace_124170 : CollatzResearch.WordTrace tailWord_124170 prefixEnd_124170 28337285719504185779537 := by
  unfold tailWord_124170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132212990040192848192491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3019234640107180928513309 1132212990040192848192491)
  ·
    refine ⟨1698319485060289272288737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1132212990040192848192491 1698319485060289272288737)
    ·
      refine ⟨1273739613795216954216553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1698319485060289272288737 1273739613795216954216553)
      ·
        refine ⟨955304710346412715662415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1273739613795216954216553 955304710346412715662415)
        ·
          refine ⟨1432957065519619073493623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955304710346412715662415 1432957065519619073493623)
          ·
            refine ⟨2149435598279428610240435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432957065519619073493623 2149435598279428610240435)
            ·
              refine ⟨3224153397419142915360653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149435598279428610240435 3224153397419142915360653)
              ·
                refine ⟨1209057524032178593260245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3224153397419142915360653 1209057524032178593260245)
                ·
                  refine ⟨28337285719504185779537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1209057524032178593260245 28337285719504185779537)
                  ·
                    rfl

theorem cell21_124170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_124170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124170 prefixEnd_124170 := by exact prefixLift 124170
  have htrace : WordTrace (prefixWord ++ tailWord_124170) baseStart_124170 baseEnd_124170 := by
    simpa [prefixWord, tailWord_124170, baseEnd_124170] using wordTrace_append hprefix tailTrace_124170
  have hstable : (prefixWord ++ tailWord_124170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124170).length < 2 ^ (prefixWord ++ tailWord_124170).sum := by decide
  have hdescent : baseEnd_124170 < baseStart_124170 := by decide
  rcases family_descends (prefixWord ++ tailWord_124170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124187 : List Nat := [1, 1, 1, 1, 1, 1, 5, 7, 3]
def baseStart_124187 : Nat := 118140960795 + 124187 * 2 ^ 59
def prefixEnd_124187 : Nat := 4983230072969 + 3 ^ 40 * 124187 * 2
def baseEnd_124187 : Nat := 28341165351115933996169

theorem tailTrace_124187 : CollatzResearch.WordTrace tailWord_124187 prefixEnd_124187 28341165351115933996169 := by
  unfold tailWord_124187
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529472001099183296138815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3019648000732788864092543 4529472001099183296138815)
  ·
    refine ⟨6794208001648774944208223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4529472001099183296138815 6794208001648774944208223)
    ·
      refine ⟨10191312002473162416312335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6794208001648774944208223 10191312002473162416312335)
      ·
        refine ⟨15286968003709743624468503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10191312002473162416312335 15286968003709743624468503)
        ·
          refine ⟨22930452005564615436702755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15286968003709743624468503 22930452005564615436702755)
          ·
            refine ⟨34395678008346923155054133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22930452005564615436702755 34395678008346923155054133)
            ·
              refine ⟨3224594813282524045786325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34395678008346923155054133 3224594813282524045786325)
              ·
                refine ⟨75576440936309157323117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3224594813282524045786325 75576440936309157323117)
                ·
                  refine ⟨28341165351115933996169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75576440936309157323117 28341165351115933996169)
                  ·
                    rfl

theorem cell21_124187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 3].length) (baseStart_124187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124187 prefixEnd_124187 := by exact prefixLift 124187
  have htrace : WordTrace (prefixWord ++ tailWord_124187) baseStart_124187 baseEnd_124187 := by
    simpa [prefixWord, tailWord_124187, baseEnd_124187] using wordTrace_append hprefix tailTrace_124187
  have hstable : (prefixWord ++ tailWord_124187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124187).length < 2 ^ (prefixWord ++ tailWord_124187).sum := by decide
  have hdescent : baseEnd_124187 < baseStart_124187 := by decide
  rcases family_descends (prefixWord ++ tailWord_124187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124190 : List Nat := [4, 3, 2, 1, 3, 8]
def baseStart_124190 : Nat := 118140960795 + 124190 * 2 ^ 59
def prefixEnd_124190 : Nat := 4983230072969 + 3 ^ 40 * 124190 * 2
def baseEnd_124190 : Nat := 1049698147851429460969

theorem tailTrace_124190 : CollatzResearch.WordTrace tailWord_124190 prefixEnd_124190 1049698147851429460969 := by
  unfold tailWord_124190
  simp only [CollatzResearch.WordTrace]
  refine ⟨566197677511039351062253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3019720946725543205665349 566197677511039351062253)
  ·
    refine ⟨212324129066639756648345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 566197677511039351062253 212324129066639756648345)
    ·
      refine ⟨159243096799979817486259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212324129066639756648345 159243096799979817486259)
      ·
        refine ⟨238864645199969726229389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159243096799979817486259 238864645199969726229389)
        ·
          refine ⟨89574241949988647336021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238864645199969726229389 89574241949988647336021)
          ·
            refine ⟨1049698147851429460969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 89574241949988647336021 1049698147851429460969)
            ·
              rfl

theorem cell21_124190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 8].length) (baseStart_124190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124190 prefixEnd_124190 := by exact prefixLift 124190
  have htrace : WordTrace (prefixWord ++ tailWord_124190) baseStart_124190 baseEnd_124190 := by
    simpa [prefixWord, tailWord_124190, baseEnd_124190] using wordTrace_append hprefix tailTrace_124190
  have hstable : (prefixWord ++ tailWord_124190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124190).length < 2 ^ (prefixWord ++ tailWord_124190).sum := by decide
  have hdescent : baseEnd_124190 < baseStart_124190 := by decide
  rcases family_descends (prefixWord ++ tailWord_124190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124297 : List Nat := [1, 2, 1, 1, 7, 2, 1, 3, 3]
def baseStart_124297 : Nat := 118140960795 + 124297 * 2 ^ 59
def prefixEnd_124297 : Nat := 4983230072969 + 3 ^ 40 * 124297 * 2
def baseEnd_124297 : Nat := 28366268849780187162611

theorem tailTrace_124297 : CollatzResearch.WordTrace tailWord_124297 prefixEnd_124297 28366268849780187162611 := by
  unfold tailWord_124297
  simp only [CollatzResearch.WordTrace]
  refine ⟨4533484030700672082643145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3022322687133781388428763 4533484030700672082643145)
  ·
    refine ⟨3400113023025504061982359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4533484030700672082643145 3400113023025504061982359)
    ·
      refine ⟨5100169534538256092973539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3400113023025504061982359 5100169534538256092973539)
      ·
        refine ⟨7650254301807384139460309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100169534538256092973539 7650254301807384139460309)
        ·
          refine ⟨179302835198610565768601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7650254301807384139460309 179302835198610565768601)
          ·
            refine ⟨134477126398957924326451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179302835198610565768601 134477126398957924326451)
            ·
              refine ⟨201715689598436886489677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134477126398957924326451 201715689598436886489677)
              ·
                refine ⟨75643383599413832433629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201715689598436886489677 75643383599413832433629)
                ·
                  refine ⟨28366268849780187162611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75643383599413832433629 28366268849780187162611)
                  ·
                    rfl

theorem cell21_124297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_124297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124297 prefixEnd_124297 := by exact prefixLift 124297
  have htrace : WordTrace (prefixWord ++ tailWord_124297) baseStart_124297 baseEnd_124297 := by
    simpa [prefixWord, tailWord_124297, baseEnd_124297] using wordTrace_append hprefix tailTrace_124297
  have hstable : (prefixWord ++ tailWord_124297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124297).length < 2 ^ (prefixWord ++ tailWord_124297).sum := by decide
  have hdescent : baseEnd_124297 < baseStart_124297 := by decide
  rcases family_descends (prefixWord ++ tailWord_124297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124308 : List Nat := [2, 4, 2, 1, 2, 1, 9]
def baseStart_124308 : Nat := 118140960795 + 124308 * 2 ^ 59
def prefixEnd_124308 : Nat := 4983230072969 + 3 ^ 40 * 124308 * 2
def baseEnd_124308 : Nat := 3152086577738512497695

theorem tailTrace_124308 : CollatzResearch.WordTrace tailWord_124308 prefixEnd_124308 3152086577738512497695 := by
  unfold tailWord_124308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266942616830410480646789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3022590155773880640862385 2266942616830410480646789)
  ·
    refine ⟨425051740655701965121273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2266942616830410480646789 425051740655701965121273)
    ·
      refine ⟨318788805491776473840955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425051740655701965121273 318788805491776473840955)
      ·
        refine ⟨478183208237664710761433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318788805491776473840955 478183208237664710761433)
        ·
          refine ⟨358637406178248533071075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478183208237664710761433 358637406178248533071075)
          ·
            refine ⟨537956109267372799606613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358637406178248533071075 537956109267372799606613)
            ·
              refine ⟨3152086577738512497695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 537956109267372799606613 3152086577738512497695)
              ·
                rfl

theorem cell21_124308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 9].length) (baseStart_124308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124308 prefixEnd_124308 := by exact prefixLift 124308
  have htrace : WordTrace (prefixWord ++ tailWord_124308) baseStart_124308 baseEnd_124308 := by
    simpa [prefixWord, tailWord_124308, baseEnd_124308] using wordTrace_append hprefix tailTrace_124308
  have hstable : (prefixWord ++ tailWord_124308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124308).length < 2 ^ (prefixWord ++ tailWord_124308).sum := by decide
  have hdescent : baseEnd_124308 < baseStart_124308 := by decide
  rcases family_descends (prefixWord ++ tailWord_124308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124336 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_124336 : Nat := 118140960795 + 124336 * 2 ^ 59
def prefixEnd_124336 : Nat := 4983230072969 + 3 ^ 40 * 124336 * 2
def baseEnd_124336 : Nat := 28375169181124786012531

theorem tailTrace_124336 : CollatzResearch.WordTrace tailWord_124336 prefixEnd_124336 28375169181124786012531 := by
  unfold tailWord_124336
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267453238779690871656431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3023270985039587828875241 2267453238779690871656431)
  ·
    refine ⟨3401179858169536307484647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2267453238779690871656431 3401179858169536307484647)
    ·
      refine ⟨5101769787254304461226971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3401179858169536307484647 5101769787254304461226971)
      ·
        refine ⟨7652654680881456691840457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5101769787254304461226971 7652654680881456691840457)
        ·
          refine ⟨5739491010661092518880343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7652654680881456691840457 5739491010661092518880343)
          ·
            refine ⟨8609236515991638778320515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739491010661092518880343 8609236515991638778320515)
            ·
              refine ⟨12913854773987458167480773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8609236515991638778320515 12913854773987458167480773)
              ·
                refine ⟨2421347770122648406402645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12913854773987458167480773 2421347770122648406402645)
                ·
                  refine ⟨28375169181124786012531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2421347770122648406402645 28375169181124786012531)
                  ·
                    rfl

theorem cell21_124336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_124336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124336 prefixEnd_124336 := by exact prefixLift 124336
  have htrace : WordTrace (prefixWord ++ tailWord_124336) baseStart_124336 baseEnd_124336 := by
    simpa [prefixWord, tailWord_124336, baseEnd_124336] using wordTrace_append hprefix tailTrace_124336
  have hstable : (prefixWord ++ tailWord_124336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124336).length < 2 ^ (prefixWord ++ tailWord_124336).sum := by decide
  have hdescent : baseEnd_124336 < baseStart_124336 := by decide
  rcases family_descends (prefixWord ++ tailWord_124336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124477 : List Nat := [1, 4, 1, 3, 4, 1, 7]
def baseStart_124477 : Nat := 118140960795 + 124477 * 2 ^ 59
def prefixEnd_124477 : Nat := 4983230072969 + 3 ^ 40 * 124477 * 2
def baseEnd_124477 : Nat := 3156371922459986018027

theorem tailTrace_124477 : CollatzResearch.WordTrace tailWord_124477 prefixEnd_124477 3156371922459986018027 := by
  unfold tailWord_124477
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540049170048562824195685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3026699446699041882797123 4540049170048562824195685)
  ·
    refine ⟨851259219384105529536691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4540049170048562824195685 851259219384105529536691)
    ·
      refine ⟨1276888829076158294305037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 851259219384105529536691 1276888829076158294305037)
      ·
        refine ⟨478833310903559360364389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1276888829076158294305037 478833310903559360364389)
        ·
          refine ⟨89781245794417380068323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 478833310903559360364389 89781245794417380068323)
          ·
            refine ⟨134671868691626070102485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89781245794417380068323 134671868691626070102485)
            ·
              refine ⟨3156371922459986018027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134671868691626070102485 3156371922459986018027)
              ·
                rfl

theorem cell21_124477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 7].length) (baseStart_124477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124477 prefixEnd_124477 := by exact prefixLift 124477
  have htrace : WordTrace (prefixWord ++ tailWord_124477) baseStart_124477 baseEnd_124477 := by
    simpa [prefixWord, tailWord_124477, baseEnd_124477] using wordTrace_append hprefix tailTrace_124477
  have hstable : (prefixWord ++ tailWord_124477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124477).length < 2 ^ (prefixWord ++ tailWord_124477).sum := by decide
  have hdescent : baseEnd_124477 < baseStart_124477 := by decide
  rcases family_descends (prefixWord ++ tailWord_124477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124519 : List Nat := [1, 1, 5, 1, 1, 1, 4, 7]
def baseStart_124519 : Nat := 118140960795 + 124519 * 2 ^ 59
def prefixEnd_124519 : Nat := 4983230072969 + 3 ^ 40 * 124519 * 2
def baseEnd_124519 : Nat := 9472310758119044820719

theorem tailTrace_124519 : CollatzResearch.WordTrace tailWord_124519 prefixEnd_124519 9472310758119044820719 := by
  unfold tailWord_124519
  simp only [CollatzResearch.WordTrace]
  refine ⟨4541581035896403997224611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3027720690597602664816407 4541581035896403997224611)
  ·
    refine ⟨6812371553844605995836917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4541581035896403997224611 6812371553844605995836917)
    ·
      refine ⟨638659833172931812109711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6812371553844605995836917 638659833172931812109711)
      ·
        refine ⟨957989749759397718164567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638659833172931812109711 957989749759397718164567)
        ·
          refine ⟨1436984624639096577246851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957989749759397718164567 1436984624639096577246851)
          ·
            refine ⟨2155476936958644865870277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436984624639096577246851 2155476936958644865870277)
            ·
              refine ⟨404151925679745912350677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2155476936958644865870277 404151925679745912350677)
              ·
                refine ⟨9472310758119044820719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 404151925679745912350677 9472310758119044820719)
                ·
                  rfl

theorem cell21_124519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 7].length) (baseStart_124519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124519 prefixEnd_124519 := by exact prefixLift 124519
  have htrace : WordTrace (prefixWord ++ tailWord_124519) baseStart_124519 baseEnd_124519 := by
    simpa [prefixWord, tailWord_124519, baseEnd_124519] using wordTrace_append hprefix tailTrace_124519
  have hstable : (prefixWord ++ tailWord_124519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124519).length < 2 ^ (prefixWord ++ tailWord_124519).sum := by decide
  have hdescent : baseEnd_124519 < baseStart_124519 := by decide
  rcases family_descends (prefixWord ++ tailWord_124519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124640 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_124640 : Nat := 118140960795 + 124640 * 2 ^ 59
def prefixEnd_124640 : Nat := 4983230072969 + 3 ^ 40 * 124640 * 2
def baseEnd_124640 : Nat := 28444546122887812945243

theorem tailTrace_124640 : CollatzResearch.WordTrace tailWord_124640 prefixEnd_124640 28444546122887812945243 := by
  unfold tailWord_124640
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272997134229020831189687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3030662845638694441586249 2272997134229020831189687)
  ·
    refine ⟨3409495701343531246784531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2272997134229020831189687 3409495701343531246784531)
    ·
      refine ⟨5114243552015296870176797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3409495701343531246784531 5114243552015296870176797)
      ·
        refine ⟨1917841332005736326316299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5114243552015296870176797 1917841332005736326316299)
        ·
          refine ⟨2876761998008604489474449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917841332005736326316299 2876761998008604489474449)
          ·
            refine ⟨2157571498506453367105837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876761998008604489474449 2157571498506453367105837)
            ·
              refine ⟨809089311939920012664689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2157571498506453367105837 809089311939920012664689)
              ·
                refine ⟨606816983954940009498517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809089311939920012664689 606816983954940009498517)
                ·
                  refine ⟨28444546122887812945243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 606816983954940009498517 28444546122887812945243)
                  ·
                    rfl

theorem cell21_124640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_124640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124640 prefixEnd_124640 := by exact prefixLift 124640
  have htrace : WordTrace (prefixWord ++ tailWord_124640) baseStart_124640 baseEnd_124640 := by
    simpa [prefixWord, tailWord_124640, baseEnd_124640] using wordTrace_append hprefix tailTrace_124640
  have hstable : (prefixWord ++ tailWord_124640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124640).length < 2 ^ (prefixWord ++ tailWord_124640).sum := by decide
  have hdescent : baseEnd_124640 < baseStart_124640 := by decide
  rcases family_descends (prefixWord ++ tailWord_124640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124674 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_124674 : Nat := 118140960795 + 124674 * 2 ^ 59
def prefixEnd_124674 : Nat := 4983230072969 + 3 ^ 40 * 124674 * 2
def baseEnd_124674 : Nat := 28452305386111309378507

theorem tailTrace_124674 : CollatzResearch.WordTrace tailWord_124674 prefixEnd_124674 28452305386111309378507 := by
  unfold tailWord_124674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1136808587583716367279269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3031489566889910312744717 1136808587583716367279269)
  ·
    refine ⟨213151610171946818864863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1136808587583716367279269 213151610171946818864863)
    ·
      refine ⟨319727415257920228297295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213151610171946818864863 319727415257920228297295)
      ·
        refine ⟨479591122886880342445943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319727415257920228297295 479591122886880342445943)
        ·
          refine ⟨719386684330320513668915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479591122886880342445943 719386684330320513668915)
          ·
            refine ⟨1079080026495480770503373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719386684330320513668915 1079080026495480770503373)
            ·
              refine ⟨404655009935805288938765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1079080026495480770503373 404655009935805288938765)
              ·
                refine ⟨151745628725926983352037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404655009935805288938765 151745628725926983352037)
                ·
                  refine ⟨28452305386111309378507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151745628725926983352037 28452305386111309378507)
                  ·
                    rfl

theorem cell21_124674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_124674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124674 prefixEnd_124674 := by exact prefixLift 124674
  have htrace : WordTrace (prefixWord ++ tailWord_124674) baseStart_124674 baseEnd_124674 := by
    simpa [prefixWord, tailWord_124674, baseEnd_124674] using wordTrace_append hprefix tailTrace_124674
  have hstable : (prefixWord ++ tailWord_124674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124674).length < 2 ^ (prefixWord ++ tailWord_124674).sum := by decide
  have hdescent : baseEnd_124674 < baseStart_124674 := by decide
  rcases family_descends (prefixWord ++ tailWord_124674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124761 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 7]
def baseStart_124761 : Nat := 118140960795 + 124761 * 2 ^ 59
def prefixEnd_124761 : Nat := 4983230072969 + 3 ^ 40 * 124761 * 2
def baseEnd_124761 : Nat := 28472159971418491428329

theorem tailTrace_124761 : CollatzResearch.WordTrace tailWord_124761 prefixEnd_124761 28472159971418491428329 := by
  unfold tailWord_124761
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550407501019679327534137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3033605000679786218356091 4550407501019679327534137)
  ·
    refine ⟨3412805625764759495650603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4550407501019679327534137 3412805625764759495650603)
    ·
      refine ⟨5119208438647139243475905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3412805625764759495650603 5119208438647139243475905)
      ·
        refine ⟨3839406328985354432606929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5119208438647139243475905 3839406328985354432606929)
        ·
          refine ⟨2879554746739015824455197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3839406328985354432606929 2879554746739015824455197)
          ·
            refine ⟨1079833030027130934170699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2879554746739015824455197 1079833030027130934170699)
            ·
              refine ⟨1619749545040696401256049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079833030027130934170699 1619749545040696401256049)
              ·
                refine ⟨1214812158780522300942037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619749545040696401256049 1214812158780522300942037)
                ·
                  refine ⟨28472159971418491428329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1214812158780522300942037 28472159971418491428329)
                  ·
                    rfl

theorem cell21_124761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_124761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124761 prefixEnd_124761 := by exact prefixLift 124761
  have htrace : WordTrace (prefixWord ++ tailWord_124761) baseStart_124761 baseEnd_124761 := by
    simpa [prefixWord, tailWord_124761, baseEnd_124761] using wordTrace_append hprefix tailTrace_124761
  have hstable : (prefixWord ++ tailWord_124761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124761).length < 2 ^ (prefixWord ++ tailWord_124761).sum := by decide
  have hdescent : baseEnd_124761 < baseStart_124761 := by decide
  rcases family_descends (prefixWord ++ tailWord_124761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124764 : List Nat := [2, 2, 4, 2, 2, 1, 8]
def baseStart_124764 : Nat := 118140960795 + 124764 * 2 ^ 59
def prefixEnd_124764 : Nat := 4983230072969 + 3 ^ 40 * 124764 * 2
def baseEnd_124764 : Nat := 3163649401365683653147

theorem tailTrace_124764 : CollatzResearch.WordTrace tailWord_124764 prefixEnd_124764 3163649401365683653147 := by
  unfold tailWord_124764
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275258460004405419946673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3033677946672540559928897 2275258460004405419946673)
  ·
    refine ⟨1706443845003304064960005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2275258460004405419946673 1706443845003304064960005)
    ·
      refine ⟨319958220938119512180001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1706443845003304064960005 319958220938119512180001)
      ·
        refine ⟨239968665703589634135001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319958220938119512180001 239968665703589634135001)
        ·
          refine ⟨179976499277692225601251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239968665703589634135001 179976499277692225601251)
          ·
            refine ⟨269964748916538338401877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179976499277692225601251 269964748916538338401877)
            ·
              refine ⟨3163649401365683653147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 269964748916538338401877 3163649401365683653147)
              ·
                rfl

theorem cell21_124764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 8].length) (baseStart_124764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124764 prefixEnd_124764 := by exact prefixLift 124764
  have htrace : WordTrace (prefixWord ++ tailWord_124764) baseStart_124764 baseEnd_124764 := by
    simpa [prefixWord, tailWord_124764, baseEnd_124764] using wordTrace_append hprefix tailTrace_124764
  have hstable : (prefixWord ++ tailWord_124764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124764).length < 2 ^ (prefixWord ++ tailWord_124764).sum := by decide
  have hdescent : baseEnd_124764 < baseStart_124764 := by decide
  rcases family_descends (prefixWord ++ tailWord_124764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124798 : List Nat := [4, 2, 3, 1, 1, 3, 2, 5]
def baseStart_124798 : Nat := 118140960795 + 124798 * 2 ^ 59
def prefixEnd_124798 : Nat := 4983230072969 + 3 ^ 40 * 124798 * 2
def baseEnd_124798 : Nat := 9493534625171549770529

theorem tailTrace_124798 : CollatzResearch.WordTrace tailWord_124798 prefixEnd_124798 9493534625171549770529 := by
  unfold tailWord_124798
  simp only [CollatzResearch.WordTrace]
  refine ⟨568969625235704330828881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3034504667923756431087365 568969625235704330828881)
  ·
    refine ⟨426727218926778248121661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 568969625235704330828881 426727218926778248121661)
    ·
      refine ⟨160022707097541843045623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426727218926778248121661 160022707097541843045623)
      ·
        refine ⟨240034060646312764568435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160022707097541843045623 240034060646312764568435)
        ·
          refine ⟨360051090969469146852653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240034060646312764568435 360051090969469146852653)
          ·
            refine ⟨135019159113550930069745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360051090969469146852653 135019159113550930069745)
            ·
              refine ⟨101264369335163197552309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135019159113550930069745 101264369335163197552309)
              ·
                refine ⟨9493534625171549770529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101264369335163197552309 9493534625171549770529)
                ·
                  rfl

theorem cell21_124798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_124798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124798 prefixEnd_124798 := by exact prefixLift 124798
  have htrace : WordTrace (prefixWord ++ tailWord_124798) baseStart_124798 baseEnd_124798 := by
    simpa [prefixWord, tailWord_124798, baseEnd_124798] using wordTrace_append hprefix tailTrace_124798
  have hstable : (prefixWord ++ tailWord_124798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124798).length < 2 ^ (prefixWord ++ tailWord_124798).sum := by decide
  have hdescent : baseEnd_124798 < baseStart_124798 := by decide
  rcases family_descends (prefixWord ++ tailWord_124798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124823 : List Nat := [1, 1, 3, 3, 1, 5, 7]
def baseStart_124823 : Nat := 118140960795 + 124823 * 2 ^ 59
def prefixEnd_124823 : Nat := 4983230072969 + 3 ^ 40 * 124823 * 2
def baseEnd_124823 : Nat := 3165145468457795710541

theorem tailTrace_124823 : CollatzResearch.WordTrace tailWord_124823 prefixEnd_124823 3165145468457795710541 := by
  unfold tailWord_124823
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552668826795063916291123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3035112551196709277527415 4552668826795063916291123)
  ·
    refine ⟨6829003240192595874436685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4552668826795063916291123 6829003240192595874436685)
    ·
      refine ⟨2560876215072223452913757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6829003240192595874436685 2560876215072223452913757)
      ·
        refine ⟨960328580652083794842659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2560876215072223452913757 960328580652083794842659)
        ·
          refine ⟨1440492870978125692263989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960328580652083794842659 1440492870978125692263989)
          ·
            refine ⟨135046206654199283649749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1440492870978125692263989 135046206654199283649749)
            ·
              refine ⟨3165145468457795710541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 135046206654199283649749 3165145468457795710541)
              ·
                rfl

theorem cell21_124823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 7].length) (baseStart_124823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124823 prefixEnd_124823 := by exact prefixLift 124823
  have htrace : WordTrace (prefixWord ++ tailWord_124823) baseStart_124823 baseEnd_124823 := by
    simpa [prefixWord, tailWord_124823, baseEnd_124823] using wordTrace_append hprefix tailTrace_124823
  have hstable : (prefixWord ++ tailWord_124823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124823).length < 2 ^ (prefixWord ++ tailWord_124823).sum := by decide
  have hdescent : baseEnd_124823 < baseStart_124823 := by decide
  rcases family_descends (prefixWord ++ tailWord_124823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124885 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 4]
def baseStart_124885 : Nat := 118140960795 + 124885 * 2 ^ 59
def prefixEnd_124885 : Nat := 4983230072969 + 3 ^ 40 * 124885 * 2
def baseEnd_124885 : Nat := 28500458460821831361409

theorem tailTrace_124885 : CollatzResearch.WordTrace tailWord_124885 prefixEnd_124885 28500458460821831361409 := by
  unfold tailWord_124885
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554930152570448505048109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3036620101713632336698739 4554930152570448505048109)
  ·
    refine ⟨1708098807213918189393041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4554930152570448505048109 1708098807213918189393041)
    ·
      refine ⟨1281074105410438642044781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1708098807213918189393041 1281074105410438642044781)
      ·
        refine ⟨480402789528914490766793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1281074105410438642044781 480402789528914490766793)
        ·
          refine ⟨360302092146685868075095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480402789528914490766793 360302092146685868075095)
          ·
            refine ⟨540453138220028802112643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360302092146685868075095 540453138220028802112643)
            ·
              refine ⟨810679707330043203168965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540453138220028802112643 810679707330043203168965)
              ·
                refine ⟨152002445124383100594181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 810679707330043203168965 152002445124383100594181)
                ·
                  refine ⟨28500458460821831361409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152002445124383100594181 28500458460821831361409)
                  ·
                    rfl

theorem cell21_124885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_124885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124885 prefixEnd_124885 := by exact prefixLift 124885
  have htrace : WordTrace (prefixWord ++ tailWord_124885) baseStart_124885 baseEnd_124885 := by
    simpa [prefixWord, tailWord_124885, baseEnd_124885] using wordTrace_append hprefix tailTrace_124885
  have hstable : (prefixWord ++ tailWord_124885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124885).length < 2 ^ (prefixWord ++ tailWord_124885).sum := by decide
  have hdescent : baseEnd_124885 < baseStart_124885 := by decide
  rcases family_descends (prefixWord ++ tailWord_124885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124899 : List Nat := [1, 1, 1, 6, 1, 2, 3, 6]
def baseStart_124899 : Nat := 118140960795 + 124899 * 2 ^ 59
def prefixEnd_124899 : Nat := 4983230072969 + 3 ^ 40 * 124899 * 2
def baseEnd_124899 : Nat := 9501217817186972709349

theorem tailTrace_124899 : CollatzResearch.WordTrace tailWord_124899 prefixEnd_124899 9501217817186972709349 := by
  unfold tailWord_124899
  simp only [CollatzResearch.WordTrace]
  refine ⟨4555440774519728896057751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3036960516346485930705167 4555440774519728896057751)
  ·
    refine ⟨6833161161779593344086627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4555440774519728896057751 6833161161779593344086627)
    ·
      refine ⟨10249741742669390016129941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6833161161779593344086627 10249741742669390016129941)
      ·
        refine ⟨480456644187627657006091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10249741742669390016129941 480456644187627657006091)
        ·
          refine ⟨720684966281441485509137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480456644187627657006091 720684966281441485509137)
          ·
            refine ⟨540513724711081114131853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720684966281441485509137 540513724711081114131853)
            ·
              refine ⟨202692646766655417799445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 540513724711081114131853 202692646766655417799445)
              ·
                refine ⟨9501217817186972709349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202692646766655417799445 9501217817186972709349)
                ·
                  rfl

theorem cell21_124899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 6].length) (baseStart_124899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_124899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_124899 prefixEnd_124899 := by exact prefixLift 124899
  have htrace : WordTrace (prefixWord ++ tailWord_124899) baseStart_124899 baseEnd_124899 := by
    simpa [prefixWord, tailWord_124899, baseEnd_124899] using wordTrace_append hprefix tailTrace_124899
  have hstable : (prefixWord ++ tailWord_124899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124899).length < 2 ^ (prefixWord ++ tailWord_124899).sum := by decide
  have hdescent : baseEnd_124899 < baseStart_124899 := by decide
  rcases family_descends (prefixWord ++ tailWord_124899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125006 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_125006 : Nat := 118140960795 + 125006 * 2 ^ 59
def prefixEnd_125006 : Nat := 4983230072969 + 3 ^ 40 * 125006 * 2
def baseEnd_125006 : Nat := 28528072309352509844495

theorem tailTrace_125006 : CollatzResearch.WordTrace tailWord_125006 prefixEnd_125006 28528072309352509844495 := by
  unfold tailWord_125006
  simp only [CollatzResearch.WordTrace]
  refine ⟨569917923141510771275359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3039562256754724113468581 569917923141510771275359)
  ·
    refine ⟨854876884712266156913039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 569917923141510771275359 854876884712266156913039)
    ·
      refine ⟨1282315327068399235369559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854876884712266156913039 1282315327068399235369559)
      ·
        refine ⟨1923472990602598853054339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282315327068399235369559 1923472990602598853054339)
        ·
          refine ⟨2885209485903898279581509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923472990602598853054339 2885209485903898279581509)
          ·
            refine ⟨540976778606980927421533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2885209485903898279581509 540976778606980927421533)
            ·
              refine ⟨202866291977617847783075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 540976778606980927421533 202866291977617847783075)
              ·
                refine ⟨304299437966426771674613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202866291977617847783075 304299437966426771674613)
                ·
                  refine ⟨28528072309352509844495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304299437966426771674613 28528072309352509844495)
                  ·
                    rfl

theorem cell21_125006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_125006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125006 prefixEnd_125006 := by exact prefixLift 125006
  have htrace : WordTrace (prefixWord ++ tailWord_125006) baseStart_125006 baseEnd_125006 := by
    simpa [prefixWord, tailWord_125006, baseEnd_125006] using wordTrace_append hprefix tailTrace_125006
  have hstable : (prefixWord ++ tailWord_125006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125006).length < 2 ^ (prefixWord ++ tailWord_125006).sum := by decide
  have hdescent : baseEnd_125006 < baseStart_125006 := by decide
  rcases family_descends (prefixWord ++ tailWord_125006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125057 : List Nat := [1, 2, 4, 2, 3, 2, 2, 2, 3]
def baseStart_125057 : Nat := 118140960795 + 125057 * 2 ^ 59
def prefixEnd_125057 : Nat := 4983230072969 + 3 ^ 40 * 125057 * 2
def baseEnd_125057 : Nat := 28539711204187754494391

theorem tailTrace_125057 : CollatzResearch.WordTrace tailWord_125057 prefixEnd_125057 28539711204187754494391 := by
  unfold tailWord_125057
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561203507947321880309425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3040802338631547920206283 4561203507947321880309425)
  ·
    refine ⟨3420902630960491410232069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4561203507947321880309425 3420902630960491410232069)
    ·
      refine ⟨641419243305092139418513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3420902630960491410232069 641419243305092139418513)
      ·
        refine ⟨481064432478819104563885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641419243305092139418513 481064432478819104563885)
        ·
          refine ⟨180399162179557164211457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481064432478819104563885 180399162179557164211457)
          ·
            refine ⟨135299371634667873158593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180399162179557164211457 135299371634667873158593)
            ·
              refine ⟨101474528726000904868945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135299371634667873158593 101474528726000904868945)
              ·
                refine ⟨76105896544500678651709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101474528726000904868945 76105896544500678651709)
                ·
                  refine ⟨28539711204187754494391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76105896544500678651709 28539711204187754494391)
                  ·
                    rfl

theorem cell21_125057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_125057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125057 prefixEnd_125057 := by exact prefixLift 125057
  have htrace : WordTrace (prefixWord ++ tailWord_125057) baseStart_125057 baseEnd_125057 := by
    simpa [prefixWord, tailWord_125057, baseEnd_125057] using wordTrace_append hprefix tailTrace_125057
  have hstable : (prefixWord ++ tailWord_125057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125057).length < 2 ^ (prefixWord ++ tailWord_125057).sum := by decide
  have hdescent : baseEnd_125057 < baseStart_125057 := by decide
  rcases family_descends (prefixWord ++ tailWord_125057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125065 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 5]
def baseStart_125065 : Nat := 118140960795 + 125065 * 2 ^ 59
def prefixEnd_125065 : Nat := 4983230072969 + 3 ^ 40 * 125065 * 2
def baseEnd_125065 : Nat := 28541536913181518361041

theorem tailTrace_125065 : CollatzResearch.WordTrace tailWord_125065 prefixEnd_125065 28541536913181518361041 := by
  unfold tailWord_125065
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561495291918339246600649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3040996861278892831067099 4561495291918339246600649)
  ·
    refine ⟨3421121468938754434950487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4561495291918339246600649 3421121468938754434950487)
    ·
      refine ⟨5131682203408131652425731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421121468938754434950487 5131682203408131652425731)
      ·
        refine ⟨7697523305112197478638597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131682203408131652425731 7697523305112197478638597)
        ·
          refine ⟨1443285619708537027244737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7697523305112197478638597 1443285619708537027244737)
          ·
            refine ⟨1082464214781402770433553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443285619708537027244737 1082464214781402770433553)
            ·
              refine ⟨811848161086052077825165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082464214781402770433553 811848161086052077825165)
              ·
                refine ⟨304443060407269529184437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 811848161086052077825165 304443060407269529184437)
                ·
                  refine ⟨28541536913181518361041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304443060407269529184437 28541536913181518361041)
                  ·
                    rfl

theorem cell21_125065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_125065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125065 prefixEnd_125065 := by exact prefixLift 125065
  have htrace : WordTrace (prefixWord ++ tailWord_125065) baseStart_125065 baseEnd_125065 := by
    simpa [prefixWord, tailWord_125065, baseEnd_125065] using wordTrace_append hprefix tailTrace_125065
  have hstable : (prefixWord ++ tailWord_125065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125065).length < 2 ^ (prefixWord ++ tailWord_125065).sum := by decide
  have hdescent : baseEnd_125065 < baseStart_125065 := by decide
  rcases family_descends (prefixWord ++ tailWord_125065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125144 : List Nat := [2, 1, 2, 2, 4, 3, 2, 5]
def baseStart_125144 : Nat := 118140960795 + 125144 * 2 ^ 59
def prefixEnd_125144 : Nat := 4983230072969 + 3 ^ 40 * 125144 * 2
def baseEnd_125144 : Nat := 9519855263164978848071

theorem tailTrace_125144 : CollatzResearch.WordTrace tailWord_125144 prefixEnd_125144 9519855263164978848071 := by
  unfold tailWord_125144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282188329316067869363243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3042917772421423825817657 2282188329316067869363243)
  ·
    refine ⟨3423282493974101804044865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2282188329316067869363243 3423282493974101804044865)
    ·
      refine ⟨2567461870480576353033649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3423282493974101804044865 2567461870480576353033649)
      ·
        refine ⟨1925596402860432264775237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2567461870480576353033649 1925596402860432264775237)
        ·
          refine ⟨361049325536331049645357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1925596402860432264775237 361049325536331049645357)
          ·
            refine ⟨135393497076124143617009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361049325536331049645357 135393497076124143617009)
            ·
              refine ⟨101545122807093107712757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135393497076124143617009 101545122807093107712757)
              ·
                refine ⟨9519855263164978848071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101545122807093107712757 9519855263164978848071)
                ·
                  rfl

theorem cell21_125144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_125144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125144 prefixEnd_125144 := by exact prefixLift 125144
  have htrace : WordTrace (prefixWord ++ tailWord_125144) baseStart_125144 baseEnd_125144 := by
    simpa [prefixWord, tailWord_125144, baseEnd_125144] using wordTrace_append hprefix tailTrace_125144
  have hstable : (prefixWord ++ tailWord_125144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125144).length < 2 ^ (prefixWord ++ tailWord_125144).sum := by decide
  have hdescent : baseEnd_125144 < baseStart_125144 := by decide
  rcases family_descends (prefixWord ++ tailWord_125144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125226 : List Nat := [3, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_125226 : Nat := 118140960795 + 125226 * 2 ^ 59
def prefixEnd_125226 : Nat := 4983230072969 + 3 ^ 40 * 125226 * 2
def baseEnd_125226 : Nat := 28578279306681016177379

theorem tailTrace_125226 : CollatzResearch.WordTrace tailWord_125226 prefixEnd_125226 28578279306681016177379 := by
  unfold tailWord_125226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141841861083765935802883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3044911629556709162141021 1141841861083765935802883)
  ·
    refine ⟨1712762791625648903704325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1141841861083765935802883 1712762791625648903704325)
    ·
      refine ⟨321143023429809169444561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1712762791625648903704325 321143023429809169444561)
      ·
        refine ⟨240857267572356877083421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321143023429809169444561 240857267572356877083421)
        ·
          refine ⟨90321475339633828906283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240857267572356877083421 90321475339633828906283)
          ·
            refine ⟨135482213009450743359425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90321475339633828906283 135482213009450743359425)
            ·
              refine ⟨101611659757088057519569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135482213009450743359425 101611659757088057519569)
              ·
                refine ⟨76208744817816043139677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101611659757088057519569 76208744817816043139677)
                ·
                  refine ⟨28578279306681016177379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76208744817816043139677 28578279306681016177379)
                  ·
                    rfl

theorem cell21_125226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_125226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125226 prefixEnd_125226 := by exact prefixLift 125226
  have htrace : WordTrace (prefixWord ++ tailWord_125226) baseStart_125226 baseEnd_125226 := by
    simpa [prefixWord, tailWord_125226, baseEnd_125226] using wordTrace_append hprefix tailTrace_125226
  have hstable : (prefixWord ++ tailWord_125226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125226).length < 2 ^ (prefixWord ++ tailWord_125226).sum := by decide
  have hdescent : baseEnd_125226 < baseStart_125226 := by decide
  rcases family_descends (prefixWord ++ tailWord_125226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125231 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 6]
def baseStart_125231 : Nat := 118140960795 + 125231 * 2 ^ 59
def prefixEnd_125231 : Nat := 4983230072969 + 3 ^ 40 * 125231 * 2
def baseEnd_125231 : Nat := 28579420374802118594035

theorem tailTrace_125231 : CollatzResearch.WordTrace tailWord_125231 prefixEnd_125231 28579420374802118594035 := by
  unfold tailWord_125231
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567549809316949597143547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3045033206211299731429031 4567549809316949597143547)
  ·
    refine ⟨6851324713975424395715321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4567549809316949597143547 6851324713975424395715321)
    ·
      refine ⟨5138493535481568296786491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6851324713975424395715321 5138493535481568296786491)
      ·
        refine ⟨7707740303222352445179737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138493535481568296786491 7707740303222352445179737)
        ·
          refine ⟨5780805227416764333884803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7707740303222352445179737 5780805227416764333884803)
          ·
            refine ⟨8671207841125146500827205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780805227416764333884803 8671207841125146500827205)
            ·
              refine ⟨1625851470210964968905101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8671207841125146500827205 1625851470210964968905101)
              ·
                refine ⟨609694301329111863339413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1625851470210964968905101 609694301329111863339413)
                ·
                  refine ⟨28579420374802118594035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 609694301329111863339413 28579420374802118594035)
                  ·
                    rfl

theorem cell21_125231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_125231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125231 prefixEnd_125231 := by exact prefixLift 125231
  have htrace : WordTrace (prefixWord ++ tailWord_125231) baseStart_125231 baseEnd_125231 := by
    simpa [prefixWord, tailWord_125231, baseEnd_125231] using wordTrace_append hprefix tailTrace_125231
  have hstable : (prefixWord ++ tailWord_125231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125231).length < 2 ^ (prefixWord ++ tailWord_125231).sum := by decide
  have hdescent : baseEnd_125231 < baseStart_125231 := by decide
  rcases family_descends (prefixWord ++ tailWord_125231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125282 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_125282 : Nat := 118140960795 + 125282 * 2 ^ 59
def prefixEnd_125282 : Nat := 4983230072969 + 3 ^ 40 * 125282 * 2
def baseEnd_125282 : Nat := 28591059269637363243931

theorem tailTrace_125282 : CollatzResearch.WordTrace tailWord_125282 prefixEnd_125282 28591059269637363243931 := by
  unfold tailWord_125282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142352483033046326812525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3046273288088123538166733 1142352483033046326812525)
  ·
    refine ⟨428382181137392372554697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1142352483033046326812525 428382181137392372554697)
    ·
      refine ⟨321286635853044279416023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428382181137392372554697 321286635853044279416023)
      ·
        refine ⟨481929953779566419124035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321286635853044279416023 481929953779566419124035)
        ·
          refine ⟨722894930669349628686053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481929953779566419124035 722894930669349628686053)
          ·
            refine ⟨135542799500503055378635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 722894930669349628686053 135542799500503055378635)
            ·
              refine ⟨203314199250754583067953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135542799500503055378635 203314199250754583067953)
              ·
                refine ⟨152485649438065937300965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203314199250754583067953 152485649438065937300965)
                ·
                  refine ⟨28591059269637363243931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152485649438065937300965 28591059269637363243931)
                  ·
                    rfl

theorem cell21_125282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_125282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125282 prefixEnd_125282 := by exact prefixLift 125282
  have htrace : WordTrace (prefixWord ++ tailWord_125282) baseStart_125282 baseEnd_125282 := by
    simpa [prefixWord, tailWord_125282, baseEnd_125282] using wordTrace_append hprefix tailTrace_125282
  have hstable : (prefixWord ++ tailWord_125282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125282).length < 2 ^ (prefixWord ++ tailWord_125282).sum := by decide
  have hdescent : baseEnd_125282 < baseStart_125282 := by decide
  rcases family_descends (prefixWord ++ tailWord_125282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125338 : List Nat := [3, 1, 1, 4, 1, 2, 9]
def baseStart_125338 : Nat := 118140960795 + 125338 * 2 ^ 59
def prefixEnd_125338 : Nat := 4983230072969 + 3 ^ 40 * 125338 * 2
def baseEnd_125338 : Nat := 3178204359177078923387

theorem tailTrace_125338 : CollatzResearch.WordTrace tailWord_125338 prefixEnd_125338 3178204359177078923387 := by
  unfold tailWord_125338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142863104982326717822167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3047634946619537914192445 1142863104982326717822167)
  ·
    refine ⟨1714294657473490076733251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142863104982326717822167 1714294657473490076733251)
    ·
      refine ⟨2571441986210235115099877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714294657473490076733251 2571441986210235115099877)
      ·
        refine ⟨482145372414419084081227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2571441986210235115099877 482145372414419084081227)
        ·
          refine ⟨723218058621628626121841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482145372414419084081227 723218058621628626121841)
          ·
            refine ⟨542413543966221469591381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723218058621628626121841 542413543966221469591381)
            ·
              refine ⟨3178204359177078923387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 542413543966221469591381 3178204359177078923387)
              ·
                rfl

theorem cell21_125338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 9].length) (baseStart_125338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125338 prefixEnd_125338 := by exact prefixLift 125338
  have htrace : WordTrace (prefixWord ++ tailWord_125338) baseStart_125338 baseEnd_125338 := by
    simpa [prefixWord, tailWord_125338, baseEnd_125338] using wordTrace_append hprefix tailTrace_125338
  have hstable : (prefixWord ++ tailWord_125338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125338).length < 2 ^ (prefixWord ++ tailWord_125338).sum := by decide
  have hdescent : baseEnd_125338 < baseStart_125338 := by decide
  rcases family_descends (prefixWord ++ tailWord_125338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125386 : List Nat := [3, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_125386 : Nat := 118140960795 + 125386 * 2 ^ 59
def prefixEnd_125386 : Nat := 4983230072969 + 3 ^ 40 * 125386 * 2
def baseEnd_125386 : Nat := 28614793486556293510385

theorem tailTrace_125386 : CollatzResearch.WordTrace tailWord_125386 prefixEnd_125386 28614793486556293510385 := by
  unfold tailWord_125386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1143300780938852767259003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3048802082503607379357341 1143300780938852767259003)
  ·
    refine ⟨1714951171408279150888505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1143300780938852767259003 1714951171408279150888505)
    ·
      refine ⟨1286213378556209363166379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1714951171408279150888505 1286213378556209363166379)
      ·
        refine ⟨1929320067834314044749569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1286213378556209363166379 1929320067834314044749569)
        ·
          refine ⟨1446990050875735533562177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1929320067834314044749569 1446990050875735533562177)
          ·
            refine ⟨1085242538156801650171633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446990050875735533562177 1085242538156801650171633)
            ·
              refine ⟨813931903617601237628725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085242538156801650171633 813931903617601237628725)
              ·
                refine ⟨76306115964150116027693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 813931903617601237628725 76306115964150116027693)
                ·
                  refine ⟨28614793486556293510385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76306115964150116027693 28614793486556293510385)
                  ·
                    rfl

theorem cell21_125386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_125386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125386 prefixEnd_125386 := by exact prefixLift 125386
  have htrace : WordTrace (prefixWord ++ tailWord_125386) baseStart_125386 baseEnd_125386 := by
    simpa [prefixWord, tailWord_125386, baseEnd_125386] using wordTrace_append hprefix tailTrace_125386
  have hstable : (prefixWord ++ tailWord_125386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125386).length < 2 ^ (prefixWord ++ tailWord_125386).sum := by decide
  have hdescent : baseEnd_125386 < baseStart_125386 := by decide
  rcases family_descends (prefixWord ++ tailWord_125386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125459 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 6]
def baseStart_125459 : Nat := 118140960795 + 125459 * 2 ^ 59
def prefixEnd_125459 : Nat := 4983230072969 + 3 ^ 40 * 125459 * 2
def baseEnd_125459 : Nat := 28631453081124388793569

theorem tailTrace_125459 : CollatzResearch.WordTrace tailWord_125459 prefixEnd_125459 28631453081124388793569 := by
  unfold tailWord_125459
  simp only [CollatzResearch.WordTrace]
  refine ⟨4575865652490944536443431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3050577101660629690962287 4575865652490944536443431)
  ·
    refine ⟨6863798478736416804665147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4575865652490944536443431 6863798478736416804665147)
    ·
      refine ⟨10295697718104625206997721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6863798478736416804665147 10295697718104625206997721)
      ·
        refine ⟨7721773288578468905248291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10295697718104625206997721 7721773288578468905248291)
        ·
          refine ⟨11582659932867703357872437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7721773288578468905248291 11582659932867703357872437)
          ·
            refine ⟨1085874368706347189800541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11582659932867703357872437 1085874368706347189800541)
            ·
              refine ⟨407202888264880196175203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1085874368706347189800541 407202888264880196175203)
              ·
                refine ⟨610804332397320294262805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407202888264880196175203 610804332397320294262805)
                ·
                  refine ⟨28631453081124388793569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 610804332397320294262805 28631453081124388793569)
                  ·
                    rfl

theorem cell21_125459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_125459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125459 prefixEnd_125459 := by exact prefixLift 125459
  have htrace : WordTrace (prefixWord ++ tailWord_125459) baseStart_125459 baseEnd_125459 := by
    simpa [prefixWord, tailWord_125459, baseEnd_125459] using wordTrace_append hprefix tailTrace_125459
  have hstable : (prefixWord ++ tailWord_125459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125459).length < 2 ^ (prefixWord ++ tailWord_125459).sum := by decide
  have hdescent : baseEnd_125459 < baseStart_125459 := by decide
  rcases family_descends (prefixWord ++ tailWord_125459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125504 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_125504 : Nat := 118140960795 + 125504 * 2 ^ 59
def prefixEnd_125504 : Nat := 4983230072969 + 3 ^ 40 * 125504 * 2
def baseEnd_125504 : Nat := 28641722694214310543477

theorem tailTrace_125504 : CollatzResearch.WordTrace tailWord_125504 prefixEnd_125504 28641722694214310543477 := by
  unfold tailWord_125504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288753468663958610915783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3051671291551944814554377 2288753468663958610915783)
  ·
    refine ⟨3433130202995937916373675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288753468663958610915783 3433130202995937916373675)
    ·
      refine ⟨5149695304493906874560513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3433130202995937916373675 5149695304493906874560513)
      ·
        refine ⟨3862271478370430155920385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5149695304493906874560513 3862271478370430155920385)
        ·
          refine ⟨2896703608777822616940289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3862271478370430155920385 2896703608777822616940289)
          ·
            refine ⟨2172527706583366962705217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2896703608777822616940289 2172527706583366962705217)
            ·
              refine ⟨1629395779937525222028913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172527706583366962705217 1629395779937525222028913)
              ·
                refine ⟨1222046834953143916521685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629395779937525222028913 1222046834953143916521685)
                ·
                  refine ⟨28641722694214310543477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1222046834953143916521685 28641722694214310543477)
                  ·
                    rfl

theorem cell21_125504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_125504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125504 prefixEnd_125504 := by exact prefixLift 125504
  have htrace : WordTrace (prefixWord ++ tailWord_125504) baseStart_125504 baseEnd_125504 := by
    simpa [prefixWord, tailWord_125504, baseEnd_125504] using wordTrace_append hprefix tailTrace_125504
  have hstable : (prefixWord ++ tailWord_125504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125504).length < 2 ^ (prefixWord ++ tailWord_125504).sum := by decide
  have hdescent : baseEnd_125504 < baseStart_125504 := by decide
  rcases family_descends (prefixWord ++ tailWord_125504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125521 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 5]
def baseStart_125521 : Nat := 118140960795 + 125521 * 2 ^ 59
def prefixEnd_125521 : Nat := 4983230072969 + 3 ^ 40 * 125521 * 2
def baseEnd_125521 : Nat := 28645602325826058760109

theorem tailTrace_125521 : CollatzResearch.WordTrace tailWord_125521 prefixEnd_125521 28645602325826058760109 := by
  unfold tailWord_125521
  simp only [CollatzResearch.WordTrace]
  refine ⟨4578126978266329125200417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3052084652177552750133611 4578126978266329125200417)
  ·
    refine ⟨3433595233699746843900313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4578126978266329125200417 3433595233699746843900313)
    ·
      refine ⟨2575196425274810132925235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3433595233699746843900313 2575196425274810132925235)
      ·
        refine ⟨3862794637912215199387853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575196425274810132925235 3862794637912215199387853)
        ·
          refine ⟨1448547989217080699770445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3862794637912215199387853 1448547989217080699770445)
          ·
            refine ⟨543205495956405262413917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1448547989217080699770445 543205495956405262413917)
            ·
              refine ⟨203702060983651973405219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543205495956405262413917 203702060983651973405219)
              ·
                refine ⟨305553091475477960107829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203702060983651973405219 305553091475477960107829)
                ·
                  refine ⟨28645602325826058760109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 305553091475477960107829 28645602325826058760109)
                  ·
                    rfl

theorem cell21_125521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_125521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125521 prefixEnd_125521 := by exact prefixLift 125521
  have htrace : WordTrace (prefixWord ++ tailWord_125521) baseStart_125521 baseEnd_125521 := by
    simpa [prefixWord, tailWord_125521, baseEnd_125521] using wordTrace_append hprefix tailTrace_125521
  have hstable : (prefixWord ++ tailWord_125521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125521).length < 2 ^ (prefixWord ++ tailWord_125521).sum := by decide
  have hdescent : baseEnd_125521 < baseStart_125521 := by decide
  rcases family_descends (prefixWord ++ tailWord_125521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125572 : List Nat := [2, 3, 2, 1, 3, 3, 2, 2, 3]
def baseStart_125572 : Nat := 118140960795 + 125572 * 2 ^ 59
def prefixEnd_125572 : Nat := 4983230072969 + 3 ^ 40 * 125572 * 2
def baseEnd_125572 : Nat := 28657241220661303410005

theorem tailTrace_125572 : CollatzResearch.WordTrace tailWord_125572 prefixEnd_125572 28657241220661303410005 := by
  unfold tailWord_125572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289993550540782417653485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3053324734054376556871313 2289993550540782417653485)
  ·
    refine ⟨858747581452793406620057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2289993550540782417653485 858747581452793406620057)
    ·
      refine ⟨644060686089595054965043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 858747581452793406620057 644060686089595054965043)
      ·
        refine ⟨966091029134392582447565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644060686089595054965043 966091029134392582447565)
        ·
          refine ⟨362284135925397218417837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 966091029134392582447565 362284135925397218417837)
          ·
            refine ⟨135856550972023956906689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362284135925397218417837 135856550972023956906689)
            ·
              refine ⟨101892413229017967680017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135856550972023956906689 101892413229017967680017)
              ·
                refine ⟨76419309921763475760013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101892413229017967680017 76419309921763475760013)
                ·
                  refine ⟨28657241220661303410005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76419309921763475760013 28657241220661303410005)
                  ·
                    rfl

theorem cell21_125572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_125572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125572 prefixEnd_125572 := by exact prefixLift 125572
  have htrace : WordTrace (prefixWord ++ tailWord_125572) baseStart_125572 baseEnd_125572 := by
    simpa [prefixWord, tailWord_125572, baseEnd_125572] using wordTrace_append hprefix tailTrace_125572
  have hstable : (prefixWord ++ tailWord_125572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125572).length < 2 ^ (prefixWord ++ tailWord_125572).sum := by decide
  have hdescent : baseEnd_125572 < baseStart_125572 := by decide
  rcases family_descends (prefixWord ++ tailWord_125572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125687 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 4]
def baseStart_125687 : Nat := 118140960795 + 125687 * 2 ^ 59
def prefixEnd_125687 : Nat := 4983230072969 + 3 ^ 40 * 125687 * 2
def baseEnd_125687 : Nat := 28683485787446658993103

theorem tailTrace_125687 : CollatzResearch.WordTrace tailWord_125687 prefixEnd_125687 28683485787446658993103 := by
  unfold tailWord_125687
  simp only [CollatzResearch.WordTrace]
  refine ⟨4584181495664939475743315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3056120997109959650495543 4584181495664939475743315)
  ·
    refine ⟨6876272243497409213614973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4584181495664939475743315 6876272243497409213614973)
    ·
      refine ⟨2578602091311528455105615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6876272243497409213614973 2578602091311528455105615)
      ·
        refine ⟨3867903136967292682658423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2578602091311528455105615 3867903136967292682658423)
        ·
          refine ⟨5801854705450939023987635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867903136967292682658423 5801854705450939023987635)
          ·
            refine ⟨8702782058176408535981453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5801854705450939023987635 8702782058176408535981453)
            ·
              refine ⟨3263543271816153200993045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8702782058176408535981453 3263543271816153200993045)
              ·
                refine ⟨152978590866382181296549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3263543271816153200993045 152978590866382181296549)
                ·
                  refine ⟨28683485787446658993103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152978590866382181296549 28683485787446658993103)
                  ·
                    rfl

theorem cell21_125687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 4].length) (baseStart_125687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125687 prefixEnd_125687 := by exact prefixLift 125687
  have htrace : WordTrace (prefixWord ++ tailWord_125687) baseStart_125687 baseEnd_125687 := by
    simpa [prefixWord, tailWord_125687, baseEnd_125687] using wordTrace_append hprefix tailTrace_125687
  have hstable : (prefixWord ++ tailWord_125687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125687).length < 2 ^ (prefixWord ++ tailWord_125687).sum := by decide
  have hdescent : baseEnd_125687 < baseStart_125687 := by decide
  rcases family_descends (prefixWord ++ tailWord_125687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125704 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_125704 : Nat := 118140960795 + 125704 * 2 ^ 59
def prefixEnd_125704 : Nat := 4983230072969 + 3 ^ 40 * 125704 * 2
def baseEnd_125704 : Nat := 28687365419058407209735

theorem tailTrace_125704 : CollatzResearch.WordTrace tailWord_125704 prefixEnd_125704 28687365419058407209735 := by
  unfold tailWord_125704
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292400768301675689556083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3056534357735567586074777 2292400768301675689556083)
  ·
    refine ⟨3438601152452513534334125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2292400768301675689556083 3438601152452513534334125)
    ·
      refine ⟨1289475432169692575375297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3438601152452513534334125 1289475432169692575375297)
      ·
        refine ⟨967106574127269431531473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1289475432169692575375297 967106574127269431531473)
        ·
          refine ⟨725329930595452073648605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967106574127269431531473 725329930595452073648605)
          ·
            refine ⟨271998723973294527618227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 725329930595452073648605 271998723973294527618227)
            ·
              refine ⟨407998085959941791427341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271998723973294527618227 407998085959941791427341)
              ·
                refine ⟨152999282234978171785253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407998085959941791427341 152999282234978171785253)
                ·
                  refine ⟨28687365419058407209735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152999282234978171785253 28687365419058407209735)
                  ·
                    rfl

theorem cell21_125704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_125704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125704 prefixEnd_125704 := by exact prefixLift 125704
  have htrace : WordTrace (prefixWord ++ tailWord_125704) baseStart_125704 baseEnd_125704 := by
    simpa [prefixWord, tailWord_125704, baseEnd_125704] using wordTrace_append hprefix tailTrace_125704
  have hstable : (prefixWord ++ tailWord_125704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125704).length < 2 ^ (prefixWord ++ tailWord_125704).sum := by decide
  have hdescent : baseEnd_125704 < baseStart_125704 := by decide
  rcases family_descends (prefixWord ++ tailWord_125704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125738 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_125738 : Nat := 118140960795 + 125738 * 2 ^ 59
def prefixEnd_125738 : Nat := 4983230072969 + 3 ^ 40 * 125738 * 2
def baseEnd_125738 : Nat := 28695124682281903642999

theorem tailTrace_125738 : CollatzResearch.WordTrace tailWord_125738 prefixEnd_125738 28695124682281903642999 := by
  unfold tailWord_125738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146510404620043796462467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3057361078986783457233245 1146510404620043796462467)
  ·
    refine ⟨1719765606930065694693701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146510404620043796462467 1719765606930065694693701)
    ·
      refine ⟨322456051299387317755069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1719765606930065694693701 322456051299387317755069)
      ·
        refine ⟨120921019237270244158151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322456051299387317755069 120921019237270244158151)
        ·
          refine ⟨181381528855905366237227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120921019237270244158151 181381528855905366237227)
          ·
            refine ⟨272072293283858049355841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181381528855905366237227 272072293283858049355841)
            ·
              refine ⟨204054219962893537016881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272072293283858049355841 204054219962893537016881)
              ·
                refine ⟨153040664972170152762661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204054219962893537016881 153040664972170152762661)
                ·
                  refine ⟨28695124682281903642999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153040664972170152762661 28695124682281903642999)
                  ·
                    rfl

theorem cell21_125738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_125738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125738 prefixEnd_125738 := by exact prefixLift 125738
  have htrace : WordTrace (prefixWord ++ tailWord_125738) baseStart_125738 baseEnd_125738 := by
    simpa [prefixWord, tailWord_125738, baseEnd_125738] using wordTrace_append hprefix tailTrace_125738
  have hstable : (prefixWord ++ tailWord_125738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125738).length < 2 ^ (prefixWord ++ tailWord_125738).sum := by decide
  have hdescent : baseEnd_125738 < baseStart_125738 := by decide
  rcases family_descends (prefixWord ++ tailWord_125738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125763 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 4]
def baseStart_125763 : Nat := 118140960795 + 125763 * 2 ^ 59
def prefixEnd_125763 : Nat := 4983230072969 + 3 ^ 40 * 125763 * 2
def baseEnd_125763 : Nat := 28700830022887415726281

theorem tailTrace_125763 : CollatzResearch.WordTrace tailWord_125763 prefixEnd_125763 28700830022887415726281 := by
  unfold tailWord_125763
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586953443389604455509943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3057968962259736303673295 4586953443389604455509943)
  ·
    refine ⟨6880430165084406683264915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4586953443389604455509943 6880430165084406683264915)
    ·
      refine ⟨10320645247626610024897373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6880430165084406683264915 10320645247626610024897373)
      ·
        refine ⟨3870241967859978759336515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10320645247626610024897373 3870241967859978759336515)
        ·
          refine ⟨5805362951789968139004773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870241967859978759336515 5805362951789968139004773)
          ·
            refine ⟨1088505553460619026063395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5805362951789968139004773 1088505553460619026063395)
            ·
              refine ⟨1632758330190928539095093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088505553460619026063395 1632758330190928539095093)
              ·
                refine ⟨153071093455399550540165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1632758330190928539095093 153071093455399550540165)
                ·
                  refine ⟨28700830022887415726281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153071093455399550540165 28700830022887415726281)
                  ·
                    rfl

theorem cell21_125763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 4].length) (baseStart_125763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125763 prefixEnd_125763 := by exact prefixLift 125763
  have htrace : WordTrace (prefixWord ++ tailWord_125763) baseStart_125763 baseEnd_125763 := by
    simpa [prefixWord, tailWord_125763, baseEnd_125763] using wordTrace_append hprefix tailTrace_125763
  have hstable : (prefixWord ++ tailWord_125763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125763).length < 2 ^ (prefixWord ++ tailWord_125763).sum := by decide
  have hdescent : baseEnd_125763 < baseStart_125763 := by decide
  rcases family_descends (prefixWord ++ tailWord_125763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125808 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_125808 : Nat := 118140960795 + 125808 * 2 ^ 59
def prefixEnd_125808 : Nat := 4983230072969 + 3 ^ 40 * 125808 * 2
def baseEnd_125808 : Nat := 28711099635977337476189

theorem tailTrace_125808 : CollatzResearch.WordTrace tailWord_125808 prefixEnd_125808 28711099635977337476189 := by
  unfold tailWord_125808
  simp only [CollatzResearch.WordTrace]
  refine ⟨2294297364113288570449039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3059063152151051427265385 2294297364113288570449039)
  ·
    refine ⟨3441446046169932855673559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2294297364113288570449039 3441446046169932855673559)
    ·
      refine ⟨5162169069254899283510339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3441446046169932855673559 5162169069254899283510339)
      ·
        refine ⟨7743253603882348925265509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5162169069254899283510339 7743253603882348925265509)
        ·
          refine ⟨1451860050727940423487283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7743253603882348925265509 1451860050727940423487283)
          ·
            refine ⟨2177790076091910635230925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451860050727940423487283 2177790076091910635230925)
            ·
              refine ⟨816671278534466488211597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2177790076091910635230925 816671278534466488211597)
              ·
                refine ⟨306251729450424933079349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 816671278534466488211597 306251729450424933079349)
                ·
                  refine ⟨28711099635977337476189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306251729450424933079349 28711099635977337476189)
                  ·
                    rfl

theorem cell21_125808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_125808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125808 prefixEnd_125808 := by exact prefixLift 125808
  have htrace : WordTrace (prefixWord ++ tailWord_125808) baseStart_125808 baseEnd_125808 := by
    simpa [prefixWord, tailWord_125808, baseEnd_125808] using wordTrace_append hprefix tailTrace_125808
  have hstable : (prefixWord ++ tailWord_125808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125808).length < 2 ^ (prefixWord ++ tailWord_125808).sum := by decide
  have hdescent : baseEnd_125808 < baseStart_125808 := by decide
  rcases family_descends (prefixWord ++ tailWord_125808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125814 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_125814 : Nat := 118140960795 + 125814 * 2 ^ 59
def prefixEnd_125814 : Nat := 4983230072969 + 3 ^ 40 * 125814 * 2
def baseEnd_125814 : Nat := 28712468917722660376177

theorem tailTrace_125814 : CollatzResearch.WordTrace tailWord_125814 prefixEnd_125814 28712468917722660376177 := by
  unfold tailWord_125814
  simp only [CollatzResearch.WordTrace]
  refine ⟨286800847887802510351031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3059209044136560110410997 286800847887802510351031)
  ·
    refine ⟨430201271831703765526547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286800847887802510351031 430201271831703765526547)
    ·
      refine ⟨645301907747555648289821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430201271831703765526547 645301907747555648289821)
      ·
        refine ⟨241988215405333368108683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 645301907747555648289821 241988215405333368108683)
        ·
          refine ⟨362982323108000052163025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241988215405333368108683 362982323108000052163025)
          ·
            refine ⟨272236742331000039122269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362982323108000052163025 272236742331000039122269)
            ·
              refine ⟨102088778374125014670851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272236742331000039122269 102088778374125014670851)
              ·
                refine ⟨153133167561187522006277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102088778374125014670851 153133167561187522006277)
                ·
                  refine ⟨28712468917722660376177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153133167561187522006277 28712468917722660376177)
                  ·
                    rfl

theorem cell21_125814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_125814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125814 prefixEnd_125814 := by exact prefixLift 125814
  have htrace : WordTrace (prefixWord ++ tailWord_125814) baseStart_125814 baseEnd_125814 := by
    simpa [prefixWord, tailWord_125814, baseEnd_125814] using wordTrace_append hprefix tailTrace_125814
  have hstable : (prefixWord ++ tailWord_125814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125814).length < 2 ^ (prefixWord ++ tailWord_125814).sum := by decide
  have hdescent : baseEnd_125814 < baseStart_125814 := by decide
  rcases family_descends (prefixWord ++ tailWord_125814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125977 : List Nat := [1, 2, 1, 2, 1, 1, 6, 4, 3]
def baseStart_125977 : Nat := 118140960795 + 125977 * 2 ^ 59
def prefixEnd_125977 : Nat := 4983230072969 + 3 ^ 40 * 125977 * 2
def baseEnd_125977 : Nat := 28749667738470599159177

theorem tailTrace_125977 : CollatzResearch.WordTrace tailWord_125977 prefixEnd_125977 28749667738470599159177 := by
  unfold tailWord_125977
  simp only [CollatzResearch.WordTrace]
  refine ⟨4594758664614319003800185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3063172443076212669200123 4594758664614319003800185)
  ·
    refine ⟨3446068998460739252850139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4594758664614319003800185 3446068998460739252850139)
    ·
      refine ⟨5169103497691108879275209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446068998460739252850139 5169103497691108879275209)
      ·
        refine ⟨3876827623268331659456407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5169103497691108879275209 3876827623268331659456407)
        ·
          refine ⟨5815241434902497489184611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876827623268331659456407 5815241434902497489184611)
          ·
            refine ⟨8722862152353746233776917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5815241434902497489184611 8722862152353746233776917)
            ·
              refine ⟨408884163391581854708293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8722862152353746233776917 408884163391581854708293)
              ·
                refine ⟨76665780635921597757805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408884163391581854708293 76665780635921597757805)
                ·
                  refine ⟨28749667738470599159177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76665780635921597757805 28749667738470599159177)
                  ·
                    rfl

theorem cell21_125977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_125977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_125977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_125977 prefixEnd_125977 := by exact prefixLift 125977
  have htrace : WordTrace (prefixWord ++ tailWord_125977) baseStart_125977 baseEnd_125977 := by
    simpa [prefixWord, tailWord_125977, baseEnd_125977] using wordTrace_append hprefix tailTrace_125977
  have hstable : (prefixWord ++ tailWord_125977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125977).length < 2 ^ (prefixWord ++ tailWord_125977).sum := by decide
  have hdescent : baseEnd_125977 < baseStart_125977 := by decide
  rcases family_descends (prefixWord ++ tailWord_125977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126070 : List Nat := [5, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_126070 : Nat := 118140960795 + 126070 * 2 ^ 59
def prefixEnd_126070 : Nat := 4983230072969 + 3 ^ 40 * 126070 * 2
def baseEnd_126070 : Nat := 28770891605523104108987

theorem tailTrace_126070 : CollatzResearch.WordTrace tailWord_126070 prefixEnd_126070 28770891605523104108987 := by
  unfold tailWord_126070
  simp only [CollatzResearch.WordTrace]
  refine ⟨287384415829837242933479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3065433768851597257957109 287384415829837242933479)
  ·
    refine ⟨431076623744755864400219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287384415829837242933479 431076623744755864400219)
    ·
      refine ⟨646614935617133796600329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431076623744755864400219 646614935617133796600329)
      ·
        refine ⟨484961201712850347450247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646614935617133796600329 484961201712850347450247)
        ·
          refine ⟨727441802569275521175371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484961201712850347450247 727441802569275521175371)
          ·
            refine ⟨1091162703853913281763057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727441802569275521175371 1091162703853913281763057)
            ·
              refine ⟨818372027890434961322293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091162703853913281763057 818372027890434961322293)
              ·
                refine ⟨76722377614728277623965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 818372027890434961322293 76722377614728277623965)
                ·
                  refine ⟨28770891605523104108987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76722377614728277623965 28770891605523104108987)
                  ·
                    rfl

theorem cell21_126070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_126070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126070 prefixEnd_126070 := by exact prefixLift 126070
  have htrace : WordTrace (prefixWord ++ tailWord_126070) baseStart_126070 baseEnd_126070 := by
    simpa [prefixWord, tailWord_126070, baseEnd_126070] using wordTrace_append hprefix tailTrace_126070
  have hstable : (prefixWord ++ tailWord_126070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126070).length < 2 ^ (prefixWord ++ tailWord_126070).sum := by decide
  have hdescent : baseEnd_126070 < baseStart_126070 := by decide
  rcases family_descends (prefixWord ++ tailWord_126070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126081 : List Nat := [1, 2, 4, 2, 2, 10]
def baseStart_126081 : Nat := 118140960795 + 126081 * 2 ^ 59
def prefixEnd_126081 : Nat := 4983230072969 + 3 ^ 40 * 126081 * 2
def baseEnd_126081 : Nat := 1065681553903315904653

theorem tailTrace_126081 : CollatzResearch.WordTrace tailWord_126081 prefixEnd_126081 1065681553903315904653 := by
  unfold tailWord_126081
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598551856237544765586097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3065701237491696510390731 4598551856237544765586097)
  ·
    refine ⟨3448913892178158574189573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4598551856237544765586097 3448913892178158574189573)
    ·
      refine ⟨646671354783404732660545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3448913892178158574189573 646671354783404732660545)
      ·
        refine ⟨485003516087553549495409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 646671354783404732660545 485003516087553549495409)
        ·
          refine ⟨363752637065665162121557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485003516087553549495409 363752637065665162121557)
          ·
            refine ⟨1065681553903315904653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 363752637065665162121557 1065681553903315904653)
            ·
              rfl

theorem cell21_126081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 10].length) (baseStart_126081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126081 prefixEnd_126081 := by exact prefixLift 126081
  have htrace : WordTrace (prefixWord ++ tailWord_126081) baseStart_126081 baseEnd_126081 := by
    simpa [prefixWord, tailWord_126081, baseEnd_126081] using wordTrace_append hprefix tailTrace_126081
  have hstable : (prefixWord ++ tailWord_126081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126081).length < 2 ^ (prefixWord ++ tailWord_126081).sum := by decide
  have hdescent : baseEnd_126081 < baseStart_126081 := by decide
  rcases family_descends (prefixWord ++ tailWord_126081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126084 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_126084 : Nat := 118140960795 + 126084 * 2 ^ 59
def prefixEnd_126084 : Nat := 4983230072969 + 3 ^ 40 * 126084 * 2
def baseEnd_126084 : Nat := 28774086596262190875625

theorem tailTrace_126084 : CollatzResearch.WordTrace tailWord_126084 prefixEnd_126084 28774086596262190875625 := by
  unfold tailWord_126084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299330637613338138972653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3065774183484450851963537 2299330637613338138972653)
  ·
    refine ⟨862248989105001802114745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2299330637613338138972653 862248989105001802114745)
    ·
      refine ⟨646686741828751351586059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 862248989105001802114745 646686741828751351586059)
      ·
        refine ⟨970030112743127027379089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646686741828751351586059 970030112743127027379089)
        ·
          refine ⟨727522584557345270534317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970030112743127027379089 727522584557345270534317)
          ·
            refine ⟨272820969209004476450369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 727522584557345270534317 272820969209004476450369)
            ·
              refine ⟨204615726906753357337777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272820969209004476450369 204615726906753357337777)
              ·
                refine ⟨153461795180065018003333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204615726906753357337777 153461795180065018003333)
                ·
                  refine ⟨28774086596262190875625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153461795180065018003333 28774086596262190875625)
                  ·
                    rfl

theorem cell21_126084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_126084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126084 prefixEnd_126084 := by exact prefixLift 126084
  have htrace : WordTrace (prefixWord ++ tailWord_126084) baseStart_126084 baseEnd_126084 := by
    simpa [prefixWord, tailWord_126084, baseEnd_126084] using wordTrace_append hprefix tailTrace_126084
  have hstable : (prefixWord ++ tailWord_126084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126084).length < 2 ^ (prefixWord ++ tailWord_126084).sum := by decide
  have hdescent : baseEnd_126084 < baseStart_126084 := by decide
  rcases family_descends (prefixWord ++ tailWord_126084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126098 : List Nat := [3, 2, 3, 1, 1, 2, 3, 6]
def baseStart_126098 : Nat := 118140960795 + 126098 * 2 ^ 59
def prefixEnd_126098 : Nat := 4983230072969 + 3 ^ 40 * 126098 * 2
def baseEnd_126098 : Nat := 9592427195667092547421

theorem tailTrace_126098 : CollatzResearch.WordTrace tailWord_126098 prefixEnd_126098 9592427195667092547421 := by
  unfold tailWord_126098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149792974293989167238737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3066114598117304445969965 1149792974293989167238737)
  ·
    refine ⟨862344730720491875429053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1149792974293989167238737 862344730720491875429053)
    ·
      refine ⟨323379274020184453285895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 862344730720491875429053 323379274020184453285895)
      ·
        refine ⟨485068911030276679928843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323379274020184453285895 485068911030276679928843)
        ·
          refine ⟨727603366545415019893265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485068911030276679928843 727603366545415019893265)
          ·
            refine ⟨545702524909061264919949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727603366545415019893265 545702524909061264919949)
            ·
              refine ⟨204638446840897974344981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 545702524909061264919949 204638446840897974344981)
              ·
                refine ⟨9592427195667092547421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204638446840897974344981 9592427195667092547421)
                ·
                  rfl

theorem cell21_126098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_126098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126098 prefixEnd_126098 := by exact prefixLift 126098
  have htrace : WordTrace (prefixWord ++ tailWord_126098) baseStart_126098 baseEnd_126098 := by
    simpa [prefixWord, tailWord_126098, baseEnd_126098] using wordTrace_append hprefix tailTrace_126098
  have hstable : (prefixWord ++ tailWord_126098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126098).length < 2 ^ (prefixWord ++ tailWord_126098).sum := by decide
  have hdescent : baseEnd_126098 < baseStart_126098 := by decide
  rcases family_descends (prefixWord ++ tailWord_126098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126112 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_126112 : Nat := 118140960795 + 126112 * 2 ^ 59
def prefixEnd_126112 : Nat := 4983230072969 + 3 ^ 40 * 126112 * 2
def baseEnd_126112 : Nat := 28780476577740364408901

theorem tailTrace_126112 : CollatzResearch.WordTrace tailWord_126112 prefixEnd_126112 28780476577740364408901 := by
  unfold tailWord_126112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299841259562618529982295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3066455012750158039976393 2299841259562618529982295)
  ·
    refine ⟨3449761889343927794973443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2299841259562618529982295 3449761889343927794973443)
    ·
      refine ⟨5174642834015891692460165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3449761889343927794973443 5174642834015891692460165)
      ·
        refine ⟨970245531377979692336281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5174642834015891692460165 970245531377979692336281)
        ·
          refine ⟨727684148533484769252211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970245531377979692336281 727684148533484769252211)
          ·
            refine ⟨1091526222800227153878317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727684148533484769252211 1091526222800227153878317)
            ·
              refine ⟨409322333550085182704369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091526222800227153878317 409322333550085182704369)
              ·
                refine ⟨306991750162563887028277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409322333550085182704369 306991750162563887028277)
                ·
                  refine ⟨28780476577740364408901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306991750162563887028277 28780476577740364408901)
                  ·
                    rfl

theorem cell21_126112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_126112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126112 prefixEnd_126112 := by exact prefixLift 126112
  have htrace : WordTrace (prefixWord ++ tailWord_126112) baseStart_126112 baseEnd_126112 := by
    simpa [prefixWord, tailWord_126112, baseEnd_126112] using wordTrace_append hprefix tailTrace_126112
  have hstable : (prefixWord ++ tailWord_126112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126112).length < 2 ^ (prefixWord ++ tailWord_126112).sum := by decide
  have hdescent : baseEnd_126112 < baseStart_126112 := by decide
  rcases family_descends (prefixWord ++ tailWord_126112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126143 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 4]
def baseStart_126143 : Nat := 118140960795 + 126143 * 2 ^ 59
def prefixEnd_126143 : Nat := 4983230072969 + 3 ^ 40 * 126143 * 2
def baseEnd_126143 : Nat := 28787551200091199392171

theorem tailTrace_126143 : CollatzResearch.WordTrace tailWord_126143 prefixEnd_126143 28787551200091199392171 := by
  unfold tailWord_126143
  simp only [CollatzResearch.WordTrace]
  refine ⟨4600813182012929354343083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3067208788008619569562055 4600813182012929354343083)
  ·
    refine ⟨6901219773019394031514625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4600813182012929354343083 6901219773019394031514625)
    ·
      refine ⟨5175914829764545523635969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6901219773019394031514625 5175914829764545523635969)
      ·
        refine ⟨3881936122323409142726977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5175914829764545523635969 3881936122323409142726977)
        ·
          refine ⟨2911452091742556857045233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881936122323409142726977 2911452091742556857045233)
          ·
            refine ⟨2183589068806917642783925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911452091742556857045233 2183589068806917642783925)
            ·
              refine ⟨204711475200648529010993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2183589068806917642783925 204711475200648529010993)
              ·
                refine ⟨153533606400486396758245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204711475200648529010993 153533606400486396758245)
                ·
                  refine ⟨28787551200091199392171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153533606400486396758245 28787551200091199392171)
                  ·
                    rfl

theorem cell21_126143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 4].length) (baseStart_126143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126143 prefixEnd_126143 := by exact prefixLift 126143
  have htrace : WordTrace (prefixWord ++ tailWord_126143) baseStart_126143 baseEnd_126143 := by
    simpa [prefixWord, tailWord_126143, baseEnd_126143] using wordTrace_append hprefix tailTrace_126143
  have hstable : (prefixWord ++ tailWord_126143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126143).length < 2 ^ (prefixWord ++ tailWord_126143).sum := by decide
  have hdescent : baseEnd_126143 < baseStart_126143 := by decide
  rcases family_descends (prefixWord ++ tailWord_126143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126202 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_126202 : Nat := 118140960795 + 126202 * 2 ^ 59
def prefixEnd_126202 : Nat := 4983230072969 + 3 ^ 40 * 126202 * 2
def baseEnd_126202 : Nat := 28801015803920207908717

theorem tailTrace_126202 : CollatzResearch.WordTrace tailWord_126202 prefixEnd_126202 28801015803920207908717 := by
  unfold tailWord_126202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150741272199795607685215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3068643392532788287160573 1150741272199795607685215)
  ·
    refine ⟨1726111908299693411527823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1150741272199795607685215 1726111908299693411527823)
    ·
      refine ⟨2589167862449540117291735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726111908299693411527823 2589167862449540117291735)
      ·
        refine ⟨3883751793674310175937603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589167862449540117291735 3883751793674310175937603)
        ·
          refine ⟨5825627690511465263906405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883751793674310175937603 5825627690511465263906405)
          ·
            refine ⟨1092305191970899736982451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5825627690511465263906405 1092305191970899736982451)
            ·
              refine ⟨1638457787956349605473677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092305191970899736982451 1638457787956349605473677)
              ·
                refine ⟨614421670483631102052629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1638457787956349605473677 614421670483631102052629)
                ·
                  refine ⟨28801015803920207908717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 614421670483631102052629 28801015803920207908717)
                  ·
                    rfl

theorem cell21_126202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_126202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126202 prefixEnd_126202 := by exact prefixLift 126202
  have htrace : WordTrace (prefixWord ++ tailWord_126202) baseStart_126202 baseEnd_126202 := by
    simpa [prefixWord, tailWord_126202, baseEnd_126202] using wordTrace_append hprefix tailTrace_126202
  have hstable : (prefixWord ++ tailWord_126202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126202).length < 2 ^ (prefixWord ++ tailWord_126202).sum := by decide
  have hdescent : baseEnd_126202 < baseStart_126202 := by decide
  rcases family_descends (prefixWord ++ tailWord_126202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126219 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 4]
def baseStart_126219 : Nat := 118140960795 + 126219 * 2 ^ 59
def prefixEnd_126219 : Nat := 4983230072969 + 3 ^ 40 * 126219 * 2
def baseEnd_126219 : Nat := 28804895435531956125349

theorem tailTrace_126219 : CollatzResearch.WordTrace tailWord_126219 prefixEnd_126219 28804895435531956125349 := by
  unfold tailWord_126219
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603585129737594334109711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3069056753158396222739807 4603585129737594334109711)
  ·
    refine ⟨6905377694606391501164567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4603585129737594334109711 6905377694606391501164567)
    ·
      refine ⟨10358066541909587251746851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6905377694606391501164567 10358066541909587251746851)
      ·
        refine ⟨15537099812864380877620277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10358066541909587251746851 15537099812864380877620277)
        ·
          refine ⟨1456603107456035707276901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15537099812864380877620277 1456603107456035707276901)
          ·
            refine ⟨273113082648006695114419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1456603107456035707276901 273113082648006695114419)
            ·
              refine ⟨409669623972010042671629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273113082648006695114419 409669623972010042671629)
              ·
                refine ⟨153626108989503766001861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409669623972010042671629 153626108989503766001861)
                ·
                  refine ⟨28804895435531956125349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153626108989503766001861 28804895435531956125349)
                  ·
                    rfl

theorem cell21_126219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 4].length) (baseStart_126219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126219 prefixEnd_126219 := by exact prefixLift 126219
  have htrace : WordTrace (prefixWord ++ tailWord_126219) baseStart_126219 baseEnd_126219 := by
    simpa [prefixWord, tailWord_126219, baseEnd_126219] using wordTrace_append hprefix tailTrace_126219
  have hstable : (prefixWord ++ tailWord_126219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126219).length < 2 ^ (prefixWord ++ tailWord_126219).sum := by decide
  have hdescent : baseEnd_126219 < baseStart_126219 := by decide
  rcases family_descends (prefixWord ++ tailWord_126219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126253 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 4]
def baseStart_126253 : Nat := 118140960795 + 126253 * 2 ^ 59
def prefixEnd_126253 : Nat := 4983230072969 + 3 ^ 40 * 126253 * 2
def baseEnd_126253 : Nat := 28812654698755452558613

theorem tailTrace_126253 : CollatzResearch.WordTrace tailWord_126253 prefixEnd_126253 28812654698755452558613 := by
  unfold tailWord_126253
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604825211614418140847413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3069883474409612093898275 4604825211614418140847413)
  ·
    refine ⟨431702363588851700704445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4604825211614418140847413 431702363588851700704445)
    ·
      refine ⟨161888386345819387764167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 431702363588851700704445 161888386345819387764167)
      ·
        refine ⟨242832579518729081646251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161888386345819387764167 242832579518729081646251)
        ·
          refine ⟨364248869278093622469377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242832579518729081646251 364248869278093622469377)
          ·
            refine ⟨273186651958570216852033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364248869278093622469377 273186651958570216852033)
            ·
              refine ⟨204889988968927662639025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273186651958570216852033 204889988968927662639025)
              ·
                refine ⟨153667491726695746979269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204889988968927662639025 153667491726695746979269)
                ·
                  refine ⟨28812654698755452558613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153667491726695746979269 28812654698755452558613)
                  ·
                    rfl

theorem cell21_126253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_126253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126253 prefixEnd_126253 := by exact prefixLift 126253
  have htrace : WordTrace (prefixWord ++ tailWord_126253) baseStart_126253 baseEnd_126253 := by
    simpa [prefixWord, tailWord_126253, baseEnd_126253] using wordTrace_append hprefix tailTrace_126253
  have hstable : (prefixWord ++ tailWord_126253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126253).length < 2 ^ (prefixWord ++ tailWord_126253).sum := by decide
  have hdescent : baseEnd_126253 < baseStart_126253 := by decide
  rcases family_descends (prefixWord ++ tailWord_126253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126340 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_126340 : Nat := 118140960795 + 126340 * 2 ^ 59
def prefixEnd_126340 : Nat := 4983230072969 + 3 ^ 40 * 126340 * 2
def baseEnd_126340 : Nat := 28832509284062634608435

theorem tailTrace_126340 : CollatzResearch.WordTrace tailWord_126340 prefixEnd_126340 28832509284062634608435 := by
  unfold tailWord_126340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303999181149615999632237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3071998908199487999509649 2303999181149615999632237)
  ·
    refine ⟨863999692931105999862089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2303999181149615999632237 863999692931105999862089)
    ·
      refine ⟨647999769698329499896567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 863999692931105999862089 647999769698329499896567)
      ·
        refine ⟨971999654547494249844851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647999769698329499896567 971999654547494249844851)
        ·
          refine ⟨1457999481821241374767277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971999654547494249844851 1457999481821241374767277)
          ·
            refine ⟨546749805682965515537729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1457999481821241374767277 546749805682965515537729)
            ·
              refine ⟨410062354262224136653297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546749805682965515537729 410062354262224136653297)
              ·
                refine ⟨307546765696668102489973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410062354262224136653297 307546765696668102489973)
                ·
                  refine ⟨28832509284062634608435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307546765696668102489973 28832509284062634608435)
                  ·
                    rfl

theorem cell21_126340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_126340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126340 prefixEnd_126340 := by exact prefixLift 126340
  have htrace : WordTrace (prefixWord ++ tailWord_126340) baseStart_126340 baseEnd_126340 := by
    simpa [prefixWord, tailWord_126340, baseEnd_126340] using wordTrace_append hprefix tailTrace_126340
  have hstable : (prefixWord ++ tailWord_126340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126340).length < 2 ^ (prefixWord ++ tailWord_126340).sum := by decide
  have hdescent : baseEnd_126340 < baseStart_126340 := by decide
  rcases family_descends (prefixWord ++ tailWord_126340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126357 : List Nat := [1, 3, 2, 1, 1, 2, 5, 3, 3]
def baseStart_126357 : Nat := 118140960795 + 126357 * 2 ^ 59
def prefixEnd_126357 : Nat := 4983230072969 + 3 ^ 40 * 126357 * 2
def baseEnd_126357 : Nat := 28836388915674382825067

theorem tailTrace_126357 : CollatzResearch.WordTrace tailWord_126357 prefixEnd_126357 28836388915674382825067 := by
  unfold tailWord_126357
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608618403237643902633325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3072412268825095935088883 4608618403237643902633325)
  ·
    refine ⟨1728231901214116463487497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4608618403237643902633325 1728231901214116463487497)
    ·
      refine ⟨1296173925910587347615623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1728231901214116463487497 1296173925910587347615623)
      ·
        refine ⟨1944260888865881021423435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296173925910587347615623 1944260888865881021423435)
        ·
          refine ⟨2916391333298821532135153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944260888865881021423435 2916391333298821532135153)
          ·
            refine ⟨2187293499974116149101365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916391333298821532135153 2187293499974116149101365)
            ·
              refine ⟨205058765622573388978253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2187293499974116149101365 205058765622573388978253)
              ·
                refine ⟨76897037108465020866845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205058765622573388978253 76897037108465020866845)
                ·
                  refine ⟨28836388915674382825067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76897037108465020866845 28836388915674382825067)
                  ·
                    rfl

theorem cell21_126357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_126357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126357 prefixEnd_126357 := by exact prefixLift 126357
  have htrace : WordTrace (prefixWord ++ tailWord_126357) baseStart_126357 baseEnd_126357 := by
    simpa [prefixWord, tailWord_126357, baseEnd_126357] using wordTrace_append hprefix tailTrace_126357
  have hstable : (prefixWord ++ tailWord_126357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126357).length < 2 ^ (prefixWord ++ tailWord_126357).sum := by decide
  have hdescent : baseEnd_126357 < baseStart_126357 := by decide
  rcases family_descends (prefixWord ++ tailWord_126357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126385 : List Nat := [1, 2, 2, 4, 1, 1, 4, 6]
def baseStart_126385 : Nat := 118140960795 + 126385 * 2 ^ 59
def prefixEnd_126385 : Nat := 4983230072969 + 3 ^ 40 * 126385 * 2
def baseEnd_126385 : Nat := 9614259632384185452781

theorem tailTrace_126385 : CollatzResearch.WordTrace tailWord_126385 prefixEnd_126385 9614259632384185452781 := by
  unfold tailWord_126385
  simp only [CollatzResearch.WordTrace]
  refine ⟨4609639647136204684652609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3073093098090803123101739 4609639647136204684652609)
  ·
    refine ⟨3457229735352153513489457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4609639647136204684652609 3457229735352153513489457)
    ·
      refine ⟨2592922301514115135117093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3457229735352153513489457 2592922301514115135117093)
      ·
        refine ⟨486172931533896587834455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2592922301514115135117093 486172931533896587834455)
        ·
          refine ⟨729259397300844881751683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486172931533896587834455 729259397300844881751683)
          ·
            refine ⟨1093889095951267322627525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729259397300844881751683 1093889095951267322627525)
            ·
              refine ⟨205104205490862622992661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1093889095951267322627525 205104205490862622992661)
              ·
                refine ⟨9614259632384185452781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205104205490862622992661 9614259632384185452781)
                ·
                  rfl

theorem cell21_126385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 6].length) (baseStart_126385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126385 prefixEnd_126385 := by exact prefixLift 126385
  have htrace : WordTrace (prefixWord ++ tailWord_126385) baseStart_126385 baseEnd_126385 := by
    simpa [prefixWord, tailWord_126385, baseEnd_126385] using wordTrace_append hprefix tailTrace_126385
  have hstable : (prefixWord ++ tailWord_126385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126385).length < 2 ^ (prefixWord ++ tailWord_126385).sum := by decide
  have hdescent : baseEnd_126385 < baseStart_126385 := by decide
  rcases family_descends (prefixWord ++ tailWord_126385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126399 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 5]
def baseStart_126399 : Nat := 118140960795 + 126399 * 2 ^ 59
def prefixEnd_126399 : Nat := 4983230072969 + 3 ^ 40 * 126399 * 2
def baseEnd_126399 : Nat := 28845973887891643124981

theorem tailTrace_126399 : CollatzResearch.WordTrace tailWord_126399 prefixEnd_126399 28845973887891643124981 := by
  unfold tailWord_126399
  simp only [CollatzResearch.WordTrace]
  refine ⟨4610150269085485075662251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3073433512723656717108167 4610150269085485075662251)
  ·
    refine ⟨6915225403628227613493377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4610150269085485075662251 6915225403628227613493377)
    ·
      refine ⟨5186419052721170710120033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6915225403628227613493377 5186419052721170710120033)
      ·
        refine ⟨3889814289540878032590025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5186419052721170710120033 3889814289540878032590025)
        ·
          refine ⟨2917360717155658524442519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3889814289540878032590025 2917360717155658524442519)
          ·
            refine ⟨4376041075733487786663779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2917360717155658524442519 4376041075733487786663779)
            ·
              refine ⟨6564061613600231679995669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376041075733487786663779 6564061613600231679995669)
              ·
                refine ⟨307690388137510859999797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6564061613600231679995669 307690388137510859999797)
                ·
                  refine ⟨28845973887891643124981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307690388137510859999797 28845973887891643124981)
                  ·
                    rfl

theorem cell21_126399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_126399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126399 prefixEnd_126399 := by exact prefixLift 126399
  have htrace : WordTrace (prefixWord ++ tailWord_126399) baseStart_126399 baseEnd_126399 := by
    simpa [prefixWord, tailWord_126399, baseEnd_126399] using wordTrace_append hprefix tailTrace_126399
  have hstable : (prefixWord ++ tailWord_126399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126399).length < 2 ^ (prefixWord ++ tailWord_126399).sum := by decide
  have hdescent : baseEnd_126399 < baseStart_126399 := by decide
  rcases family_descends (prefixWord ++ tailWord_126399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126433 : List Nat := [1, 2, 3, 1, 2, 4, 1, 4, 3]
def baseStart_126433 : Nat := 118140960795 + 126433 * 2 ^ 59
def prefixEnd_126433 : Nat := 4983230072969 + 3 ^ 40 * 126433 * 2
def baseEnd_126433 : Nat := 28853733151115139558245

theorem tailTrace_126433 : CollatzResearch.WordTrace tailWord_126433 prefixEnd_126433 28853733151115139558245 := by
  unfold tailWord_126433
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611390350962308882399953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3074260233974872588266635 4611390350962308882399953)
  ·
    refine ⟨3458542763221731661799965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4611390350962308882399953 3458542763221731661799965)
    ·
      refine ⟨1296953536208149373174987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3458542763221731661799965 1296953536208149373174987)
      ·
        refine ⟨1945430304312224059762481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296953536208149373174987 1945430304312224059762481)
        ·
          refine ⟨1459072728234168044821861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1945430304312224059762481 1459072728234168044821861)
          ·
            refine ⟨273576136543906508404099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1459072728234168044821861 273576136543906508404099)
            ·
              refine ⟨410364204815859762606149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273576136543906508404099 410364204815859762606149)
              ·
                refine ⟨76943288402973705488653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410364204815859762606149 76943288402973705488653)
                ·
                  refine ⟨28853733151115139558245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76943288402973705488653 28853733151115139558245)
                  ·
                    rfl

theorem cell21_126433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_126433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126433 prefixEnd_126433 := by exact prefixLift 126433
  have htrace : WordTrace (prefixWord ++ tailWord_126433) baseStart_126433 baseEnd_126433 := by
    simpa [prefixWord, tailWord_126433, baseEnd_126433] using wordTrace_append hprefix tailTrace_126433
  have hstable : (prefixWord ++ tailWord_126433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126433).length < 2 ^ (prefixWord ++ tailWord_126433).sum := by decide
  have hdescent : baseEnd_126433 < baseStart_126433 := by decide
  rcases family_descends (prefixWord ++ tailWord_126433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126444 : List Nat := [2, 2, 1, 1, 2, 1, 2, 10]
def baseStart_126444 : Nat := 118140960795 + 126444 * 2 ^ 59
def prefixEnd_126444 : Nat := 4983230072969 + 3 ^ 40 * 126444 * 2
def baseEnd_126444 : Nat := 9618747833660521624963

theorem tailTrace_126444 : CollatzResearch.WordTrace tailWord_126444 prefixEnd_126444 9618747833660521624963 := by
  unfold tailWord_126444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305895776961228880525193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3074527702614971840700257 2305895776961228880525193)
  ·
    refine ⟨1729421832720921660393895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2305895776961228880525193 1729421832720921660393895)
    ·
      refine ⟨2594132749081382490590843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729421832720921660393895 2594132749081382490590843)
      ·
        refine ⟨3891199123622073735886265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2594132749081382490590843 3891199123622073735886265)
        ·
          refine ⟨2918399342716555301914699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3891199123622073735886265 2918399342716555301914699)
          ·
            refine ⟨4377599014074832952872049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918399342716555301914699 4377599014074832952872049)
            ·
              refine ⟨3283199260556124714654037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4377599014074832952872049 3283199260556124714654037)
              ·
                refine ⟨9618747833660521624963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3283199260556124714654037 9618747833660521624963)
                ·
                  rfl

theorem cell21_126444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_126444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126444 prefixEnd_126444 := by exact prefixLift 126444
  have htrace : WordTrace (prefixWord ++ tailWord_126444) baseStart_126444 baseEnd_126444 := by
    simpa [prefixWord, tailWord_126444, baseEnd_126444] using wordTrace_append hprefix tailTrace_126444
  have hstable : (prefixWord ++ tailWord_126444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126444).length < 2 ^ (prefixWord ++ tailWord_126444).sum := by decide
  have hdescent : baseEnd_126444 < baseStart_126444 := by decide
  rcases family_descends (prefixWord ++ tailWord_126444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126492 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_126492 : Nat := 118140960795 + 126492 * 2 ^ 59
def prefixEnd_126492 : Nat := 4983230072969 + 3 ^ 40 * 126492 * 2
def baseEnd_126492 : Nat := 28867197754944148074791

theorem tailTrace_126492 : CollatzResearch.WordTrace tailWord_126492 prefixEnd_126492 28867197754944148074791 := by
  unfold tailWord_126492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306771128874280979398865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3075694838499041305865153 2306771128874280979398865)
  ·
    refine ⟨1730078346655710734549149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2306771128874280979398865 1730078346655710734549149)
    ·
      refine ⟨648779379995891525455931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1730078346655710734549149 648779379995891525455931)
      ·
        refine ⟨973169069993837288183897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648779379995891525455931 973169069993837288183897)
        ·
          refine ⟨729876802495377966137923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 973169069993837288183897 729876802495377966137923)
          ·
            refine ⟨1094815203743066949206885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729876802495377966137923 1094815203743066949206885)
            ·
              refine ⟨205277850701825052976291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1094815203743066949206885 205277850701825052976291)
              ·
                refine ⟨307916776052737579464437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205277850701825052976291 307916776052737579464437)
                ·
                  refine ⟨28867197754944148074791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307916776052737579464437 28867197754944148074791)
                  ·
                    rfl

theorem cell21_126492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_126492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126492 prefixEnd_126492 := by exact prefixLift 126492
  have htrace : WordTrace (prefixWord ++ tailWord_126492) baseStart_126492 baseEnd_126492 := by
    simpa [prefixWord, tailWord_126492, baseEnd_126492] using wordTrace_append hprefix tailTrace_126492
  have hstable : (prefixWord ++ tailWord_126492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126492).length < 2 ^ (prefixWord ++ tailWord_126492).sum := by decide
  have hdescent : baseEnd_126492 < baseStart_126492 := by decide
  rcases family_descends (prefixWord ++ tailWord_126492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126557 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 4]
def baseStart_126557 : Nat := 118140960795 + 126557 * 2 ^ 59
def prefixEnd_126557 : Nat := 4983230072969 + 3 ^ 40 * 126557 * 2
def baseEnd_126557 : Nat := 28882031640518479491325

theorem tailTrace_126557 : CollatzResearch.WordTrace tailWord_126557 prefixEnd_126557 28882031640518479491325 := by
  unfold tailWord_126557
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615913002513078059913925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3077275335008718706609283 4615913002513078059913925)
  ·
    refine ⟨865483687971202136233861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4615913002513078059913925 865483687971202136233861)
    ·
      refine ⟨162278191494600400543849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 865483687971202136233861 162278191494600400543849)
      ·
        refine ⟨121708643620950300407887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162278191494600400543849 121708643620950300407887)
        ·
          refine ⟨182562965431425450611831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121708643620950300407887 182562965431425450611831)
          ·
            refine ⟨273844448147138175917747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182562965431425450611831 273844448147138175917747)
            ·
              refine ⟨410766672220707263876621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273844448147138175917747 410766672220707263876621)
              ·
                refine ⟨154037502082765223953733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410766672220707263876621 154037502082765223953733)
                ·
                  refine ⟨28882031640518479491325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154037502082765223953733 28882031640518479491325)
                  ·
                    rfl

theorem cell21_126557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_126557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126557 prefixEnd_126557 := by exact prefixLift 126557
  have htrace : WordTrace (prefixWord ++ tailWord_126557) baseStart_126557 baseEnd_126557 := by
    simpa [prefixWord, tailWord_126557, baseEnd_126557] using wordTrace_append hprefix tailTrace_126557
  have hstable : (prefixWord ++ tailWord_126557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126557).length < 2 ^ (prefixWord ++ tailWord_126557).sum := by decide
  have hdescent : baseEnd_126557 < baseStart_126557 := by decide
  rcases family_descends (prefixWord ++ tailWord_126557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126596 : List Nat := [2, 3, 2, 1, 13]
def baseStart_126596 : Nat := 118140960795 + 126596 * 2 ^ 59
def prefixEnd_126596 : Nat := 4983230072969 + 3 ^ 40 * 126596 * 2
def baseEnd_126596 : Nat := 356678172492136769645

theorem tailTrace_126596 : CollatzResearch.WordTrace tailWord_126596 prefixEnd_126596 356678172492136769645 := by
  unfold tailWord_126596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308667724685893860291821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3078223632914525147055761 2308667724685893860291821)
  ·
    refine ⟨865750396757210197609433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2308667724685893860291821 865750396757210197609433)
    ·
      refine ⟨649312797567907648207075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 865750396757210197609433 649312797567907648207075)
      ·
        refine ⟨973969196351861472310613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649312797567907648207075 973969196351861472310613)
        ·
          refine ⟨356678172492136769645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 973969196351861472310613 356678172492136769645)
          ·
            rfl

theorem cell21_126596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 13].length) (baseStart_126596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126596 prefixEnd_126596 := by exact prefixLift 126596
  have htrace : WordTrace (prefixWord ++ tailWord_126596) baseStart_126596 baseEnd_126596 := by
    simpa [prefixWord, tailWord_126596, baseEnd_126596] using wordTrace_append hprefix tailTrace_126596
  have hstable : (prefixWord ++ tailWord_126596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126596).length < 2 ^ (prefixWord ++ tailWord_126596).sum := by decide
  have hdescent : baseEnd_126596 < baseStart_126596 := by decide
  rcases family_descends (prefixWord ++ tailWord_126596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126599 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 4]
def baseStart_126599 : Nat := 118140960795 + 126599 * 2 ^ 59
def prefixEnd_126599 : Nat := 4983230072969 + 3 ^ 40 * 126599 * 2
def baseEnd_126599 : Nat := 28891616612735739791239

theorem tailTrace_126599 : CollatzResearch.WordTrace tailWord_126599 prefixEnd_126599 28891616612735739791239 := by
  unfold tailWord_126599
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617444868360919232942851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3078296578907279488628567 4617444868360919232942851)
  ·
    refine ⟨6926167302541378849414277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4617444868360919232942851 6926167302541378849414277)
    ·
      refine ⟨1298656369226508534265177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6926167302541378849414277 1298656369226508534265177)
      ·
        refine ⟨973992276919881400698883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1298656369226508534265177 973992276919881400698883)
        ·
          refine ⟨1460988415379822101048325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973992276919881400698883 1460988415379822101048325)
          ·
            refine ⟨273935327883716643946561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1460988415379822101048325 273935327883716643946561)
            ·
              refine ⟨205451495912787482959921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273935327883716643946561 205451495912787482959921)
              ·
                refine ⟨154088621934590612219941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205451495912787482959921 154088621934590612219941)
                ·
                  refine ⟨28891616612735739791239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154088621934590612219941 28891616612735739791239)
                  ·
                    rfl

theorem cell21_126599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 4].length) (baseStart_126599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126599 prefixEnd_126599 := by exact prefixLift 126599
  have htrace : WordTrace (prefixWord ++ tailWord_126599) baseStart_126599 baseEnd_126599 := by
    simpa [prefixWord, tailWord_126599, baseEnd_126599] using wordTrace_append hprefix tailTrace_126599
  have hstable : (prefixWord ++ tailWord_126599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126599).length < 2 ^ (prefixWord ++ tailWord_126599).sum := by decide
  have hdescent : baseEnd_126599 < baseStart_126599 := by decide
  rcases family_descends (prefixWord ++ tailWord_126599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126602 : List Nat := [3, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_126602 : Nat := 118140960795 + 126602 * 2 ^ 59
def prefixEnd_126602 : Nat := 4983230072969 + 3 ^ 40 * 126602 * 2
def baseEnd_126602 : Nat := 28892301253608401241233

theorem tailTrace_126602 : CollatzResearch.WordTrace tailWord_126602 prefixEnd_126602 28892301253608401241233 := by
  unfold tailWord_126602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1154388571837512686325515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3078369524900033830201373 1154388571837512686325515)
  ·
    refine ⟨1731582857756269029488273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1154388571837512686325515 1731582857756269029488273)
    ·
      refine ⟨1298687143317201772116205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1731582857756269029488273 1298687143317201772116205)
      ·
        refine ⟨487007678743950664543577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1298687143317201772116205 487007678743950664543577)
        ·
          refine ⟨365255759057962998407683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487007678743950664543577 365255759057962998407683)
          ·
            refine ⟨547883638586944497611525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365255759057962998407683 547883638586944497611525)
            ·
              refine ⟨102728182235052093302161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 547883638586944497611525 102728182235052093302161)
              ·
                refine ⟨77046136676289069976621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102728182235052093302161 77046136676289069976621)
                ·
                  refine ⟨28892301253608401241233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77046136676289069976621 28892301253608401241233)
                  ·
                    rfl

theorem cell21_126602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_126602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126602 prefixEnd_126602 := by exact prefixLift 126602
  have htrace : WordTrace (prefixWord ++ tailWord_126602) baseStart_126602 baseEnd_126602 := by
    simpa [prefixWord, tailWord_126602, baseEnd_126602] using wordTrace_append hprefix tailTrace_126602
  have hstable : (prefixWord ++ tailWord_126602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126602).length < 2 ^ (prefixWord ++ tailWord_126602).sum := by decide
  have hdescent : baseEnd_126602 < baseStart_126602 := by decide
  rcases family_descends (prefixWord ++ tailWord_126602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126627 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 5]
def baseStart_126627 : Nat := 118140960795 + 126627 * 2 ^ 59
def prefixEnd_126627 : Nat := 4983230072969 + 3 ^ 40 * 126627 * 2
def baseEnd_126627 : Nat := 28898006594213913324515

theorem tailTrace_126627 : CollatzResearch.WordTrace tailWord_126627 prefixEnd_126627 28898006594213913324515 := by
  unfold tailWord_126627
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618466112259480014962135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3078977408172986676641423 4618466112259480014962135)
  ·
    refine ⟨6927699168389220022443203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618466112259480014962135 6927699168389220022443203)
    ·
      refine ⟨10391548752583830033664805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927699168389220022443203 10391548752583830033664805)
      ·
        refine ⟨1948415391109468131312151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10391548752583830033664805 1948415391109468131312151)
        ·
          refine ⟨2922623086664202196968227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948415391109468131312151 2922623086664202196968227)
          ·
            refine ⟨4383934629996303295452341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922623086664202196968227 4383934629996303295452341)
            ·
              refine ⟨410993871562153433948657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4383934629996303295452341 410993871562153433948657)
              ·
                refine ⟨308245403671615075461493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410993871562153433948657 308245403671615075461493)
                ·
                  refine ⟨28898006594213913324515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308245403671615075461493 28898006594213913324515)
                  ·
                    rfl

theorem cell21_126627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_126627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126627 prefixEnd_126627 := by exact prefixLift 126627
  have htrace : WordTrace (prefixWord ++ tailWord_126627) baseStart_126627 baseEnd_126627 := by
    simpa [prefixWord, tailWord_126627, baseEnd_126627] using wordTrace_append hprefix tailTrace_126627
  have hstable : (prefixWord ++ tailWord_126627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126627).length < 2 ^ (prefixWord ++ tailWord_126627).sum := by decide
  have hdescent : baseEnd_126627 < baseStart_126627 := by decide
  rcases family_descends (prefixWord ++ tailWord_126627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126689 : List Nat := [1, 2, 3, 1, 5, 1, 1, 7]
def baseStart_126689 : Nat := 118140960795 + 126689 * 2 ^ 59
def prefixEnd_126689 : Nat := 4983230072969 + 3 ^ 40 * 126689 * 2
def baseEnd_126689 : Nat := 9637385279638527763685

theorem tailTrace_126689 : CollatzResearch.WordTrace tailWord_126689 prefixEnd_126689 9637385279638527763685 := by
  unfold tailWord_126689
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620727438034864603719121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3080484958689909735812747 4620727438034864603719121)
  ·
    refine ⟨3465545578526148452789341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4620727438034864603719121 3465545578526148452789341)
    ·
      refine ⟨1299579591947305669796003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3465545578526148452789341 1299579591947305669796003)
      ·
        refine ⟨1949369387920958504694005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299579591947305669796003 1949369387920958504694005)
        ·
          refine ⟨182753380117589859815063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1949369387920958504694005 182753380117589859815063)
          ·
            refine ⟨274130070176384789722595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182753380117589859815063 274130070176384789722595)
            ·
              refine ⟨411195105264577184583893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274130070176384789722595 411195105264577184583893)
              ·
                refine ⟨9637385279638527763685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 411195105264577184583893 9637385279638527763685)
                ·
                  rfl

theorem cell21_126689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 7].length) (baseStart_126689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126689 prefixEnd_126689 := by exact prefixLift 126689
  have htrace : WordTrace (prefixWord ++ tailWord_126689) baseStart_126689 baseEnd_126689 := by
    simpa [prefixWord, tailWord_126689, baseEnd_126689] using wordTrace_append hprefix tailTrace_126689
  have hstable : (prefixWord ++ tailWord_126689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126689).length < 2 ^ (prefixWord ++ tailWord_126689).sum := by decide
  have hdescent : baseEnd_126689 < baseStart_126689 := by decide
  rcases family_descends (prefixWord ++ tailWord_126689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126695 : List Nat := [1, 1, 5, 4, 1, 2, 1, 3, 3]
def baseStart_126695 : Nat := 118140960795 + 126695 * 2 ^ 59
def prefixEnd_126695 : Nat := 4983230072969 + 3 ^ 40 * 126695 * 2
def baseEnd_126695 : Nat := 28913525120660906191043

theorem tailTrace_126695 : CollatzResearch.WordTrace tailWord_126695 prefixEnd_126695 28913525120660906191043 := by
  unfold tailWord_126695
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620946276013127628437539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3080630850675418418958359 4620946276013127628437539)
  ·
    refine ⟨6931419414019691442656309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620946276013127628437539 6931419414019691442656309)
    ·
      refine ⟨649820570064346072749029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6931419414019691442656309 649820570064346072749029)
      ·
        refine ⟨121841356887064888640443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 649820570064346072749029 121841356887064888640443)
        ·
          refine ⟨182762035330597332960665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121841356887064888640443 182762035330597332960665)
          ·
            refine ⟨137071526497947999720499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182762035330597332960665 137071526497947999720499)
            ·
              refine ⟨205607289746921999580749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137071526497947999720499 205607289746921999580749)
              ·
                refine ⟨77102733655095749842781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205607289746921999580749 77102733655095749842781)
                ·
                  refine ⟨28913525120660906191043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77102733655095749842781 28913525120660906191043)
                  ·
                    rfl

theorem cell21_126695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 3].length) (baseStart_126695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126695 prefixEnd_126695 := by exact prefixLift 126695
  have htrace : WordTrace (prefixWord ++ tailWord_126695) baseStart_126695 baseEnd_126695 := by
    simpa [prefixWord, tailWord_126695, baseEnd_126695] using wordTrace_append hprefix tailTrace_126695
  have hstable : (prefixWord ++ tailWord_126695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126695).length < 2 ^ (prefixWord ++ tailWord_126695).sum := by decide
  have hdescent : baseEnd_126695 < baseStart_126695 := by decide
  rcases family_descends (prefixWord ++ tailWord_126695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126748 : List Nat := [2, 2, 3, 1, 1, 2, 1, 9]
def baseStart_126748 : Nat := 118140960795 + 126748 * 2 ^ 59
def prefixEnd_126748 : Nat := 4983230072969 + 3 ^ 40 * 126748 * 2
def baseEnd_126748 : Nat := 9641873480914863935867

theorem tailTrace_126748 : CollatzResearch.WordTrace tailWord_126748 prefixEnd_126748 9641873480914863935867 := by
  unfold tailWord_126748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311439672410558840058449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3081919563214078453411265 2311439672410558840058449)
  ·
    refine ⟨1733579754307919130043837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2311439672410558840058449 1733579754307919130043837)
    ·
      refine ⟨650092407865469673766439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1733579754307919130043837 650092407865469673766439)
      ·
        refine ⟨975138611798204510649659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650092407865469673766439 975138611798204510649659)
        ·
          refine ⟨1462707917697306765974489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975138611798204510649659 1462707917697306765974489)
          ·
            refine ⟨1097030938272980074480867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462707917697306765974489 1097030938272980074480867)
            ·
              refine ⟨1645546407409470111721301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097030938272980074480867 1645546407409470111721301)
              ·
                refine ⟨9641873480914863935867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1645546407409470111721301 9641873480914863935867)
                ·
                  rfl

theorem cell21_126748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_126748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126748 prefixEnd_126748 := by exact prefixLift 126748
  have htrace : WordTrace (prefixWord ++ tailWord_126748) baseStart_126748 baseEnd_126748 := by
    simpa [prefixWord, tailWord_126748, baseEnd_126748] using wordTrace_append hprefix tailTrace_126748
  have hstable : (prefixWord ++ tailWord_126748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126748).length < 2 ^ (prefixWord ++ tailWord_126748).sum := by decide
  have hdescent : baseEnd_126748 < baseStart_126748 := by decide
  rcases family_descends (prefixWord ++ tailWord_126748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126771 : List Nat := [1, 1, 1, 2, 8, 1, 2, 2, 3]
def baseStart_126771 : Nat := 118140960795 + 126771 * 2 ^ 59
def prefixEnd_126771 : Nat := 4983230072969 + 3 ^ 40 * 126771 * 2
def baseEnd_126771 : Nat := 28930869356101662924221

theorem tailTrace_126771 : CollatzResearch.WordTrace tailWord_126771 prefixEnd_126771 28930869356101662924221 := by
  unfold tailWord_126771
  simp only [CollatzResearch.WordTrace]
  refine ⟨4623718223737792608204167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3082478815825195072136111 4623718223737792608204167)
  ·
    refine ⟨6935577335606688912306251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4623718223737792608204167 6935577335606688912306251)
    ·
      refine ⟨10403366003410033368459377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6935577335606688912306251 10403366003410033368459377)
      ·
        refine ⟨7802524502557525026344533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10403366003410033368459377 7802524502557525026344533)
        ·
          refine ⟨91435834014345996402475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 7802524502557525026344533 91435834014345996402475)
          ·
            refine ⟨137153751021518994603713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91435834014345996402475 137153751021518994603713)
            ·
              refine ⟨102865313266139245952785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137153751021518994603713 102865313266139245952785)
              ·
                refine ⟨77148984949604434464589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102865313266139245952785 77148984949604434464589)
                ·
                  refine ⟨28930869356101662924221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77148984949604434464589 28930869356101662924221)
                  ·
                    rfl

theorem cell21_126771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 3].length) (baseStart_126771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126771 prefixEnd_126771 := by exact prefixLift 126771
  have htrace : WordTrace (prefixWord ++ tailWord_126771) baseStart_126771 baseEnd_126771 := by
    simpa [prefixWord, tailWord_126771, baseEnd_126771] using wordTrace_append hprefix tailTrace_126771
  have hstable : (prefixWord ++ tailWord_126771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126771).length < 2 ^ (prefixWord ++ tailWord_126771).sum := by decide
  have hdescent : baseEnd_126771 < baseStart_126771 := by decide
  rcases family_descends (prefixWord ++ tailWord_126771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126782 : List Nat := [4, 2, 1, 2, 2, 3, 1, 6]
def baseStart_126782 : Nat := 118140960795 + 126782 * 2 ^ 59
def prefixEnd_126782 : Nat := 4983230072969 + 3 ^ 40 * 126782 * 2
def baseEnd_126782 : Nat := 9644459901989362746955

theorem tailTrace_126782 : CollatzResearch.WordTrace tailWord_126782 prefixEnd_126782 9644459901989362746955 := by
  unfold tailWord_126782
  simp only [CollatzResearch.WordTrace]
  refine ⟨578014928337242685856825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3082746284465294324569733 578014928337242685856825)
  ·
    refine ⟨433511196252932014392619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 578014928337242685856825 433511196252932014392619)
    ·
      refine ⟨650266794379398021588929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433511196252932014392619 650266794379398021588929)
      ·
        refine ⟨487700095784548516191697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650266794379398021588929 487700095784548516191697)
        ·
          refine ⟨365775071838411387143773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487700095784548516191697 365775071838411387143773)
          ·
            refine ⟨137165651939404270178915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365775071838411387143773 137165651939404270178915)
            ·
              refine ⟨205748477909106405268373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137165651939404270178915 205748477909106405268373)
              ·
                refine ⟨9644459901989362746955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205748477909106405268373 9644459901989362746955)
                ·
                  rfl

theorem cell21_126782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_126782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126782 prefixEnd_126782 := by exact prefixLift 126782
  have htrace : WordTrace (prefixWord ++ tailWord_126782) baseStart_126782 baseEnd_126782 := by
    simpa [prefixWord, tailWord_126782, baseEnd_126782] using wordTrace_append hprefix tailTrace_126782
  have hstable : (prefixWord ++ tailWord_126782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126782).length < 2 ^ (prefixWord ++ tailWord_126782).sum := by decide
  have hdescent : baseEnd_126782 < baseStart_126782 := by decide
  rcases family_descends (prefixWord ++ tailWord_126782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126796 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_126796 : Nat := 118140960795 + 126796 * 2 ^ 59
def prefixEnd_126796 : Nat := 4983230072969 + 3 ^ 40 * 126796 * 2
def baseEnd_126796 : Nat := 28936574696707175007503

theorem tailTrace_126796 : CollatzResearch.WordTrace tailWord_126796 prefixEnd_126796 28936574696707175007503 := by
  unfold tailWord_126796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2312315024323610938932121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3083086699098147918576161 2312315024323610938932121)
  ·
    refine ⟨1734236268242708204199091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2312315024323610938932121 1734236268242708204199091)
    ·
      refine ⟨2601354402364062306298637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1734236268242708204199091 2601354402364062306298637)
      ·
        refine ⟨975507900886523364861989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2601354402364062306298637 975507900886523364861989)
        ·
          refine ⟨182907731416223130911623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 975507900886523364861989 182907731416223130911623)
          ·
            refine ⟨274361597124334696367435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182907731416223130911623 274361597124334696367435)
            ·
              refine ⟨411542395686502044551153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274361597124334696367435 411542395686502044551153)
              ·
                refine ⟨308656796764876533413365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411542395686502044551153 308656796764876533413365)
                ·
                  refine ⟨28936574696707175007503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308656796764876533413365 28936574696707175007503)
                  ·
                    rfl

theorem cell21_126796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_126796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126796 prefixEnd_126796 := by exact prefixLift 126796
  have htrace : WordTrace (prefixWord ++ tailWord_126796) baseStart_126796 baseEnd_126796 := by
    simpa [prefixWord, tailWord_126796, baseEnd_126796] using wordTrace_append hprefix tailTrace_126796
  have hstable : (prefixWord ++ tailWord_126796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126796).length < 2 ^ (prefixWord ++ tailWord_126796).sum := by decide
  have hdescent : baseEnd_126796 < baseStart_126796 := by decide
  rcases family_descends (prefixWord ++ tailWord_126796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126824 : List Nat := [2, 1, 4, 2, 1, 1, 10]
def baseStart_126824 : Nat := 118140960795 + 126824 * 2 ^ 59
def prefixEnd_126824 : Nat := 4983230072969 + 3 ^ 40 * 126824 * 2
def baseEnd_126824 : Nat := 3215884964242816504531

theorem tailTrace_126824 : CollatzResearch.WordTrace tailWord_126824 prefixEnd_126824 3215884964242816504531 := by
  unfold tailWord_126824
  simp only [CollatzResearch.WordTrace]
  refine ⟨2312825646272891329941763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3083767528363855106589017 2312825646272891329941763)
  ·
    refine ⟨3469238469409336994912645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2312825646272891329941763 3469238469409336994912645)
    ·
      refine ⟨650482213014250686546121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3469238469409336994912645 650482213014250686546121)
      ·
        refine ⟨487861659760688014909591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650482213014250686546121 487861659760688014909591)
        ·
          refine ⟨731792489641032022364387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487861659760688014909591 731792489641032022364387)
          ·
            refine ⟨1097688734461548033546581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731792489641032022364387 1097688734461548033546581)
            ·
              refine ⟨3215884964242816504531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1097688734461548033546581 3215884964242816504531)
              ·
                rfl

theorem cell21_126824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 10].length) (baseStart_126824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126824 prefixEnd_126824 := by exact prefixLift 126824
  have htrace : WordTrace (prefixWord ++ tailWord_126824) baseStart_126824 baseEnd_126824 := by
    simpa [prefixWord, tailWord_126824, baseEnd_126824] using wordTrace_append hprefix tailTrace_126824
  have hstable : (prefixWord ++ tailWord_126824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126824).length < 2 ^ (prefixWord ++ tailWord_126824).sum := by decide
  have hdescent : baseEnd_126824 < baseStart_126824 := by decide
  rcases family_descends (prefixWord ++ tailWord_126824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126869 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 8]
def baseStart_126869 : Nat := 118140960795 + 126869 * 2 ^ 59
def prefixEnd_126869 : Nat := 4983230072969 + 3 ^ 40 * 126869 * 2
def baseEnd_126869 : Nat := 28953234291275270290687

theorem tailTrace_126869 : CollatzResearch.WordTrace tailWord_126869 prefixEnd_126869 28953234291275270290687 := by
  unfold tailWord_126869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627292577382755345271661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3084861718255170230181107 4627292577382755345271661)
  ·
    refine ⟨1735234716518533254476873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4627292577382755345271661 1735234716518533254476873)
    ·
      refine ⟨1301426037388899940857655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1735234716518533254476873 1301426037388899940857655)
      ·
        refine ⟨1952139056083349911286483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301426037388899940857655 1952139056083349911286483)
        ·
          refine ⟨2928208584125024866929725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952139056083349911286483 2928208584125024866929725)
          ·
            refine ⟨1098078219046884325098647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2928208584125024866929725 1098078219046884325098647)
            ·
              refine ⟨1647117328570326487647971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098078219046884325098647 1647117328570326487647971)
              ·
                refine ⟨2470675992855489731471957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647117328570326487647971 2470675992855489731471957)
                ·
                  refine ⟨28953234291275270290687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2470675992855489731471957 28953234291275270290687)
                  ·
                    rfl

theorem cell21_126869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_126869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126869 prefixEnd_126869 := by exact prefixLift 126869
  have htrace : WordTrace (prefixWord ++ tailWord_126869) baseStart_126869 baseEnd_126869 := by
    simpa [prefixWord, tailWord_126869, baseEnd_126869] using wordTrace_append hprefix tailTrace_126869
  have hstable : (prefixWord ++ tailWord_126869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126869).length < 2 ^ (prefixWord ++ tailWord_126869).sum := by decide
  have hdescent : baseEnd_126869 < baseStart_126869 := by decide
  rcases family_descends (prefixWord ++ tailWord_126869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126934 : List Nat := [5, 2, 1, 1, 4, 8]
def baseStart_126934 : Nat := 118140960795 + 126934 * 2 ^ 59
def prefixEnd_126934 : Nat := 4983230072969 + 3 ^ 40 * 126934 * 2
def baseEnd_126934 : Nat := 1072891413957392655823

theorem tailTrace_126934 : CollatzResearch.WordTrace tailWord_126934 prefixEnd_126934 1072891413957392655823 := by
  unfold tailWord_126934
  simp only [CollatzResearch.WordTrace]
  refine ⟨289353957634204465399241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3086442214764847630925237 289353957634204465399241)
  ·
    refine ⟨217015468225653349049431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289353957634204465399241 217015468225653349049431)
    ·
      refine ⟨325523202338480023574147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217015468225653349049431 325523202338480023574147)
      ·
        refine ⟨488284803507720035361221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325523202338480023574147 488284803507720035361221)
        ·
          refine ⟨91553400657697506630229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488284803507720035361221 91553400657697506630229)
          ·
            refine ⟨1072891413957392655823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 91553400657697506630229 1072891413957392655823)
            ·
              rfl

theorem cell21_126934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 8].length) (baseStart_126934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126934 prefixEnd_126934 := by exact prefixLift 126934
  have htrace : WordTrace (prefixWord ++ tailWord_126934) baseStart_126934 baseEnd_126934 := by
    simpa [prefixWord, tailWord_126934, baseEnd_126934] using wordTrace_append hprefix tailTrace_126934
  have hstable : (prefixWord ++ tailWord_126934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126934).length < 2 ^ (prefixWord ++ tailWord_126934).sum := by decide
  have hdescent : baseEnd_126934 < baseStart_126934 := by decide
  rcases family_descends (prefixWord ++ tailWord_126934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126945 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 6]
def baseStart_126945 : Nat := 118140960795 + 126945 * 2 ^ 59
def prefixEnd_126945 : Nat := 4983230072969 + 3 ^ 40 * 126945 * 2
def baseEnd_126945 : Nat := 28970578526716027023865

theorem tailTrace_126945 : CollatzResearch.WordTrace tailWord_126945 prefixEnd_126945 28970578526716027023865 := by
  unfold tailWord_126945
  simp only [CollatzResearch.WordTrace]
  refine ⟨4630064525107420325038289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3086709683404946883358859 4630064525107420325038289)
  ·
    refine ⟨3472548393830565243778717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4630064525107420325038289 3472548393830565243778717)
    ·
      refine ⟨1302205647686461966417019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3472548393830565243778717 1302205647686461966417019)
      ·
        refine ⟨1953308471529692949625529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302205647686461966417019 1953308471529692949625529)
        ·
          refine ⟨1464981353647269712219147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953308471529692949625529 1464981353647269712219147)
          ·
            refine ⟨2197472030470904568328721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464981353647269712219147 2197472030470904568328721)
            ·
              refine ⟨1648104022853178426246541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197472030470904568328721 1648104022853178426246541)
              ·
                refine ⟨618039008569941909842453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648104022853178426246541 618039008569941909842453)
                ·
                  refine ⟨28970578526716027023865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 618039008569941909842453 28970578526716027023865)
                  ·
                    rfl

theorem cell21_126945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_126945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126945 prefixEnd_126945 := by exact prefixLift 126945
  have htrace : WordTrace (prefixWord ++ tailWord_126945) baseStart_126945 baseEnd_126945 := by
    simpa [prefixWord, tailWord_126945, baseEnd_126945] using wordTrace_append hprefix tailTrace_126945
  have hstable : (prefixWord ++ tailWord_126945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126945).length < 2 ^ (prefixWord ++ tailWord_126945).sum := by decide
  have hdescent : baseEnd_126945 < baseStart_126945 := by decide
  rcases family_descends (prefixWord ++ tailWord_126945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126948 : List Nat := [2, 3, 1, 1, 1, 1, 5, 4, 3]
def baseStart_126948 : Nat := 118140960795 + 126948 * 2 ^ 59
def prefixEnd_126948 : Nat := 4983230072969 + 3 ^ 40 * 126948 * 2
def baseEnd_126948 : Nat := 28971263167588688473859

theorem tailTrace_126948 : CollatzResearch.WordTrace tailWord_126948 prefixEnd_126948 28971263167588688473859 := by
  unfold tailWord_126948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2315086972048275918698749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3086782629397701224931665 2315086972048275918698749)
  ·
    refine ⟨868157614518103469512031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2315086972048275918698749 868157614518103469512031)
    ·
      refine ⟨1302236421777155204268047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 868157614518103469512031 1302236421777155204268047)
      ·
        refine ⟨1953354632665732806402071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1302236421777155204268047 1953354632665732806402071)
        ·
          refine ⟨2930031948998599209603107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1953354632665732806402071 2930031948998599209603107)
          ·
            refine ⟨4395047923497898814404661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930031948998599209603107 4395047923497898814404661)
            ·
              refine ⟨412035742827928013850437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4395047923497898814404661 412035742827928013850437)
              ·
                refine ⟨77256701780236502596957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412035742827928013850437 77256701780236502596957)
                ·
                  refine ⟨28971263167588688473859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77256701780236502596957 28971263167588688473859)
                  ·
                    rfl

theorem cell21_126948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_126948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126948 prefixEnd_126948 := by exact prefixLift 126948
  have htrace : WordTrace (prefixWord ++ tailWord_126948) baseStart_126948 baseEnd_126948 := by
    simpa [prefixWord, tailWord_126948, baseEnd_126948] using wordTrace_append hprefix tailTrace_126948
  have hstable : (prefixWord ++ tailWord_126948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126948).length < 2 ^ (prefixWord ++ tailWord_126948).sum := by decide
  have hdescent : baseEnd_126948 < baseStart_126948 := by decide
  rcases family_descends (prefixWord ++ tailWord_126948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126996 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_126996 : Nat := 118140960795 + 126996 * 2 ^ 59
def prefixEnd_126996 : Nat := 4983230072969 + 3 ^ 40 * 126996 * 2
def baseEnd_126996 : Nat := 28982217421551271673761

theorem tailTrace_126996 : CollatzResearch.WordTrace tailWord_126996 prefixEnd_126996 28982217421551271673761 := by
  unfold tailWord_126996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2315962323961328017572421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3087949765281770690096561 2315962323961328017572421)
  ·
    refine ⟨434242935742749003294829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2315962323961328017572421 434242935742749003294829)
    ·
      refine ⟨162841100903530876235561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434242935742749003294829 162841100903530876235561)
      ·
        refine ⟨122130825677648157176671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162841100903530876235561 122130825677648157176671)
        ·
          refine ⟨183196238516472235765007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122130825677648157176671 183196238516472235765007)
          ·
            refine ⟨274794357774708353647511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183196238516472235765007 274794357774708353647511)
            ·
              refine ⟨412191536662062530471267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274794357774708353647511 412191536662062530471267)
              ·
                refine ⟨618287304993093795706901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412191536662062530471267 618287304993093795706901)
                ·
                  refine ⟨28982217421551271673761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 618287304993093795706901 28982217421551271673761)
                  ·
                    rfl

theorem cell21_126996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_126996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_126996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_126996 prefixEnd_126996 := by exact prefixLift 126996
  have htrace : WordTrace (prefixWord ++ tailWord_126996) baseStart_126996 baseEnd_126996 := by
    simpa [prefixWord, tailWord_126996, baseEnd_126996] using wordTrace_append hprefix tailTrace_126996
  have hstable : (prefixWord ++ tailWord_126996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126996).length < 2 ^ (prefixWord ++ tailWord_126996).sum := by decide
  have hdescent : baseEnd_126996 < baseStart_126996 := by decide
  rcases family_descends (prefixWord ++ tailWord_126996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127007 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 5]
def baseStart_127007 : Nat := 118140960795 + 127007 * 2 ^ 59
def prefixEnd_127007 : Nat := 4983230072969 + 3 ^ 40 * 127007 * 2
def baseEnd_127007 : Nat := 28984727771417696990405

theorem tailTrace_127007 : CollatzResearch.WordTrace tailWord_127007 prefixEnd_127007 28984727771417696990405 := by
  unfold tailWord_127007
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632325850882804913795275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3088217233921869942530183 4632325850882804913795275)
  ·
    refine ⟨6948488776324207370692913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4632325850882804913795275 6948488776324207370692913)
    ·
      refine ⟨5211366582243155528019685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6948488776324207370692913 5211366582243155528019685)
      ·
        refine ⟨977131234170591661503691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5211366582243155528019685 977131234170591661503691)
        ·
          refine ⟨1465696851255887492255537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977131234170591661503691 1465696851255887492255537)
          ·
            refine ⟨1099272638441915619191653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465696851255887492255537 1099272638441915619191653)
            ·
              refine ⟨206113619707859178598435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1099272638441915619191653 206113619707859178598435)
              ·
                refine ⟨309170429561788767897653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206113619707859178598435 309170429561788767897653)
                ·
                  refine ⟨28984727771417696990405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 309170429561788767897653 28984727771417696990405)
                  ·
                    rfl

theorem cell21_127007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_127007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127007 prefixEnd_127007 := by exact prefixLift 127007
  have htrace : WordTrace (prefixWord ++ tailWord_127007) baseStart_127007 baseEnd_127007 := by
    simpa [prefixWord, tailWord_127007, baseEnd_127007] using wordTrace_append hprefix tailTrace_127007
  have hstable : (prefixWord ++ tailWord_127007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127007).length < 2 ^ (prefixWord ++ tailWord_127007).sum := by decide
  have hdescent : baseEnd_127007 < baseStart_127007 := by decide
  rcases family_descends (prefixWord ++ tailWord_127007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127035 : List Nat := [1, 1, 1, 1, 1, 2, 1, 13]
def baseStart_127035 : Nat := 118140960795 + 127035 * 2 ^ 59
def prefixEnd_127035 : Nat := 4983230072969 + 3 ^ 40 * 127035 * 2
def baseEnd_127035 : Nat := 9663705917631956841227

theorem tailTrace_127035 : CollatzResearch.WordTrace tailWord_127035 prefixEnd_127035 9663705917631956841227 := by
  unfold tailWord_127035
  simp only [CollatzResearch.WordTrace]
  refine ⟨4633347094781365695814559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3088898063187577130543039 4633347094781365695814559)
  ·
    refine ⟨6950020642172048543721839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4633347094781365695814559 6950020642172048543721839)
    ·
      refine ⟨10425030963258072815582759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6950020642172048543721839 10425030963258072815582759)
      ·
        refine ⟨15637546444887109223374139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10425030963258072815582759 15637546444887109223374139)
        ·
          refine ⟨23456319667330663835061209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15637546444887109223374139 23456319667330663835061209)
          ·
            refine ⟨17592239750497997876295907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23456319667330663835061209 17592239750497997876295907)
            ·
              refine ⟨26388359625746996814443861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17592239750497997876295907 26388359625746996814443861)
              ·
                refine ⟨9663705917631956841227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 26388359625746996814443861 9663705917631956841227)
                ·
                  rfl

theorem cell21_127035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 13].length) (baseStart_127035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127035 prefixEnd_127035 := by exact prefixLift 127035
  have htrace : WordTrace (prefixWord ++ tailWord_127035) baseStart_127035 baseEnd_127035 := by
    simpa [prefixWord, tailWord_127035, baseEnd_127035] using wordTrace_append hprefix tailTrace_127035
  have hstable : (prefixWord ++ tailWord_127035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127035).length < 2 ^ (prefixWord ++ tailWord_127035).sum := by decide
  have hdescent : baseEnd_127035 < baseStart_127035 := by decide
  rcases family_descends (prefixWord ++ tailWord_127035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127041 : List Nat := [1, 2, 5, 1, 2, 1, 3, 3, 3]
def baseStart_127041 : Nat := 118140960795 + 127041 * 2 ^ 59
def prefixEnd_127041 : Nat := 4983230072969 + 3 ^ 40 * 127041 * 2
def baseEnd_127041 : Nat := 28992487034641193423669

theorem tailTrace_127041 : CollatzResearch.WordTrace tailWord_127041 prefixEnd_127041 28992487034641193423669 := by
  unfold tailWord_127041
  simp only [CollatzResearch.WordTrace]
  refine ⟨4633565932759628720532977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3089043955173085813688651 4633565932759628720532977)
  ·
    refine ⟨3475174449569721540399733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4633565932759628720532977 3475174449569721540399733)
    ·
      refine ⟨325797604647161394412475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3475174449569721540399733 325797604647161394412475)
      ·
        refine ⟨488696406970742091618713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325797604647161394412475 488696406970742091618713)
        ·
          refine ⟨366522305228056568714035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488696406970742091618713 366522305228056568714035)
          ·
            refine ⟨549783457842084853071053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366522305228056568714035 549783457842084853071053)
            ·
              refine ⟨206168796690781819901645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549783457842084853071053 206168796690781819901645)
              ·
                refine ⟨77313298759043182463117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206168796690781819901645 77313298759043182463117)
                ·
                  refine ⟨28992487034641193423669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77313298759043182463117 28992487034641193423669)
                  ·
                    rfl

theorem cell21_127041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_127041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127041 prefixEnd_127041 := by exact prefixLift 127041
  have htrace : WordTrace (prefixWord ++ tailWord_127041) baseStart_127041 baseEnd_127041 := by
    simpa [prefixWord, tailWord_127041, baseEnd_127041] using wordTrace_append hprefix tailTrace_127041
  have hstable : (prefixWord ++ tailWord_127041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127041).length < 2 ^ (prefixWord ++ tailWord_127041).sum := by decide
  have hdescent : baseEnd_127041 < baseStart_127041 := by decide
  rcases family_descends (prefixWord ++ tailWord_127041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127058 : List Nat := [3, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_127058 : Nat := 118140960795 + 127058 * 2 ^ 59
def prefixEnd_127058 : Nat := 4983230072969 + 3 ^ 40 * 127058 * 2
def baseEnd_127058 : Nat := 28996366666252941640301

theorem tailTrace_127058 : CollatzResearch.WordTrace tailWord_127058 prefixEnd_127058 28996366666252941640301 := by
  unfold tailWord_127058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158546493424510155975457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3089457315798693749267885 1158546493424510155975457)
  ·
    refine ⟨868909870068382616981593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1158546493424510155975457 868909870068382616981593)
    ·
      refine ⟨651682402551286962736195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 868909870068382616981593 651682402551286962736195)
      ·
        refine ⟨977523603826930444104293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651682402551286962736195 977523603826930444104293)
        ·
          refine ⟨183285675717549458269555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 977523603826930444104293 183285675717549458269555)
          ·
            refine ⟨274928513576324187404333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183285675717549458269555 274928513576324187404333)
            ·
              refine ⟨103098192591121570276625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274928513576324187404333 103098192591121570276625)
              ·
                refine ⟨77323644443341177707469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103098192591121570276625 77323644443341177707469)
                ·
                  refine ⟨28996366666252941640301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77323644443341177707469 28996366666252941640301)
                  ·
                    rfl

theorem cell21_127058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_127058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127058 prefixEnd_127058 := by exact prefixLift 127058
  have htrace : WordTrace (prefixWord ++ tailWord_127058) baseStart_127058 baseEnd_127058 := by
    simpa [prefixWord, tailWord_127058, baseEnd_127058] using wordTrace_append hprefix tailTrace_127058
  have hstable : (prefixWord ++ tailWord_127058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127058).length < 2 ^ (prefixWord ++ tailWord_127058).sum := by decide
  have hdescent : baseEnd_127058 < baseStart_127058 := by decide
  rcases family_descends (prefixWord ++ tailWord_127058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127069 : List Nat := [1, 4, 4, 1, 1, 1, 1, 8]
def baseStart_127069 : Nat := 118140960795 + 127069 * 2 ^ 59
def prefixEnd_127069 : Nat := 4983230072969 + 3 ^ 40 * 127069 * 2
def baseEnd_127069 : Nat := 9666292338706455652315

theorem tailTrace_127069 : CollatzResearch.WordTrace tailWord_127069 prefixEnd_127069 9666292338706455652315 := by
  unfold tailWord_127069
  simp only [CollatzResearch.WordTrace]
  refine ⟨4634587176658189502552261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3089724784438793001701507 4634587176658189502552261)
  ·
    refine ⟨868985095623410531728549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4634587176658189502552261 868985095623410531728549)
    ·
      refine ⟨162934705429389474699103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 868985095623410531728549 162934705429389474699103)
      ·
        refine ⟨244402058144084212048655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162934705429389474699103 244402058144084212048655)
        ·
          refine ⟨366603087216126318072983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244402058144084212048655 366603087216126318072983)
          ·
            refine ⟨549904630824189477109475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366603087216126318072983 549904630824189477109475)
            ·
              refine ⟨824856946236284215664213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549904630824189477109475 824856946236284215664213)
              ·
                refine ⟨9666292338706455652315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 824856946236284215664213 9666292338706455652315)
                ·
                  rfl

theorem cell21_127069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 8].length) (baseStart_127069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127069 prefixEnd_127069 := by exact prefixLift 127069
  have htrace : WordTrace (prefixWord ++ tailWord_127069) baseStart_127069 baseEnd_127069 := by
    simpa [prefixWord, tailWord_127069, baseEnd_127069] using wordTrace_append hprefix tailTrace_127069
  have hstable : (prefixWord ++ tailWord_127069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127069).length < 2 ^ (prefixWord ++ tailWord_127069).sum := by decide
  have hdescent : baseEnd_127069 < baseStart_127069 := by decide
  rcases family_descends (prefixWord ++ tailWord_127069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127114 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_127114 : Nat := 118140960795 + 127114 * 2 ^ 59
def prefixEnd_127114 : Nat := 4983230072969 + 3 ^ 40 * 127114 * 2
def baseEnd_127114 : Nat := 29009146629209288706853

theorem tailTrace_127114 : CollatzResearch.WordTrace tailWord_127114 prefixEnd_127114 29009146629209288706853 := by
  unfold tailWord_127114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159057115373790546985099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3090818974330108125293597 1159057115373790546985099)
  ·
    refine ⟨1738585673060685820477649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1159057115373790546985099 1738585673060685820477649)
    ·
      refine ⟨1303939254795514365358237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1738585673060685820477649 1303939254795514365358237)
      ·
        refine ⟨488977220548317887009339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1303939254795514365358237 488977220548317887009339)
        ·
          refine ⟨733465830822476830514009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488977220548317887009339 733465830822476830514009)
          ·
            refine ⟨550099373116857622885507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733465830822476830514009 550099373116857622885507)
            ·
              refine ⟨825149059675286434328261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550099373116857622885507 825149059675286434328261)
              ·
                refine ⟨154715448689116206436549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 825149059675286434328261 154715448689116206436549)
                ·
                  refine ⟨29009146629209288706853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154715448689116206436549 29009146629209288706853)
                  ·
                    rfl

theorem cell21_127114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_127114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127114 prefixEnd_127114 := by exact prefixLift 127114
  have htrace : WordTrace (prefixWord ++ tailWord_127114) baseStart_127114 baseEnd_127114 := by
    simpa [prefixWord, tailWord_127114, baseEnd_127114] using wordTrace_append hprefix tailTrace_127114
  have hstable : (prefixWord ++ tailWord_127114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127114).length < 2 ^ (prefixWord ++ tailWord_127114).sum := by decide
  have hdescent : baseEnd_127114 < baseStart_127114 := by decide
  rcases family_descends (prefixWord ++ tailWord_127114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127196 : List Nat := [2, 2, 5, 2, 2, 1, 2, 5]
def baseStart_127196 : Nat := 118140960795 + 127196 * 2 ^ 59
def prefixEnd_127196 : Nat := 4983230072969 + 3 ^ 40 * 127196 * 2
def baseEnd_127196 : Nat := 9675953382131789446673

theorem tailTrace_127196 : CollatzResearch.WordTrace tailWord_127196 prefixEnd_127196 9675953382131789446673 := by
  unfold tailWord_127196
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319609623599045096212721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3092812831465393461616961 2319609623599045096212721)
  ·
    refine ⟨1739707217699283822159541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2319609623599045096212721 1739707217699283822159541)
    ·
      refine ⟨163097551659307858327457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1739707217699283822159541 163097551659307858327457)
      ·
        refine ⟨122323163744480893745593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163097551659307858327457 122323163744480893745593)
        ·
          refine ⟨91742372808360670309195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122323163744480893745593 91742372808360670309195)
          ·
            refine ⟨137613559212541005463793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91742372808360670309195 137613559212541005463793)
            ·
              refine ⟨103210169409405754097845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137613559212541005463793 103210169409405754097845)
              ·
                refine ⟨9675953382131789446673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103210169409405754097845 9675953382131789446673)
                ·
                  rfl

theorem cell21_127196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_127196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127196 prefixEnd_127196 := by exact prefixLift 127196
  have htrace : WordTrace (prefixWord ++ tailWord_127196) baseStart_127196 baseEnd_127196 := by
    simpa [prefixWord, tailWord_127196, baseEnd_127196] using wordTrace_append hprefix tailTrace_127196
  have hstable : (prefixWord ++ tailWord_127196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127196).length < 2 ^ (prefixWord ++ tailWord_127196).sum := by decide
  have hdescent : baseEnd_127196 < baseStart_127196 := by decide
  rcases family_descends (prefixWord ++ tailWord_127196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127415 : List Nat := [1, 1, 3, 1, 3, 3, 1, 8]
def baseStart_127415 : Nat := 118140960795 + 127415 * 2 ^ 59
def prefixEnd_127415 : Nat := 4983230072969 + 3 ^ 40 * 127415 * 2
def baseEnd_127415 : Nat := 9692612976699884729857

theorem tailTrace_127415 : CollatzResearch.WordTrace tailWord_127415 prefixEnd_127415 9692612976699884729857 := by
  unfold tailWord_127415
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647206833404690594647699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3098137888936460396431799 4647206833404690594647699)
  ·
    refine ⟨6970810250107035891971549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4647206833404690594647699 6970810250107035891971549)
    ·
      refine ⟨2614053843790138459489331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6970810250107035891971549 2614053843790138459489331)
      ·
        refine ⟨3921080765685207689233997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2614053843790138459489331 3921080765685207689233997)
        ·
          refine ⟨1470405287131952883462749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3921080765685207689233997 1470405287131952883462749)
          ·
            refine ⟨551401982674482331298531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1470405287131952883462749 551401982674482331298531)
            ·
              refine ⟨827102974011723496947797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551401982674482331298531 827102974011723496947797)
              ·
                refine ⟨9692612976699884729857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 827102974011723496947797 9692612976699884729857)
                ·
                  rfl

theorem cell21_127415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 8].length) (baseStart_127415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127415 prefixEnd_127415 := by exact prefixLift 127415
  have htrace : WordTrace (prefixWord ++ tailWord_127415) baseStart_127415 baseEnd_127415 := by
    simpa [prefixWord, tailWord_127415, baseEnd_127415] using wordTrace_append hprefix tailTrace_127415
  have hstable : (prefixWord ++ tailWord_127415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127415).length < 2 ^ (prefixWord ++ tailWord_127415).sum := by decide
  have hdescent : baseEnd_127415 < baseStart_127415 := by decide
  rcases family_descends (prefixWord ++ tailWord_127415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127542 : List Nat := [5, 1, 2, 1, 2, 3, 2, 5]
def baseStart_127542 : Nat := 118140960795 + 127542 * 2 ^ 59
def prefixEnd_127542 : Nat := 4983230072969 + 3 ^ 40 * 127542 * 2
def baseEnd_127542 : Nat := 9702274020125218524215

theorem tailTrace_127542 : CollatzResearch.WordTrace tailWord_127542 prefixEnd_127542 9702274020125218524215 := by
  unfold tailWord_127542
  simp only [CollatzResearch.WordTrace]
  refine ⟨290739931496536955282555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3101225935963060856347253 290739931496536955282555)
  ·
    refine ⟨436109897244805432923833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290739931496536955282555 436109897244805432923833)
    ·
      refine ⟨327082422933604074692875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436109897244805432923833 327082422933604074692875)
      ·
        refine ⟨490623634400406112039313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327082422933604074692875 490623634400406112039313)
        ·
          refine ⟨367967725800304584029485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 490623634400406112039313 367967725800304584029485)
          ·
            refine ⟨137987897175114219011057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367967725800304584029485 137987897175114219011057)
            ·
              refine ⟨103490922881335664258293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137987897175114219011057 103490922881335664258293)
              ·
                refine ⟨9702274020125218524215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103490922881335664258293 9702274020125218524215)
                ·
                  rfl

theorem cell21_127542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_127542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127542 prefixEnd_127542 := by exact prefixLift 127542
  have htrace : WordTrace (prefixWord ++ tailWord_127542) baseStart_127542 baseEnd_127542 := by
    simpa [prefixWord, tailWord_127542, baseEnd_127542] using wordTrace_append hprefix tailTrace_127542
  have hstable : (prefixWord ++ tailWord_127542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127542).length < 2 ^ (prefixWord ++ tailWord_127542).sum := by decide
  have hdescent : baseEnd_127542 < baseStart_127542 := by decide
  rcases family_descends (prefixWord ++ tailWord_127542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127553 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 6]
def baseStart_127553 : Nat := 118140960795 + 127553 * 2 ^ 59
def prefixEnd_127553 : Nat := 4983230072969 + 3 ^ 40 * 127553 * 2
def baseEnd_127553 : Nat := 29109332410242080889289

theorem tailTrace_127553 : CollatzResearch.WordTrace tailWord_127553 prefixEnd_127553 29109332410242080889289 := by
  unfold tailWord_127553
  simp only [CollatzResearch.WordTrace]
  refine ⟨4652240106904740163171313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3101493404603160108780875 4652240106904740163171313)
  ·
    refine ⟨3489180080178555122378485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4652240106904740163171313 3489180080178555122378485)
    ·
      refine ⟨327110632516739542722983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3489180080178555122378485 327110632516739542722983)
      ·
        refine ⟨490665948775109314084475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327110632516739542722983 490665948775109314084475)
        ·
          refine ⟨735998923162663971126713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490665948775109314084475 735998923162663971126713)
          ·
            refine ⟨551999192371997978345035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735998923162663971126713 551999192371997978345035)
            ·
              refine ⟨827998788557996967517553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551999192371997978345035 827998788557996967517553)
              ·
                refine ⟨620999091418497725638165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827998788557996967517553 620999091418497725638165)
                ·
                  refine ⟨29109332410242080889289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 620999091418497725638165 29109332410242080889289)
                  ·
                    rfl

theorem cell21_127553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_127553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127553 prefixEnd_127553 := by exact prefixLift 127553
  have htrace : WordTrace (prefixWord ++ tailWord_127553) baseStart_127553 baseEnd_127553 := by
    simpa [prefixWord, tailWord_127553, baseEnd_127553] using wordTrace_append hprefix tailTrace_127553
  have hstable : (prefixWord ++ tailWord_127553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127553).length < 2 ^ (prefixWord ++ tailWord_127553).sum := by decide
  have hdescent : baseEnd_127553 < baseStart_127553 := by decide
  rcases family_descends (prefixWord ++ tailWord_127553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127612 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_127612 : Nat := 118140960795 + 127612 * 2 ^ 59
def prefixEnd_127612 : Nat := 4983230072969 + 3 ^ 40 * 127612 * 2
def baseEnd_127612 : Nat := 29122797014071089405835

theorem tailTrace_127612 : CollatzResearch.WordTrace tailWord_127612 prefixEnd_127612 29122797014071089405835 := by
  unfold tailWord_127612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327196006845496619784545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3102928009127328826379393 2327196006845496619784545)
  ·
    refine ⟨1745397005134122464838409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2327196006845496619784545 1745397005134122464838409)
    ·
      refine ⟨1309047753850591848628807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1745397005134122464838409 1309047753850591848628807)
      ·
        refine ⟨1963571630775887772943211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1309047753850591848628807 1963571630775887772943211)
        ·
          refine ⟨2945357446163831659414817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963571630775887772943211 2945357446163831659414817)
          ·
            refine ⟨2209018084622873744561113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2945357446163831659414817 2209018084622873744561113)
            ·
              refine ⟨1656763563467155308420835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209018084622873744561113 1656763563467155308420835)
              ·
                refine ⟨2485145345200732962631253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656763563467155308420835 2485145345200732962631253)
                ·
                  refine ⟨29122797014071089405835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2485145345200732962631253 29122797014071089405835)
                  ·
                    rfl

theorem cell21_127612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_127612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127612 prefixEnd_127612 := by exact prefixLift 127612
  have htrace : WordTrace (prefixWord ++ tailWord_127612) baseStart_127612 baseEnd_127612 := by
    simpa [prefixWord, tailWord_127612, baseEnd_127612] using wordTrace_append hprefix tailTrace_127612
  have hstable : (prefixWord ++ tailWord_127612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127612).length < 2 ^ (prefixWord ++ tailWord_127612).sum := by decide
  have hdescent : baseEnd_127612 < baseStart_127612 := by decide
  rcases family_descends (prefixWord ++ tailWord_127612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127618 : List Nat := [3, 4, 3, 1, 1, 9]
def baseStart_127618 : Nat := 118140960795 + 127618 * 2 ^ 59
def prefixEnd_127618 : Nat := 4983230072969 + 3 ^ 40 * 127618 * 2
def baseEnd_127618 : Nat := 1078672825770978233549

theorem tailTrace_127618 : CollatzResearch.WordTrace tailWord_127618 prefixEnd_127618 1078672825770978233549 := by
  unfold tailWord_127618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163652712917314066071877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3103073901112837509525005 1163652712917314066071877)
  ·
    refine ⟨218184883671996387388477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1163652712917314066071877 218184883671996387388477)
    ·
      refine ⟨81819331376998645270679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218184883671996387388477 81819331376998645270679)
      ·
        refine ⟨122728997065497967906019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81819331376998645270679 122728997065497967906019)
        ·
          refine ⟨184093495598246951859029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122728997065497967906019 184093495598246951859029)
          ·
            refine ⟨1078672825770978233549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 184093495598246951859029 1078672825770978233549)
            ·
              rfl

theorem cell21_127618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 9].length) (baseStart_127618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127618 prefixEnd_127618 := by exact prefixLift 127618
  have htrace : WordTrace (prefixWord ++ tailWord_127618) baseStart_127618 baseEnd_127618 := by
    simpa [prefixWord, tailWord_127618, baseEnd_127618] using wordTrace_append hprefix tailTrace_127618
  have hstable : (prefixWord ++ tailWord_127618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127618).length < 2 ^ (prefixWord ++ tailWord_127618).sum := by decide
  have hdescent : baseEnd_127618 < baseStart_127618 := by decide
  rcases family_descends (prefixWord ++ tailWord_127618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127646 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_127646 : Nat := 118140960795 + 127646 * 2 ^ 59
def prefixEnd_127646 : Nat := 4983230072969 + 3 ^ 40 * 127646 * 2
def baseEnd_127646 : Nat := 29130556277294585839099

theorem tailTrace_127646 : CollatzResearch.WordTrace tailWord_127646 prefixEnd_127646 29130556277294585839099 := by
  unfold tailWord_127646
  simp only [CollatzResearch.WordTrace]
  refine ⟨581954011945977130788349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3103754730378544697537861 581954011945977130788349)
  ·
    refine ⟨218232754479741424045631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 581954011945977130788349 218232754479741424045631)
    ·
      refine ⟨327349131719612136068447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218232754479741424045631 327349131719612136068447)
      ·
        refine ⟨491023697579418204102671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327349131719612136068447 491023697579418204102671)
        ·
          refine ⟨736535546369127306154007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491023697579418204102671 736535546369127306154007)
          ·
            refine ⟨1104803319553690959231011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736535546369127306154007 1104803319553690959231011)
            ·
              refine ⟨1657204979330536438846517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104803319553690959231011 1657204979330536438846517)
              ·
                refine ⟨155362966812237791141861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1657204979330536438846517 155362966812237791141861)
                ·
                  refine ⟨29130556277294585839099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155362966812237791141861 29130556277294585839099)
                  ·
                    rfl

theorem cell21_127646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_127646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127646 prefixEnd_127646 := by exact prefixLift 127646
  have htrace : WordTrace (prefixWord ++ tailWord_127646) baseStart_127646 baseEnd_127646 := by
    simpa [prefixWord, tailWord_127646, baseEnd_127646] using wordTrace_append hprefix tailTrace_127646
  have hstable : (prefixWord ++ tailWord_127646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127646).length < 2 ^ (prefixWord ++ tailWord_127646).sum := by decide
  have hdescent : baseEnd_127646 < baseStart_127646 := by decide
  rcases family_descends (prefixWord ++ tailWord_127646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127657 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 7]
def baseStart_127657 : Nat := 118140960795 + 127657 * 2 ^ 59
def prefixEnd_127657 : Nat := 4983230072969 + 3 ^ 40 * 127657 * 2
def baseEnd_127657 : Nat := 29133066627161011155743

theorem tailTrace_127657 : CollatzResearch.WordTrace tailWord_127657 prefixEnd_127657 29133066627161011155743 := by
  unfold tailWord_127657
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656033298527965924957225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3104022199018643949971483 4656033298527965924957225)
  ·
    refine ⟨3492024973895974443717919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4656033298527965924957225 3492024973895974443717919)
    ·
      refine ⟨5238037460843961665576879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3492024973895974443717919 5238037460843961665576879)
      ·
        refine ⟨7857056191265942498365319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238037460843961665576879 7857056191265942498365319)
        ·
          refine ⟨11785584286898913747547979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857056191265942498365319 11785584286898913747547979)
          ·
            refine ⟨17678376430348370621321969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11785584286898913747547979 17678376430348370621321969)
            ·
              refine ⟨13258782322761277965991477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17678376430348370621321969 13258782322761277965991477)
              ·
                refine ⟨1243010842758869809311701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13258782322761277965991477 1243010842758869809311701)
                ·
                  refine ⟨29133066627161011155743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1243010842758869809311701 29133066627161011155743)
                  ·
                    rfl

theorem cell21_127657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_127657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127657 prefixEnd_127657 := by exact prefixLift 127657
  have htrace : WordTrace (prefixWord ++ tailWord_127657) baseStart_127657 baseEnd_127657 := by
    simpa [prefixWord, tailWord_127657, baseEnd_127657] using wordTrace_append hprefix tailTrace_127657
  have hstable : (prefixWord ++ tailWord_127657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127657).length < 2 ^ (prefixWord ++ tailWord_127657).sum := by decide
  have hdescent : baseEnd_127657 < baseStart_127657 := by decide
  rcases family_descends (prefixWord ++ tailWord_127657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127826 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_127826 : Nat := 118140960795 + 127826 * 2 ^ 59
def prefixEnd_127826 : Nat := 4983230072969 + 3 ^ 40 * 127826 * 2
def baseEnd_127826 : Nat := 29171634729654272838731

theorem tailTrace_127826 : CollatzResearch.WordTrace tailWord_127826 prefixEnd_127826 29171634729654272838731 := by
  unfold tailWord_127826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165549308728926946964833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3108131489943805191906221 1165549308728926946964833)
  ·
    refine ⟨874161981546695210223625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1165549308728926946964833 874161981546695210223625)
    ·
      refine ⟨655621486160021407667719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 874161981546695210223625 655621486160021407667719)
      ·
        refine ⟨983432229240032111501579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655621486160021407667719 983432229240032111501579)
        ·
          refine ⟨1475148343860048167252369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983432229240032111501579 1475148343860048167252369)
          ·
            refine ⟨1106361257895036125439277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1475148343860048167252369 1106361257895036125439277)
            ·
              refine ⟨414885471710638547039729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1106361257895036125439277 414885471710638547039729)
              ·
                refine ⟨311164103782978910279797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414885471710638547039729 311164103782978910279797)
                ·
                  refine ⟨29171634729654272838731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311164103782978910279797 29171634729654272838731)
                  ·
                    rfl

theorem cell21_127826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_127826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127826 prefixEnd_127826 := by exact prefixLift 127826
  have htrace : WordTrace (prefixWord ++ tailWord_127826) baseStart_127826 baseEnd_127826 := by
    simpa [prefixWord, tailWord_127826, baseEnd_127826] using wordTrace_append hprefix tailTrace_127826
  have hstable : (prefixWord ++ tailWord_127826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127826).length < 2 ^ (prefixWord ++ tailWord_127826).sum := by decide
  have hdescent : baseEnd_127826 < baseStart_127826 := by decide
  rcases family_descends (prefixWord ++ tailWord_127826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127840 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_127840 : Nat := 118140960795 + 127840 * 2 ^ 59
def prefixEnd_127840 : Nat := 4983230072969 + 3 ^ 40 * 127840 * 2
def baseEnd_127840 : Nat := 29174829720393359605369

theorem tailTrace_127840 : CollatzResearch.WordTrace tailWord_127840 prefixEnd_127840 29174829720393359605369 := by
  unfold tailWord_127840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2331353928432494089434487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3108471904576658785912649 2331353928432494089434487)
  ·
    refine ⟨3497030892648741134151731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2331353928432494089434487 3497030892648741134151731)
    ·
      refine ⟨5245546338973111701227597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3497030892648741134151731 5245546338973111701227597)
      ·
        refine ⟨1967079877114916887960349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5245546338973111701227597 1967079877114916887960349)
        ·
          refine ⟨737654953918093832985131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1967079877114916887960349 737654953918093832985131)
          ·
            refine ⟨1106482430877140749477697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737654953918093832985131 1106482430877140749477697)
            ·
              refine ⟨829861823157855562108273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106482430877140749477697 829861823157855562108273)
              ·
                refine ⟨622396367368391671581205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829861823157855562108273 622396367368391671581205)
                ·
                  refine ⟨29174829720393359605369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 622396367368391671581205 29174829720393359605369)
                  ·
                    rfl

theorem cell21_127840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_127840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127840 prefixEnd_127840 := by exact prefixLift 127840
  have htrace : WordTrace (prefixWord ++ tailWord_127840) baseStart_127840 baseEnd_127840 := by
    simpa [prefixWord, tailWord_127840, baseEnd_127840] using wordTrace_append hprefix tailTrace_127840
  have hstable : (prefixWord ++ tailWord_127840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127840).length < 2 ^ (prefixWord ++ tailWord_127840).sum := by decide
  have hdescent : baseEnd_127840 < baseStart_127840 := by decide
  rcases family_descends (prefixWord ++ tailWord_127840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127843 : List Nat := [1, 1, 1, 5, 3, 1, 1, 5, 3]
def baseStart_127843 : Nat := 118140960795 + 127843 * 2 ^ 59
def prefixEnd_127843 : Nat := 4983230072969 + 3 ^ 40 * 127843 * 2
def baseEnd_127843 : Nat := 29175514361266021055363

theorem tailTrace_127843 : CollatzResearch.WordTrace tailWord_127843 prefixEnd_127843 29175514361266021055363 := by
  unfold tailWord_127843
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662817275854119691228183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3108544850569413127485455 4662817275854119691228183)
  ·
    refine ⟨6994225913781179536842275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4662817275854119691228183 6994225913781179536842275)
    ·
      refine ⟨10491338870671769305263413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6994225913781179536842275 10491338870671769305263413)
      ·
        refine ⟨983563019125478372368445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10491338870671769305263413 983563019125478372368445)
        ·
          refine ⟨368836132172054389638167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 983563019125478372368445 368836132172054389638167)
          ·
            refine ⟨553254198258081584457251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368836132172054389638167 553254198258081584457251)
            ·
              refine ⟨829881297387122376685877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553254198258081584457251 829881297387122376685877)
              ·
                refine ⟨77801371630042722814301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 829881297387122376685877 77801371630042722814301)
                ·
                  refine ⟨29175514361266021055363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77801371630042722814301 29175514361266021055363)
                  ·
                    rfl

theorem cell21_127843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 3].length) (baseStart_127843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127843 prefixEnd_127843 := by exact prefixLift 127843
  have htrace : WordTrace (prefixWord ++ tailWord_127843) baseStart_127843 baseEnd_127843 := by
    simpa [prefixWord, tailWord_127843, baseEnd_127843] using wordTrace_append hprefix tailTrace_127843
  have hstable : (prefixWord ++ tailWord_127843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127843).length < 2 ^ (prefixWord ++ tailWord_127843).sum := by decide
  have hdescent : baseEnd_127843 < baseStart_127843 := by decide
  rcases family_descends (prefixWord ++ tailWord_127843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127857 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 4]
def baseStart_127857 : Nat := 118140960795 + 127857 * 2 ^ 59
def prefixEnd_127857 : Nat := 4983230072969 + 3 ^ 40 * 127857 * 2
def baseEnd_127857 : Nat := 29178709352005107822001

theorem tailTrace_127857 : CollatzResearch.WordTrace tailWord_127857 prefixEnd_127857 29178709352005107822001 := by
  unfold tailWord_127857
  simp only [CollatzResearch.WordTrace]
  refine ⟨4663327897803400082237825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3108885265202266721491883 4663327897803400082237825)
  ·
    refine ⟨3497495923352550061678369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4663327897803400082237825 3497495923352550061678369)
    ·
      refine ⟨2623121942514412546258777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3497495923352550061678369 2623121942514412546258777)
      ·
        refine ⟨1967341456885809409694083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2623121942514412546258777 1967341456885809409694083)
        ·
          refine ⟨2951012185328714114541125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967341456885809409694083 2951012185328714114541125)
          ·
            refine ⟨553314784749133896476461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2951012185328714114541125 553314784749133896476461)
            ·
              refine ⟨207493044280925211178673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553314784749133896476461 207493044280925211178673)
              ·
                refine ⟨155619783210693908384005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207493044280925211178673 155619783210693908384005)
                ·
                  refine ⟨29178709352005107822001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155619783210693908384005 29178709352005107822001)
                  ·
                    rfl

theorem cell21_127857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_127857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127857 prefixEnd_127857 := by exact prefixLift 127857
  have htrace : WordTrace (prefixWord ++ tailWord_127857) baseStart_127857 baseEnd_127857 := by
    simpa [prefixWord, tailWord_127857, baseEnd_127857] using wordTrace_append hprefix tailTrace_127857
  have hstable : (prefixWord ++ tailWord_127857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127857).length < 2 ^ (prefixWord ++ tailWord_127857).sum := by decide
  have hdescent : baseEnd_127857 < baseStart_127857 := by decide
  rcases family_descends (prefixWord ++ tailWord_127857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127894 : List Nat := [5, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_127894 : Nat := 118140960795 + 127894 * 2 ^ 59
def prefixEnd_127894 : Nat := 4983230072969 + 3 ^ 40 * 127894 * 2
def baseEnd_127894 : Nat := 29187153256101265705259

theorem tailTrace_127894 : CollatzResearch.WordTrace tailWord_127894 prefixEnd_127894 29187153256101265705259 := by
  unfold tailWord_127894
  simp only [CollatzResearch.WordTrace]
  refine ⟨291542337416834712583421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3109784932446236934223157 291542337416834712583421)
  ·
    refine ⟨109328376531313017218783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291542337416834712583421 109328376531313017218783)
    ·
      refine ⟨163992564796969525828175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109328376531313017218783 163992564796969525828175)
      ·
        refine ⟨245988847195454288742263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163992564796969525828175 245988847195454288742263)
        ·
          refine ⟨368983270793181433113395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245988847195454288742263 368983270793181433113395)
          ·
            refine ⟨553474906189772149670093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368983270793181433113395 553474906189772149670093)
            ·
              refine ⟨207553089821164556126285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553474906189772149670093 207553089821164556126285)
              ·
                refine ⟨77832408682936708547357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207553089821164556126285 77832408682936708547357)
                ·
                  refine ⟨29187153256101265705259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77832408682936708547357 29187153256101265705259)
                  ·
                    rfl

theorem cell21_127894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_127894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127894 prefixEnd_127894 := by exact prefixLift 127894
  have htrace : WordTrace (prefixWord ++ tailWord_127894) baseStart_127894 baseEnd_127894 := by
    simpa [prefixWord, tailWord_127894, baseEnd_127894] using wordTrace_append hprefix tailTrace_127894
  have hstable : (prefixWord ++ tailWord_127894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127894).length < 2 ^ (prefixWord ++ tailWord_127894).sum := by decide
  have hdescent : baseEnd_127894 < baseStart_127894 := by decide
  rcases family_descends (prefixWord ++ tailWord_127894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127970 : List Nat := [3, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_127970 : Nat := 118140960795 + 127970 * 2 ^ 59
def prefixEnd_127970 : Nat := 4983230072969 + 3 ^ 40 * 127970 * 2
def baseEnd_127970 : Nat := 29204497491542022438437

theorem tailTrace_127970 : CollatzResearch.WordTrace tailWord_127970 prefixEnd_127970 29204497491542022438437 := by
  unfold tailWord_127970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166862336598505095275341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3111632897596013587400909 1166862336598505095275341)
  ·
    refine ⟨437573376224439410728253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1166862336598505095275341 437573376224439410728253)
    ·
      refine ⟨164090016084164779023095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437573376224439410728253 164090016084164779023095)
      ·
        refine ⟨246135024126247168534643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164090016084164779023095 246135024126247168534643)
        ·
          refine ⟨369202536189370752801965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246135024126247168534643 369202536189370752801965)
          ·
            refine ⟨138450951071014032300737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369202536189370752801965 138450951071014032300737)
            ·
              refine ⟨103838213303260524225553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138450951071014032300737 103838213303260524225553)
              ·
                refine ⟨77878659977445393169165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103838213303260524225553 77878659977445393169165)
                ·
                  refine ⟨29204497491542022438437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77878659977445393169165 29204497491542022438437)
                  ·
                    rfl

theorem cell21_127970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_127970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_127970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_127970 prefixEnd_127970 := by exact prefixLift 127970
  have htrace : WordTrace (prefixWord ++ tailWord_127970) baseStart_127970 baseEnd_127970 := by
    simpa [prefixWord, tailWord_127970, baseEnd_127970] using wordTrace_append hprefix tailTrace_127970
  have hstable : (prefixWord ++ tailWord_127970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127970).length < 2 ^ (prefixWord ++ tailWord_127970).sum := by decide
  have hdescent : baseEnd_127970 < baseStart_127970 := by decide
  rcases family_descends (prefixWord ++ tailWord_127970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128023 : List Nat := [1, 1, 3, 5, 1, 2, 8]
def baseStart_128023 : Nat := 118140960795 + 128023 * 2 ^ 59
def prefixEnd_128023 : Nat := 4983230072969 + 3 ^ 40 * 128023 * 2
def baseEnd_128023 : Nat := 3246288090402856450555

theorem tailTrace_128023 : CollatzResearch.WordTrace tailWord_128023 prefixEnd_128023 3246288090402856450555 := by
  unfold tailWord_128023
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669382415202010432780723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3112921610134673621853815 4669382415202010432780723)
  ·
    refine ⟨7004073622803015649171085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4669382415202010432780723 7004073622803015649171085)
    ·
      refine ⟨2626527608551130868439157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7004073622803015649171085 2626527608551130868439157)
      ·
        refine ⟨246236963301668518916171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2626527608551130868439157 246236963301668518916171)
        ·
          refine ⟨369355444952502778374257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246236963301668518916171 369355444952502778374257)
          ·
            refine ⟨277016583714377083780693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369355444952502778374257 277016583714377083780693)
            ·
              refine ⟨3246288090402856450555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 277016583714377083780693 3246288090402856450555)
              ·
                rfl

theorem cell21_128023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 8].length) (baseStart_128023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128023 prefixEnd_128023 := by exact prefixLift 128023
  have htrace : WordTrace (prefixWord ++ tailWord_128023) baseStart_128023 baseEnd_128023 := by
    simpa [prefixWord, tailWord_128023, baseEnd_128023] using wordTrace_append hprefix tailTrace_128023
  have hstable : (prefixWord ++ tailWord_128023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128023).length < 2 ^ (prefixWord ++ tailWord_128023).sum := by decide
  have hdescent : baseEnd_128023 < baseStart_128023 := by decide
  rcases family_descends (prefixWord ++ tailWord_128023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128071 : List Nat := [1, 1, 4, 1, 3, 2, 3, 3, 3]
def baseStart_128071 : Nat := 118140960795 + 128071 * 2 ^ 59
def prefixEnd_128071 : Nat := 4983230072969 + 3 ^ 40 * 128071 * 2
def baseEnd_128071 : Nat := 29227547067588291254897

theorem tailTrace_128071 : CollatzResearch.WordTrace tailWord_128071 prefixEnd_128071 29227547067588291254897 := by
  unfold tailWord_128071
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671133119028114630528067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3114088746018743087018711 4671133119028114630528067)
  ·
    refine ⟨7006699678542171945792101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4671133119028114630528067 7006699678542171945792101)
    ·
      refine ⟨1313756189726657239836019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7006699678542171945792101 1313756189726657239836019)
      ·
        refine ⟨1970634284589985859754029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313756189726657239836019 1970634284589985859754029)
        ·
          refine ⟨738987856721244697407761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1970634284589985859754029 738987856721244697407761)
          ·
            refine ⟨554240892540933523055821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738987856721244697407761 554240892540933523055821)
            ·
              refine ⟨207840334702850071145933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554240892540933523055821 207840334702850071145933)
              ·
                refine ⟨77940125513568776679725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207840334702850071145933 77940125513568776679725)
                ·
                  refine ⟨29227547067588291254897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77940125513568776679725 29227547067588291254897)
                  ·
                    rfl

theorem cell21_128071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 3].length) (baseStart_128071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128071 prefixEnd_128071 := by exact prefixLift 128071
  have htrace : WordTrace (prefixWord ++ tailWord_128071) baseStart_128071 baseEnd_128071 := by
    simpa [prefixWord, tailWord_128071, baseEnd_128071] using wordTrace_append hprefix tailTrace_128071
  have hstable : (prefixWord ++ tailWord_128071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128071).length < 2 ^ (prefixWord ++ tailWord_128071).sum := by decide
  have hdescent : baseEnd_128071 < baseStart_128071 := by decide
  rcases family_descends (prefixWord ++ tailWord_128071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128147 : List Nat := [1, 1, 1, 2, 1, 2, 8, 2, 3]
def baseStart_128147 : Nat := 118140960795 + 128147 * 2 ^ 59
def prefixEnd_128147 : Nat := 4983230072969 + 3 ^ 40 * 128147 * 2
def baseEnd_128147 : Nat := 29244891303029047988075

theorem tailTrace_128147 : CollatzResearch.WordTrace tailWord_128147 prefixEnd_128147 29244891303029047988075 := by
  unfold tailWord_128147
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673905066752779610294695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3115936711168519740196463 4673905066752779610294695)
  ·
    refine ⟨7010857600129169415442043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4673905066752779610294695 7010857600129169415442043)
    ·
      refine ⟨10516286400193754123163065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7010857600129169415442043 10516286400193754123163065)
      ·
        refine ⟨7887214800145315592372299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10516286400193754123163065 7887214800145315592372299)
        ·
          refine ⟨11830822200217973388558449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7887214800145315592372299 11830822200217973388558449)
          ·
            refine ⟨8873116650163480041418837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11830822200217973388558449 8873116650163480041418837)
            ·
              refine ⟨103981835744103281735377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 8873116650163480041418837 103981835744103281735377)
              ·
                refine ⟨77986376808077461301533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103981835744103281735377 77986376808077461301533)
                ·
                  refine ⟨29244891303029047988075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77986376808077461301533 29244891303029047988075)
                  ·
                    rfl

theorem cell21_128147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 3].length) (baseStart_128147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128147 prefixEnd_128147 := by exact prefixLift 128147
  have htrace : WordTrace (prefixWord ++ tailWord_128147) baseStart_128147 baseEnd_128147 := by
    simpa [prefixWord, tailWord_128147, baseEnd_128147] using wordTrace_append hprefix tailTrace_128147
  have hstable : (prefixWord ++ tailWord_128147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128147).length < 2 ^ (prefixWord ++ tailWord_128147).sum := by decide
  have hdescent : baseEnd_128147 < baseStart_128147 := by decide
  rcases family_descends (prefixWord ++ tailWord_128147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128316 : List Nat := [2, 2, 2, 2, 1, 5, 2, 2, 3]
def baseStart_128316 : Nat := 118140960795 + 128316 * 2 ^ 59
def prefixEnd_128316 : Nat := 4983230072969 + 3 ^ 40 * 128316 * 2
def baseEnd_128316 : Nat := 29283459405522309671063

theorem tailTrace_128316 : CollatzResearch.WordTrace tailWord_128316 prefixEnd_128316 29283459405522309671063 := by
  unfold tailWord_128316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340034501570260736598401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3120046002093680982131201 2340034501570260736598401)
  ·
    refine ⟨1755025876177695552448801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2340034501570260736598401 1755025876177695552448801)
    ·
      refine ⟨1316269407133271664336601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1755025876177695552448801 1316269407133271664336601)
      ·
        refine ⟨987202055349953748252451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316269407133271664336601 987202055349953748252451)
        ·
          refine ⟨1480803083024930622378677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987202055349953748252451 1480803083024930622378677)
          ·
            refine ⟨138825289033587245848001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1480803083024930622378677 138825289033587245848001)
            ·
              refine ⟨104118966775190434386001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138825289033587245848001 104118966775190434386001)
              ·
                refine ⟨78089225081392825789501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104118966775190434386001 78089225081392825789501)
                ·
                  refine ⟨29283459405522309671063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78089225081392825789501 29283459405522309671063)
                  ·
                    rfl

theorem cell21_128316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_128316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128316 prefixEnd_128316 := by exact prefixLift 128316
  have htrace : WordTrace (prefixWord ++ tailWord_128316) baseStart_128316 baseEnd_128316 := by
    simpa [prefixWord, tailWord_128316, baseEnd_128316] using wordTrace_append hprefix tailTrace_128316
  have hstable : (prefixWord ++ tailWord_128316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128316).length < 2 ^ (prefixWord ++ tailWord_128316).sum := by decide
  have hdescent : baseEnd_128316 < baseStart_128316 := by decide
  rcases family_descends (prefixWord ++ tailWord_128316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128327 : List Nat := [1, 1, 4, 1, 2, 5, 1, 6]
def baseStart_128327 : Nat := 118140960795 + 128327 * 2 ^ 59
def prefixEnd_128327 : Nat := 4983230072969 + 3 ^ 40 * 128327 * 2
def baseEnd_128327 : Nat := 9761989918462911662569

theorem tailTrace_128327 : CollatzResearch.WordTrace tailWord_128327 prefixEnd_128327 9761989918462911662569 := by
  unfold tailWord_128327
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680470206100670351847235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3120313470733780234564823 4680470206100670351847235)
  ·
    refine ⟨7020705309151005527770853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4680470206100670351847235 7020705309151005527770853)
    ·
      refine ⟨1316382245465813536457035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7020705309151005527770853 1316382245465813536457035)
      ·
        refine ⟨1974573368198720304685553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316382245465813536457035 1974573368198720304685553)
        ·
          refine ⟨1480930026149040228514165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974573368198720304685553 1480930026149040228514165)
          ·
            refine ⟨138837189951472521423203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1480930026149040228514165 138837189951472521423203)
            ·
              refine ⟨208255784927208782134805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138837189951472521423203 208255784927208782134805)
              ·
                refine ⟨9761989918462911662569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208255784927208782134805 9761989918462911662569)
                ·
                  rfl

theorem cell21_128327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 6].length) (baseStart_128327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128327 prefixEnd_128327 := by exact prefixLift 128327
  have htrace : WordTrace (prefixWord ++ tailWord_128327) baseStart_128327 baseEnd_128327 := by
    simpa [prefixWord, tailWord_128327, baseEnd_128327] using wordTrace_append hprefix tailTrace_128327
  have hstable : (prefixWord ++ tailWord_128327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128327).length < 2 ^ (prefixWord ++ tailWord_128327).sum := by decide
  have hdescent : baseEnd_128327 < baseStart_128327 := by decide
  rcases family_descends (prefixWord ++ tailWord_128327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128341 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 7]
def baseStart_128341 : Nat := 118140960795 + 128341 * 2 ^ 59
def prefixEnd_128341 : Nat := 4983230072969 + 3 ^ 40 * 128341 * 2
def baseEnd_128341 : Nat := 29289164746127821754345

theorem tailTrace_128341 : CollatzResearch.WordTrace tailWord_128341 prefixEnd_128341 29289164746127821754345 := by
  unfold tailWord_128341
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680980828049950742856877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3120653885366633828571251 4680980828049950742856877)
  ·
    refine ⟨1755367810518731528571329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4680980828049950742856877 1755367810518731528571329)
    ·
      refine ⟨1316525857889048646428497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1755367810518731528571329 1316525857889048646428497)
      ·
        refine ⟨987394393416786484821373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316525857889048646428497 987394393416786484821373)
        ·
          refine ⟨370272897531294931808015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 987394393416786484821373 370272897531294931808015)
          ·
            refine ⟨555409346296942397712023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370272897531294931808015 555409346296942397712023)
            ·
              refine ⟨833114019445413596568035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555409346296942397712023 833114019445413596568035)
              ·
                refine ⟨1249671029168120394852053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833114019445413596568035 1249671029168120394852053)
                ·
                  refine ⟨29289164746127821754345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1249671029168120394852053 29289164746127821754345)
                  ·
                    rfl

theorem cell21_128341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_128341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128341 prefixEnd_128341 := by exact prefixLift 128341
  have htrace : WordTrace (prefixWord ++ tailWord_128341) baseStart_128341 baseEnd_128341 := by
    simpa [prefixWord, tailWord_128341, baseEnd_128341] using wordTrace_append hprefix tailTrace_128341
  have hstable : (prefixWord ++ tailWord_128341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128341).length < 2 ^ (prefixWord ++ tailWord_128341).sum := by decide
  have hdescent : baseEnd_128341 < baseStart_128341 := by decide
  rcases family_descends (prefixWord ++ tailWord_128341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128462 : List Nat := [4, 1, 1, 1, 2, 1, 4, 7]
def baseStart_128462 : Nat := 118140960795 + 128462 * 2 ^ 59
def prefixEnd_128462 : Nat := 4983230072969 + 3 ^ 40 * 128462 * 2
def baseEnd_128462 : Nat := 9772259531552833412477

theorem tailTrace_128462 : CollatzResearch.WordTrace tailWord_128462 prefixEnd_128462 9772259531552833412477 := by
  unfold tailWord_128462
  simp only [CollatzResearch.WordTrace]
  refine ⟨585674257576448551001455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3123596040407725605341093 585674257576448551001455)
  ·
    refine ⟨878511386364672826502183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585674257576448551001455 878511386364672826502183)
    ·
      refine ⟨1317767079547009239753275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878511386364672826502183 1317767079547009239753275)
      ·
        refine ⟨1976650619320513859629913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317767079547009239753275 1976650619320513859629913)
        ·
          refine ⟨1482487964490385394722435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1976650619320513859629913 1482487964490385394722435)
          ·
            refine ⟨2223731946735578092083653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482487964490385394722435 2223731946735578092083653)
            ·
              refine ⟨416949740012920892265685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2223731946735578092083653 416949740012920892265685)
              ·
                refine ⟨9772259531552833412477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 416949740012920892265685 9772259531552833412477)
                ·
                  rfl

theorem cell21_128462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_128462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128462 prefixEnd_128462 := by exact prefixLift 128462
  have htrace : WordTrace (prefixWord ++ tailWord_128462) baseStart_128462 baseEnd_128462 := by
    simpa [prefixWord, tailWord_128462, baseEnd_128462] using wordTrace_append hprefix tailTrace_128462
  have hstable : (prefixWord ++ tailWord_128462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128462).length < 2 ^ (prefixWord ++ tailWord_128462).sum := by decide
  have hdescent : baseEnd_128462 < baseStart_128462 := by decide
  rcases family_descends (prefixWord ++ tailWord_128462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128558 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_128558 : Nat := 118140960795 + 128558 * 2 ^ 59
def prefixEnd_128558 : Nat := 4983230072969 + 3 ^ 40 * 128558 * 2
def baseEnd_128558 : Nat := 29338687102583666637235

theorem tailTrace_128558 : CollatzResearch.WordTrace tailWord_128558 prefixEnd_128558 29338687102583666637235 := by
  unfold tailWord_128558
  simp only [CollatzResearch.WordTrace]
  refine ⟨586111933532974600438291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3125930312175864535670885 586111933532974600438291)
  ·
    refine ⟨879167900299461900657437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 586111933532974600438291 879167900299461900657437)
    ·
      refine ⟨329687962612298212746539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 879167900299461900657437 329687962612298212746539)
      ·
        refine ⟨494531943918447319119809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329687962612298212746539 494531943918447319119809)
        ·
          refine ⟨370898957938835489339857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494531943918447319119809 370898957938835489339857)
          ·
            refine ⟨278174218454126617004893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370898957938835489339857 278174218454126617004893)
            ·
              refine ⟨104315331920297481376835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278174218454126617004893 104315331920297481376835)
              ·
                refine ⟨156472997880446222065253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104315331920297481376835 156472997880446222065253)
                ·
                  refine ⟨29338687102583666637235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156472997880446222065253 29338687102583666637235)
                  ·
                    rfl

theorem cell21_128558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_128558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128558 prefixEnd_128558 := by exact prefixLift 128558
  have htrace : WordTrace (prefixWord ++ tailWord_128558) baseStart_128558 baseEnd_128558 := by
    simpa [prefixWord, tailWord_128558, baseEnd_128558] using wordTrace_append hprefix tailTrace_128558
  have hstable : (prefixWord ++ tailWord_128558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128558).length < 2 ^ (prefixWord ++ tailWord_128558).sum := by decide
  have hdescent : baseEnd_128558 < baseStart_128558 := by decide
  rcases family_descends (prefixWord ++ tailWord_128558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128569 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 5]
def baseStart_128569 : Nat := 118140960795 + 128569 * 2 ^ 59
def prefixEnd_128569 : Nat := 4983230072969 + 3 ^ 40 * 128569 * 2
def baseEnd_128569 : Nat := 29341197452450091953879

theorem tailTrace_128569 : CollatzResearch.WordTrace tailWord_128569 prefixEnd_128569 29341197452450091953879 := by
  unfold tailWord_128569
  simp only [CollatzResearch.WordTrace]
  refine ⟨4689296671223945682156761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3126197780815963788104507 4689296671223945682156761)
  ·
    refine ⟨3516972503417959261617571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4689296671223945682156761 3516972503417959261617571)
    ·
      refine ⟨5275458755126938892426357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516972503417959261617571 5275458755126938892426357)
      ·
        refine ⟨494574258293150521164971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5275458755126938892426357 494574258293150521164971)
        ·
          refine ⟨741861387439725781747457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494574258293150521164971 741861387439725781747457)
          ·
            refine ⟨556396040579794336310593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741861387439725781747457 556396040579794336310593)
            ·
              refine ⟨417297030434845752232945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556396040579794336310593 417297030434845752232945)
              ·
                refine ⟨312972772826134314174709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417297030434845752232945 312972772826134314174709)
                ·
                  refine ⟨29341197452450091953879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312972772826134314174709 29341197452450091953879)
                  ·
                    rfl

theorem cell21_128569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_128569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128569 prefixEnd_128569 := by exact prefixLift 128569
  have htrace : WordTrace (prefixWord ++ tailWord_128569) baseStart_128569 baseEnd_128569 := by
    simpa [prefixWord, tailWord_128569, baseEnd_128569] using wordTrace_append hprefix tailTrace_128569
  have hstable : (prefixWord ++ tailWord_128569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128569).length < 2 ^ (prefixWord ++ tailWord_128569).sum := by decide
  have hdescent : baseEnd_128569 < baseStart_128569 := by decide
  rcases family_descends (prefixWord ++ tailWord_128569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128572 : List Nat := [2, 2, 2, 2, 4, 2, 2, 5]
def baseStart_128572 : Nat := 118140960795 + 128572 * 2 ^ 59
def prefixEnd_128572 : Nat := 4983230072969 + 3 ^ 40 * 128572 * 2
def baseEnd_128572 : Nat := 9780627364440917801291

theorem tailTrace_128572 : CollatzResearch.WordTrace tailWord_128572 prefixEnd_128572 9780627364440917801291 := by
  unfold tailWord_128572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2344703045106538597257985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3126270726808718129677313 2344703045106538597257985)
  ·
    refine ⟨1758527283829903947943489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2344703045106538597257985 1758527283829903947943489)
    ·
      refine ⟨1318895462872427960957617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1758527283829903947943489 1318895462872427960957617)
      ·
        refine ⟨989171597154320970718213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318895462872427960957617 989171597154320970718213)
        ·
          refine ⟨185469674466435182009665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 989171597154320970718213 185469674466435182009665)
          ·
            refine ⟨139102255849826386507249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185469674466435182009665 139102255849826386507249)
            ·
              refine ⟨104326691887369789880437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139102255849826386507249 104326691887369789880437)
              ·
                refine ⟨9780627364440917801291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104326691887369789880437 9780627364440917801291)
                ·
                  rfl

theorem cell21_128572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_128572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128572 prefixEnd_128572 := by exact prefixLift 128572
  have htrace : WordTrace (prefixWord ++ tailWord_128572) baseStart_128572 baseEnd_128572 := by
    simpa [prefixWord, tailWord_128572, baseEnd_128572] using wordTrace_append hprefix tailTrace_128572
  have hstable : (prefixWord ++ tailWord_128572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128572).length < 2 ^ (prefixWord ++ tailWord_128572).sum := by decide
  have hdescent : baseEnd_128572 < baseStart_128572 := by decide
  rcases family_descends (prefixWord ++ tailWord_128572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128676 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_128676 : Nat := 118140960795 + 128676 * 2 ^ 59
def prefixEnd_128676 : Nat := 4983230072969 + 3 ^ 40 * 128676 * 2
def baseEnd_128676 : Nat := 29365616310241683670327

theorem tailTrace_128676 : CollatzResearch.WordTrace tailWord_128676 prefixEnd_128676 29365616310241683670327 := by
  unfold tailWord_128676
  simp only [CollatzResearch.WordTrace]
  refine ⟨2346599640918151478150941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3128799521224201970867921 2346599640918151478150941)
  ·
    refine ⟨879974865344306804306603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2346599640918151478150941 879974865344306804306603)
    ·
      refine ⟨1319962298016460206459905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879974865344306804306603 1319962298016460206459905)
      ·
        refine ⟨989971723512345154844929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1319962298016460206459905 989971723512345154844929)
        ·
          refine ⟨742478792634258866133697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989971723512345154844929 742478792634258866133697)
          ·
            refine ⟨556859094475694149600273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742478792634258866133697 556859094475694149600273)
            ·
              refine ⟨417644320856770612200205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556859094475694149600273 417644320856770612200205)
              ·
                refine ⟨156616620321288979575077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417644320856770612200205 156616620321288979575077)
                ·
                  refine ⟨29365616310241683670327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156616620321288979575077 29365616310241683670327)
                  ·
                    rfl

theorem cell21_128676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_128676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128676 prefixEnd_128676 := by exact prefixLift 128676
  have htrace : WordTrace (prefixWord ++ tailWord_128676) baseStart_128676 baseEnd_128676 := by
    simpa [prefixWord, tailWord_128676, baseEnd_128676] using wordTrace_append hprefix tailTrace_128676
  have hstable : (prefixWord ++ tailWord_128676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128676).length < 2 ^ (prefixWord ++ tailWord_128676).sum := by decide
  have hdescent : baseEnd_128676 < baseStart_128676 := by decide
  rcases family_descends (prefixWord ++ tailWord_128676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128704 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_128704 : Nat := 118140960795 + 128704 * 2 ^ 59
def prefixEnd_128704 : Nat := 4983230072969 + 3 ^ 40 * 128704 * 2
def baseEnd_128704 : Nat := 29372006291719857203603

theorem tailTrace_128704 : CollatzResearch.WordTrace tailWord_128704 prefixEnd_128704 29372006291719857203603 := by
  unfold tailWord_128704
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347110262867431869160583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3129480350489909158880777 2347110262867431869160583)
  ·
    refine ⟨3520665394301147803740875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2347110262867431869160583 3520665394301147803740875)
    ·
      refine ⟨5280998091451721705611313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520665394301147803740875 5280998091451721705611313)
      ·
        refine ⟨3960748568588791279208485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5280998091451721705611313 3960748568588791279208485)
        ·
          refine ⟨742640356610398364851591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3960748568588791279208485 742640356610398364851591)
          ·
            refine ⟨1113960534915597547277387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742640356610398364851591 1113960534915597547277387)
            ·
              refine ⟨1670940802373396320916081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113960534915597547277387 1670940802373396320916081)
              ·
                refine ⟨1253205601780047240687061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670940802373396320916081 1253205601780047240687061)
                ·
                  refine ⟨29372006291719857203603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1253205601780047240687061 29372006291719857203603)
                  ·
                    rfl

theorem cell21_128704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_128704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128704 prefixEnd_128704 := by exact prefixLift 128704
  have htrace : WordTrace (prefixWord ++ tailWord_128704) baseStart_128704 baseEnd_128704 := by
    simpa [prefixWord, tailWord_128704, baseEnd_128704] using wordTrace_append hprefix tailTrace_128704
  have hstable : (prefixWord ++ tailWord_128704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128704).length < 2 ^ (prefixWord ++ tailWord_128704).sum := by decide
  have hdescent : baseEnd_128704 < baseStart_128704 := by decide
  rcases family_descends (prefixWord ++ tailWord_128704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128710 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_128710 : Nat := 118140960795 + 128710 * 2 ^ 59
def prefixEnd_128710 : Nat := 4983230072969 + 3 ^ 40 * 128710 * 2
def baseEnd_128710 : Nat := 29373375573465180103591

theorem tailTrace_128710 : CollatzResearch.WordTrace tailWord_128710 prefixEnd_128710 29373375573465180103591 := by
  unfold tailWord_128710
  simp only [CollatzResearch.WordTrace]
  refine ⟨146701230116035211344987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3129626242475417842026389 146701230116035211344987)
  ·
    refine ⟨220051845174052817017481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146701230116035211344987 220051845174052817017481)
    ·
      refine ⟨165038883880539612763111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220051845174052817017481 165038883880539612763111)
      ·
        refine ⟨247558325820809419144667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165038883880539612763111 247558325820809419144667)
        ·
          refine ⟨371337488731214128717001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247558325820809419144667 371337488731214128717001)
          ·
            refine ⟨278503116548410596537751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371337488731214128717001 278503116548410596537751)
            ·
              refine ⟨417754674822615894806627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278503116548410596537751 417754674822615894806627)
              ·
                refine ⟨626632012233923842209941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417754674822615894806627 626632012233923842209941)
                ·
                  refine ⟨29373375573465180103591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 626632012233923842209941 29373375573465180103591)
                  ·
                    rfl

theorem cell21_128710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_128710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128710 prefixEnd_128710 := by exact prefixLift 128710
  have htrace : WordTrace (prefixWord ++ tailWord_128710) baseStart_128710 baseEnd_128710 := by
    simpa [prefixWord, tailWord_128710, baseEnd_128710] using wordTrace_append hprefix tailTrace_128710
  have hstable : (prefixWord ++ tailWord_128710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128710).length < 2 ^ (prefixWord ++ tailWord_128710).sum := by decide
  have hdescent : baseEnd_128710 < baseStart_128710 := by decide
  rcases family_descends (prefixWord ++ tailWord_128710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128721 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 5]
def baseStart_128721 : Nat := 118140960795 + 128721 * 2 ^ 59
def prefixEnd_128721 : Nat := 4983230072969 + 3 ^ 40 * 128721 * 2
def baseEnd_128721 : Nat := 29375885923331605420235

theorem tailTrace_128721 : CollatzResearch.WordTrace tailWord_128721 prefixEnd_128721 29375885923331605420235 := by
  unfold tailWord_128721
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694840566673275641690017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3129893711115517094460011 4694840566673275641690017)
  ·
    refine ⟨3521130425004956731267513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4694840566673275641690017 3521130425004956731267513)
    ·
      refine ⟨2640847818753717548450635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3521130425004956731267513 2640847818753717548450635)
      ·
        refine ⟨3961271728130576322675953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640847818753717548450635 3961271728130576322675953)
        ·
          refine ⟨2970953796097932242006965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3961271728130576322675953 2970953796097932242006965)
          ·
            refine ⟨278526918384181147688153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2970953796097932242006965 278526918384181147688153)
            ·
              refine ⟨208895188788135860766115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278526918384181147688153 208895188788135860766115)
              ·
                refine ⟨313342783182203791149173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208895188788135860766115 313342783182203791149173)
                ·
                  refine ⟨29375885923331605420235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 313342783182203791149173 29375885923331605420235)
                  ·
                    rfl

theorem cell21_128721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_128721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128721 prefixEnd_128721 := by exact prefixLift 128721
  have htrace : WordTrace (prefixWord ++ tailWord_128721) baseStart_128721 baseEnd_128721 := by
    simpa [prefixWord, tailWord_128721, baseEnd_128721] using wordTrace_append hprefix tailTrace_128721
  have hstable : (prefixWord ++ tailWord_128721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128721).length < 2 ^ (prefixWord ++ tailWord_128721).sum := by decide
  have hdescent : baseEnd_128721 < baseStart_128721 := by decide
  rcases family_descends (prefixWord ++ tailWord_128721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128786 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_128786 : Nat := 118140960795 + 128786 * 2 ^ 59
def prefixEnd_128786 : Nat := 4983230072969 + 3 ^ 40 * 128786 * 2
def baseEnd_128786 : Nat := 29390719808905936836769

theorem tailTrace_128786 : CollatzResearch.WordTrace tailWord_128786 prefixEnd_128786 29390719808905936836769 := by
  unfold tailWord_128786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174302827859447935701553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3131474207625194495204141 1174302827859447935701553)
  ·
    refine ⟨880727120894585951776165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1174302827859447935701553 880727120894585951776165)
    ·
      refine ⟨165136335167734865958031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 880727120894585951776165 165136335167734865958031)
      ·
        refine ⟨247704502751602298937047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165136335167734865958031 247704502751602298937047)
        ·
          refine ⟨371556754127403448405571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247704502751602298937047 371556754127403448405571)
          ·
            refine ⟨557335131191105172608357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371556754127403448405571 557335131191105172608357)
            ·
              refine ⟨104500337098332219864067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 557335131191105172608357 104500337098332219864067)
              ·
                refine ⟨156750505647498329796101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104500337098332219864067 156750505647498329796101)
                ·
                  refine ⟨29390719808905936836769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156750505647498329796101 29390719808905936836769)
                  ·
                    rfl

theorem cell21_128786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_128786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128786 prefixEnd_128786 := by exact prefixLift 128786
  have htrace : WordTrace (prefixWord ++ tailWord_128786) baseStart_128786 baseEnd_128786 := by
    simpa [prefixWord, tailWord_128786, baseEnd_128786] using wordTrace_append hprefix tailTrace_128786
  have hstable : (prefixWord ++ tailWord_128786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128786).length < 2 ^ (prefixWord ++ tailWord_128786).sum := by decide
  have hdescent : baseEnd_128786 < baseStart_128786 := by decide
  rcases family_descends (prefixWord ++ tailWord_128786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128845 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 4]
def baseStart_128845 : Nat := 118140960795 + 128845 * 2 ^ 59
def prefixEnd_128845 : Nat := 4983230072969 + 3 ^ 40 * 128845 * 2
def baseEnd_128845 : Nat := 29404184412734945353315

theorem tailTrace_128845 : CollatzResearch.WordTrace tailWord_128845 prefixEnd_128845 29404184412734945353315 := by
  unfold tailWord_128845
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699363218224044819203989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3132908812149363212802659 4699363218224044819203989)
  ·
    refine ⟨220282650854252100900187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4699363218224044819203989 220282650854252100900187)
    ·
      refine ⟨330423976281378151350281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220282650854252100900187 330423976281378151350281)
      ·
        refine ⟨247817982211033613512711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330423976281378151350281 247817982211033613512711)
        ·
          refine ⟨371726973316550420269067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247817982211033613512711 371726973316550420269067)
          ·
            refine ⟨557590459974825630403601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371726973316550420269067 557590459974825630403601)
            ·
              refine ⟨418192844981119222802701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557590459974825630403601 418192844981119222802701)
              ·
                refine ⟨156822316867919708551013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418192844981119222802701 156822316867919708551013)
                ·
                  refine ⟨29404184412734945353315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156822316867919708551013 29404184412734945353315)
                  ·
                    rfl

theorem cell21_128845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_128845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128845 prefixEnd_128845 := by exact prefixLift 128845
  have htrace : WordTrace (prefixWord ++ tailWord_128845) baseStart_128845 baseEnd_128845 := by
    simpa [prefixWord, tailWord_128845, baseEnd_128845] using wordTrace_append hprefix tailTrace_128845
  have hstable : (prefixWord ++ tailWord_128845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128845).length < 2 ^ (prefixWord ++ tailWord_128845).sum := by decide
  have hdescent : baseEnd_128845 < baseStart_128845 := by decide
  rcases family_descends (prefixWord ++ tailWord_128845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128901 : List Nat := [1, 3, 1, 1, 3, 2, 2, 8]
def baseStart_128901 : Nat := 118140960795 + 128901 * 2 ^ 59
def prefixEnd_128901 : Nat := 4983230072969 + 3 ^ 40 * 128901 * 2
def baseEnd_128901 : Nat := 9805654791897097473289

theorem tailTrace_128901 : CollatzResearch.WordTrace tailWord_128901 prefixEnd_128901 9805654791897097473289 := by
  unfold tailWord_128901
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701405706021166383242557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3134270470680777588828371 4701405706021166383242557)
  ·
    refine ⟨1763027139757937393715959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4701405706021166383242557 1763027139757937393715959)
    ·
      refine ⟨2644540709636906090573939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763027139757937393715959 2644540709636906090573939)
      ·
        refine ⟨3966811064455359135860909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644540709636906090573939 3966811064455359135860909)
        ·
          refine ⟨1487554149170759675947841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3966811064455359135860909 1487554149170759675947841)
          ·
            refine ⟨1115665611878069756960881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487554149170759675947841 1115665611878069756960881)
            ·
              refine ⟨836749208908552317720661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115665611878069756960881 836749208908552317720661)
              ·
                refine ⟨9805654791897097473289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 836749208908552317720661 9805654791897097473289)
                ·
                  rfl

theorem cell21_128901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 8].length) (baseStart_128901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128901 prefixEnd_128901 := by exact prefixLift 128901
  have htrace : WordTrace (prefixWord ++ tailWord_128901) baseStart_128901 baseEnd_128901 := by
    simpa [prefixWord, tailWord_128901, baseEnd_128901] using wordTrace_append hprefix tailTrace_128901
  have hstable : (prefixWord ++ tailWord_128901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128901).length < 2 ^ (prefixWord ++ tailWord_128901).sum := by decide
  have hdescent : baseEnd_128901 < baseStart_128901 := by decide
  rcases family_descends (prefixWord ++ tailWord_128901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128949 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 5]
def baseStart_128949 : Nat := 118140960795 + 128949 * 2 ^ 59
def prefixEnd_128949 : Nat := 4983230072969 + 3 ^ 40 * 128949 * 2
def baseEnd_128949 : Nat := 29427918629653875619769

theorem tailTrace_128949 : CollatzResearch.WordTrace tailWord_128949 prefixEnd_128949 29427918629653875619769 := by
  unfold tailWord_128949
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703156409847270580989901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3135437606564847053993267 4703156409847270580989901)
  ·
    refine ⟨1763683653692726467871213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4703156409847270580989901 1763683653692726467871213)
    ·
      refine ⟨661381370134772425451705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1763683653692726467871213 661381370134772425451705)
      ·
        refine ⟨496036027601079319088779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661381370134772425451705 496036027601079319088779)
        ·
          refine ⟨744054041401618978633169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496036027601079319088779 744054041401618978633169)
          ·
            refine ⟨558040531051214233974877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744054041401618978633169 558040531051214233974877)
            ·
              refine ⟨209265199144205337740579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558040531051214233974877 209265199144205337740579)
              ·
                refine ⟨313897798716308006610869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209265199144205337740579 313897798716308006610869)
                ·
                  refine ⟨29427918629653875619769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 313897798716308006610869 29427918629653875619769)
                  ·
                    rfl

theorem cell21_128949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_128949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128949 prefixEnd_128949 := by exact prefixLift 128949
  have htrace : WordTrace (prefixWord ++ tailWord_128949) baseStart_128949 baseEnd_128949 := by
    simpa [prefixWord, tailWord_128949, baseEnd_128949] using wordTrace_append hprefix tailTrace_128949
  have hstable : (prefixWord ++ tailWord_128949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128949).length < 2 ^ (prefixWord ++ tailWord_128949).sum := by decide
  have hdescent : baseEnd_128949 < baseStart_128949 := by decide
  rcases family_descends (prefixWord ++ tailWord_128949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128994 : List Nat := [3, 3, 3, 1, 11]
def baseStart_128994 : Nat := 118140960795 + 128994 * 2 ^ 59
def prefixEnd_128994 : Nat := 4983230072969 + 3 ^ 40 * 128994 * 2
def baseEnd_128994 : Nat := 363434422749923424317

theorem tailTrace_128994 : CollatzResearch.WordTrace tailWord_128994 prefixEnd_128994 363434422749923424317 := by
  unfold tailWord_128994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176199423671060816594509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3136531796456162177585357 1176199423671060816594509)
  ·
    refine ⟨441074783876647806222941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1176199423671060816594509 441074783876647806222941)
    ·
      refine ⟨165403043953742927333603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441074783876647806222941 165403043953742927333603)
      ·
        refine ⟨248104565930614391000405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165403043953742927333603 248104565930614391000405)
        ·
          refine ⟨363434422749923424317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 248104565930614391000405 363434422749923424317)
          ·
            rfl

theorem cell21_128994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 11].length) (baseStart_128994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_128994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_128994 prefixEnd_128994 := by exact prefixLift 128994
  have htrace : WordTrace (prefixWord ++ tailWord_128994) baseStart_128994 baseEnd_128994 := by
    simpa [prefixWord, tailWord_128994, baseEnd_128994] using wordTrace_append hprefix tailTrace_128994
  have hstable : (prefixWord ++ tailWord_128994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128994).length < 2 ^ (prefixWord ++ tailWord_128994).sum := by decide
  have hdescent : baseEnd_128994 < baseStart_128994 := by decide
  rcases family_descends (prefixWord ++ tailWord_128994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129028 : List Nat := [2, 3, 2, 4, 1, 1, 3, 5]
def baseStart_129028 : Nat := 118140960795 + 129028 * 2 ^ 59
def prefixEnd_129028 : Nat := 4983230072969 + 3 ^ 40 * 129028 * 2
def baseEnd_129028 : Nat := 9815315835322431267647

theorem tailTrace_129028 : CollatzResearch.WordTrace tailWord_129028 prefixEnd_129028 9815315835322431267647 := by
  unfold tailWord_129028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353018888280533536557869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3137358517707378048743825 2353018888280533536557869)
  ·
    refine ⟨882382083105200076209201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2353018888280533536557869 882382083105200076209201)
    ·
      refine ⟨661786562328900057156901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 882382083105200076209201 661786562328900057156901)
      ·
        refine ⟨124084980436668760716919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 661786562328900057156901 124084980436668760716919)
        ·
          refine ⟨186127470655003141075379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124084980436668760716919 186127470655003141075379)
          ·
            refine ⟨279191205982504711613069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186127470655003141075379 279191205982504711613069)
            ·
              refine ⟨104696702243439266854901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279191205982504711613069 104696702243439266854901)
              ·
                refine ⟨9815315835322431267647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104696702243439266854901 9815315835322431267647)
                ·
                  rfl

theorem cell21_129028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_129028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129028 prefixEnd_129028 := by exact prefixLift 129028
  have htrace : WordTrace (prefixWord ++ tailWord_129028) baseStart_129028 baseEnd_129028 := by
    simpa [prefixWord, tailWord_129028, baseEnd_129028] using wordTrace_append hprefix tailTrace_129028
  have hstable : (prefixWord ++ tailWord_129028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129028).length < 2 ^ (prefixWord ++ tailWord_129028).sum := by decide
  have hdescent : baseEnd_129028 < baseStart_129028 := by decide
  rcases family_descends (prefixWord ++ tailWord_129028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129084 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_129084 : Nat := 118140960795 + 129084 * 2 ^ 59
def prefixEnd_129084 : Nat := 4983230072969 + 3 ^ 40 * 129084 * 2
def baseEnd_129084 : Nat := 29458727468923640869493

theorem tailTrace_129084 : CollatzResearch.WordTrace tailWord_129084 prefixEnd_129084 29458727468923640869493 := by
  unfold tailWord_129084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354040132179094318577153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3138720176238792424769537 2354040132179094318577153)
  ·
    refine ⟨1765530099134320738932865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2354040132179094318577153 1765530099134320738932865)
    ·
      refine ⟨1324147574350740554199649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1765530099134320738932865 1324147574350740554199649)
      ·
        refine ⟨993110680763055415649737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1324147574350740554199649 993110680763055415649737)
        ·
          refine ⟨744833010572291561737303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993110680763055415649737 744833010572291561737303)
          ·
            refine ⟨1117249515858437342605955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744833010572291561737303 1117249515858437342605955)
            ·
              refine ⟨1675874273787656013908933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117249515858437342605955 1675874273787656013908933)
              ·
                refine ⟨314226426335185502607925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1675874273787656013908933 314226426335185502607925)
                ·
                  refine ⟨29458727468923640869493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314226426335185502607925 29458727468923640869493)
                  ·
                    rfl

theorem cell21_129084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_129084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129084 prefixEnd_129084 := by exact prefixLift 129084
  have htrace : WordTrace (prefixWord ++ tailWord_129084) baseStart_129084 baseEnd_129084 := by
    simpa [prefixWord, tailWord_129084, baseEnd_129084] using wordTrace_append hprefix tailTrace_129084
  have hstable : (prefixWord ++ tailWord_129084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129084).length < 2 ^ (prefixWord ++ tailWord_129084).sum := by decide
  have hdescent : baseEnd_129084 < baseStart_129084 := by decide
  rcases family_descends (prefixWord ++ tailWord_129084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129129 : List Nat := [1, 2, 1, 1, 1, 5, 4, 6]
def baseStart_129129 : Nat := 118140960795 + 129129 * 2 ^ 59
def prefixEnd_129129 : Nat := 4983230072969 + 3 ^ 40 * 129129 * 2
def baseEnd_129129 : Nat := 9822999027337854206467

theorem tailTrace_129129 : CollatzResearch.WordTrace tailWord_129129 prefixEnd_129129 9822999027337854206467 := by
  unfold tailWord_129129
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709721549195161322542441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3139814366130107548361627 4709721549195161322542441)
  ·
    refine ⟨3532291161896370991906831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4709721549195161322542441 3532291161896370991906831)
    ·
      refine ⟨5298436742844556487860247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3532291161896370991906831 5298436742844556487860247)
      ·
        refine ⟨7947655114266834731790371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298436742844556487860247 7947655114266834731790371)
        ·
          refine ⟨11921482671400252097685557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947655114266834731790371 11921482671400252097685557)
          ·
            refine ⟨1117639000443773634158021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11921482671400252097685557 1117639000443773634158021)
            ·
              refine ⟨209557312583207556404629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1117639000443773634158021 209557312583207556404629)
              ·
                refine ⟨9822999027337854206467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209557312583207556404629 9822999027337854206467)
                ·
                  rfl

theorem cell21_129129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 6].length) (baseStart_129129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129129 prefixEnd_129129 := by exact prefixLift 129129
  have htrace : WordTrace (prefixWord ++ tailWord_129129) baseStart_129129 baseEnd_129129 := by
    simpa [prefixWord, tailWord_129129, baseEnd_129129] using wordTrace_append hprefix tailTrace_129129
  have hstable : (prefixWord ++ tailWord_129129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129129).length < 2 ^ (prefixWord ++ tailWord_129129).sum := by decide
  have hdescent : baseEnd_129129 < baseStart_129129 := by decide
  rcases family_descends (prefixWord ++ tailWord_129129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129132 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_129132 : Nat := 118140960795 + 129132 * 2 ^ 59
def prefixEnd_129132 : Nat := 4983230072969 + 3 ^ 40 * 129132 * 2
def baseEnd_129132 : Nat := 29469681722886224069395

theorem tailTrace_129132 : CollatzResearch.WordTrace tailWord_129132 prefixEnd_129132 29469681722886224069395 := by
  unfold tailWord_129132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354915484092146417450825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3139887312122861889934433 2354915484092146417450825)
  ·
    refine ⟨1766186613069109813088119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2354915484092146417450825 1766186613069109813088119)
    ·
      refine ⟨2649279919603664719632179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1766186613069109813088119 2649279919603664719632179)
      ·
        refine ⟨3973919879405497079448269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649279919603664719632179 3973919879405497079448269)
        ·
          refine ⟨1490219954777061404793101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3973919879405497079448269 1490219954777061404793101)
          ·
            refine ⟨558832483041398026797413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1490219954777061404793101 558832483041398026797413)
            ·
              refine ⟨104781090570262130024515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 558832483041398026797413 104781090570262130024515)
              ·
                refine ⟨157171635855393195036773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104781090570262130024515 157171635855393195036773)
                ·
                  refine ⟨29469681722886224069395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157171635855393195036773 29469681722886224069395)
                  ·
                    rfl

theorem cell21_129132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_129132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129132 prefixEnd_129132 := by exact prefixLift 129132
  have htrace : WordTrace (prefixWord ++ tailWord_129132) baseStart_129132 baseEnd_129132 := by
    simpa [prefixWord, tailWord_129132, baseEnd_129132] using wordTrace_append hprefix tailTrace_129132
  have hstable : (prefixWord ++ tailWord_129132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129132).length < 2 ^ (prefixWord ++ tailWord_129132).sum := by decide
  have hdescent : baseEnd_129132 < baseStart_129132 := by decide
  rcases family_descends (prefixWord ++ tailWord_129132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129194 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_129194 : Nat := 118140960795 + 129194 * 2 ^ 59
def prefixEnd_129194 : Nat := 4983230072969 + 3 ^ 40 * 129194 * 2
def baseEnd_129194 : Nat := 29483830967587894035935

theorem tailTrace_129194 : CollatzResearch.WordTrace tailWord_129194 prefixEnd_129194 29483830967587894035935 := by
  unfold tailWord_129194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178023073489919355914659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3141394862639784949105757 1178023073489919355914659)
  ·
    refine ⟨1767034610234879033871989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1178023073489919355914659 1767034610234879033871989)
    ·
      refine ⟨165659494709519909425499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1767034610234879033871989 165659494709519909425499)
      ·
        refine ⟨248489242064279864138249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165659494709519909425499 248489242064279864138249)
        ·
          refine ⟨186366931548209898103687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248489242064279864138249 186366931548209898103687)
          ·
            refine ⟨279550397322314847155531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186366931548209898103687 279550397322314847155531)
            ·
              refine ⟨419325595983472270733297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279550397322314847155531 419325595983472270733297)
              ·
                refine ⟨314494196987604203049973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419325595983472270733297 314494196987604203049973)
                ·
                  refine ⟨29483830967587894035935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314494196987604203049973 29483830967587894035935)
                  ·
                    rfl

theorem cell21_129194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_129194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129194 prefixEnd_129194 := by exact prefixLift 129194
  have htrace : WordTrace (prefixWord ++ tailWord_129194) baseStart_129194 baseEnd_129194 := by
    simpa [prefixWord, tailWord_129194, baseEnd_129194] using wordTrace_append hprefix tailTrace_129194
  have hstable : (prefixWord ++ tailWord_129194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129194).length < 2 ^ (prefixWord ++ tailWord_129194).sum := by decide
  have hdescent : baseEnd_129194 < baseStart_129194 := by decide
  rcases family_descends (prefixWord ++ tailWord_129194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129270 : List Nat := [5, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_129270 : Nat := 118140960795 + 129270 * 2 ^ 59
def prefixEnd_129270 : Nat := 4983230072969 + 3 ^ 40 * 129270 * 2
def baseEnd_129270 : Nat := 29501175203028650769113

theorem tailTrace_129270 : CollatzResearch.WordTrace tailWord_129270 prefixEnd_129270 29501175203028650769113 := by
  unfold tailWord_129270
  simp only [CollatzResearch.WordTrace]
  refine ⟨294679015105271400214079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3143242827789561602283509 294679015105271400214079)
  ·
    refine ⟨442018522657907100321119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294679015105271400214079 442018522657907100321119)
    ·
      refine ⟨663027783986860650481679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442018522657907100321119 663027783986860650481679)
      ·
        refine ⟨994541675980290975722519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663027783986860650481679 994541675980290975722519)
        ·
          refine ⟨1491812513970436463583779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994541675980290975722519 1491812513970436463583779)
          ·
            refine ⟨2237718770955654695375669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491812513970436463583779 2237718770955654695375669)
            ·
              refine ⟨209786134777092627691469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2237718770955654695375669 209786134777092627691469)
              ·
                refine ⟨78669800541409735384301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209786134777092627691469 78669800541409735384301)
                ·
                  refine ⟨29501175203028650769113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78669800541409735384301 29501175203028650769113)
                  ·
                    rfl

theorem cell21_129270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_129270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129270 prefixEnd_129270 := by exact prefixLift 129270
  have htrace : WordTrace (prefixWord ++ tailWord_129270) baseStart_129270 baseEnd_129270 := by
    simpa [prefixWord, tailWord_129270, baseEnd_129270] using wordTrace_append hprefix tailTrace_129270
  have hstable : (prefixWord ++ tailWord_129270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129270).length < 2 ^ (prefixWord ++ tailWord_129270).sum := by decide
  have hdescent : baseEnd_129270 < baseStart_129270 := by decide
  rcases family_descends (prefixWord ++ tailWord_129270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129287 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 5]
def baseStart_129287 : Nat := 118140960795 + 129287 * 2 ^ 59
def prefixEnd_129287 : Nat := 4983230072969 + 3 ^ 40 * 129287 * 2
def baseEnd_129287 : Nat := 29505054834640398985745

theorem tailTrace_129287 : CollatzResearch.WordTrace tailWord_129287 prefixEnd_129287 29505054834640398985745 := by
  unfold tailWord_129287
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715484282622754306794115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3143656188415169537862743 4715484282622754306794115)
  ·
    refine ⟨7073226423934131460191173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4715484282622754306794115 7073226423934131460191173)
    ·
      refine ⟨1326229954487649648785845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7073226423934131460191173 1326229954487649648785845)
      ·
        refine ⟨124334058233217154573673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1326229954487649648785845 124334058233217154573673)
        ·
          refine ⟨93250543674912865930255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124334058233217154573673 93250543674912865930255)
          ·
            refine ⟨139875815512369298895383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93250543674912865930255 139875815512369298895383)
            ·
              refine ⟨209813723268553948343075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139875815512369298895383 209813723268553948343075)
              ·
                refine ⟨314720584902830922514613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209813723268553948343075 314720584902830922514613)
                ·
                  refine ⟨29505054834640398985745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314720584902830922514613 29505054834640398985745)
                  ·
                    rfl

theorem cell21_129287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 5].length) (baseStart_129287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129287 prefixEnd_129287 := by exact prefixLift 129287
  have htrace : WordTrace (prefixWord ++ tailWord_129287) baseStart_129287 baseEnd_129287 := by
    simpa [prefixWord, tailWord_129287, baseEnd_129287] using wordTrace_append hprefix tailTrace_129287
  have hstable : (prefixWord ++ tailWord_129287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129287).length < 2 ^ (prefixWord ++ tailWord_129287).sum := by decide
  have hdescent : baseEnd_129287 < baseStart_129287 := by decide
  rcases family_descends (prefixWord ++ tailWord_129287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129343 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 4]
def baseStart_129343 : Nat := 118140960795 + 129343 * 2 ^ 59
def prefixEnd_129343 : Nat := 4983230072969 + 3 ^ 40 * 129343 * 2
def baseEnd_129343 : Nat := 29517834797596746052297

theorem tailTrace_129343 : CollatzResearch.WordTrace tailWord_129343 prefixEnd_129343 29517834797596746052297 := by
  unfold tailWord_129343
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717526770419875870832683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3145017846946583913888455 4717526770419875870832683)
  ·
    refine ⟨7076290155629813806249025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717526770419875870832683 7076290155629813806249025)
    ·
      refine ⟨5307217616722360354686769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7076290155629813806249025 5307217616722360354686769)
      ·
        refine ⟨3980413212541770266015077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5307217616722360354686769 3980413212541770266015077)
        ·
          refine ⟨746327477351581924877827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3980413212541770266015077 746327477351581924877827)
          ·
            refine ⟨1119491216027372887316741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746327477351581924877827 1119491216027372887316741)
            ·
              refine ⟨209904603005132416371889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1119491216027372887316741 209904603005132416371889)
              ·
                refine ⟨157428452253849312278917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209904603005132416371889 157428452253849312278917)
                ·
                  refine ⟨29517834797596746052297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157428452253849312278917 29517834797596746052297)
                  ·
                    rfl

theorem cell21_129343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 4].length) (baseStart_129343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129343 prefixEnd_129343 := by exact prefixLift 129343
  have htrace : WordTrace (prefixWord ++ tailWord_129343) baseStart_129343 baseEnd_129343 := by
    simpa [prefixWord, tailWord_129343, baseEnd_129343] using wordTrace_append hprefix tailTrace_129343
  have hstable : (prefixWord ++ tailWord_129343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129343).length < 2 ^ (prefixWord ++ tailWord_129343).sum := by decide
  have hdescent : baseEnd_129343 < baseStart_129343 := by decide
  rcases family_descends (prefixWord ++ tailWord_129343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129405 : List Nat := [1, 4, 1, 1, 2, 3, 2, 4, 3]
def baseStart_129405 : Nat := 118140960795 + 129405 * 2 ^ 59
def prefixEnd_129405 : Nat := 4983230072969 + 3 ^ 40 * 129405 * 2
def baseEnd_129405 : Nat := 29531984042298416018837

theorem tailTrace_129405 : CollatzResearch.WordTrace tailWord_129405 prefixEnd_129405 29531984042298416018837 := by
  unfold tailWord_129405
  simp only [CollatzResearch.WordTrace]
  refine ⟨4719788096195260459589669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3146525397463506973059779 4719788096195260459589669)
  ·
    refine ⟨884960268036611336173063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4719788096195260459589669 884960268036611336173063)
    ·
      refine ⟨1327440402054917004259595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 884960268036611336173063 1327440402054917004259595)
      ·
        refine ⟨1991160603082375506389393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327440402054917004259595 1991160603082375506389393)
        ·
          refine ⟨1493370452311781629792045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991160603082375506389393 1493370452311781629792045)
          ·
            refine ⟨560013919616918111172017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1493370452311781629792045 560013919616918111172017)
            ·
              refine ⟨420010439712688583379013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560013919616918111172017 420010439712688583379013)
              ·
                refine ⟨78751957446129109383565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420010439712688583379013 78751957446129109383565)
                ·
                  refine ⟨29531984042298416018837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78751957446129109383565 29531984042298416018837)
                  ·
                    rfl

theorem cell21_129405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_129405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129405 prefixEnd_129405 := by exact prefixLift 129405
  have htrace : WordTrace (prefixWord ++ tailWord_129405) baseStart_129405 baseEnd_129405 := by
    simpa [prefixWord, tailWord_129405, baseEnd_129405] using wordTrace_append hprefix tailTrace_129405
  have hstable : (prefixWord ++ tailWord_129405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129405).length < 2 ^ (prefixWord ++ tailWord_129405).sum := by decide
  have hdescent : baseEnd_129405 < baseStart_129405 := by decide
  rcases family_descends (prefixWord ++ tailWord_129405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129509 : List Nat := [1, 3, 1, 5, 2, 9]
def baseStart_129509 : Nat := 118140960795 + 129509 * 2 ^ 59
def prefixEnd_129509 : Nat := 4983230072969 + 3 ^ 40 * 129509 * 2
def baseEnd_129509 : Nat := 1094656231822864677233

theorem tailTrace_129509 : CollatzResearch.WordTrace tailWord_129509 prefixEnd_129509 1094656231822864677233 := by
  unfold tailWord_129509
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723581287818486221375581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3149054191878990814250387 4723581287818486221375581)
  ·
    refine ⟨1771342982931932333015843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4723581287818486221375581 1771342982931932333015843)
    ·
      refine ⟨2657014474397898499523765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771342982931932333015843 2657014474397898499523765)
      ·
        refine ⟨249095106974802984330353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2657014474397898499523765 249095106974802984330353)
        ·
          refine ⟨186821330231102238247765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249095106974802984330353 186821330231102238247765)
          ·
            refine ⟨1094656231822864677233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 186821330231102238247765 1094656231822864677233)
            ·
              rfl

theorem cell21_129509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 9].length) (baseStart_129509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129509 prefixEnd_129509 := by exact prefixLift 129509
  have htrace : WordTrace (prefixWord ++ tailWord_129509) baseStart_129509 baseEnd_129509 := by
    simpa [prefixWord, tailWord_129509, baseEnd_129509] using wordTrace_append hprefix tailTrace_129509
  have hstable : (prefixWord ++ tailWord_129509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129509).length < 2 ^ (prefixWord ++ tailWord_129509).sum := by decide
  have hdescent : baseEnd_129509 < baseStart_129509 := by decide
  rcases family_descends (prefixWord ++ tailWord_129509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129523 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 5]
def baseStart_129523 : Nat := 118140960795 + 129523 * 2 ^ 59
def prefixEnd_129523 : Nat := 4983230072969 + 3 ^ 40 * 129523 * 2
def baseEnd_129523 : Nat := 29558913249956433051929

theorem tailTrace_129523 : CollatzResearch.WordTrace tailWord_129523 prefixEnd_129523 29558913249956433051929 := by
  unfold tailWord_129523
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724091909767766612385223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3149394606511844408256815 4724091909767766612385223)
  ·
    refine ⟨7086137864651649918577835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4724091909767766612385223 7086137864651649918577835)
    ·
      refine ⟨10629206796977474877866753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7086137864651649918577835 10629206796977474877866753)
      ·
        refine ⟨7971905097733106158400065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10629206796977474877866753 7971905097733106158400065)
        ·
          refine ⟨5978928823299829618800049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7971905097733106158400065 5978928823299829618800049)
          ·
            refine ⟨4484196617474872214100037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5978928823299829618800049 4484196617474872214100037)
            ·
              refine ⟨840786865776538540143757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4484196617474872214100037 840786865776538540143757)
              ·
                refine ⟨315295074666201952553909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840786865776538540143757 315295074666201952553909)
                ·
                  refine ⟨29558913249956433051929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315295074666201952553909 29558913249956433051929)
                  ·
                    rfl

theorem cell21_129523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_129523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129523 prefixEnd_129523 := by exact prefixLift 129523
  have htrace : WordTrace (prefixWord ++ tailWord_129523) baseStart_129523 baseEnd_129523 := by
    simpa [prefixWord, tailWord_129523, baseEnd_129523] using wordTrace_append hprefix tailTrace_129523
  have hstable : (prefixWord ++ tailWord_129523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129523).length < 2 ^ (prefixWord ++ tailWord_129523).sum := by decide
  have hdescent : baseEnd_129523 < baseStart_129523 := by decide
  rcases family_descends (prefixWord ++ tailWord_129523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129540 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_129540 : Nat := 118140960795 + 129540 * 2 ^ 59
def prefixEnd_129540 : Nat := 4983230072969 + 3 ^ 40 * 129540 * 2
def baseEnd_129540 : Nat := 29562792881568181268561

theorem tailTrace_129540 : CollatzResearch.WordTrace tailWord_129540 prefixEnd_129540 29562792881568181268561 := by
  unfold tailWord_129540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362355975353089257877037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3149807967137452343836049 2362355975353089257877037)
  ·
    refine ⟨885883490757408471703889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2362355975353089257877037 885883490757408471703889)
    ·
      refine ⟨664412618068056353777917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 885883490757408471703889 664412618068056353777917)
      ·
        refine ⟨249154731775521132666719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664412618068056353777917 249154731775521132666719)
        ·
          refine ⟨373732097663281699000079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249154731775521132666719 373732097663281699000079)
          ·
            refine ⟨560598146494922548500119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373732097663281699000079 560598146494922548500119)
            ·
              refine ⟨840897219742383822750179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560598146494922548500119 840897219742383822750179)
              ·
                refine ⟨1261345829613575734125269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840897219742383822750179 1261345829613575734125269)
                ·
                  refine ⟨29562792881568181268561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1261345829613575734125269 29562792881568181268561)
                  ·
                    rfl

theorem cell21_129540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_129540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129540 prefixEnd_129540 := by exact prefixLift 129540
  have htrace : WordTrace (prefixWord ++ tailWord_129540) baseStart_129540 baseEnd_129540 := by
    simpa [prefixWord, tailWord_129540, baseEnd_129540] using wordTrace_append hprefix tailTrace_129540
  have hstable : (prefixWord ++ tailWord_129540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129540).length < 2 ^ (prefixWord ++ tailWord_129540).sum := by decide
  have hdescent : baseEnd_129540 < baseStart_129540 := by decide
  rcases family_descends (prefixWord ++ tailWord_129540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129557 : List Nat := [1, 3, 2, 1, 3, 1, 4, 3, 3]
def baseStart_129557 : Nat := 118140960795 + 129557 * 2 ^ 59
def prefixEnd_129557 : Nat := 4983230072969 + 3 ^ 40 * 129557 * 2
def baseEnd_129557 : Nat := 29566672513179929485193

theorem tailTrace_129557 : CollatzResearch.WordTrace tailWord_129557 prefixEnd_129557 29566672513179929485193 := by
  unfold tailWord_129557
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725331991644590419122925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3150221327763060279415283 4725331991644590419122925)
  ·
    refine ⟨1771999496866721407171097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4725331991644590419122925 1771999496866721407171097)
    ·
      refine ⟨1328999622650041055378323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1771999496866721407171097 1328999622650041055378323)
      ·
        refine ⟨1993499433975061583067485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328999622650041055378323 1993499433975061583067485)
        ·
          refine ⟨747562287740648093650307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1993499433975061583067485 747562287740648093650307)
          ·
            refine ⟨1121343431610972140475461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747562287740648093650307 1121343431610972140475461)
            ·
              refine ⟨210251893427057276339149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1121343431610972140475461 210251893427057276339149)
              ·
                refine ⟨78844460035146478627181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210251893427057276339149 78844460035146478627181)
                ·
                  refine ⟨29566672513179929485193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78844460035146478627181 29566672513179929485193)
                  ·
                    rfl

theorem cell21_129557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_129557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129557 prefixEnd_129557 := by exact prefixLift 129557
  have htrace : WordTrace (prefixWord ++ tailWord_129557) baseStart_129557 baseEnd_129557 := by
    simpa [prefixWord, tailWord_129557, baseEnd_129557] using wordTrace_append hprefix tailTrace_129557
  have hstable : (prefixWord ++ tailWord_129557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129557).length < 2 ^ (prefixWord ++ tailWord_129557).sum := by decide
  have hdescent : baseEnd_129557 < baseStart_129557 := by decide
  rcases family_descends (prefixWord ++ tailWord_129557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129571 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 4]
def baseStart_129571 : Nat := 118140960795 + 129571 * 2 ^ 59
def prefixEnd_129571 : Nat := 4983230072969 + 3 ^ 40 * 129571 * 2
def baseEnd_129571 : Nat := 29569867503919016251831

theorem tailTrace_129571 : CollatzResearch.WordTrace tailWord_129571 prefixEnd_129571 29569867503919016251831 := by
  unfold tailWord_129571
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725842613593870810132567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3150561742395913873421711 4725842613593870810132567)
  ·
    refine ⟨7088763920390806215198851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4725842613593870810132567 7088763920390806215198851)
    ·
      refine ⟨10633145880586209322798277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088763920390806215198851 10633145880586209322798277)
      ·
        refine ⟨1993714852609914248024677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10633145880586209322798277 1993714852609914248024677)
        ·
          refine ⟨373821534864358921504627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1993714852609914248024677 373821534864358921504627)
          ·
            refine ⟨560732302296538382256941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373821534864358921504627 560732302296538382256941)
            ·
              refine ⟨210274613361201893346353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 560732302296538382256941 210274613361201893346353)
              ·
                refine ⟨157705960020901420009765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210274613361201893346353 157705960020901420009765)
                ·
                  refine ⟨29569867503919016251831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157705960020901420009765 29569867503919016251831)
                  ·
                    rfl

theorem cell21_129571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 4].length) (baseStart_129571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129571 prefixEnd_129571 := by exact prefixLift 129571
  have htrace : WordTrace (prefixWord ++ tailWord_129571) baseStart_129571 baseEnd_129571 := by
    simpa [prefixWord, tailWord_129571, baseEnd_129571] using wordTrace_append hprefix tailTrace_129571
  have hstable : (prefixWord ++ tailWord_129571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129571).length < 2 ^ (prefixWord ++ tailWord_129571).sum := by decide
  have hdescent : baseEnd_129571 < baseStart_129571 := by decide
  rcases family_descends (prefixWord ++ tailWord_129571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129599 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 5]
def baseStart_129599 : Nat := 118140960795 + 129599 * 2 ^ 59
def prefixEnd_129599 : Nat := 4983230072969 + 3 ^ 40 * 129599 * 2
def baseEnd_129599 : Nat := 29576257485397189785107

theorem tailTrace_129599 : CollatzResearch.WordTrace tailWord_129599 prefixEnd_129599 29576257485397189785107 := by
  unfold tailWord_129599
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726863857492431592151851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3151242571661621061434567 4726863857492431592151851)
  ·
    refine ⟨7090295786238647388227777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4726863857492431592151851 7090295786238647388227777)
    ·
      refine ⟨5317721839678985541170833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7090295786238647388227777 5317721839678985541170833)
      ·
        refine ⟨3988291379759239155878125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5317721839678985541170833 3988291379759239155878125)
        ·
          refine ⟨1495609267409714683454297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3988291379759239155878125 1495609267409714683454297)
          ·
            refine ⟨1121706950557286012590723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495609267409714683454297 1121706950557286012590723)
            ·
              refine ⟨1682560425835929018886085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121706950557286012590723 1682560425835929018886085)
              ·
                refine ⟨315480079844236691041141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1682560425835929018886085 315480079844236691041141)
                ·
                  refine ⟨29576257485397189785107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315480079844236691041141 29576257485397189785107)
                  ·
                    rfl

theorem cell21_129599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_129599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129599 prefixEnd_129599 := by exact prefixLift 129599
  have htrace : WordTrace (prefixWord ++ tailWord_129599) baseStart_129599 baseEnd_129599 := by
    simpa [prefixWord, tailWord_129599, baseEnd_129599] using wordTrace_append hprefix tailTrace_129599
  have hstable : (prefixWord ++ tailWord_129599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129599).length < 2 ^ (prefixWord ++ tailWord_129599).sum := by decide
  have hdescent : baseEnd_129599 < baseStart_129599 := by decide
  rcases family_descends (prefixWord ++ tailWord_129599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129616 : List Nat := [2, 1, 1, 1, 1, 3, 2, 7, 3]
def baseStart_129616 : Nat := 118140960795 + 129616 * 2 ^ 59
def prefixEnd_129616 : Nat := 4983230072969 + 3 ^ 40 * 129616 * 2
def baseEnd_129616 : Nat := 29580137117008938001739

theorem tailTrace_129616 : CollatzResearch.WordTrace tailWord_129616 prefixEnd_129616 29580137117008938001739 := by
  unfold tailWord_129616
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363741949215421747760351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3151655932287228997013801 2363741949215421747760351)
  ·
    refine ⟨3545612923823132621640527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2363741949215421747760351 3545612923823132621640527)
    ·
      refine ⟨5318419385734698932460791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545612923823132621640527 5318419385734698932460791)
      ·
        refine ⟨7977629078602048398691187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318419385734698932460791 7977629078602048398691187)
        ·
          refine ⟨11966443617903072598036781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977629078602048398691187 11966443617903072598036781)
          ·
            refine ⟨4487416356713652224263793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11966443617903072598036781 4487416356713652224263793)
            ·
              refine ⟨3365562267535239168197845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4487416356713652224263793 3365562267535239168197845)
              ·
                refine ⟨78880365645357168004637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3365562267535239168197845 78880365645357168004637)
                ·
                  refine ⟨29580137117008938001739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78880365645357168004637 29580137117008938001739)
                  ·
                    rfl

theorem cell21_129616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_129616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129616 prefixEnd_129616 := by exact prefixLift 129616
  have htrace : WordTrace (prefixWord ++ tailWord_129616) baseStart_129616 baseEnd_129616 := by
    simpa [prefixWord, tailWord_129616, baseEnd_129616] using wordTrace_append hprefix tailTrace_129616
  have hstable : (prefixWord ++ tailWord_129616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129616).length < 2 ^ (prefixWord ++ tailWord_129616).sum := by decide
  have hdescent : baseEnd_129616 < baseStart_129616 := by decide
  rcases family_descends (prefixWord ++ tailWord_129616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129644 : List Nat := [2, 2, 1, 1, 3, 1, 3, 8]
def baseStart_129644 : Nat := 118140960795 + 129644 * 2 ^ 59
def prefixEnd_129644 : Nat := 4983230072969 + 3 ^ 40 * 129644 * 2
def baseEnd_129644 : Nat := 9862175699495703845005

theorem tailTrace_129644 : CollatzResearch.WordTrace tailWord_129644 prefixEnd_129644 9862175699495703845005 := by
  unfold tailWord_129644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364252571164702138769993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3152336761552936185026657 2364252571164702138769993)
  ·
    refine ⟨1773189428373526604077495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2364252571164702138769993 1773189428373526604077495)
    ·
      refine ⟨2659784142560289906116243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773189428373526604077495 2659784142560289906116243)
      ·
        refine ⟨3989676213840434859174365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2659784142560289906116243 3989676213840434859174365)
        ·
          refine ⟨1496128580190163072190387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3989676213840434859174365 1496128580190163072190387)
          ·
            refine ⟨2244192870285244608285581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496128580190163072190387 2244192870285244608285581)
            ·
              refine ⟨841572326356966728107093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2244192870285244608285581 841572326356966728107093)
              ·
                refine ⟨9862175699495703845005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 841572326356966728107093 9862175699495703845005)
                ·
                  rfl

theorem cell21_129644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_129644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129644 prefixEnd_129644 := by exact prefixLift 129644
  have htrace : WordTrace (prefixWord ++ tailWord_129644) baseStart_129644 baseEnd_129644 := by
    simpa [prefixWord, tailWord_129644, baseEnd_129644] using wordTrace_append hprefix tailTrace_129644
  have hstable : (prefixWord ++ tailWord_129644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129644).length < 2 ^ (prefixWord ++ tailWord_129644).sum := by decide
  have hdescent : baseEnd_129644 < baseStart_129644 := by decide
  rcases family_descends (prefixWord ++ tailWord_129644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129647 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 4]
def baseStart_129647 : Nat := 118140960795 + 129647 * 2 ^ 59
def prefixEnd_129647 : Nat := 4983230072969 + 3 ^ 40 * 129647 * 2
def baseEnd_129647 : Nat := 29587211739359772985009

theorem tailTrace_129647 : CollatzResearch.WordTrace tailWord_129647 prefixEnd_129647 29587211739359772985009 := by
  unfold tailWord_129647
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728614561318535789899195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3152409707545690526599463 4728614561318535789899195)
  ·
    refine ⟨7092921841977803684848793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4728614561318535789899195 7092921841977803684848793)
    ·
      refine ⟨5319691381483352763636595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7092921841977803684848793 5319691381483352763636595)
      ·
        refine ⟨7979537072225029145454893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5319691381483352763636595 7979537072225029145454893)
        ·
          refine ⟨2992326402084385929545585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7979537072225029145454893 2992326402084385929545585)
          ·
            refine ⟨2244244801563289447159189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992326402084385929545585 2244244801563289447159189)
            ·
              refine ⟨105198975073279192835587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2244244801563289447159189 105198975073279192835587)
              ·
                refine ⟨157798462609918789253381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105198975073279192835587 157798462609918789253381)
                ·
                  refine ⟨29587211739359772985009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157798462609918789253381 29587211739359772985009)
                  ·
                    rfl

theorem cell21_129647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 4].length) (baseStart_129647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129647 prefixEnd_129647 := by exact prefixLift 129647
  have htrace : WordTrace (prefixWord ++ tailWord_129647) baseStart_129647 baseEnd_129647 := by
    simpa [prefixWord, tailWord_129647, baseEnd_129647] using wordTrace_append hprefix tailTrace_129647
  have hstable : (prefixWord ++ tailWord_129647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129647).length < 2 ^ (prefixWord ++ tailWord_129647).sum := by decide
  have hdescent : baseEnd_129647 < baseStart_129647 := by decide
  rcases family_descends (prefixWord ++ tailWord_129647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129740 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_129740 : Nat := 118140960795 + 129740 * 2 ^ 59
def prefixEnd_129740 : Nat := 4983230072969 + 3 ^ 40 * 129740 * 2
def baseEnd_129740 : Nat := 29608435606412277934819

theorem tailTrace_129740 : CollatzResearch.WordTrace tailWord_129740 prefixEnd_129740 29608435606412277934819 := by
  unfold tailWord_129740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366003274990806336517337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3154671033321075115356449 2366003274990806336517337)
  ·
    refine ⟨1774502456243104752388003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2366003274990806336517337 1774502456243104752388003)
    ·
      refine ⟨2661753684364657128582005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774502456243104752388003 2661753684364657128582005)
      ·
        refine ⟨249539407909186605804563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2661753684364657128582005 249539407909186605804563)
        ·
          refine ⟨374309111863779908706845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249539407909186605804563 374309111863779908706845)
          ·
            refine ⟨140365916948917465765067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374309111863779908706845 140365916948917465765067)
            ·
              refine ⟨210548875423376198647601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140365916948917465765067 210548875423376198647601)
              ·
                refine ⟨157911656567532148985701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210548875423376198647601 157911656567532148985701)
                ·
                  refine ⟨29608435606412277934819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157911656567532148985701 29608435606412277934819)
                  ·
                    rfl

theorem cell21_129740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_129740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129740 prefixEnd_129740 := by exact prefixLift 129740
  have htrace : WordTrace (prefixWord ++ tailWord_129740) baseStart_129740 baseEnd_129740 := by
    simpa [prefixWord, tailWord_129740, baseEnd_129740] using wordTrace_append hprefix tailTrace_129740
  have hstable : (prefixWord ++ tailWord_129740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129740).length < 2 ^ (prefixWord ++ tailWord_129740).sum := by decide
  have hdescent : baseEnd_129740 < baseStart_129740 := by decide
  rcases family_descends (prefixWord ++ tailWord_129740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129751 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 5]
def baseStart_129751 : Nat := 118140960795 + 129751 * 2 ^ 59
def prefixEnd_129751 : Nat := 4983230072969 + 3 ^ 40 * 129751 * 2
def baseEnd_129751 : Nat := 29610945956278703251463

theorem tailTrace_129751 : CollatzResearch.WordTrace tailWord_129751 prefixEnd_129751 29610945956278703251463 := by
  unfold tailWord_129751
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732407752941761551685107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3154938501961174367790071 4732407752941761551685107)
  ·
    refine ⟨7098611629412642327527661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4732407752941761551685107 7098611629412642327527661)
    ·
      refine ⟨2661979361029740872822873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7098611629412642327527661 2661979361029740872822873)
      ·
        refine ⟨1996484520772305654617155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2661979361029740872822873 1996484520772305654617155)
        ·
          refine ⟨2994726781158458481925733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996484520772305654617155 2994726781158458481925733)
          ·
            refine ⟨561511271467210965361075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2994726781158458481925733 561511271467210965361075)
            ·
              refine ⟨842266907200816448041613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561511271467210965361075 842266907200816448041613)
              ·
                refine ⟨315850090200306168015605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 842266907200816448041613 315850090200306168015605)
                ·
                  refine ⟨29610945956278703251463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315850090200306168015605 29610945956278703251463)
                  ·
                    rfl

theorem cell21_129751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_129751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129751 prefixEnd_129751 := by exact prefixLift 129751
  have htrace : WordTrace (prefixWord ++ tailWord_129751) baseStart_129751 baseEnd_129751 := by
    simpa [prefixWord, tailWord_129751, baseEnd_129751] using wordTrace_append hprefix tailTrace_129751
  have hstable : (prefixWord ++ tailWord_129751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129751).length < 2 ^ (prefixWord ++ tailWord_129751).sum := by decide
  have hdescent : baseEnd_129751 < baseStart_129751 := by decide
  rcases family_descends (prefixWord ++ tailWord_129751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129782 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_129782 : Nat := 118140960795 + 129782 * 2 ^ 59
def prefixEnd_129782 : Nat := 4983230072969 + 3 ^ 40 * 129782 * 2
def baseEnd_129782 : Nat := 29618020578629538234733

theorem tailTrace_129782 : CollatzResearch.WordTrace tailWord_129782 prefixEnd_129782 29618020578629538234733 := by
  unfold tailWord_129782
  simp only [CollatzResearch.WordTrace]
  refine ⟨295846150989340865378975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3155692277219635897375733 295846150989340865378975)
  ·
    refine ⟨443769226484011298068463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295846150989340865378975 443769226484011298068463)
    ·
      refine ⟨665653839726016947102695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443769226484011298068463 665653839726016947102695)
      ·
        refine ⟨998480759589025420654043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665653839726016947102695 998480759589025420654043)
        ·
          refine ⟨1497721139383538130981065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998480759589025420654043 1497721139383538130981065)
          ·
            refine ⟨1123290854537653598235799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497721139383538130981065 1123290854537653598235799)
            ·
              refine ⟨1684936281806480397353699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123290854537653598235799 1684936281806480397353699)
              ·
                refine ⟨2527404422709720596030549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684936281806480397353699 2527404422709720596030549)
                ·
                  refine ⟨29618020578629538234733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2527404422709720596030549 29618020578629538234733)
                  ·
                    rfl

theorem cell21_129782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_129782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129782 prefixEnd_129782 := by exact prefixLift 129782
  have htrace : WordTrace (prefixWord ++ tailWord_129782) baseStart_129782 baseEnd_129782 := by
    simpa [prefixWord, tailWord_129782, baseEnd_129782] using wordTrace_append hprefix tailTrace_129782
  have hstable : (prefixWord ++ tailWord_129782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129782).length < 2 ^ (prefixWord ++ tailWord_129782).sum := by decide
  have hdescent : baseEnd_129782 < baseStart_129782 := by decide
  rcases family_descends (prefixWord ++ tailWord_129782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129872 : List Nat := [2, 1, 1, 1, 1, 4, 5, 6]
def baseStart_129872 : Nat := 118140960795 + 129872 * 2 ^ 59
def prefixEnd_129872 : Nat := 4983230072969 + 3 ^ 40 * 129872 * 2
def baseEnd_129872 : Nat := 9879519934936460578183

theorem tailTrace_129872 : CollatzResearch.WordTrace tailWord_129872 prefixEnd_129872 9879519934936460578183 := by
  unfold tailWord_129872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2368410492751699608419935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3157880657002266144559913 2368410492751699608419935)
  ·
    refine ⟨3552615739127549412629903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2368410492751699608419935 3552615739127549412629903)
    ·
      refine ⟨5328923608691324118944855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552615739127549412629903 5328923608691324118944855)
      ·
        refine ⟨7993385413036986178417283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328923608691324118944855 7993385413036986178417283)
        ·
          refine ⟨11990078119555479267625925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993385413036986178417283 11990078119555479267625925)
          ·
            refine ⟨2248139647416652362679861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11990078119555479267625925 2248139647416652362679861)
            ·
              refine ⟨210763091945311159001237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2248139647416652362679861 210763091945311159001237)
              ·
                refine ⟨9879519934936460578183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 210763091945311159001237 9879519934936460578183)
                ·
                  rfl

theorem cell21_129872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_129872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129872 prefixEnd_129872 := by exact prefixLift 129872
  have htrace : WordTrace (prefixWord ++ tailWord_129872) baseStart_129872 baseEnd_129872 := by
    simpa [prefixWord, tailWord_129872, baseEnd_129872] using wordTrace_append hprefix tailTrace_129872
  have hstable : (prefixWord ++ tailWord_129872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129872).length < 2 ^ (prefixWord ++ tailWord_129872).sum := by decide
  have hdescent : baseEnd_129872 < baseStart_129872 := by decide
  rcases family_descends (prefixWord ++ tailWord_129872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129954 : List Nat := [3, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_129954 : Nat := 118140960795 + 129954 * 2 ^ 59
def prefixEnd_129954 : Nat := 4983230072969 + 3 ^ 40 * 129954 * 2
def baseEnd_129954 : Nat := 29657273321995461367715

theorem tailTrace_129954 : CollatzResearch.WordTrace tailWord_129954 prefixEnd_129954 29657273321995461367715 := by
  unfold tailWord_129954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184952942801581805331229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3159874514137551480883277 1184952942801581805331229)
  ·
    refine ⟨444357353550593176999211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1184952942801581805331229 444357353550593176999211)
    ·
      refine ⟨666536030325889765498817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444357353550593176999211 666536030325889765498817)
      ·
        refine ⟨499902022744417324124113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666536030325889765498817 499902022744417324124113)
        ·
          refine ⟨374926517058312993093085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499902022744417324124113 374926517058312993093085)
          ·
            refine ⟨140597443896867372409907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374926517058312993093085 140597443896867372409907)
            ·
              refine ⟨210896165845301058614861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140597443896867372409907 210896165845301058614861)
              ·
                refine ⟨79086062191987896980573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210896165845301058614861 79086062191987896980573)
                ·
                  refine ⟨29657273321995461367715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79086062191987896980573 29657273321995461367715)
                  ·
                    rfl

theorem cell21_129954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_129954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_129954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_129954 prefixEnd_129954 := by exact prefixLift 129954
  have htrace : WordTrace (prefixWord ++ tailWord_129954) baseStart_129954 baseEnd_129954 := by
    simpa [prefixWord, tailWord_129954, baseEnd_129954] using wordTrace_append hprefix tailTrace_129954
  have hstable : (prefixWord ++ tailWord_129954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129954).length < 2 ^ (prefixWord ++ tailWord_129954).sum := by decide
  have hdescent : baseEnd_129954 < baseStart_129954 := by decide
  rcases family_descends (prefixWord ++ tailWord_129954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130055 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 5]
def baseStart_130055 : Nat := 118140960795 + 130055 * 2 ^ 59
def prefixEnd_130055 : Nat := 4983230072969 + 3 ^ 40 * 130055 * 2
def baseEnd_130055 : Nat := 29680322898041730184175

theorem tailTrace_130055 : CollatzResearch.WordTrace tailWord_130055 prefixEnd_130055 29680322898041730184175 := by
  unfold tailWord_130055
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743495543840421470751619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3162330362560280980501079 4743495543840421470751619)
  ·
    refine ⟨7115243315760632206127429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4743495543840421470751619 7115243315760632206127429)
    ·
      refine ⟨1334108121705118538648893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7115243315760632206127429 1334108121705118538648893)
      ·
        refine ⟨500290545639419451993335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1334108121705118538648893 500290545639419451993335)
        ·
          refine ⟨750435818459129177990003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500290545639419451993335 750435818459129177990003)
          ·
            refine ⟨1125653727688693766985005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750435818459129177990003 1125653727688693766985005)
            ·
              refine ⟨422120147883260162619377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1125653727688693766985005 422120147883260162619377)
              ·
                refine ⟨316590110912445121964533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422120147883260162619377 316590110912445121964533)
                ·
                  refine ⟨29680322898041730184175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 316590110912445121964533 29680322898041730184175)
                  ·
                    rfl

theorem cell21_130055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_130055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130055 prefixEnd_130055 := by exact prefixLift 130055
  have htrace : WordTrace (prefixWord ++ tailWord_130055) baseStart_130055 baseEnd_130055 := by
    simpa [prefixWord, tailWord_130055, baseEnd_130055] using wordTrace_append hprefix tailTrace_130055
  have hstable : (prefixWord ++ tailWord_130055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130055).length < 2 ^ (prefixWord ++ tailWord_130055).sum := by decide
  have hdescent : baseEnd_130055 < baseStart_130055 := by decide
  rcases family_descends (prefixWord ++ tailWord_130055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130072 : List Nat := [2, 1, 2, 3, 2, 2, 1, 5, 3]
def baseStart_130072 : Nat := 118140960795 + 130072 * 2 ^ 59
def prefixEnd_130072 : Nat := 4983230072969 + 3 ^ 40 * 130072 * 2
def baseEnd_130072 : Nat := 29684202529653478400807

theorem tailTrace_130072 : CollatzResearch.WordTrace tailWord_130072 prefixEnd_130072 29684202529653478400807 := by
  unfold tailWord_130072
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372057792389416687060235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3162743723185888916080313 2372057792389416687060235)
  ·
    refine ⟨3558086688584125030590353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2372057792389416687060235 3558086688584125030590353)
    ·
      refine ⟨2668565016438093772942765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3558086688584125030590353 2668565016438093772942765)
      ·
        refine ⟨1000711881164285164853537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2668565016438093772942765 1000711881164285164853537)
        ·
          refine ⟨750533910873213873640153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000711881164285164853537 750533910873213873640153)
          ·
            refine ⟨562900433154910405230115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750533910873213873640153 562900433154910405230115)
            ·
              refine ⟨844350649732365607845173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562900433154910405230115 844350649732365607845173)
              ·
                refine ⟨79157873412409275735485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 844350649732365607845173 79157873412409275735485)
                ·
                  refine ⟨29684202529653478400807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79157873412409275735485 29684202529653478400807)
                  ·
                    rfl

theorem cell21_130072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_130072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130072 prefixEnd_130072 := by exact prefixLift 130072
  have htrace : WordTrace (prefixWord ++ tailWord_130072) baseStart_130072 baseEnd_130072 := by
    simpa [prefixWord, tailWord_130072, baseEnd_130072] using wordTrace_append hprefix tailTrace_130072
  have hstable : (prefixWord ++ tailWord_130072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130072).length < 2 ^ (prefixWord ++ tailWord_130072).sum := by decide
  have hdescent : baseEnd_130072 < baseStart_130072 := by decide
  rcases family_descends (prefixWord ++ tailWord_130072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130145 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 6]
def baseStart_130145 : Nat := 118140960795 + 130145 * 2 ^ 59
def prefixEnd_130145 : Nat := 4983230072969 + 3 ^ 40 * 130145 * 2
def baseEnd_130145 : Nat := 29700862124221573683991

theorem tailTrace_130145 : CollatzResearch.WordTrace tailWord_130145 prefixEnd_130145 29700862124221573683991 := by
  unfold tailWord_130145
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746778113514366841527889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3164518742342911227685259 4746778113514366841527889)
  ·
    refine ⟨3560083585135775131145917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4746778113514366841527889 3560083585135775131145917)
    ·
      refine ⟨1335031344425915674179719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3560083585135775131145917 1335031344425915674179719)
      ·
        refine ⟨2002547016638873511269579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335031344425915674179719 2002547016638873511269579)
        ·
          refine ⟨3003820524958310266904369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002547016638873511269579 3003820524958310266904369)
          ·
            refine ⟨2252865393718732700178277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3003820524958310266904369 2252865393718732700178277)
            ·
              refine ⟨422412261322262381283427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2252865393718732700178277 422412261322262381283427)
              ·
                refine ⟨633618391983393571925141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422412261322262381283427 633618391983393571925141)
                ·
                  refine ⟨29700862124221573683991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 633618391983393571925141 29700862124221573683991)
                  ·
                    rfl

theorem cell21_130145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_130145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130145 prefixEnd_130145 := by exact prefixLift 130145
  have htrace : WordTrace (prefixWord ++ tailWord_130145) baseStart_130145 baseEnd_130145 := by
    simpa [prefixWord, tailWord_130145, baseEnd_130145] using wordTrace_append hprefix tailTrace_130145
  have hstable : (prefixWord ++ tailWord_130145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130145).length < 2 ^ (prefixWord ++ tailWord_130145).sum := by decide
  have hdescent : baseEnd_130145 < baseStart_130145 := by decide
  rcases family_descends (prefixWord ++ tailWord_130145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130162 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_130162 : Nat := 118140960795 + 130162 * 2 ^ 59
def prefixEnd_130162 : Nat := 4983230072969 + 3 ^ 40 * 130162 * 2
def baseEnd_130162 : Nat := 29704741755833321900623

theorem tailTrace_130162 : CollatzResearch.WordTrace tailWord_130162 prefixEnd_130162 29704741755833321900623 := by
  unfold tailWord_130162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186849538613194686224185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3164932102968519163264493 1186849538613194686224185)
  ·
    refine ⟨890137153959896014668139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1186849538613194686224185 890137153959896014668139)
    ·
      refine ⟨1335205730939844022002209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890137153959896014668139 1335205730939844022002209)
      ·
        refine ⟨1001404298204883016501657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1335205730939844022002209 1001404298204883016501657)
        ·
          refine ⟨751053223653662262376243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001404298204883016501657 751053223653662262376243)
          ·
            refine ⟨1126579835480493393564365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751053223653662262376243 1126579835480493393564365)
            ·
              refine ⟨422467438305185022586637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126579835480493393564365 422467438305185022586637)
              ·
                refine ⟨158425289364444383469989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422467438305185022586637 158425289364444383469989)
                ·
                  refine ⟨29704741755833321900623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158425289364444383469989 29704741755833321900623)
                  ·
                    rfl

theorem cell21_130162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_130162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130162 prefixEnd_130162 := by exact prefixLift 130162
  have htrace : WordTrace (prefixWord ++ tailWord_130162) baseStart_130162 baseEnd_130162 := by
    simpa [prefixWord, tailWord_130162, baseEnd_130162] using wordTrace_append hprefix tailTrace_130162
  have hstable : (prefixWord ++ tailWord_130162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130162).length < 2 ^ (prefixWord ++ tailWord_130162).sum := by decide
  have hdescent : baseEnd_130162 < baseStart_130162 := by decide
  rcases family_descends (prefixWord ++ tailWord_130162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130210 : List Nat := [3, 3, 1, 3, 2, 2, 1, 6]
def baseStart_130210 : Nat := 118140960795 + 130210 * 2 ^ 59
def prefixEnd_130210 : Nat := 4983230072969 + 3 ^ 40 * 130210 * 2
def baseEnd_130210 : Nat := 9905232003265301700175

theorem tailTrace_130210 : CollatzResearch.WordTrace tailWord_130210 prefixEnd_130210 9905232003265301700175 := by
  unfold tailWord_130210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187287214569720735661021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3166099238852588628429389 1187287214569720735661021)
  ·
    refine ⟨445232705463645275872883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1187287214569720735661021 445232705463645275872883)
    ·
      refine ⟨667849058195467913809325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445232705463645275872883 667849058195467913809325)
      ·
        refine ⟨250443396823300467678497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667849058195467913809325 250443396823300467678497)
        ·
          refine ⟨187832547617475350758873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250443396823300467678497 187832547617475350758873)
          ·
            refine ⟨140874410713106513069155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187832547617475350758873 140874410713106513069155)
            ·
              refine ⟨211311616069659769603733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140874410713106513069155 211311616069659769603733)
              ·
                refine ⟨9905232003265301700175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211311616069659769603733 9905232003265301700175)
                ·
                  rfl

theorem cell21_130210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_130210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130210 prefixEnd_130210 := by exact prefixLift 130210
  have htrace : WordTrace (prefixWord ++ tailWord_130210) baseStart_130210 baseEnd_130210 := by
    simpa [prefixWord, tailWord_130210, baseEnd_130210] using wordTrace_append hprefix tailTrace_130210
  have hstable : (prefixWord ++ tailWord_130210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130210).length < 2 ^ (prefixWord ++ tailWord_130210).sum := by decide
  have hdescent : baseEnd_130210 < baseStart_130210 := by decide
  rcases family_descends (prefixWord ++ tailWord_130210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130241 : List Nat := [1, 2, 6, 1, 1, 1, 1, 5, 3]
def baseStart_130241 : Nat := 118140960795 + 130241 * 2 ^ 59
def prefixEnd_130241 : Nat := 4983230072969 + 3 ^ 40 * 130241 * 2
def baseEnd_130241 : Nat := 29722770632146740083795

theorem tailTrace_130241 : CollatzResearch.WordTrace tailWord_130241 prefixEnd_130241 29722770632146740083795 := by
  unfold tailWord_130241
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750279521166575237022577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3166853014111050158015051 4750279521166575237022577)
  ·
    refine ⟨3562709640874931427766933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4750279521166575237022577 3562709640874931427766933)
    ·
      refine ⟨167002014416012410676575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3562709640874931427766933 167002014416012410676575)
      ·
        refine ⟨250503021624018616014863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167002014416012410676575 250503021624018616014863)
        ·
          refine ⟨375754532436027924022295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250503021624018616014863 375754532436027924022295)
          ·
            refine ⟨563631798654041886033443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375754532436027924022295 563631798654041886033443)
            ·
              refine ⟨845447697981062829050165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563631798654041886033443 845447697981062829050165)
              ·
                refine ⟨79260721685724640223453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 845447697981062829050165 79260721685724640223453)
                ·
                  refine ⟨29722770632146740083795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79260721685724640223453 29722770632146740083795)
                  ·
                    rfl

theorem cell21_130241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_130241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130241 prefixEnd_130241 := by exact prefixLift 130241
  have htrace : WordTrace (prefixWord ++ tailWord_130241) baseStart_130241 baseEnd_130241 := by
    simpa [prefixWord, tailWord_130241, baseEnd_130241] using wordTrace_append hprefix tailTrace_130241
  have hstable : (prefixWord ++ tailWord_130241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130241).length < 2 ^ (prefixWord ++ tailWord_130241).sum := by decide
  have hdescent : baseEnd_130241 < baseStart_130241 := by decide
  rcases family_descends (prefixWord ++ tailWord_130241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130292 : List Nat := [2, 6, 1, 2, 1, 2, 1, 3, 3]
def baseStart_130292 : Nat := 118140960795 + 130292 * 2 ^ 59
def prefixEnd_130292 : Nat := 4983230072969 + 3 ^ 40 * 130292 * 2
def baseEnd_130292 : Nat := 29734409526981984733691

theorem tailTrace_130292 : CollatzResearch.WordTrace tailWord_130292 prefixEnd_130292 29734409526981984733691 := by
  unfold tailWord_130292
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376069821990905473564565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3168093095987873964752753 2376069821990905473564565)
  ·
    refine ⟨111378272905823694073339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2376069821990905473564565 111378272905823694073339)
    ·
      refine ⟨167067409358735541110009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111378272905823694073339 167067409358735541110009)
      ·
        refine ⟨125300557019051655832507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167067409358735541110009 125300557019051655832507)
        ·
          refine ⟨187950835528577483748761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125300557019051655832507 187950835528577483748761)
          ·
            refine ⟨140963126646433112811571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187950835528577483748761 140963126646433112811571)
            ·
              refine ⟨211444689969649669217357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140963126646433112811571 211444689969649669217357)
              ·
                refine ⟨79291758738618625956509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211444689969649669217357 79291758738618625956509)
                ·
                  refine ⟨29734409526981984733691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79291758738618625956509 29734409526981984733691)
                  ·
                    rfl

theorem cell21_130292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_130292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130292 prefixEnd_130292 := by exact prefixLift 130292
  have htrace : WordTrace (prefixWord ++ tailWord_130292) baseStart_130292 baseEnd_130292 := by
    simpa [prefixWord, tailWord_130292, baseEnd_130292] using wordTrace_append hprefix tailTrace_130292
  have hstable : (prefixWord ++ tailWord_130292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130292).length < 2 ^ (prefixWord ++ tailWord_130292).sum := by decide
  have hdescent : baseEnd_130292 < baseStart_130292 := by decide
  rcases family_descends (prefixWord ++ tailWord_130292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130328 : List Nat := [2, 1, 2, 3, 1, 4, 2, 6]
def baseStart_130328 : Nat := 118140960795 + 130328 * 2 ^ 59
def prefixEnd_130328 : Nat := 4983230072969 + 3 ^ 40 * 130328 * 2
def baseEnd_130328 : Nat := 9914208405817974044539

theorem tailTrace_130328 : CollatzResearch.WordTrace tailWord_130328 prefixEnd_130328 9914208405817974044539 := by
  unfold tailWord_130328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376726335925694547719819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3168968447900926063626425 2376726335925694547719819)
  ·
    refine ⟨3565089503888541821579729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2376726335925694547719819 3565089503888541821579729)
    ·
      refine ⟨2673817127916406366184797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3565089503888541821579729 2673817127916406366184797)
      ·
        refine ⟨1002681422968652387319299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2673817127916406366184797 1002681422968652387319299)
        ·
          refine ⟨1504022134452978580978949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002681422968652387319299 1504022134452978580978949)
          ·
            refine ⟨282004150209933483933553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1504022134452978580978949 282004150209933483933553)
            ·
              refine ⟨211503112657450112950165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282004150209933483933553 211503112657450112950165)
              ·
                refine ⟨9914208405817974044539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211503112657450112950165 9914208405817974044539)
                ·
                  rfl

theorem cell21_130328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_130328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130328 prefixEnd_130328 := by exact prefixLift 130328
  have htrace : WordTrace (prefixWord ++ tailWord_130328) baseStart_130328 baseEnd_130328 := by
    simpa [prefixWord, tailWord_130328, baseEnd_130328] using wordTrace_append hprefix tailTrace_130328
  have hstable : (prefixWord ++ tailWord_130328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130328).length < 2 ^ (prefixWord ++ tailWord_130328).sum := by decide
  have hdescent : baseEnd_130328 < baseStart_130328 := by decide
  rcases family_descends (prefixWord ++ tailWord_130328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130418 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_130418 : Nat := 118140960795 + 130418 * 2 ^ 59
def prefixEnd_130418 : Nat := 4983230072969 + 3 ^ 40 * 130418 * 2
def baseEnd_130418 : Nat := 29763164443633765633433

theorem tailTrace_130418 : CollatzResearch.WordTrace tailWord_130418 prefixEnd_130418 29763164443633765633433 := by
  unfold tailWord_130418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189183810381333616553977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3171156827683556310810605 1189183810381333616553977)
  ·
    refine ⟨891887857786000212415483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1189183810381333616553977 891887857786000212415483)
    ·
      refine ⟨1337831786679000318623225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 891887857786000212415483 1337831786679000318623225)
      ·
        refine ⟨1003373840009250238967419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337831786679000318623225 1003373840009250238967419)
        ·
          refine ⟨1505060760013875358451129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003373840009250238967419 1505060760013875358451129)
          ·
            refine ⟨1128795570010406518838347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505060760013875358451129 1128795570010406518838347)
            ·
              refine ⟨1693193355015609778257521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128795570010406518838347 1693193355015609778257521)
              ·
                refine ⟨1269895016261707333693141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693193355015609778257521 1269895016261707333693141)
                ·
                  refine ⟨29763164443633765633433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1269895016261707333693141 29763164443633765633433)
                  ·
                    rfl

theorem cell21_130418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_130418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130418 prefixEnd_130418 := by exact prefixLift 130418
  have htrace : WordTrace (prefixWord ++ tailWord_130418) baseStart_130418 baseEnd_130418 := by
    simpa [prefixWord, tailWord_130418, baseEnd_130418] using wordTrace_append hprefix tailTrace_130418
  have hstable : (prefixWord ++ tailWord_130418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130418).length < 2 ^ (prefixWord ++ tailWord_130418).sum := by decide
  have hdescent : baseEnd_130418 < baseStart_130418 := by decide
  rcases family_descends (prefixWord ++ tailWord_130418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130435 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 5]
def baseStart_130435 : Nat := 118140960795 + 130435 * 2 ^ 59
def prefixEnd_130435 : Nat := 4983230072969 + 3 ^ 40 * 130435 * 2
def baseEnd_130435 : Nat := 29767044075245513850065

theorem tailTrace_130435 : CollatzResearch.WordTrace tailWord_130435 prefixEnd_130435 29767044075245513850065 := by
  unfold tailWord_130435
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757355282463746369584759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3171570188309164246389839 4757355282463746369584759)
  ·
    refine ⟨7136032923695619554377139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4757355282463746369584759 7136032923695619554377139)
    ·
      refine ⟨10704049385543429331565709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136032923695619554377139 10704049385543429331565709)
      ·
        refine ⟨4014018519578785999337141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10704049385543429331565709 4014018519578785999337141)
        ·
          refine ⟨376314236210511187437857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4014018519578785999337141 376314236210511187437857)
          ·
            refine ⟨282235677157883390578393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376314236210511187437857 282235677157883390578393)
            ·
              refine ⟨211676757868412542933795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282235677157883390578393 211676757868412542933795)
              ·
                refine ⟨317515136802618814400693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211676757868412542933795 317515136802618814400693)
                ·
                  refine ⟨29767044075245513850065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 317515136802618814400693 29767044075245513850065)
                  ·
                    rfl

theorem cell21_130435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_130435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130435 prefixEnd_130435 := by exact prefixLift 130435
  have htrace : WordTrace (prefixWord ++ tailWord_130435) baseStart_130435 baseEnd_130435 := by
    simpa [prefixWord, tailWord_130435, baseEnd_130435] using wordTrace_append hprefix tailTrace_130435
  have hstable : (prefixWord ++ tailWord_130435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130435).length < 2 ^ (prefixWord ++ tailWord_130435).sum := by decide
  have hdescent : baseEnd_130435 < baseStart_130435 := by decide
  rcases family_descends (prefixWord ++ tailWord_130435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130500 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_130500 : Nat := 118140960795 + 130500 * 2 ^ 59
def prefixEnd_130500 : Nat := 4983230072969 + 3 ^ 40 * 130500 * 2
def baseEnd_130500 : Nat := 29781877960819845266599

theorem tailTrace_130500 : CollatzResearch.WordTrace tailWord_130500 prefixEnd_130500 29781877960819845266599 := by
  unfold tailWord_130500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379863013614131235350477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3173150684818841647133969 2379863013614131235350477)
  ·
    refine ⟨892448630105299213256429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2379863013614131235350477 892448630105299213256429)
    ·
      refine ⟨334668236289487204971161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 892448630105299213256429 334668236289487204971161)
      ·
        refine ⟨251001177217115403728371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334668236289487204971161 251001177217115403728371)
        ·
          refine ⟨376501765825673105592557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251001177217115403728371 376501765825673105592557)
          ·
            refine ⟨141188162184627414597209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376501765825673105592557 141188162184627414597209)
            ·
              refine ⟨105891121638470560947907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141188162184627414597209 105891121638470560947907)
              ·
                refine ⟨158836682457705841421861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105891121638470560947907 158836682457705841421861)
                ·
                  refine ⟨29781877960819845266599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158836682457705841421861 29781877960819845266599)
                  ·
                    rfl

theorem cell21_130500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_130500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130500 prefixEnd_130500 := by exact prefixLift 130500
  have htrace : WordTrace (prefixWord ++ tailWord_130500) baseStart_130500 baseEnd_130500 := by
    simpa [prefixWord, tailWord_130500, baseEnd_130500] using wordTrace_append hprefix tailTrace_130500
  have hstable : (prefixWord ++ tailWord_130500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130500).length < 2 ^ (prefixWord ++ tailWord_130500).sum := by decide
  have hdescent : baseEnd_130500 < baseStart_130500 := by decide
  rcases family_descends (prefixWord ++ tailWord_130500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130542 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_130542 : Nat := 118140960795 + 130542 * 2 ^ 59
def prefixEnd_130542 : Nat := 4983230072969 + 3 ^ 40 * 130542 * 2
def baseEnd_130542 : Nat := 29791462933037105566513

theorem tailTrace_130542 : CollatzResearch.WordTrace tailWord_130542 prefixEnd_130542 29791462933037105566513 := by
  unfold tailWord_130542
  simp only [CollatzResearch.WordTrace]
  refine ⟨595157236634512955466235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3174171928717402429153253 595157236634512955466235)
  ·
    refine ⟨892735854951769433199353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 595157236634512955466235 892735854951769433199353)
    ·
      refine ⟨669551891213827074899515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 892735854951769433199353 669551891213827074899515)
      ·
        refine ⟨1004327836820740612349273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669551891213827074899515 1004327836820740612349273)
        ·
          refine ⟨753245877615555459261955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1004327836820740612349273 753245877615555459261955)
          ·
            refine ⟨1129868816423333188892933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753245877615555459261955 1129868816423333188892933)
            ·
              refine ⟨211850403079374972917425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1129868816423333188892933 211850403079374972917425)
              ·
                refine ⟨158887802309531229688069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211850403079374972917425 158887802309531229688069)
                ·
                  refine ⟨29791462933037105566513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158887802309531229688069 29791462933037105566513)
                  ·
                    rfl

theorem cell21_130542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_130542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130542 prefixEnd_130542 := by exact prefixLift 130542
  have htrace : WordTrace (prefixWord ++ tailWord_130542) baseStart_130542 baseEnd_130542 := by
    simpa [prefixWord, tailWord_130542, baseEnd_130542] using wordTrace_append hprefix tailTrace_130542
  have hstable : (prefixWord ++ tailWord_130542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130542).length < 2 ^ (prefixWord ++ tailWord_130542).sum := by decide
  have hdescent : baseEnd_130542 < baseStart_130542 := by decide
  rcases family_descends (prefixWord ++ tailWord_130542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130545 : List Nat := [1, 2, 2, 2, 3, 4, 2, 2, 3]
def baseStart_130545 : Nat := 118140960795 + 130545 * 2 ^ 59
def prefixEnd_130545 : Nat := 4983230072969 + 3 ^ 40 * 130545 * 2
def baseEnd_130545 : Nat := 29792147573909767016507

theorem tailTrace_130545 : CollatzResearch.WordTrace tailWord_130545 prefixEnd_130545 29792147573909767016507 := by
  unfold tailWord_130545
  simp only [CollatzResearch.WordTrace]
  refine ⟨4761367312065235156089089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3174244874710156770726059 4761367312065235156089089)
  ·
    refine ⟨3571025484048926367066817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4761367312065235156089089 3571025484048926367066817)
    ·
      refine ⟨2678269113036694775300113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3571025484048926367066817 2678269113036694775300113)
      ·
        refine ⟨2008701834777521081475085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2678269113036694775300113 2008701834777521081475085)
        ·
          refine ⟨753263188041570405553157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2008701834777521081475085 753263188041570405553157)
          ·
            refine ⟨141236847757794451041217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 753263188041570405553157 141236847757794451041217)
            ·
              refine ⟨105927635818345838280913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141236847757794451041217 105927635818345838280913)
              ·
                refine ⟨79445726863759378710685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105927635818345838280913 79445726863759378710685)
                ·
                  refine ⟨29792147573909767016507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79445726863759378710685 29792147573909767016507)
                  ·
                    rfl

theorem cell21_130545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_130545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130545 prefixEnd_130545 := by exact prefixLift 130545
  have htrace : WordTrace (prefixWord ++ tailWord_130545) baseStart_130545 baseEnd_130545 := by
    simpa [prefixWord, tailWord_130545, baseEnd_130545] using wordTrace_append hprefix tailTrace_130545
  have hstable : (prefixWord ++ tailWord_130545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130545).length < 2 ^ (prefixWord ++ tailWord_130545).sum := by decide
  have hdescent : baseEnd_130545 < baseStart_130545 := by decide
  rcases family_descends (prefixWord ++ tailWord_130545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130570 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_130570 : Nat := 118140960795 + 130570 * 2 ^ 59
def prefixEnd_130570 : Nat := 4983230072969 + 3 ^ 40 * 130570 * 2
def baseEnd_130570 : Nat := 29797852914515279099789

theorem tailTrace_130570 : CollatzResearch.WordTrace tailWord_130570 prefixEnd_130570 29797852914515279099789 := by
  unfold tailWord_130570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190569784243666106437291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3174852757983109617166109 1190569784243666106437291)
  ·
    refine ⟨1785854676365499159655937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1190569784243666106437291 1785854676365499159655937)
    ·
      refine ⟨1339391007274124369741953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1785854676365499159655937 1339391007274124369741953)
      ·
        refine ⟨1004543255455593277306465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1339391007274124369741953 1004543255455593277306465)
        ·
          refine ⟨753407441591694957979849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1004543255455593277306465 753407441591694957979849)
          ·
            refine ⟨565055581193771218484887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753407441591694957979849 565055581193771218484887)
            ·
              refine ⟨847583371790656827727331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565055581193771218484887 847583371790656827727331)
              ·
                refine ⟨1271375057685985241590997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847583371790656827727331 1271375057685985241590997)
                ·
                  refine ⟨29797852914515279099789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1271375057685985241590997 29797852914515279099789)
                  ·
                    rfl

theorem cell21_130570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_130570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130570 prefixEnd_130570 := by exact prefixLift 130570
  have htrace : WordTrace (prefixWord ++ tailWord_130570) baseStart_130570 baseEnd_130570 := by
    simpa [prefixWord, tailWord_130570, baseEnd_130570] using wordTrace_append hprefix tailTrace_130570
  have hstable : (prefixWord ++ tailWord_130570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130570).length < 2 ^ (prefixWord ++ tailWord_130570).sum := by decide
  have hdescent : baseEnd_130570 < baseStart_130570 := by decide
  rcases family_descends (prefixWord ++ tailWord_130570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130618 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_130618 : Nat := 118140960795 + 130618 * 2 ^ 59
def prefixEnd_130618 : Nat := 4983230072969 + 3 ^ 40 * 130618 * 2
def baseEnd_130618 : Nat := 29808807168477862299691

theorem tailTrace_130618 : CollatzResearch.WordTrace tailWord_130618 prefixEnd_130618 29808807168477862299691 := by
  unfold tailWord_130618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191007460200192155874127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3176019893867179082331005 1191007460200192155874127)
  ·
    refine ⟨1786511190300288233811191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1191007460200192155874127 1786511190300288233811191)
    ·
      refine ⟨2679766785450432350716787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786511190300288233811191 2679766785450432350716787)
      ·
        refine ⟨4019650178175648526075181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679766785450432350716787 4019650178175648526075181)
        ·
          refine ⟨1507368816815868197278193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4019650178175648526075181 1507368816815868197278193)
          ·
            refine ⟨1130526612611901147958645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507368816815868197278193 1130526612611901147958645)
            ·
              refine ⟨105986869932365732621123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1130526612611901147958645 105986869932365732621123)
              ·
                refine ⟨158980304898548598931685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105986869932365732621123 158980304898548598931685)
                ·
                  refine ⟨29808807168477862299691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158980304898548598931685 29808807168477862299691)
                  ·
                    rfl

theorem cell21_130618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_130618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130618 prefixEnd_130618 := by exact prefixLift 130618
  have htrace : WordTrace (prefixWord ++ tailWord_130618) baseStart_130618 baseEnd_130618 := by
    simpa [prefixWord, tailWord_130618, baseEnd_130618] using wordTrace_append hprefix tailTrace_130618
  have hstable : (prefixWord ++ tailWord_130618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130618).length < 2 ^ (prefixWord ++ tailWord_130618).sum := by decide
  have hdescent : baseEnd_130618 < baseStart_130618 := by decide
  rcases family_descends (prefixWord ++ tailWord_130618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130663 : List Nat := [1, 1, 5, 1, 1, 1, 2, 6, 3]
def baseStart_130663 : Nat := 118140960795 + 130663 * 2 ^ 59
def prefixEnd_130663 : Nat := 4983230072969 + 3 ^ 40 * 130663 * 2
def baseEnd_130663 : Nat := 29819076781567784049599

theorem tailTrace_130663 : CollatzResearch.WordTrace tailWord_130663 prefixEnd_130663 29819076781567784049599 := by
  unfold tailWord_130663
  simp only [CollatzResearch.WordTrace]
  refine ⟨4765671125637741308884643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3177114083758494205923095 4765671125637741308884643)
  ·
    refine ⟨7148506688456611963326965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4765671125637741308884643 7148506688456611963326965)
    ·
      refine ⟨670172502042807371561903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7148506688456611963326965 670172502042807371561903)
      ·
        refine ⟨1005258753064211057342855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670172502042807371561903 1005258753064211057342855)
        ·
          refine ⟨1507888129596316586014283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005258753064211057342855 1507888129596316586014283)
          ·
            refine ⟨2261832194394474879021425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507888129596316586014283 2261832194394474879021425)
            ·
              refine ⟨1696374145795856159266069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261832194394474879021425 1696374145795856159266069)
              ·
                refine ⟨79517538084180757465597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1696374145795856159266069 79517538084180757465597)
                ·
                  refine ⟨29819076781567784049599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79517538084180757465597 29819076781567784049599)
                  ·
                    rfl

theorem cell21_130663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 3].length) (baseStart_130663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130663 prefixEnd_130663 := by exact prefixLift 130663
  have htrace : WordTrace (prefixWord ++ tailWord_130663) baseStart_130663 baseEnd_130663 := by
    simpa [prefixWord, tailWord_130663, baseEnd_130663] using wordTrace_append hprefix tailTrace_130663
  have hstable : (prefixWord ++ tailWord_130663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130663).length < 2 ^ (prefixWord ++ tailWord_130663).sum := by decide
  have hdescent : baseEnd_130663 < baseStart_130663 := by decide
  rcases family_descends (prefixWord ++ tailWord_130663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130705 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 9]
def baseStart_130705 : Nat := 118140960795 + 130705 * 2 ^ 59
def prefixEnd_130705 : Nat := 4983230072969 + 3 ^ 40 * 130705 * 2
def baseEnd_130705 : Nat := 29828661753785044349513

theorem tailTrace_130705 : CollatzResearch.WordTrace tailWord_130705 prefixEnd_130705 29828661753785044349513 := by
  unfold tailWord_130705
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767202991485582481913569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3178135327657054987942379 4767202991485582481913569)
  ·
    refine ⟨3575402243614186861435177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4767202991485582481913569 3575402243614186861435177)
    ·
      refine ⟨2681551682710640146076383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3575402243614186861435177 2681551682710640146076383)
      ·
        refine ⟨4022327524065960219114575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681551682710640146076383 4022327524065960219114575)
        ·
          refine ⟨6033491286098940328671863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022327524065960219114575 6033491286098940328671863)
          ·
            refine ⟨9050236929148410493007795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6033491286098940328671863 9050236929148410493007795)
            ·
              refine ⟨13575355393722615739511693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9050236929148410493007795 13575355393722615739511693)
              ·
                refine ⟨5090758272645980902316885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13575355393722615739511693 5090758272645980902316885)
                ·
                  refine ⟨29828661753785044349513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5090758272645980902316885 29828661753785044349513)
                  ·
                    rfl

theorem cell21_130705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_130705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130705 prefixEnd_130705 := by exact prefixLift 130705
  have htrace : WordTrace (prefixWord ++ tailWord_130705) baseStart_130705 baseEnd_130705 := by
    simpa [prefixWord, tailWord_130705, baseEnd_130705] using wordTrace_append hprefix tailTrace_130705
  have hstable : (prefixWord ++ tailWord_130705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130705).length < 2 ^ (prefixWord ++ tailWord_130705).sum := by decide
  have hdescent : baseEnd_130705 < baseStart_130705 := by decide
  rcases family_descends (prefixWord ++ tailWord_130705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
