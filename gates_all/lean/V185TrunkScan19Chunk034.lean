import V185TrunkScan19Chunk033

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_341401 : List Nat := [1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_341401 : Nat := 118140960795 + 341401 * 2 ^ 59
def prefixEnd_341401 : Nat := 4983230072969 + 3 ^ 40 * 341401 * 2
def baseEnd_341401 : Nat := 103883146030058667091811

theorem tailTrace_341401 : CollatzResearch.WordTrace tailWord_341401 prefixEnd_341401 103883146030058667091811 := by
  unfold tailWord_341401
  simp only [CollatzResearch.WordTrace]
  refine ⟨12451917436169958493880057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8301278290779972329253371 12451917436169958493880057)
  ·
    refine ⟨9338938077127468870410043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12451917436169958493880057 9338938077127468870410043)
    ·
      refine ⟨14008407115691203305615065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9338938077127468870410043 14008407115691203305615065)
      ·
        refine ⟨10506305336768402479211299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14008407115691203305615065 10506305336768402479211299)
        ·
          refine ⟨15759458005152603718816949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10506305336768402479211299 15759458005152603718816949)
          ·
            refine ⟨1477449187983056598639089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15759458005152603718816949 1477449187983056598639089)
            ·
              refine ⟨1108086890987292448979317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477449187983056598639089 1108086890987292448979317)
              ·
                refine ⟨103883146030058667091811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1108086890987292448979317 103883146030058667091811)
                ·
                  rfl

theorem cell19_341401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_341401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341401 prefixEnd_341401 := by exact prefixLift 341401
  have htrace : WordTrace (prefixWord ++ tailWord_341401) baseStart_341401 baseEnd_341401 := by
    simpa [prefixWord, tailWord_341401, baseEnd_341401] using wordTrace_append hprefix tailTrace_341401
  have hstable : (prefixWord ++ tailWord_341401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341401).length < 2 ^ (prefixWord ++ tailWord_341401).sum := by decide
  have hdescent : baseEnd_341401 < baseStart_341401 := by decide
  rcases family_descends (prefixWord ++ tailWord_341401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341416 : List Nat := [2, 1, 6, 1, 3, 6]
def baseStart_341416 : Nat := 118140960795 + 341416 * 2 ^ 59
def prefixEnd_341416 : Nat := 4983230072969 + 3 ^ 40 * 341416 * 2
def baseEnd_341416 : Nat := 11543078922504786306493

theorem tailTrace_341416 : CollatzResearch.WordTrace tailWord_341416 prefixEnd_341416 11543078922504786306493 := by
  unfold tailWord_341416
  simp only [CollatzResearch.WordTrace]
  refine ⟨6226232265557808027838051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8301643020743744037117401 6226232265557808027838051)
  ·
    refine ⟨9339348398336712041757077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6226232265557808027838051 9339348398336712041757077)
    ·
      refine ⟨437781956172033376957363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9339348398336712041757077 437781956172033376957363)
      ·
        refine ⟨656672934258050065436045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437781956172033376957363 656672934258050065436045)
        ·
          refine ⟨246252350346768774538517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656672934258050065436045 246252350346768774538517)
          ·
            refine ⟨11543078922504786306493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 246252350346768774538517 11543078922504786306493)
            ·
              rfl

theorem cell19_341416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 6].length) (baseStart_341416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341416 prefixEnd_341416 := by exact prefixLift 341416
  have htrace : WordTrace (prefixWord ++ tailWord_341416) baseStart_341416 baseEnd_341416 := by
    simpa [prefixWord, tailWord_341416, baseEnd_341416] using wordTrace_append hprefix tailTrace_341416
  have hstable : (prefixWord ++ tailWord_341416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341416).length < 2 ^ (prefixWord ++ tailWord_341416).sum := by decide
  have hdescent : baseEnd_341416 < baseStart_341416 := by decide
  rcases family_descends (prefixWord ++ tailWord_341416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341418 : List Nat := [3, 1, 6, 9]
def baseStart_341418 : Nat := 118140960795 + 341418 * 2 ^ 59
def prefixEnd_341418 : Nat := 4983230072969 + 3 ^ 40 * 341418 * 2
def baseEnd_341418 : Nat := 1282571837928489687827

theorem tailTrace_341418 : CollatzResearch.WordTrace tailWord_341418 prefixEnd_341418 1282571837928489687827 := by
  unfold tailWord_341418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113134369277092599312227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8301691651405580264832605 3113134369277092599312227)
  ·
    refine ⟨4669701553915638898968341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3113134369277092599312227 4669701553915638898968341)
    ·
      refine ⟨218892260339795573389141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4669701553915638898968341 218892260339795573389141)
      ·
        refine ⟨1282571837928489687827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 218892260339795573389141 1282571837928489687827)
        ·
          rfl

theorem cell19_341418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 9].length) (baseStart_341418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341418 prefixEnd_341418 := by exact prefixLift 341418
  have htrace : WordTrace (prefixWord ++ tailWord_341418) baseStart_341418 baseEnd_341418 := by
    simpa [prefixWord, tailWord_341418, baseEnd_341418] using wordTrace_append hprefix tailTrace_341418
  have hstable : (prefixWord ++ tailWord_341418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341418).length < 2 ^ (prefixWord ++ tailWord_341418).sum := by decide
  have hdescent : baseEnd_341418 < baseStart_341418 := by decide
  rcases family_descends (prefixWord ++ tailWord_341418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341511 : List Nat := [1, 1, 4, 3, 2, 3, 2, 3]
def baseStart_341511 : Nat := 118140960795 + 341511 * 2 ^ 59
def prefixEnd_341511 : Nat := 4983230072969 + 3 ^ 40 * 341511 * 2
def baseEnd_341511 : Nat := 103916617361611004647067

theorem tailTrace_341511 : CollatzResearch.WordTrace tailWord_341511 prefixEnd_341511 103916617361611004647067 := by
  unfold tailWord_341511
  simp only [CollatzResearch.WordTrace]
  refine ⟨12455929465771447280384387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8303952977180964853589591 12455929465771447280384387)
  ·
    refine ⟨18683894198657170920576581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12455929465771447280384387 18683894198657170920576581)
    ·
      refine ⟨3503230162248219547608109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18683894198657170920576581 3503230162248219547608109)
      ·
        refine ⟨1313711310843082330353041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3503230162248219547608109 1313711310843082330353041)
        ·
          refine ⟨985283483132311747764781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1313711310843082330353041 985283483132311747764781)
          ·
            refine ⟨369481306174616905411793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 985283483132311747764781 369481306174616905411793)
            ·
              refine ⟨277110979630962679058845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369481306174616905411793 277110979630962679058845)
              ·
                refine ⟨103916617361611004647067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277110979630962679058845 103916617361611004647067)
                ·
                  rfl

theorem cell19_341511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_341511 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341511 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341511 prefixEnd_341511 := by exact prefixLift 341511
  have htrace : WordTrace (prefixWord ++ tailWord_341511) baseStart_341511 baseEnd_341511 := by
    simpa [prefixWord, tailWord_341511, baseEnd_341511] using wordTrace_append hprefix tailTrace_341511
  have hstable : (prefixWord ++ tailWord_341511).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341511).length < 2 ^ (prefixWord ++ tailWord_341511).sum := by decide
  have hdescent : baseEnd_341511 < baseStart_341511 := by decide
  rcases family_descends (prefixWord ++ tailWord_341511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341608 : List Nat := [2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_341608 : Nat := 118140960795 + 341608 * 2 ^ 59
def prefixEnd_341608 : Nat := 4983230072969 + 3 ^ 40 * 341608 * 2
def baseEnd_341608 : Nat := 103946132990343520491247

theorem tailTrace_341608 : CollatzResearch.WordTrace tailWord_341608 prefixEnd_341608 103946132990343520491247 := by
  unfold tailWord_341608
  simp only [CollatzResearch.WordTrace]
  refine ⟨6229733673210016423332739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8306311564280021897776985 6229733673210016423332739)
  ·
    refine ⟨9344600509815024634999109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6229733673210016423332739 9344600509815024634999109)
    ·
      refine ⟨1752112595590317119062333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9344600509815024634999109 1752112595590317119062333)
      ·
        refine ⟨657042223346368919648375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1752112595590317119062333 657042223346368919648375)
        ·
          refine ⟨985563335019553379472563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657042223346368919648375 985563335019553379472563)
          ·
            refine ⟨1478345002529330069208845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985563335019553379472563 1478345002529330069208845)
            ·
              refine ⟨554379375948498775953317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1478345002529330069208845 554379375948498775953317)
              ·
                refine ⟨103946132990343520491247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554379375948498775953317 103946132990343520491247)
                ·
                  rfl

theorem cell19_341608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_341608 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341608 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341608 prefixEnd_341608 := by exact prefixLift 341608
  have htrace : WordTrace (prefixWord ++ tailWord_341608) baseStart_341608 baseEnd_341608 := by
    simpa [prefixWord, tailWord_341608, baseEnd_341608] using wordTrace_append hprefix tailTrace_341608
  have hstable : (prefixWord ++ tailWord_341608).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341608).length < 2 ^ (prefixWord ++ tailWord_341608).sum := by decide
  have hdescent : baseEnd_341608 < baseStart_341608 := by decide
  rcases family_descends (prefixWord ++ tailWord_341608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341678 : List Nat := [4, 1, 4, 1, 3, 1, 2, 3]
def baseStart_341678 : Nat := 118140960795 + 341678 * 2 ^ 59
def prefixEnd_341678 : Nat := 4983230072969 + 3 ^ 40 * 341678 * 2
def baseEnd_341678 : Nat := 103967432928604098935501

theorem tailTrace_341678 : CollatzResearch.WordTrace tailWord_341678 prefixEnd_341678 103967432928604098935501 := by
  unfold tailWord_341678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1557752557020804350214211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8308013637444289867809125 1557752557020804350214211)
  ·
    refine ⟨2336628835531206525321317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1557752557020804350214211 2336628835531206525321317)
    ·
      refine ⟨438117906662101223497747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2336628835531206525321317 438117906662101223497747)
      ·
        refine ⟨657176859993151835246621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438117906662101223497747 657176859993151835246621)
        ·
          refine ⟨246441322497431938217483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 657176859993151835246621 246441322497431938217483)
          ·
            refine ⟨369661983746147907326225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246441322497431938217483 369661983746147907326225)
            ·
              refine ⟨277246487809610930494669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369661983746147907326225 277246487809610930494669)
              ·
                refine ⟨103967432928604098935501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277246487809610930494669 103967432928604098935501)
                ·
                  rfl

theorem cell19_341678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_341678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341678 prefixEnd_341678 := by exact prefixLift 341678
  have htrace : WordTrace (prefixWord ++ tailWord_341678) baseStart_341678 baseEnd_341678 := by
    simpa [prefixWord, tailWord_341678, baseEnd_341678] using wordTrace_append hprefix tailTrace_341678
  have hstable : (prefixWord ++ tailWord_341678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341678).length < 2 ^ (prefixWord ++ tailWord_341678).sum := by decide
  have hdescent : baseEnd_341678 < baseStart_341678 := by decide
  rcases family_descends (prefixWord ++ tailWord_341678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341718 : List Nat := [5, 2, 1, 3, 1, 1, 2, 4]
def baseStart_341718 : Nat := 118140960795 + 341718 * 2 ^ 59
def prefixEnd_341718 : Nat := 4983230072969 + 3 ^ 40 * 341718 * 2
def baseEnd_341718 : Nat := 103979604321895858046503

theorem tailTrace_341718 : CollatzResearch.WordTrace tailWord_341718 prefixEnd_341718 103979604321895858046503 := by
  unfold tailWord_341718
  simp only [CollatzResearch.WordTrace]
  refine ⟨778967461001345102073113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8308986250681014422113205 778967461001345102073113)
  ·
    refine ⟨584225595751008826554835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 778967461001345102073113 584225595751008826554835)
    ·
      refine ⟨876338393626513239832253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 584225595751008826554835 876338393626513239832253)
      ·
        refine ⟨328626897609942464937095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 876338393626513239832253 328626897609942464937095)
        ·
          refine ⟨492940346414913697405643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328626897609942464937095 492940346414913697405643)
          ·
            refine ⟨739410519622370546108465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492940346414913697405643 739410519622370546108465)
            ·
              refine ⟨554557889716777909581349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739410519622370546108465 554557889716777909581349)
              ·
                refine ⟨103979604321895858046503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554557889716777909581349 103979604321895858046503)
                ·
                  rfl

theorem cell19_341718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_341718 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341718 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341718 prefixEnd_341718 := by exact prefixLift 341718
  have htrace : WordTrace (prefixWord ++ tailWord_341718) baseStart_341718 baseEnd_341718 := by
    simpa [prefixWord, tailWord_341718, baseEnd_341718] using wordTrace_append hprefix tailTrace_341718
  have hstable : (prefixWord ++ tailWord_341718).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341718).length < 2 ^ (prefixWord ++ tailWord_341718).sum := by decide
  have hdescent : baseEnd_341718 < baseStart_341718 := by decide
  rcases family_descends (prefixWord ++ tailWord_341718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341781 : List Nat := [1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_341781 : Nat := 118140960795 + 341781 * 2 ^ 59
def prefixEnd_341781 : Nat := 4983230072969 + 3 ^ 40 * 341781 * 2
def baseEnd_341781 : Nat := 103998774266330378646331

theorem tailTrace_341781 : CollatzResearch.WordTrace tailWord_341781 prefixEnd_341781 103998774266330378646331 := by
  unfold tailWord_341781
  simp only [CollatzResearch.WordTrace]
  refine ⟨12465777174793283392713197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8310518116528855595142131 12465777174793283392713197)
  ·
    refine ⟨4674666440547481272267449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12465777174793283392713197 4674666440547481272267449)
    ·
      refine ⟨3505999830410610954200587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4674666440547481272267449 3505999830410610954200587)
      ·
        refine ⟨5258999745615916431300881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505999830410610954200587 5258999745615916431300881)
        ·
          refine ⟨3944249809211937323475661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5258999745615916431300881 3944249809211937323475661)
          ·
            refine ⟨1479093678454476496303373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3944249809211937323475661 1479093678454476496303373)
            ·
              refine ⟨554660129420428686113765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1479093678454476496303373 554660129420428686113765)
              ·
                refine ⟨103998774266330378646331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554660129420428686113765 103998774266330378646331)
                ·
                  rfl

theorem cell19_341781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_341781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341781 prefixEnd_341781 := by exact prefixLift 341781
  have htrace : WordTrace (prefixWord ++ tailWord_341781) baseStart_341781 baseEnd_341781 := by
    simpa [prefixWord, tailWord_341781, baseEnd_341781] using wordTrace_append hprefix tailTrace_341781
  have hstable : (prefixWord ++ tailWord_341781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341781).length < 2 ^ (prefixWord ++ tailWord_341781).sum := by decide
  have hdescent : baseEnd_341781 < baseStart_341781 := by decide
  rcases family_descends (prefixWord ++ tailWord_341781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341817 : List Nat := [1, 2, 1, 7, 1, 1, 6]
def baseStart_341817 : Nat := 118140960795 + 341817 * 2 ^ 59
def prefixEnd_341817 : Nat := 4983230072969 + 3 ^ 40 * 341817 * 2
def baseEnd_341817 : Nat := 34669909506764320615411

theorem tailTrace_341817 : CollatzResearch.WordTrace tailWord_341817 prefixEnd_341817 34669909506764320615411 := by
  unfold tailWord_341817
  simp only [CollatzResearch.WordTrace]
  refine ⟨12467090202662861541023705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8311393468441907694015803 12467090202662861541023705)
  ·
    refine ⟨9350317651997146155767779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12467090202662861541023705 9350317651997146155767779)
    ·
      refine ⟨14025476477995719233651669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9350317651997146155767779 14025476477995719233651669)
      ·
        refine ⟨328722104953024669538711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14025476477995719233651669 328722104953024669538711)
        ·
          refine ⟨493083157429537004308067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328722104953024669538711 493083157429537004308067)
          ·
            refine ⟨739624736144305506462101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493083157429537004308067 739624736144305506462101)
            ·
              refine ⟨34669909506764320615411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 739624736144305506462101 34669909506764320615411)
              ·
                rfl

theorem cell19_341817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_341817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341817 prefixEnd_341817 := by exact prefixLift 341817
  have htrace : WordTrace (prefixWord ++ tailWord_341817) baseStart_341817 baseEnd_341817 := by
    simpa [prefixWord, tailWord_341817, baseEnd_341817] using wordTrace_append hprefix tailTrace_341817
  have hstable : (prefixWord ++ tailWord_341817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341817).length < 2 ^ (prefixWord ++ tailWord_341817).sum := by decide
  have hdescent : baseEnd_341817 < baseStart_341817 := by decide
  rcases family_descends (prefixWord ++ tailWord_341817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341840 : List Nat := [2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_341840 : Nat := 118140960795 + 341840 * 2 ^ 59
def prefixEnd_341840 : Nat := 4983230072969 + 3 ^ 40 * 341840 * 2
def baseEnd_341840 : Nat := 104016727071435723335059

theorem tailTrace_341840 : CollatzResearch.WordTrace tailWord_341840 prefixEnd_341840 104016727071435723335059 := by
  unfold tailWord_341840
  simp only [CollatzResearch.WordTrace]
  refine ⟨6233964540789768234555487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8311952721053024312740649 6233964540789768234555487)
  ·
    refine ⟨9350946811184652351833231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6233964540789768234555487 9350946811184652351833231)
    ·
      refine ⟨14026420216776978527749847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9350946811184652351833231 14026420216776978527749847)
      ·
        refine ⟨21039630325165467791624771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14026420216776978527749847 21039630325165467791624771)
        ·
          refine ⟨31559445487748201687437157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21039630325165467791624771 31559445487748201687437157)
          ·
            refine ⟨5917396028952787816394467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31559445487748201687437157 5917396028952787816394467)
            ·
              refine ⟨8876094043429181724591701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5917396028952787816394467 8876094043429181724591701)
              ·
                refine ⟨104016727071435723335059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8876094043429181724591701 104016727071435723335059)
                ·
                  rfl

theorem cell19_341840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_341840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341840 prefixEnd_341840 := by exact prefixLift 341840
  have htrace : WordTrace (prefixWord ++ tailWord_341840) baseStart_341840 baseEnd_341840 := by
    simpa [prefixWord, tailWord_341840, baseEnd_341840] using wordTrace_append hprefix tailTrace_341840
  have hstable : (prefixWord ++ tailWord_341840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341840).length < 2 ^ (prefixWord ++ tailWord_341840).sum := by decide
  have hdescent : baseEnd_341840 < baseStart_341840 := by decide
  rcases family_descends (prefixWord ++ tailWord_341840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341855 : List Nat := [1, 1, 2, 3, 1, 6, 2, 3]
def baseStart_341855 : Nat := 118140960795 + 341855 * 2 ^ 59
def prefixEnd_341855 : Nat := 4983230072969 + 3 ^ 40 * 341855 * 2
def baseEnd_341855 : Nat := 104021291343920133001685

theorem tailTrace_341855 : CollatzResearch.WordTrace tailWord_341855 prefixEnd_341855 104021291343920133001685 := by
  unfold tailWord_341855
  simp only [CollatzResearch.WordTrace]
  refine ⟨12468476176525194030907019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8312317451016796020604679 12468476176525194030907019)
  ·
    refine ⟨18702714264787791046360529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12468476176525194030907019 18702714264787791046360529)
    ·
      refine ⟨14027035698590843284770397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18702714264787791046360529 14027035698590843284770397)
      ·
        refine ⟨5260138386971566231788899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14027035698590843284770397 5260138386971566231788899)
        ·
          refine ⟨7890207580457349347683349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260138386971566231788899 7890207580457349347683349)
          ·
            refine ⟨369853480333938250672657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7890207580457349347683349 369853480333938250672657)
            ·
              refine ⟨277390110250453688004493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369853480333938250672657 277390110250453688004493)
              ·
                refine ⟨104021291343920133001685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277390110250453688004493 104021291343920133001685)
                ·
                  rfl

theorem cell19_341855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_341855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341855 prefixEnd_341855 := by exact prefixLift 341855
  have htrace : WordTrace (prefixWord ++ tailWord_341855) baseStart_341855 baseEnd_341855 := by
    simpa [prefixWord, tailWord_341855, baseEnd_341855] using wordTrace_append hprefix tailTrace_341855
  have hstable : (prefixWord ++ tailWord_341855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341855).length < 2 ^ (prefixWord ++ tailWord_341855).sum := by decide
  have hdescent : baseEnd_341855 < baseStart_341855 := by decide
  rcases family_descends (prefixWord ++ tailWord_341855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341914 : List Nat := [3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_341914 : Nat := 118140960795 + 341914 * 2 ^ 59
def prefixEnd_341914 : Nat := 4983230072969 + 3 ^ 40 * 341914 * 2
def baseEnd_341914 : Nat := 104039244149025477690413

theorem tailTrace_341914 : CollatzResearch.WordTrace tailWord_341914 prefixEnd_341914 104039244149025477690413 := by
  unfold tailWord_341914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117657020827861776826199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8313752055540964738203197 3117657020827861776826199)
  ·
    refine ⟨4676485531241792665239299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3117657020827861776826199 4676485531241792665239299)
    ·
      refine ⟨7014728296862688997858949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4676485531241792665239299 7014728296862688997858949)
      ·
        refine ⟨1315261555661754187098553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7014728296862688997858949 1315261555661754187098553)
        ·
          refine ⟨986446166746315640323915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1315261555661754187098553 986446166746315640323915)
          ·
            refine ⟨1479669250119473460485873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986446166746315640323915 1479669250119473460485873)
            ·
              refine ⟨1109751937589605095364405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479669250119473460485873 1109751937589605095364405)
              ·
                refine ⟨104039244149025477690413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1109751937589605095364405 104039244149025477690413)
                ·
                  rfl

theorem cell19_341914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_341914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341914 prefixEnd_341914 := by exact prefixLift 341914
  have htrace : WordTrace (prefixWord ++ tailWord_341914) baseStart_341914 baseEnd_341914 := by
    simpa [prefixWord, tailWord_341914, baseEnd_341914] using wordTrace_append hprefix tailTrace_341914
  have hstable : (prefixWord ++ tailWord_341914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341914).length < 2 ^ (prefixWord ++ tailWord_341914).sum := by decide
  have hdescent : baseEnd_341914 < baseStart_341914 := by decide
  rcases family_descends (prefixWord ++ tailWord_341914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341948 : List Nat := [2, 2, 2, 5, 1, 2, 1, 4]
def baseStart_341948 : Nat := 118140960795 + 341948 * 2 ^ 59
def prefixEnd_341948 : Nat := 4983230072969 + 3 ^ 40 * 341948 * 2
def baseEnd_341948 : Nat := 104049589833323472934765

theorem tailTrace_341948 : CollatzResearch.WordTrace tailWord_341948 prefixEnd_341948 104049589833323472934765 := by
  unfold tailWord_341948
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235934082594135457021249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8314578776792180609361665 6235934082594135457021249)
  ·
    refine ⟨4676950561945601592765937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6235934082594135457021249 4676950561945601592765937)
    ·
      refine ⟨3507712921459201194574453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4676950561945601592765937 3507712921459201194574453)
      ·
        refine ⟨328848086386800111991355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3507712921459201194574453 328848086386800111991355)
        ·
          refine ⟨493272129580200167987033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328848086386800111991355 493272129580200167987033)
          ·
            refine ⟨369954097185150125990275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493272129580200167987033 369954097185150125990275)
            ·
              refine ⟨554931145777725188985413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369954097185150125990275 554931145777725188985413)
              ·
                refine ⟨104049589833323472934765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554931145777725188985413 104049589833323472934765)
                ·
                  rfl

theorem cell19_341948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_341948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341948 prefixEnd_341948 := by exact prefixLift 341948
  have htrace : WordTrace (prefixWord ++ tailWord_341948) baseStart_341948 baseEnd_341948 := by
    simpa [prefixWord, tailWord_341948, baseEnd_341948] using wordTrace_append hprefix tailTrace_341948
  have hstable : (prefixWord ++ tailWord_341948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341948).length < 2 ^ (prefixWord ++ tailWord_341948).sum := by decide
  have hdescent : baseEnd_341948 < baseStart_341948 := by decide
  rcases family_descends (prefixWord ++ tailWord_341948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341950 : List Nat := [4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_341950 : Nat := 118140960795 + 341950 * 2 ^ 59
def prefixEnd_341950 : Nat := 4983230072969 + 3 ^ 40 * 341950 * 2
def baseEnd_341950 : Nat := 104050198402988060890315

theorem tailTrace_341950 : CollatzResearch.WordTrace tailWord_341950 prefixEnd_341950 104050198402988060890315 := by
  unfold tailWord_341950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558992638897628156951913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8314627407454016837076869 1558992638897628156951913)
  ·
    refine ⟨1169244479173221117713935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1558992638897628156951913 1169244479173221117713935)
    ·
      refine ⟨1753866718759831676570903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169244479173221117713935 1753866718759831676570903)
      ·
        refine ⟨2630800078139747514856355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753866718759831676570903 2630800078139747514856355)
        ·
          refine ⟨3946200117209621272284533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630800078139747514856355 3946200117209621272284533)
          ·
            refine ⟨369956260988401994276675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3946200117209621272284533 369956260988401994276675)
            ·
              refine ⟨554934391482602991415013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369956260988401994276675 554934391482602991415013)
              ·
                refine ⟨104050198402988060890315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554934391482602991415013 104050198402988060890315)
                ·
                  rfl

theorem cell19_341950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_341950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_341950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_341950 prefixEnd_341950 := by exact prefixLift 341950
  have htrace : WordTrace (prefixWord ++ tailWord_341950) baseStart_341950 baseEnd_341950 := by
    simpa [prefixWord, tailWord_341950, baseEnd_341950] using wordTrace_append hprefix tailTrace_341950
  have hstable : (prefixWord ++ tailWord_341950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341950).length < 2 ^ (prefixWord ++ tailWord_341950).sum := by decide
  have hdescent : baseEnd_341950 < baseStart_341950 := by decide
  rcases family_descends (prefixWord ++ tailWord_341950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342066 : List Nat := [3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_342066 : Nat := 118140960795 + 342066 * 2 ^ 59
def prefixEnd_342066 : Nat := 4983230072969 + 3 ^ 40 * 342066 * 2
def baseEnd_342066 : Nat := 104085495443534162312221

theorem tailTrace_342066 : CollatzResearch.WordTrace tailWord_342066 prefixEnd_342066 104085495443534162312221 := by
  unfold tailWord_342066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119042994690194266709513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8317447985840518044558701 3119042994690194266709513)
  ·
    refine ⟨2339282246017645700032135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3119042994690194266709513 2339282246017645700032135)
    ·
      refine ⟨3508923369026468550048203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339282246017645700032135 3508923369026468550048203)
      ·
        refine ⟨5263385053539702825072305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3508923369026468550048203 5263385053539702825072305)
        ·
          refine ⟨3947538790154777118804229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5263385053539702825072305 3947538790154777118804229)
          ·
            refine ⟨740163523154020709775793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3947538790154777118804229 740163523154020709775793)
            ·
              refine ⟨555122642365515532331845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740163523154020709775793 555122642365515532331845)
              ·
                refine ⟨104085495443534162312221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555122642365515532331845 104085495443534162312221)
                ·
                  rfl

theorem cell19_342066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_342066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342066 prefixEnd_342066 := by exact prefixLift 342066
  have htrace : WordTrace (prefixWord ++ tailWord_342066) baseStart_342066 baseEnd_342066 := by
    simpa [prefixWord, tailWord_342066, baseEnd_342066] using wordTrace_append hprefix tailTrace_342066
  have hstable : (prefixWord ++ tailWord_342066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342066).length < 2 ^ (prefixWord ++ tailWord_342066).sum := by decide
  have hdescent : baseEnd_342066 < baseStart_342066 := by decide
  rcases family_descends (prefixWord ++ tailWord_342066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342087 : List Nat := [1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_342087 : Nat := 118140960795 + 342087 * 2 ^ 59
def prefixEnd_342087 : Nat := 4983230072969 + 3 ^ 40 * 342087 * 2
def baseEnd_342087 : Nat := 104091885425012335845497

theorem tailTrace_342087 : CollatzResearch.WordTrace tailWord_342087 prefixEnd_342087 104091885425012335845497 := by
  unfold tailWord_342087
  simp only [CollatzResearch.WordTrace]
  refine ⟨12476937911684697653352515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8317958607789798435568343 12476937911684697653352515)
  ·
    refine ⟨18715406867527046480028773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12476937911684697653352515 18715406867527046480028773)
    ·
      refine ⟨3509138787661321215005395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18715406867527046480028773 3509138787661321215005395)
      ·
        refine ⟨5263708181491981822508093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509138787661321215005395 5263708181491981822508093)
        ·
          refine ⟨1973890568059493183440535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5263708181491981822508093 1973890568059493183440535)
          ·
            refine ⟨2960835852089239775160803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973890568059493183440535 2960835852089239775160803)
            ·
              refine ⟨4441253778133859662741205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960835852089239775160803 4441253778133859662741205)
              ·
                refine ⟨104091885425012335845497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4441253778133859662741205 104091885425012335845497)
                ·
                  rfl

theorem cell19_342087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_342087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342087 prefixEnd_342087 := by exact prefixLift 342087
  have htrace : WordTrace (prefixWord ++ tailWord_342087) baseStart_342087 baseEnd_342087 := by
    simpa [prefixWord, tailWord_342087, baseEnd_342087] using wordTrace_append hprefix tailTrace_342087
  have hstable : (prefixWord ++ tailWord_342087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342087).length < 2 ^ (prefixWord ++ tailWord_342087).sum := by decide
  have hdescent : baseEnd_342087 < baseStart_342087 := by decide
  rcases family_descends (prefixWord ++ tailWord_342087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342102 : List Nat := [5, 2, 2, 1, 1, 8]
def baseStart_342102 : Nat := 118140960795 + 342102 * 2 ^ 59
def prefixEnd_342102 : Nat := 4983230072969 + 3 ^ 40 * 342102 * 2
def baseEnd_342102 : Nat := 11566272188610749501347

theorem tailTrace_342102 : CollatzResearch.WordTrace tailWord_342102 prefixEnd_342102 11566272188610749501347 := by
  unfold tailWord_342102
  simp only [CollatzResearch.WordTrace]
  refine ⟨779842812914397200946785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8318323337753570143432373 779842812914397200946785)
  ·
    refine ⟨584882109685797900710089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 779842812914397200946785 584882109685797900710089)
    ·
      refine ⟨438661582264348425532567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 584882109685797900710089 438661582264348425532567)
      ·
        refine ⟨657992373396522638298851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438661582264348425532567 657992373396522638298851)
        ·
          refine ⟨986988560094783957448277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657992373396522638298851 986988560094783957448277)
          ·
            refine ⟨11566272188610749501347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 986988560094783957448277 11566272188610749501347)
            ·
              rfl

theorem cell19_342102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 8].length) (baseStart_342102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342102 prefixEnd_342102 := by exact prefixLift 342102
  have htrace : WordTrace (prefixWord ++ tailWord_342102) baseStart_342102 baseEnd_342102 := by
    simpa [prefixWord, tailWord_342102, baseEnd_342102] using wordTrace_append hprefix tailTrace_342102
  have hstable : (prefixWord ++ tailWord_342102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342102).length < 2 ^ (prefixWord ++ tailWord_342102).sum := by decide
  have hdescent : baseEnd_342102 < baseStart_342102 := by decide
  rcases family_descends (prefixWord ++ tailWord_342102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342197 : List Nat := [1, 3, 3, 4, 1, 1, 1, 5]
def baseStart_342197 : Nat := 118140960795 + 342197 * 2 ^ 59
def prefixEnd_342197 : Nat := 4983230072969 + 3 ^ 40 * 342197 * 2
def baseEnd_342197 : Nat := 104125356756564673400753

theorem tailTrace_342197 : CollatzResearch.WordTrace tailWord_342197 prefixEnd_342197 104125356756564673400753 := by
  unfold tailWord_342197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12480949941286186439856845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8320633294190790959904563 12480949941286186439856845)
  ·
    refine ⟨4680356227982319914946317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12480949941286186439856845 4680356227982319914946317)
    ·
      refine ⟨1755133585493369968104869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4680356227982319914946317 1755133585493369968104869)
      ·
        refine ⟨329087547280006869019663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1755133585493369968104869 329087547280006869019663)
        ·
          refine ⟨493631320920010303529495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329087547280006869019663 493631320920010303529495)
          ·
            refine ⟨740446981380015455294243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493631320920010303529495 740446981380015455294243)
            ·
              refine ⟨1110670472070023182941365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740446981380015455294243 1110670472070023182941365)
              ·
                refine ⟨104125356756564673400753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1110670472070023182941365 104125356756564673400753)
                ·
                  rfl

theorem cell19_342197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_342197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342197 prefixEnd_342197 := by exact prefixLift 342197
  have htrace : WordTrace (prefixWord ++ tailWord_342197) baseStart_342197 baseEnd_342197 := by
    simpa [prefixWord, tailWord_342197, baseEnd_342197] using wordTrace_append hprefix tailTrace_342197
  have hstable : (prefixWord ++ tailWord_342197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342197).length < 2 ^ (prefixWord ++ tailWord_342197).sum := by decide
  have hdescent : baseEnd_342197 < baseStart_342197 := by decide
  rcases family_descends (prefixWord ++ tailWord_342197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342199 : List Nat := [1, 1, 3, 1, 4, 2, 4, 3]
def baseStart_342199 : Nat := 118140960795 + 342199 * 2 ^ 59
def prefixEnd_342199 : Nat := 4983230072969 + 3 ^ 40 * 342199 * 2
def baseEnd_342199 : Nat := 104125965326229261356303

theorem tailTrace_342199 : CollatzResearch.WordTrace tailWord_342199 prefixEnd_342199 104125965326229261356303 := by
  unfold tailWord_342199
  simp only [CollatzResearch.WordTrace]
  refine ⟨12481022887278940781429651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8320681924852627187619767 12481022887278940781429651)
  ·
    refine ⟨18721534330918411172144477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12481022887278940781429651 18721534330918411172144477)
    ·
      refine ⟨7020575374094404189554179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18721534330918411172144477 7020575374094404189554179)
      ·
        refine ⟨10530863061141606284331269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7020575374094404189554179 10530863061141606284331269)
        ·
          refine ⟨1974536823964051178312113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10530863061141606284331269 1974536823964051178312113)
          ·
            refine ⟨1480902617973038383734085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974536823964051178312113 1480902617973038383734085)
            ·
              refine ⟨277669240869944696950141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1480902617973038383734085 277669240869944696950141)
              ·
                refine ⟨104125965326229261356303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277669240869944696950141 104125965326229261356303)
                ·
                  rfl

theorem cell19_342199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_342199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342199 prefixEnd_342199 := by exact prefixLift 342199
  have htrace : WordTrace (prefixWord ++ tailWord_342199) baseStart_342199 baseEnd_342199 := by
    simpa [prefixWord, tailWord_342199, baseEnd_342199] using wordTrace_append hprefix tailTrace_342199
  have hstable : (prefixWord ++ tailWord_342199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342199).length < 2 ^ (prefixWord ++ tailWord_342199).sum := by decide
  have hdescent : baseEnd_342199 < baseStart_342199 := by decide
  rcases family_descends (prefixWord ++ tailWord_342199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342201 : List Nat := [1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_342201 : Nat := 118140960795 + 342201 * 2 ^ 59
def prefixEnd_342201 : Nat := 4983230072969 + 3 ^ 40 * 342201 * 2
def baseEnd_342201 : Nat := 104126573895893849311853

theorem tailTrace_342201 : CollatzResearch.WordTrace tailWord_342201 prefixEnd_342201 104126573895893849311853 := by
  unfold tailWord_342201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12481095833271695123002457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8320730555514463415334971 12481095833271695123002457)
  ·
    refine ⟨9360821874953771342251843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12481095833271695123002457 9360821874953771342251843)
    ·
      refine ⟨14041232812430657013377765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9360821874953771342251843 14041232812430657013377765)
      ·
        refine ⟨2632731152330748190008331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14041232812430657013377765 2632731152330748190008331)
        ·
          refine ⟨3949096728496122285012497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2632731152330748190008331 3949096728496122285012497)
          ·
            refine ⟨2961822546372091713759373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3949096728496122285012497 2961822546372091713759373)
            ·
              refine ⟨1110683454889534392659765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2961822546372091713759373 1110683454889534392659765)
              ·
                refine ⟨104126573895893849311853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1110683454889534392659765 104126573895893849311853)
                ·
                  rfl

theorem cell19_342201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_342201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342201 prefixEnd_342201 := by exact prefixLift 342201
  have htrace : WordTrace (prefixWord ++ tailWord_342201) baseStart_342201 baseEnd_342201 := by
    simpa [prefixWord, tailWord_342201, baseEnd_342201] using wordTrace_append hprefix tailTrace_342201
  have hstable : (prefixWord ++ tailWord_342201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342201).length < 2 ^ (prefixWord ++ tailWord_342201).sum := by decide
  have hdescent : baseEnd_342201 < baseStart_342201 := by decide
  rcases family_descends (prefixWord ++ tailWord_342201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342237 : List Nat := [1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_342237 : Nat := 118140960795 + 342237 * 2 ^ 59
def prefixEnd_342237 : Nat := 4983230072969 + 3 ^ 40 * 342237 * 2
def baseEnd_342237 : Nat := 104137528149856432511755

theorem tailTrace_342237 : CollatzResearch.WordTrace tailWord_342237 prefixEnd_342237 104137528149856432511755 := by
  unfold tailWord_342237
  simp only [CollatzResearch.WordTrace]
  refine ⟨12482408861141273271312965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8321605907427515514208643 12482408861141273271312965)
  ·
    refine ⟨2340451661463988738371181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12482408861141273271312965 2340451661463988738371181)
    ·
      refine ⟨877669373048995776889193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2340451661463988738371181 877669373048995776889193)
      ·
        refine ⟨658252029786746832666895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 877669373048995776889193 658252029786746832666895)
        ·
          refine ⟨987378044680120249000343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658252029786746832666895 987378044680120249000343)
          ·
            refine ⟨1481067067020180373500515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987378044680120249000343 1481067067020180373500515)
            ·
              refine ⟨2221600600530270560250773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481067067020180373500515 2221600600530270560250773)
              ·
                refine ⟨104137528149856432511755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2221600600530270560250773 104137528149856432511755)
                ·
                  rfl

theorem cell19_342237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_342237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342237 prefixEnd_342237 := by exact prefixLift 342237
  have htrace : WordTrace (prefixWord ++ tailWord_342237) baseStart_342237 baseEnd_342237 := by
    simpa [prefixWord, tailWord_342237, baseEnd_342237] using wordTrace_append hprefix tailTrace_342237
  have hstable : (prefixWord ++ tailWord_342237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342237).length < 2 ^ (prefixWord ++ tailWord_342237).sum := by decide
  have hdescent : baseEnd_342237 < baseStart_342237 := by decide
  rcases family_descends (prefixWord ++ tailWord_342237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342364 : List Nat := [2, 2, 4, 3, 2, 1, 2, 3]
def baseStart_342364 : Nat := 118140960795 + 342364 * 2 ^ 59
def prefixEnd_342364 : Nat := 4983230072969 + 3 ^ 40 * 342364 * 2
def baseEnd_342364 : Nat := 104176172323557767689187

theorem tailTrace_342364 : CollatzResearch.WordTrace tailWord_342364 prefixEnd_342364 104176172323557767689187 := by
  unfold tailWord_342364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6243520465840586980593073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8324693954454115974124097 6243520465840586980593073)
  ·
    refine ⟨4682640349380440235444805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6243520465840586980593073 4682640349380440235444805)
    ·
      refine ⟨877995065508832544145901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4682640349380440235444805 877995065508832544145901)
      ·
        refine ⟨329248149565812204054713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 877995065508832544145901 329248149565812204054713)
        ·
          refine ⟨246936112174359153041035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329248149565812204054713 246936112174359153041035)
          ·
            refine ⟨370404168261538729561553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246936112174359153041035 370404168261538729561553)
            ·
              refine ⟨277803126196154047171165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370404168261538729561553 277803126196154047171165)
              ·
                refine ⟨104176172323557767689187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277803126196154047171165 104176172323557767689187)
                ·
                  rfl

theorem cell19_342364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_342364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342364 prefixEnd_342364 := by exact prefixLift 342364
  have htrace : WordTrace (prefixWord ++ tailWord_342364) baseStart_342364 baseEnd_342364 := by
    simpa [prefixWord, tailWord_342364, baseEnd_342364] using wordTrace_append hprefix tailTrace_342364
  have hstable : (prefixWord ++ tailWord_342364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342364).length < 2 ^ (prefixWord ++ tailWord_342364).sum := by decide
  have hdescent : baseEnd_342364 < baseStart_342364 := by decide
  rcases family_descends (prefixWord ++ tailWord_342364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342368 : List Nat := [2, 1, 1, 3, 5, 2, 2, 3]
def baseStart_342368 : Nat := 118140960795 + 342368 * 2 ^ 59
def prefixEnd_342368 : Nat := 4983230072969 + 3 ^ 40 * 342368 * 2
def baseEnd_342368 : Nat := 104177389462886943600287

theorem tailTrace_342368 : CollatzResearch.WordTrace tailWord_342368 prefixEnd_342368 104177389462886943600287 := by
  unfold tailWord_342368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6243593411833341322165879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8324791215777788429554505 6243593411833341322165879)
  ·
    refine ⟨9365390117750011983248819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6243593411833341322165879 9365390117750011983248819)
    ·
      refine ⟨14048085176625017974873229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9365390117750011983248819 14048085176625017974873229)
      ·
        refine ⟨5268031941234381740577461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14048085176625017974873229 5268031941234381740577461)
        ·
          refine ⟨493877994490723288179137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5268031941234381740577461 493877994490723288179137)
          ·
            refine ⟨370408495868042466134353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493877994490723288179137 370408495868042466134353)
            ·
              refine ⟨277806371901031849600765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370408495868042466134353 277806371901031849600765)
              ·
                refine ⟨104177389462886943600287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277806371901031849600765 104177389462886943600287)
                ·
                  rfl

theorem cell19_342368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_342368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342368 prefixEnd_342368 := by exact prefixLift 342368
  have htrace : WordTrace (prefixWord ++ tailWord_342368) baseStart_342368 baseEnd_342368 := by
    simpa [prefixWord, tailWord_342368, baseEnd_342368] using wordTrace_append hprefix tailTrace_342368
  have hstable : (prefixWord ++ tailWord_342368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342368).length < 2 ^ (prefixWord ++ tailWord_342368).sum := by decide
  have hdescent : baseEnd_342368 < baseStart_342368 := by decide
  rcases family_descends (prefixWord ++ tailWord_342368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342370 : List Nat := [3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_342370 : Nat := 118140960795 + 342370 * 2 ^ 59
def prefixEnd_342370 : Nat := 4983230072969 + 3 ^ 40 * 342370 * 2
def baseEnd_342370 : Nat := 104177998032551531555837

theorem tailTrace_342370 : CollatzResearch.WordTrace tailWord_342370 prefixEnd_342370 104177998032551531555837 := by
  unfold tailWord_342370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121814942414859246476141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8324839846439624657269709 3121814942414859246476141)
  ·
    refine ⟨1170680603405572217428553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3121814942414859246476141 1170680603405572217428553)
    ·
      refine ⟨878010452554179163071415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1170680603405572217428553 878010452554179163071415)
      ·
        refine ⟨1317015678831268744607123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878010452554179163071415 1317015678831268744607123)
        ·
          refine ⟨1975523518246903116910685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317015678831268744607123 1975523518246903116910685)
          ·
            refine ⟨740821319342588668841507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1975523518246903116910685 740821319342588668841507)
            ·
              refine ⟨1111231979013883003262261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740821319342588668841507 1111231979013883003262261)
              ·
                refine ⟨104177998032551531555837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1111231979013883003262261 104177998032551531555837)
                ·
                  rfl

theorem cell19_342370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_342370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342370 prefixEnd_342370 := by exact prefixLift 342370
  have htrace : WordTrace (prefixWord ++ tailWord_342370) baseStart_342370 baseEnd_342370 := by
    simpa [prefixWord, tailWord_342370, baseEnd_342370] using wordTrace_append hprefix tailTrace_342370
  have hstable : (prefixWord ++ tailWord_342370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342370).length < 2 ^ (prefixWord ++ tailWord_342370).sum := by decide
  have hdescent : baseEnd_342370 < baseStart_342370 := by decide
  rcases family_descends (prefixWord ++ tailWord_342370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342372 : List Nat := [2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_342372 : Nat := 118140960795 + 342372 * 2 ^ 59
def prefixEnd_342372 : Nat := 4983230072969 + 3 ^ 40 * 342372 * 2
def baseEnd_342372 : Nat := 104178606602216119511387

theorem tailTrace_342372 : CollatzResearch.WordTrace tailWord_342372 prefixEnd_342372 104178606602216119511387 := by
  unfold tailWord_342372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6243666357826095663738685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8324888477101460884984913 6243666357826095663738685)
  ·
    refine ⟨2341374884184785873902007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6243666357826095663738685 2341374884184785873902007)
    ·
      refine ⟨3512062326277178810853011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2341374884184785873902007 3512062326277178810853011)
      ·
        refine ⟨5268093489415768216279517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512062326277178810853011 5268093489415768216279517)
        ·
          refine ⟨1975535058530913081104819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5268093489415768216279517 1975535058530913081104819)
          ·
            refine ⟨2963302587796369621657229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975535058530913081104819 2963302587796369621657229)
            ·
              refine ⟨1111238470423638608121461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2963302587796369621657229 1111238470423638608121461)
              ·
                refine ⟨104178606602216119511387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1111238470423638608121461 104178606602216119511387)
                ·
                  rfl

theorem cell19_342372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_342372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342372 prefixEnd_342372 := by exact prefixLift 342372
  have htrace : WordTrace (prefixWord ++ tailWord_342372) baseStart_342372 baseEnd_342372 := by
    simpa [prefixWord, tailWord_342372, baseEnd_342372] using wordTrace_append hprefix tailTrace_342372
  have hstable : (prefixWord ++ tailWord_342372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342372).length < 2 ^ (prefixWord ++ tailWord_342372).sum := by decide
  have hdescent : baseEnd_342372 < baseStart_342372 := by decide
  rcases family_descends (prefixWord ++ tailWord_342372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342389 : List Nat := [1, 3, 4, 1, 2, 3, 5]
def baseStart_342389 : Nat := 118140960795 + 342389 * 2 ^ 59
def prefixEnd_342389 : Nat := 4983230072969 + 3 ^ 40 * 342389 * 2
def baseEnd_342389 : Nat := 34727926481455039044521

theorem tailTrace_342389 : CollatzResearch.WordTrace tailWord_342389 prefixEnd_342389 34727926481455039044521 := by
  unfold tailWord_342389
  simp only [CollatzResearch.WordTrace]
  refine ⟨12487952756590603230846221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8325301837727068820564147 12487952756590603230846221)
  ·
    refine ⟨4682982283721476211567333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12487952756590603230846221 4682982283721476211567333)
    ·
      refine ⟨878059178197776789668875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4682982283721476211567333 878059178197776789668875)
      ·
        refine ⟨1317088767296665184503313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878059178197776789668875 1317088767296665184503313)
        ·
          refine ⟨987816575472498888377485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1317088767296665184503313 987816575472498888377485)
          ·
            refine ⟨370431215802187083141557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 987816575472498888377485 370431215802187083141557)
            ·
              refine ⟨34727926481455039044521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370431215802187083141557 34727926481455039044521)
              ·
                rfl

theorem cell19_342389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_342389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342389 prefixEnd_342389 := by exact prefixLift 342389
  have htrace : WordTrace (prefixWord ++ tailWord_342389) baseStart_342389 baseEnd_342389 := by
    simpa [prefixWord, tailWord_342389, baseEnd_342389] using wordTrace_append hprefix tailTrace_342389
  have hstable : (prefixWord ++ tailWord_342389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342389).length < 2 ^ (prefixWord ++ tailWord_342389).sum := by decide
  have hdescent : baseEnd_342389 < baseStart_342389 := by decide
  rcases family_descends (prefixWord ++ tailWord_342389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342442 : List Nat := [3, 1, 6, 1, 2, 6]
def baseStart_342442 : Nat := 118140960795 + 342442 * 2 ^ 59
def prefixEnd_342442 : Nat := 4983230072969 + 3 ^ 40 * 342442 * 2
def baseEnd_342442 : Nat := 11577767393386299772849

theorem tailTrace_342442 : CollatzResearch.WordTrace tailWord_342442 prefixEnd_342442 11577767393386299772849 := by
  unfold tailWord_342442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122471456349648320631395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8326590550265728855017053 3122471456349648320631395)
  ·
    refine ⟨4683707184524472480947093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3122471456349648320631395 4683707184524472480947093)
    ·
      refine ⟨219548774274584647544395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4683707184524472480947093 219548774274584647544395)
      ·
        refine ⟨329323161411876971316593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219548774274584647544395 329323161411876971316593)
        ·
          refine ⟨246992371058907728487445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329323161411876971316593 246992371058907728487445)
          ·
            refine ⟨11577767393386299772849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 246992371058907728487445 11577767393386299772849)
            ·
              rfl

theorem cell19_342442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 6].length) (baseStart_342442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342442 prefixEnd_342442 := by exact prefixLift 342442
  have htrace : WordTrace (prefixWord ++ tailWord_342442) baseStart_342442 baseEnd_342442 := by
    simpa [prefixWord, tailWord_342442, baseEnd_342442] using wordTrace_append hprefix tailTrace_342442
  have hstable : (prefixWord ++ tailWord_342442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342442).length < 2 ^ (prefixWord ++ tailWord_342442).sum := by decide
  have hdescent : baseEnd_342442 < baseStart_342442 := by decide
  rcases family_descends (prefixWord ++ tailWord_342442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342507 : List Nat := [1, 1, 1, 1, 2, 3, 10]
def baseStart_342507 : Nat := 118140960795 + 342507 * 2 ^ 59
def prefixEnd_342507 : Nat := 4983230072969 + 3 ^ 40 * 342507 * 2
def baseEnd_342507 : Nat := 34739895018191935503673

theorem tailTrace_342507 : CollatzResearch.WordTrace tailWord_342507 prefixEnd_342507 34739895018191935503673 := by
  unfold tailWord_342507
  simp only [CollatzResearch.WordTrace]
  refine ⟨12492256570163109383641775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8328171046775406255761183 12492256570163109383641775)
  ·
    refine ⟨18738384855244664075462663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12492256570163109383641775 18738384855244664075462663)
    ·
      refine ⟨28107577282866996113193995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18738384855244664075462663 28107577282866996113193995)
      ·
        refine ⟨42161365924300494169790993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28107577282866996113193995 42161365924300494169790993)
        ·
          refine ⟨31621024443225370627343245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42161365924300494169790993 31621024443225370627343245)
          ·
            refine ⟨11857884166209513985253717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31621024443225370627343245 11857884166209513985253717)
            ·
              refine ⟨34739895018191935503673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11857884166209513985253717 34739895018191935503673)
              ·
                rfl

theorem cell19_342507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_342507 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342507 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342507 prefixEnd_342507 := by exact prefixLift 342507
  have htrace : WordTrace (prefixWord ++ tailWord_342507) baseStart_342507 baseEnd_342507 := by
    simpa [prefixWord, tailWord_342507, baseEnd_342507] using wordTrace_append hprefix tailTrace_342507
  have hstable : (prefixWord ++ tailWord_342507).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342507).length < 2 ^ (prefixWord ++ tailWord_342507).sum := by decide
  have hdescent : baseEnd_342507 < baseStart_342507 := by decide
  rcases family_descends (prefixWord ++ tailWord_342507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342560 : List Nat := [2, 1, 1, 6, 2, 2, 5]
def baseStart_342560 : Nat := 118140960795 + 342560 * 2 ^ 59
def prefixEnd_342560 : Nat := 4983230072969 + 3 ^ 40 * 342560 * 2
def baseEnd_342560 : Nat := 34745270716895795777699

theorem tailTrace_342560 : CollatzResearch.WordTrace tailWord_342560 prefixEnd_342560 34745270716895795777699 := by
  unfold tailWord_342560
  simp only [CollatzResearch.WordTrace]
  refine ⟨6247094819485549717660567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8329459759314066290214089 6247094819485549717660567)
  ·
    refine ⟨9370642229228324576490851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6247094819485549717660567 9370642229228324576490851)
    ·
      refine ⟨14055963343842486864736277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9370642229228324576490851 14055963343842486864736277)
      ·
        refine ⟨658873281742616571784513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14055963343842486864736277 658873281742616571784513)
        ·
          refine ⟨494154961306962428838385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658873281742616571784513 494154961306962428838385)
          ·
            refine ⟨370616220980221821628789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494154961306962428838385 370616220980221821628789)
            ·
              refine ⟨34745270716895795777699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370616220980221821628789 34745270716895795777699)
              ·
                rfl

theorem cell19_342560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_342560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342560 prefixEnd_342560 := by exact prefixLift 342560
  have htrace : WordTrace (prefixWord ++ tailWord_342560) baseStart_342560 baseEnd_342560 := by
    simpa [prefixWord, tailWord_342560, baseEnd_342560] using wordTrace_append hprefix tailTrace_342560
  have hstable : (prefixWord ++ tailWord_342560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342560).length < 2 ^ (prefixWord ++ tailWord_342560).sum := by decide
  have hdescent : baseEnd_342560 < baseStart_342560 := by decide
  rcases family_descends (prefixWord ++ tailWord_342560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342581 : List Nat := [1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_342581 : Nat := 118140960795 + 342581 * 2 ^ 59
def prefixEnd_342581 : Nat := 4983230072969 + 3 ^ 40 * 342581 * 2
def baseEnd_342581 : Nat := 104242202132165560866373

theorem tailTrace_342581 : CollatzResearch.WordTrace tailWord_342581 prefixEnd_342581 104242202132165560866373 := by
  unfold tailWord_342581
  simp only [CollatzResearch.WordTrace]
  refine ⟨12494955571895020021835597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8329970381263346681223731 12494955571895020021835597)
  ·
    refine ⟨4685608339460632508188349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12494955571895020021835597 4685608339460632508188349)
    ·
      refine ⟨1757103127297737190570631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4685608339460632508188349 1757103127297737190570631)
      ·
        refine ⟨2635654690946605785855947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757103127297737190570631 2635654690946605785855947)
        ·
          refine ⟨3953482036419908678783921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635654690946605785855947 3953482036419908678783921)
          ·
            refine ⟨2965111527314931509087941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3953482036419908678783921 2965111527314931509087941)
            ·
              refine ⟨555958411371549657953989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2965111527314931509087941 555958411371549657953989)
              ·
                refine ⟨104242202132165560866373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555958411371549657953989 104242202132165560866373)
                ·
                  rfl

theorem cell19_342581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_342581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342581 prefixEnd_342581 := by exact prefixLift 342581
  have htrace : WordTrace (prefixWord ++ tailWord_342581) baseStart_342581 baseEnd_342581 := by
    simpa [prefixWord, tailWord_342581, baseEnd_342581] using wordTrace_append hprefix tailTrace_342581
  have hstable : (prefixWord ++ tailWord_342581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342581).length < 2 ^ (prefixWord ++ tailWord_342581).sum := by decide
  have hdescent : baseEnd_342581 < baseStart_342581 := by decide
  rcases family_descends (prefixWord ++ tailWord_342581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342659 : List Nat := [1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_342659 : Nat := 118140960795 + 342659 * 2 ^ 59
def prefixEnd_342659 : Nat := 4983230072969 + 3 ^ 40 * 342659 * 2
def baseEnd_342659 : Nat := 104265936349084491132827

theorem tailTrace_342659 : CollatzResearch.WordTrace tailWord_342659 prefixEnd_342659 104265936349084491132827 := by
  unfold tailWord_342659
  simp only [CollatzResearch.WordTrace]
  refine ⟨12497800465612439343175031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8331866977074959562116687 12497800465612439343175031)
  ·
    refine ⟨18746700698418659014762547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12497800465612439343175031 18746700698418659014762547)
    ·
      refine ⟨28120051047627988522143821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18746700698418659014762547 28120051047627988522143821)
      ·
        refine ⟨10545019142860495695803933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28120051047627988522143821 10545019142860495695803933)
        ·
          refine ⟨3954382178572685885926475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10545019142860495695803933 3954382178572685885926475)
          ·
            refine ⟨5931573267859028828889713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954382178572685885926475 5931573267859028828889713)
            ·
              refine ⟨4448679950894271621667285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5931573267859028828889713 4448679950894271621667285)
              ·
                refine ⟨104265936349084491132827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4448679950894271621667285 104265936349084491132827)
                ·
                  rfl

theorem cell19_342659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_342659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342659 prefixEnd_342659 := by exact prefixLift 342659
  have htrace : WordTrace (prefixWord ++ tailWord_342659) baseStart_342659 baseEnd_342659 := by
    simpa [prefixWord, tailWord_342659, baseEnd_342659] using wordTrace_append hprefix tailTrace_342659
  have hstable : (prefixWord ++ tailWord_342659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342659).length < 2 ^ (prefixWord ++ tailWord_342659).sum := by decide
  have hdescent : baseEnd_342659 < baseStart_342659 := by decide
  rcases family_descends (prefixWord ++ tailWord_342659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342710 : List Nat := [5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_342710 : Nat := 118140960795 + 342710 * 2 ^ 59
def prefixEnd_342710 : Nat := 4983230072969 + 3 ^ 40 * 342710 * 2
def baseEnd_342710 : Nat := 104281454875531483999355

theorem tailTrace_342710 : CollatzResearch.WordTrace tailWord_342710 prefixEnd_342710 104281454875531483999355 := by
  unfold tailWord_342710
  simp only [CollatzResearch.WordTrace]
  refine ⟨781228786776729690830099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8333107058951783368854389 781228786776729690830099)
  ·
    refine ⟨1171843180165094536245149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 781228786776729690830099 1171843180165094536245149)
    ·
      refine ⟨439441192561910451091931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1171843180165094536245149 439441192561910451091931)
      ·
        refine ⟨659161788842865676637897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439441192561910451091931 659161788842865676637897)
        ·
          refine ⟨494371341632149257478423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 659161788842865676637897 494371341632149257478423)
          ·
            refine ⟨741557012448223886217635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494371341632149257478423 741557012448223886217635)
            ·
              refine ⟨1112335518672335829326453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741557012448223886217635 1112335518672335829326453)
              ·
                refine ⟨104281454875531483999355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1112335518672335829326453 104281454875531483999355)
                ·
                  rfl

theorem cell19_342710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_342710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342710 prefixEnd_342710 := by exact prefixLift 342710
  have htrace : WordTrace (prefixWord ++ tailWord_342710) baseStart_342710 baseEnd_342710 := by
    simpa [prefixWord, tailWord_342710, baseEnd_342710] using wordTrace_append hprefix tailTrace_342710
  have hstable : (prefixWord ++ tailWord_342710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342710).length < 2 ^ (prefixWord ++ tailWord_342710).sum := by decide
  have hdescent : baseEnd_342710 < baseStart_342710 := by decide
  rcases family_descends (prefixWord ++ tailWord_342710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342792 : List Nat := [2, 1, 3, 2, 2, 9]
def baseStart_342792 : Nat := 118140960795 + 342792 * 2 ^ 59
def prefixEnd_342792 : Nat := 4983230072969 + 3 ^ 40 * 342792 * 2
def baseEnd_342792 : Nat := 11589600692419954464101

theorem tailTrace_342792 : CollatzResearch.WordTrace tailWord_342792 prefixEnd_342792 11589600692419954464101 := by
  unfold tailWord_342792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6251325687065301528883315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8335100916087068705177753 6251325687065301528883315)
  ·
    refine ⟨9376988530597952293324973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6251325687065301528883315 9376988530597952293324973)
    ·
      refine ⟨3516370698974232109996865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9376988530597952293324973 3516370698974232109996865)
      ·
        refine ⟨2637278024230674082497649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3516370698974232109996865 2637278024230674082497649)
        ·
          refine ⟨1977958518173005561873237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2637278024230674082497649 1977958518173005561873237)
          ·
            refine ⟨11589600692419954464101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1977958518173005561873237 11589600692419954464101)
            ·
              rfl

theorem cell19_342792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 9].length) (baseStart_342792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342792 prefixEnd_342792 := by exact prefixLift 342792
  have htrace : WordTrace (prefixWord ++ tailWord_342792) baseStart_342792 baseEnd_342792 := by
    simpa [prefixWord, tailWord_342792, baseEnd_342792] using wordTrace_append hprefix tailTrace_342792
  have hstable : (prefixWord ++ tailWord_342792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342792).length < 2 ^ (prefixWord ++ tailWord_342792).sum := by decide
  have hdescent : baseEnd_342792 < baseStart_342792 := by decide
  rcases family_descends (prefixWord ++ tailWord_342792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342807 : List Nat := [1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_342807 : Nat := 118140960795 + 342807 * 2 ^ 59
def prefixEnd_342807 : Nat := 4983230072969 + 3 ^ 40 * 342807 * 2
def baseEnd_342807 : Nat := 104310970504263999843535

theorem tailTrace_342807 : CollatzResearch.WordTrace tailWord_342807 prefixEnd_342807 104310970504263999843535 := by
  unfold tailWord_342807
  simp only [CollatzResearch.WordTrace]
  refine ⟨12503198469076260619562675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8335465646050840413041783 12503198469076260619562675)
  ·
    refine ⟨18754797703614390929344013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12503198469076260619562675 18754797703614390929344013)
    ·
      refine ⟨7033049138855396598504005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18754797703614390929344013 7033049138855396598504005)
      ·
        refine ⟨1318696713535386862219501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7033049138855396598504005 1318696713535386862219501)
        ·
          refine ⟨494511267575770073332313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1318696713535386862219501 494511267575770073332313)
          ·
            refine ⟨370883450681827554999235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494511267575770073332313 370883450681827554999235)
            ·
              refine ⟨556325176022741332498853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370883450681827554999235 556325176022741332498853)
              ·
                refine ⟨104310970504263999843535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 556325176022741332498853 104310970504263999843535)
                ·
                  rfl

theorem cell19_342807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_342807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342807 prefixEnd_342807 := by exact prefixLift 342807
  have htrace : WordTrace (prefixWord ++ tailWord_342807) baseStart_342807 baseEnd_342807 := by
    simpa [prefixWord, tailWord_342807, baseEnd_342807] using wordTrace_append hprefix tailTrace_342807
  have hstable : (prefixWord ++ tailWord_342807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342807).length < 2 ^ (prefixWord ++ tailWord_342807).sum := by decide
  have hdescent : baseEnd_342807 < baseStart_342807 := by decide
  rcases family_descends (prefixWord ++ tailWord_342807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342828 : List Nat := [2, 2, 1, 1, 1, 4, 5, 3]
def baseStart_342828 : Nat := 118140960795 + 342828 * 2 ^ 59
def prefixEnd_342828 : Nat := 4983230072969 + 3 ^ 40 * 342828 * 2
def baseEnd_342828 : Nat := 104317360485742173376811

theorem tailTrace_342828 : CollatzResearch.WordTrace tailWord_342828 prefixEnd_342828 104317360485742173376811 := by
  unfold tailWord_342828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6251982201000090603038569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8335976268000120804051425 6251982201000090603038569)
  ·
    refine ⟨4688986650750067952278927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6251982201000090603038569 4688986650750067952278927)
    ·
      refine ⟨7033479976125101928418391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4688986650750067952278927 7033479976125101928418391)
      ·
        refine ⟨10550219964187652892627587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7033479976125101928418391 10550219964187652892627587)
        ·
          refine ⟨15825329946281479338941381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10550219964187652892627587 15825329946281479338941381)
          ·
            refine ⟨2967249364927777376051509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15825329946281479338941381 2967249364927777376051509)
            ·
              refine ⟨278179627961979129004829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2967249364927777376051509 278179627961979129004829)
              ·
                refine ⟨104317360485742173376811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278179627961979129004829 104317360485742173376811)
                ·
                  rfl

theorem cell19_342828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_342828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342828 prefixEnd_342828 := by exact prefixLift 342828
  have htrace : WordTrace (prefixWord ++ tailWord_342828) baseStart_342828 baseEnd_342828 := by
    simpa [prefixWord, tailWord_342828, baseEnd_342828] using wordTrace_append hprefix tailTrace_342828
  have hstable : (prefixWord ++ tailWord_342828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342828).length < 2 ^ (prefixWord ++ tailWord_342828).sum := by decide
  have hdescent : baseEnd_342828 < baseStart_342828 := by decide
  rcases family_descends (prefixWord ++ tailWord_342828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342883 : List Nat := [1, 1, 1, 5, 3, 3, 2, 3]
def baseStart_342883 : Nat := 118140960795 + 342883 * 2 ^ 59
def prefixEnd_342883 : Nat := 4983230072969 + 3 ^ 40 * 342883 * 2
def baseEnd_342883 : Nat := 104334096151518342154439

theorem tailTrace_342883 : CollatzResearch.WordTrace tailWord_342883 prefixEnd_342883 104334096151518342154439 := by
  unfold tailWord_342883
  simp only [CollatzResearch.WordTrace]
  refine ⟨12505970416800925599329303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8337313611200617066219535 12505970416800925599329303)
  ·
    refine ⟨18758955625201388398993955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12505970416800925599329303 18758955625201388398993955)
    ·
      refine ⟨28138433437802082598490933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18758955625201388398993955 28138433437802082598490933)
      ·
        refine ⟨2637978134793945243608525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28138433437802082598490933 2637978134793945243608525)
        ·
          refine ⟨989241800547729466353197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2637978134793945243608525 989241800547729466353197)
          ·
            refine ⟨370965675205398549882449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 989241800547729466353197 370965675205398549882449)
            ·
              refine ⟨278224256404048912411837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370965675205398549882449 278224256404048912411837)
              ·
                refine ⟨104334096151518342154439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278224256404048912411837 104334096151518342154439)
                ·
                  rfl

theorem cell19_342883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_342883 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342883 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342883 prefixEnd_342883 := by exact prefixLift 342883
  have htrace : WordTrace (prefixWord ++ tailWord_342883) baseStart_342883 baseEnd_342883 := by
    simpa [prefixWord, tailWord_342883, baseEnd_342883] using wordTrace_append hprefix tailTrace_342883
  have hstable : (prefixWord ++ tailWord_342883).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342883).length < 2 ^ (prefixWord ++ tailWord_342883).sum := by decide
  have hdescent : baseEnd_342883 < baseStart_342883 := by decide
  rcases family_descends (prefixWord ++ tailWord_342883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342885 : List Nat := [1, 3, 1, 3, 1, 1, 6, 3]
def baseStart_342885 : Nat := 118140960795 + 342885 * 2 ^ 59
def prefixEnd_342885 : Nat := 4983230072969 + 3 ^ 40 * 342885 * 2
def baseEnd_342885 : Nat := 104334704721182930109989

theorem tailTrace_342885 : CollatzResearch.WordTrace tailWord_342885 prefixEnd_342885 104334704721182930109989 := by
  unfold tailWord_342885
  simp only [CollatzResearch.WordTrace]
  refine ⟨12506043362793679940902109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8337362241862453293934739 12506043362793679940902109)
  ·
    refine ⟨4689766261047629977838291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12506043362793679940902109 4689766261047629977838291)
    ·
      refine ⟨7034649391571444966757437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4689766261047629977838291 7034649391571444966757437)
      ·
        refine ⟨2637993521839291862534039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7034649391571444966757437 2637993521839291862534039)
        ·
          refine ⟨3956990282758937793801059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637993521839291862534039 3956990282758937793801059)
          ·
            refine ⟨5935485424138406690701589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956990282758937793801059 5935485424138406690701589)
            ·
              refine ⟨278225879256487813626637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5935485424138406690701589 278225879256487813626637)
              ·
                refine ⟨104334704721182930109989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278225879256487813626637 104334704721182930109989)
                ·
                  rfl

theorem cell19_342885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_342885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342885 prefixEnd_342885 := by exact prefixLift 342885
  have htrace : WordTrace (prefixWord ++ tailWord_342885) baseStart_342885 baseEnd_342885 := by
    simpa [prefixWord, tailWord_342885, baseEnd_342885] using wordTrace_append hprefix tailTrace_342885
  have hstable : (prefixWord ++ tailWord_342885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342885).length < 2 ^ (prefixWord ++ tailWord_342885).sum := by decide
  have hdescent : baseEnd_342885 < baseStart_342885 := by decide
  rcases family_descends (prefixWord ++ tailWord_342885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342902 : List Nat := [5, 1, 1, 3, 1, 3, 5]
def baseStart_342902 : Nat := 118140960795 + 342902 * 2 ^ 59
def prefixEnd_342902 : Nat := 4983230072969 + 3 ^ 40 * 342902 * 2
def baseEnd_342902 : Nat := 34779959187777309244055

theorem tailTrace_342902 : CollatzResearch.WordTrace tailWord_342902 prefixEnd_342902 34779959187777309244055 := by
  unfold tailWord_342902
  simp only [CollatzResearch.WordTrace]
  refine ⟨781666462733255740266935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8337775602488061229513973 781666462733255740266935)
  ·
    refine ⟨1172499694099883610400403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 781666462733255740266935 1172499694099883610400403)
    ·
      refine ⟨1758749541149825415600605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172499694099883610400403 1758749541149825415600605)
      ·
        refine ⟨659531077931184530850227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1758749541149825415600605 659531077931184530850227)
        ·
          refine ⟨989296616896776796275341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659531077931184530850227 989296616896776796275341)
          ·
            refine ⟨370986231336291298603253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 989296616896776796275341 370986231336291298603253)
            ·
              refine ⟨34779959187777309244055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370986231336291298603253 34779959187777309244055)
              ·
                rfl

theorem cell19_342902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_342902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342902 prefixEnd_342902 := by exact prefixLift 342902
  have htrace : WordTrace (prefixWord ++ tailWord_342902) baseStart_342902 baseEnd_342902 := by
    simpa [prefixWord, tailWord_342902, baseEnd_342902] using wordTrace_append hprefix tailTrace_342902
  have hstable : (prefixWord ++ tailWord_342902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342902).length < 2 ^ (prefixWord ++ tailWord_342902).sum := by decide
  have hdescent : baseEnd_342902 < baseStart_342902 := by decide
  rcases family_descends (prefixWord ++ tailWord_342902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342944 : List Nat := [2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_342944 : Nat := 118140960795 + 342944 * 2 ^ 59
def prefixEnd_342944 : Nat := 4983230072969 + 3 ^ 40 * 342944 * 2
def baseEnd_342944 : Nat := 104352657526288274798717

theorem tailTrace_342944 : CollatzResearch.WordTrace tailWord_342944 prefixEnd_342944 104352657526288274798717 := by
  unfold tailWord_342944
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254097634789966508649943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8338796846386622011533257 6254097634789966508649943)
  ·
    refine ⟨9381146452184949762974915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6254097634789966508649943 9381146452184949762974915)
    ·
      refine ⟨14071719678277424644462373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9381146452184949762974915 14071719678277424644462373)
      ·
        refine ⟨2638447439677017120836695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14071719678277424644462373 2638447439677017120836695)
        ·
          refine ⟨3957671159515525681255043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2638447439677017120836695 3957671159515525681255043)
          ·
            refine ⟨5936506739273288521882565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957671159515525681255043 5936506739273288521882565)
            ·
              refine ⟨1113095013613741597852981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5936506739273288521882565 1113095013613741597852981)
              ·
                refine ⟨104352657526288274798717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1113095013613741597852981 104352657526288274798717)
                ·
                  rfl

theorem cell19_342944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_342944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342944 prefixEnd_342944 := by exact prefixLift 342944
  have htrace : WordTrace (prefixWord ++ tailWord_342944) baseStart_342944 baseEnd_342944 := by
    simpa [prefixWord, tailWord_342944, baseEnd_342944] using wordTrace_append hprefix tailTrace_342944
  have hstable : (prefixWord ++ tailWord_342944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342944).length < 2 ^ (prefixWord ++ tailWord_342944).sum := by decide
  have hdescent : baseEnd_342944 < baseStart_342944 := by decide
  rcases family_descends (prefixWord ++ tailWord_342944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342961 : List Nat := [1, 2, 2, 4, 4, 6]
def baseStart_342961 : Nat := 118140960795 + 342961 * 2 ^ 59
def prefixEnd_342961 : Nat := 4983230072969 + 3 ^ 40 * 342961 * 2
def baseEnd_342961 : Nat := 11595314485381919157877

theorem tailTrace_342961 : CollatzResearch.WordTrace tailWord_342961 prefixEnd_342961 11595314485381919157877 := by
  unfold tailWord_342961
  simp only [CollatzResearch.WordTrace]
  refine ⟨12508815310518344920668737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8339210207012229947112491 12508815310518344920668737)
  ·
    refine ⟨9381611482888758690501553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12508815310518344920668737 9381611482888758690501553)
    ·
      refine ⟨7036208612166569017876165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9381611482888758690501553 7036208612166569017876165)
      ·
        refine ⟨1319289114781231690851781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7036208612166569017876165 1319289114781231690851781)
        ·
          refine ⟨247366709021480942034709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1319289114781231690851781 247366709021480942034709)
          ·
            refine ⟨11595314485381919157877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 247366709021480942034709 11595314485381919157877)
            ·
              rfl

theorem cell19_342961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 6].length) (baseStart_342961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342961 prefixEnd_342961 := by exact prefixLift 342961
  have htrace : WordTrace (prefixWord ++ tailWord_342961) baseStart_342961 baseEnd_342961 := by
    simpa [prefixWord, tailWord_342961, baseEnd_342961] using wordTrace_append hprefix tailTrace_342961
  have hstable : (prefixWord ++ tailWord_342961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342961).length < 2 ^ (prefixWord ++ tailWord_342961).sum := by decide
  have hdescent : baseEnd_342961 < baseStart_342961 := by decide
  rcases family_descends (prefixWord ++ tailWord_342961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342997 : List Nat := [1, 3, 2, 3, 3, 1, 3, 3]
def baseStart_342997 : Nat := 118140960795 + 342997 * 2 ^ 59
def prefixEnd_342997 : Nat := 4983230072969 + 3 ^ 40 * 342997 * 2
def baseEnd_342997 : Nat := 104368784622399855620795

theorem tailTrace_342997 : CollatzResearch.WordTrace tailWord_342997 prefixEnd_342997 104368784622399855620795 := by
  unfold tailWord_342997
  simp only [CollatzResearch.WordTrace]
  refine ⟨12510128338387923068979245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8340085558925282045986163 12510128338387923068979245)
  ·
    refine ⟨4691298126895471150867217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12510128338387923068979245 4691298126895471150867217)
    ·
      refine ⟨3518473595171603363150413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4691298126895471150867217 3518473595171603363150413)
      ·
        refine ⟨1319427598189351261181405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3518473595171603363150413 1319427598189351261181405)
        ·
          refine ⟨494785349321006722943027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1319427598189351261181405 494785349321006722943027)
          ·
            refine ⟨742178023981510084414541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494785349321006722943027 742178023981510084414541)
            ·
              refine ⟨278316758993066281655453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742178023981510084414541 278316758993066281655453)
              ·
                refine ⟨104368784622399855620795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278316758993066281655453 104368784622399855620795)
                ·
                  rfl

theorem cell19_342997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_342997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_342997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_342997 prefixEnd_342997 := by exact prefixLift 342997
  have htrace : WordTrace (prefixWord ++ tailWord_342997) baseStart_342997 baseEnd_342997 := by
    simpa [prefixWord, tailWord_342997, baseEnd_342997] using wordTrace_append hprefix tailTrace_342997
  have hstable : (prefixWord ++ tailWord_342997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342997).length < 2 ^ (prefixWord ++ tailWord_342997).sum := by decide
  have hdescent : baseEnd_342997 < baseStart_342997 := by decide
  rcases family_descends (prefixWord ++ tailWord_342997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343054 : List Nat := [4, 1, 1, 2, 2, 4, 2, 3]
def baseStart_343054 : Nat := 118140960795 + 343054 * 2 ^ 59
def prefixEnd_343054 : Nat := 4983230072969 + 3 ^ 40 * 343054 * 2
def baseEnd_343054 : Nat := 104386128857840612353973

theorem tailTrace_343054 : CollatzResearch.WordTrace tailWord_343054 prefixEnd_343054 104386128857840612353973 := by
  unfold tailWord_343054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564025912397677725475527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8341471532787614535869477 1564025912397677725475527)
  ·
    refine ⟨2346038868596516588213291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1564025912397677725475527 2346038868596516588213291)
    ·
      refine ⟨3519058302894774882319937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346038868596516588213291 3519058302894774882319937)
      ·
        refine ⟨2639293727171081161739953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3519058302894774882319937 2639293727171081161739953)
        ·
          refine ⟨1979470295378310871304965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639293727171081161739953 1979470295378310871304965)
          ·
            refine ⟨371150680383433288369681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1979470295378310871304965 371150680383433288369681)
            ·
              refine ⟨278363010287574966277261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371150680383433288369681 278363010287574966277261)
              ·
                refine ⟨104386128857840612353973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278363010287574966277261 104386128857840612353973)
                ·
                  rfl

theorem cell19_343054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_343054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343054 prefixEnd_343054 := by exact prefixLift 343054
  have htrace : WordTrace (prefixWord ++ tailWord_343054) baseStart_343054 baseEnd_343054 := by
    simpa [prefixWord, tailWord_343054, baseEnd_343054] using wordTrace_append hprefix tailTrace_343054
  have hstable : (prefixWord ++ tailWord_343054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343054).length < 2 ^ (prefixWord ++ tailWord_343054).sum := by decide
  have hdescent : baseEnd_343054 < baseStart_343054 := by decide
  rcases family_descends (prefixWord ++ tailWord_343054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343092 : List Nat := [2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_343092 : Nat := 118140960795 + 343092 * 2 ^ 59
def prefixEnd_343092 : Nat := 4983230072969 + 3 ^ 40 * 343092 * 2
def baseEnd_343092 : Nat := 104397691681467783509425

theorem tailTrace_343092 : CollatzResearch.WordTrace tailWord_343092 prefixEnd_343092 104397691681467783509425 := by
  unfold tailWord_343092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256796636521877146843765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8342395515362502862458353 6256796636521877146843765)
  ·
    refine ⟨586574684673925982516603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6256796636521877146843765 586574684673925982516603)
    ·
      refine ⟨879862027010888973774905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586574684673925982516603 879862027010888973774905)
      ·
        refine ⟨659896520258166730331179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 879862027010888973774905 659896520258166730331179)
        ·
          refine ⟨989844780387250095496769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659896520258166730331179 989844780387250095496769)
          ·
            refine ⟨742383585290437571622577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 989844780387250095496769 742383585290437571622577)
            ·
              refine ⟨556787688967828178716933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742383585290437571622577 556787688967828178716933)
              ·
                refine ⟨104397691681467783509425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 556787688967828178716933 104397691681467783509425)
                ·
                  rfl

theorem cell19_343092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_343092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343092 prefixEnd_343092 := by exact prefixLift 343092
  have htrace : WordTrace (prefixWord ++ tailWord_343092) baseStart_343092 baseEnd_343092 := by
    simpa [prefixWord, tailWord_343092, baseEnd_343092] using wordTrace_append hprefix tailTrace_343092
  have hstable : (prefixWord ++ tailWord_343092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343092).length < 2 ^ (prefixWord ++ tailWord_343092).sum := by decide
  have hdescent : baseEnd_343092 < baseStart_343092 := by decide
  rcases family_descends (prefixWord ++ tailWord_343092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343094 : List Nat := [5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_343094 : Nat := 118140960795 + 343094 * 2 ^ 59
def prefixEnd_343094 : Nat := 4983230072969 + 3 ^ 40 * 343094 * 2
def baseEnd_343094 : Nat := 104398300251132371464975

theorem tailTrace_343094 : CollatzResearch.WordTrace tailWord_343094 prefixEnd_343094 104398300251132371464975 := by
  unfold tailWord_343094
  simp only [CollatzResearch.WordTrace]
  refine ⟨782104138689781789703771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8342444146024339090173557 782104138689781789703771)
  ·
    refine ⟨1173156208034672684555657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 782104138689781789703771 1173156208034672684555657)
    ·
      refine ⟨879867156026004513416743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1173156208034672684555657 879867156026004513416743)
      ·
        refine ⟨1319800734039006770125115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879867156026004513416743 1319800734039006770125115)
        ·
          refine ⟨1979701101058510155187673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319800734039006770125115 1979701101058510155187673)
          ·
            refine ⟨1484775825793882616390755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1979701101058510155187673 1484775825793882616390755)
            ·
              refine ⟨2227163738690823924586133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484775825793882616390755 2227163738690823924586133)
              ·
                refine ⟨104398300251132371464975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2227163738690823924586133 104398300251132371464975)
                ·
                  rfl

theorem cell19_343094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_343094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343094 prefixEnd_343094 := by exact prefixLift 343094
  have htrace : WordTrace (prefixWord ++ tailWord_343094) baseStart_343094 baseEnd_343094 := by
    simpa [prefixWord, tailWord_343094, baseEnd_343094] using wordTrace_append hprefix tailTrace_343094
  have hstable : (prefixWord ++ tailWord_343094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343094).length < 2 ^ (prefixWord ++ tailWord_343094).sum := by decide
  have hdescent : baseEnd_343094 < baseStart_343094 := by decide
  rcases family_descends (prefixWord ++ tailWord_343094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343096 : List Nat := [2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_343096 : Nat := 118140960795 + 343096 * 2 ^ 59
def prefixEnd_343096 : Nat := 4983230072969 + 3 ^ 40 * 343096 * 2
def baseEnd_343096 : Nat := 104398908820796959420525

theorem tailTrace_343096 : CollatzResearch.WordTrace tailWord_343096 prefixEnd_343096 104398908820796959420525 := by
  unfold tailWord_343096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256869582514631488416571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8342492776686175317888761 6256869582514631488416571)
  ·
    refine ⟨9385304373771947232624857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6256869582514631488416571 9385304373771947232624857)
    ·
      refine ⟨7038978280328960424468643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9385304373771947232624857 7038978280328960424468643)
      ·
        refine ⟨10558467420493440636702965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7038978280328960424468643 10558467420493440636702965)
        ·
          refine ⟨989856320671260059690903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10558467420493440636702965 989856320671260059690903)
          ·
            refine ⟨1484784481006890089536355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989856320671260059690903 1484784481006890089536355)
            ·
              refine ⟨2227176721510335134304533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484784481006890089536355 2227176721510335134304533)
              ·
                refine ⟨104398908820796959420525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2227176721510335134304533 104398908820796959420525)
                ·
                  rfl

theorem cell19_343096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_343096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343096 prefixEnd_343096 := by exact prefixLift 343096
  have htrace : WordTrace (prefixWord ++ tailWord_343096) baseStart_343096 baseEnd_343096 := by
    simpa [prefixWord, tailWord_343096, baseEnd_343096] using wordTrace_append hprefix tailTrace_343096
  have hstable : (prefixWord ++ tailWord_343096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343096).length < 2 ^ (prefixWord ++ tailWord_343096).sum := by decide
  have hdescent : baseEnd_343096 < baseStart_343096 := by decide
  rcases family_descends (prefixWord ++ tailWord_343096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343191 : List Nat := [1, 1, 3, 3, 3, 2, 6]
def baseStart_343191 : Nat := 118140960795 + 343191 * 2 ^ 59
def prefixEnd_343191 : Nat := 4983230072969 + 3 ^ 40 * 343191 * 2
def baseEnd_343191 : Nat := 34809271959954962436385

theorem tailTrace_343191 : CollatzResearch.WordTrace tailWord_343191 prefixEnd_343191 34809271959954962436385 := by
  unfold tailWord_343191
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517204099685094201541427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8344802733123396134360951 12517204099685094201541427)
  ·
    refine ⟨18775806149527641302312141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12517204099685094201541427 18775806149527641302312141)
    ·
      refine ⟨7040927306072865488367053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18775806149527641302312141 7040927306072865488367053)
      ·
        refine ⟨2640347739777324558137645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7040927306072865488367053 2640347739777324558137645)
        ·
          refine ⟨990130402416496709301617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2640347739777324558137645 990130402416496709301617)
          ·
            refine ⟨742597801812372531976213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990130402416496709301617 742597801812372531976213)
            ·
              refine ⟨34809271959954962436385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 742597801812372531976213 34809271959954962436385)
              ·
                rfl

theorem cell19_343191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_343191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343191 prefixEnd_343191 := by exact prefixLift 343191
  have htrace : WordTrace (prefixWord ++ tailWord_343191) baseStart_343191 baseEnd_343191 := by
    simpa [prefixWord, tailWord_343191, baseEnd_343191] using wordTrace_append hprefix tailTrace_343191
  have hstable : (prefixWord ++ tailWord_343191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343191).length < 2 ^ (prefixWord ++ tailWord_343191).sum := by decide
  have hdescent : baseEnd_343191 < baseStart_343191 := by decide
  rcases family_descends (prefixWord ++ tailWord_343191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343246 : List Nat := [4, 1, 1, 1, 5, 2, 5]
def baseStart_343246 : Nat := 118140960795 + 343246 * 2 ^ 59
def prefixEnd_343246 : Nat := 4983230072969 + 3 ^ 40 * 343246 * 2
def baseEnd_343246 : Nat := 34814850515213685362261

theorem tailTrace_343246 : CollatzResearch.WordTrace tailWord_343246 prefixEnd_343246 34814850515213685362261 := by
  unfold tailWord_343246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564901264310729824349199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8346140076323892396529061 1564901264310729824349199)
  ·
    refine ⟨2347351896466094736523799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1564901264310729824349199 2347351896466094736523799)
    ·
      refine ⟨3521027844699142104785699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347351896466094736523799 3521027844699142104785699)
      ·
        refine ⟨5281541767048713157178549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521027844699142104785699 5281541767048713157178549)
        ·
          refine ⟨495144540660816858485489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5281541767048713157178549 495144540660816858485489)
          ·
            refine ⟨371358405495612643864117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495144540660816858485489 371358405495612643864117)
            ·
              refine ⟨34814850515213685362261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 371358405495612643864117 34814850515213685362261)
              ·
                rfl

theorem cell19_343246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_343246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343246 prefixEnd_343246 := by exact prefixLift 343246
  have htrace : WordTrace (prefixWord ++ tailWord_343246) baseStart_343246 baseEnd_343246 := by
    simpa [prefixWord, tailWord_343246, baseEnd_343246] using wordTrace_append hprefix tailTrace_343246
  have hstable : (prefixWord ++ tailWord_343246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343246).length < 2 ^ (prefixWord ++ tailWord_343246).sum := by decide
  have hdescent : baseEnd_343246 < baseStart_343246 := by decide
  rcases family_descends (prefixWord ++ tailWord_343246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343307 : List Nat := [1, 1, 1, 1, 5, 10]
def baseStart_343307 : Nat := 118140960795 + 343307 * 2 ^ 59
def prefixEnd_343307 : Nat := 4983230072969 + 3 ^ 40 * 343307 * 2
def baseEnd_343307 : Nat := 11607012546712332081229

theorem tailTrace_343307 : CollatzResearch.WordTrace tailWord_343307 prefixEnd_343307 11607012546712332081229 := by
  unfold tailWord_343307
  simp only [CollatzResearch.WordTrace]
  refine ⟨12521434967264846012764175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8347623311509897341842783 12521434967264846012764175)
  ·
    refine ⟨18782152450897269019146263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12521434967264846012764175 18782152450897269019146263)
    ·
      refine ⟨28173228676345903528719395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18782152450897269019146263 28173228676345903528719395)
      ·
        refine ⟨42259843014518855293079093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28173228676345903528719395 42259843014518855293079093)
        ·
          refine ⟨3961860282611142683726165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42259843014518855293079093 3961860282611142683726165)
          ·
            refine ⟨11607012546712332081229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3961860282611142683726165 11607012546712332081229)
            ·
              rfl

theorem cell19_343307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 10].length) (baseStart_343307 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343307 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343307 prefixEnd_343307 := by exact prefixLift 343307
  have htrace : WordTrace (prefixWord ++ tailWord_343307) baseStart_343307 baseEnd_343307 := by
    simpa [prefixWord, tailWord_343307, baseEnd_343307] using wordTrace_append hprefix tailTrace_343307
  have hstable : (prefixWord ++ tailWord_343307).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343307).length < 2 ^ (prefixWord ++ tailWord_343307).sum := by decide
  have hdescent : baseEnd_343307 < baseStart_343307 := by decide
  rcases family_descends (prefixWord ++ tailWord_343307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343322 : List Nat := [3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_343322 : Nat := 118140960795 + 343322 * 2 ^ 59
def prefixEnd_343322 : Nat := 4983230072969 + 3 ^ 40 * 343322 * 2
def baseEnd_343322 : Nat := 104467677192895398397687

theorem tailTrace_343322 : CollatzResearch.WordTrace tailWord_343322 prefixEnd_343322 104467677192895398397687 := by
  unfold tailWord_343322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130495515552625893640055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8347988041473669049706813 3130495515552625893640055)
  ·
    refine ⟨4695743273328938840460083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3130495515552625893640055 4695743273328938840460083)
    ·
      refine ⟨7043614909993408260690125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4695743273328938840460083 7043614909993408260690125)
      ·
        refine ⟨2641355591247528097758797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7043614909993408260690125 2641355591247528097758797)
        ·
          refine ⟨990508346717823036659549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2641355591247528097758797 990508346717823036659549)
          ·
            refine ⟨371440630019183638747331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 990508346717823036659549 371440630019183638747331)
            ·
              refine ⟨557160945028775458120997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371440630019183638747331 557160945028775458120997)
              ·
                refine ⟨104467677192895398397687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557160945028775458120997 104467677192895398397687)
                ·
                  rfl

theorem cell19_343322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_343322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343322 prefixEnd_343322 := by exact prefixLift 343322
  have htrace : WordTrace (prefixWord ++ tailWord_343322) baseStart_343322 baseEnd_343322 := by
    simpa [prefixWord, tailWord_343322, baseEnd_343322] using wordTrace_append hprefix tailTrace_343322
  have hstable : (prefixWord ++ tailWord_343322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343322).length < 2 ^ (prefixWord ++ tailWord_343322).sum := by decide
  have hdescent : baseEnd_343322 < baseStart_343322 := by decide
  rcases family_descends (prefixWord ++ tailWord_343322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343324 : List Nat := [2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_343324 : Nat := 118140960795 + 343324 * 2 ^ 59
def prefixEnd_343324 : Nat := 4983230072969 + 3 ^ 40 * 343324 * 2
def baseEnd_343324 : Nat := 104468285762559986353237

theorem tailTrace_343324 : CollatzResearch.WordTrace tailWord_343324 prefixEnd_343324 104468285762559986353237 := by
  unfold tailWord_343324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6261027504101628958066513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8348036672135505277422017 6261027504101628958066513)
  ·
    refine ⟨4695770628076221718549885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6261027504101628958066513 4695770628076221718549885)
    ·
      refine ⟨1760913985528583144456207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4695770628076221718549885 1760913985528583144456207)
      ·
        refine ⟨2641370978292874716684311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760913985528583144456207 2641370978292874716684311)
        ·
          refine ⟨3962056467439312075026467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2641370978292874716684311 3962056467439312075026467)
          ·
            refine ⟨5943084701158968112539701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3962056467439312075026467 5943084701158968112539701)
            ·
              refine ⟨557164190733653260550597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5943084701158968112539701 557164190733653260550597)
              ·
                refine ⟨104468285762559986353237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557164190733653260550597 104468285762559986353237)
                ·
                  rfl

theorem cell19_343324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_343324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343324 prefixEnd_343324 := by exact prefixLift 343324
  have htrace : WordTrace (prefixWord ++ tailWord_343324) baseStart_343324 baseEnd_343324 := by
    simpa [prefixWord, tailWord_343324, baseEnd_343324] using wordTrace_append hprefix tailTrace_343324
  have hstable : (prefixWord ++ tailWord_343324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343324).length < 2 ^ (prefixWord ++ tailWord_343324).sum := by decide
  have hdescent : baseEnd_343324 < baseStart_343324 := by decide
  rcases family_descends (prefixWord ++ tailWord_343324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343459 : List Nat := [1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_343459 : Nat := 118140960795 + 343459 * 2 ^ 59
def prefixEnd_343459 : Nat := 4983230072969 + 3 ^ 40 * 343459 * 2
def baseEnd_343459 : Nat := 104509364214919673352869

theorem tailTrace_343459 : CollatzResearch.WordTrace tailWord_343459 prefixEnd_343459 104509364214919673352869 := by
  unfold tailWord_343459
  simp only [CollatzResearch.WordTrace]
  refine ⟨12526978862714175972297431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8351319241809450648198287 12526978862714175972297431)
  ·
    refine ⟨18790468294071263958446147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12526978862714175972297431 18790468294071263958446147)
    ·
      refine ⟨28185702441106895937669221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18790468294071263958446147 28185702441106895937669221)
      ·
        refine ⟨5284819207707542988312979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28185702441106895937669221 5284819207707542988312979)
        ·
          refine ⟨7927228811561314482469469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284819207707542988312979 7927228811561314482469469)
          ·
            refine ⟨2972710804335492930926051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7927228811561314482469469 2972710804335492930926051)
            ·
              refine ⟨4459066206503239396389077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972710804335492930926051 4459066206503239396389077)
              ·
                refine ⟨104509364214919673352869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4459066206503239396389077 104509364214919673352869)
                ·
                  rfl

theorem cell19_343459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_343459 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343459 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343459 prefixEnd_343459 := by exact prefixLift 343459
  have htrace : WordTrace (prefixWord ++ tailWord_343459) baseStart_343459 baseEnd_343459 := by
    simpa [prefixWord, tailWord_343459, baseEnd_343459] using wordTrace_append hprefix tailTrace_343459
  have hstable : (prefixWord ++ tailWord_343459).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343459).length < 2 ^ (prefixWord ++ tailWord_343459).sum := by decide
  have hdescent : baseEnd_343459 < baseStart_343459 := by decide
  rcases family_descends (prefixWord ++ tailWord_343459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343476 : List Nat := [2, 5, 2, 10]
def baseStart_343476 : Nat := 118140960795 + 343476 * 2 ^ 59
def prefixEnd_343476 : Nat := 4983230072969 + 3 ^ 40 * 343476 * 2
def baseEnd_343476 : Nat := 1290302926630477419445

theorem tailTrace_343476 : CollatzResearch.WordTrace tailWord_343476 prefixEnd_343476 1290302926630477419445 := by
  unfold tailWord_343476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6263799451826293937833141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8351732602435058583777521 6263799451826293937833141)
  ·
    refine ⟨587231198608715056671857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6263799451826293937833141 587231198608715056671857)
    ·
      refine ⟨440423398956536292503893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 587231198608715056671857 440423398956536292503893)
      ·
        refine ⟨1290302926630477419445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 440423398956536292503893 1290302926630477419445)
        ·
          rfl

theorem cell19_343476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 10].length) (baseStart_343476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343476 prefixEnd_343476 := by exact prefixLift 343476
  have htrace : WordTrace (prefixWord ++ tailWord_343476) baseStart_343476 baseEnd_343476 := by
    simpa [prefixWord, tailWord_343476, baseEnd_343476] using wordTrace_append hprefix tailTrace_343476
  have hstable : (prefixWord ++ tailWord_343476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343476).length < 2 ^ (prefixWord ++ tailWord_343476).sum := by decide
  have hdescent : baseEnd_343476 < baseStart_343476 := by decide
  rcases family_descends (prefixWord ++ tailWord_343476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343510 : List Nat := [5, 2, 1, 1, 1, 3, 3, 3]
def baseStart_343510 : Nat := 118140960795 + 343510 * 2 ^ 59
def prefixEnd_343510 : Nat := 4983230072969 + 3 ^ 40 * 343510 * 2
def baseEnd_343510 : Nat := 104524882741366666219397

theorem tailTrace_343510 : CollatzResearch.WordTrace tailWord_343510 prefixEnd_343510 104524882741366666219397 := by
  unfold tailWord_343510
  simp only [CollatzResearch.WordTrace]
  refine ⟨783052436595588230150249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8352559323686274454935989 783052436595588230150249)
  ·
    refine ⟨587289327446691172612687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 783052436595588230150249 587289327446691172612687)
    ·
      refine ⟨880933991170036758919031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 587289327446691172612687 880933991170036758919031)
      ·
        refine ⟨1321400986755055138378547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880933991170036758919031 1321400986755055138378547)
        ·
          refine ⟨1982101480132582707567821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321400986755055138378547 1982101480132582707567821)
          ·
            refine ⟨743288055049718515337933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1982101480132582707567821 743288055049718515337933)
            ·
              refine ⟨278733020643644443251725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743288055049718515337933 278733020643644443251725)
              ·
                refine ⟨104524882741366666219397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278733020643644443251725 104524882741366666219397)
                ·
                  rfl

theorem cell19_343510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_343510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343510 prefixEnd_343510 := by exact prefixLift 343510
  have htrace : WordTrace (prefixWord ++ tailWord_343510) baseStart_343510 baseEnd_343510 := by
    simpa [prefixWord, tailWord_343510, baseEnd_343510] using wordTrace_append hprefix tailTrace_343510
  have hstable : (prefixWord ++ tailWord_343510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343510).length < 2 ^ (prefixWord ++ tailWord_343510).sum := by decide
  have hdescent : baseEnd_343510 < baseStart_343510 := by decide
  rcases family_descends (prefixWord ++ tailWord_343510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343571 : List Nat := [1, 1, 1, 2, 1, 6, 4, 3]
def baseStart_343571 : Nat := 118140960795 + 343571 * 2 ^ 59
def prefixEnd_343571 : Nat := 4983230072969 + 3 ^ 40 * 343571 * 2
def baseEnd_343571 : Nat := 104543444116136598863675

theorem tailTrace_343571 : CollatzResearch.WordTrace tailWord_343571 prefixEnd_343571 104543444116136598863675 := by
  unfold tailWord_343571
  simp only [CollatzResearch.WordTrace]
  refine ⟨12531063838308419100374567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8354042558872279400249711 12531063838308419100374567)
  ·
    refine ⟨18796595757462628650561851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12531063838308419100374567 18796595757462628650561851)
    ·
      refine ⟨28194893636193942975842777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18796595757462628650561851 28194893636193942975842777)
      ·
        refine ⟨21146170227145457231882083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28194893636193942975842777 21146170227145457231882083)
        ·
          refine ⟨31719255340718185847823125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21146170227145457231882083 31719255340718185847823125)
          ·
            refine ⟨1486840094096164961616709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31719255340718185847823125 1486840094096164961616709)
            ·
              refine ⟨278782517643030930303133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1486840094096164961616709 278782517643030930303133)
              ·
                refine ⟨104543444116136598863675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278782517643030930303133 104543444116136598863675)
                ·
                  rfl

theorem cell19_343571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_343571 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343571 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343571 prefixEnd_343571 := by exact prefixLift 343571
  have htrace : WordTrace (prefixWord ++ tailWord_343571) baseStart_343571 baseEnd_343571 := by
    simpa [prefixWord, tailWord_343571, baseEnd_343571] using wordTrace_append hprefix tailTrace_343571
  have hstable : (prefixWord ++ tailWord_343571).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343571).length < 2 ^ (prefixWord ++ tailWord_343571).sum := by decide
  have hdescent : baseEnd_343571 < baseStart_343571 := by decide
  rcases family_descends (prefixWord ++ tailWord_343571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343582 : List Nat := [4, 3, 3, 1, 2, 1, 5]
def baseStart_343582 : Nat := 118140960795 + 343582 * 2 ^ 59
def prefixEnd_343582 : Nat := 4983230072969 + 3 ^ 40 * 343582 * 2
def baseEnd_343582 : Nat := 34848930416430610873067

theorem tailTrace_343582 : CollatzResearch.WordTrace tailWord_343582 prefixEnd_343582 34848930416430610873067 := by
  unfold tailWord_343582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566433130158570997378125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8354310027512378652683333 1566433130158570997378125)
  ·
    refine ⟨587412423809464124016797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1566433130158570997378125 587412423809464124016797)
    ·
      refine ⟨220279658928549046506299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 587412423809464124016797 220279658928549046506299)
      ·
        refine ⟨330419488392823569759449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220279658928549046506299 330419488392823569759449)
        ·
          refine ⟨247814616294617677319587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330419488392823569759449 247814616294617677319587)
          ·
            refine ⟨371721924441926515979381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247814616294617677319587 371721924441926515979381)
            ·
              refine ⟨34848930416430610873067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 371721924441926515979381 34848930416430610873067)
              ·
                rfl

theorem cell19_343582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_343582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343582 prefixEnd_343582 := by exact prefixLift 343582
  have htrace : WordTrace (prefixWord ++ tailWord_343582) baseStart_343582 baseEnd_343582 := by
    simpa [prefixWord, tailWord_343582, baseEnd_343582] using wordTrace_append hprefix tailTrace_343582
  have hstable : (prefixWord ++ tailWord_343582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343582).length < 2 ^ (prefixWord ++ tailWord_343582).sum := by decide
  have hdescent : baseEnd_343582 < baseStart_343582 := by decide
  rcases family_descends (prefixWord ++ tailWord_343582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343609 : List Nat := [1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_343609 : Nat := 118140960795 + 343609 * 2 ^ 59
def prefixEnd_343609 : Nat := 4983230072969 + 3 ^ 40 * 343609 * 2
def baseEnd_343609 : Nat := 104555006939763770019127

theorem tailTrace_343609 : CollatzResearch.WordTrace tailWord_343609 prefixEnd_343609 104555006939763770019127 := by
  unfold tailWord_343609
  simp only [CollatzResearch.WordTrace]
  refine ⟨12532449812170751590257881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8354966541447167726838587 12532449812170751590257881)
  ·
    refine ⟨9399337359128063692693411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12532449812170751590257881 9399337359128063692693411)
    ·
      refine ⟨14099006038692095539040117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9399337359128063692693411 14099006038692095539040117)
      ·
        refine ⟨1321781816127383956785011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14099006038692095539040117 1321781816127383956785011)
        ·
          refine ⟨1982672724191075935177517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321781816127383956785011 1982672724191075935177517)
          ·
            refine ⟨743502271571653475691569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1982672724191075935177517 743502271571653475691569)
            ·
              refine ⟨557626703678740106768677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743502271571653475691569 557626703678740106768677)
              ·
                refine ⟨104555006939763770019127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557626703678740106768677 104555006939763770019127)
                ·
                  rfl

theorem cell19_343609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_343609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343609 prefixEnd_343609 := by exact prefixLift 343609
  have htrace : WordTrace (prefixWord ++ tailWord_343609) baseStart_343609 baseEnd_343609 := by
    simpa [prefixWord, tailWord_343609, baseEnd_343609] using wordTrace_append hprefix tailTrace_343609
  have hstable : (prefixWord ++ tailWord_343609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343609).length < 2 ^ (prefixWord ++ tailWord_343609).sum := by decide
  have hdescent : baseEnd_343609 < baseStart_343609 := by decide
  rcases family_descends (prefixWord ++ tailWord_343609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343645 : List Nat := [1, 4, 4, 2, 1, 7]
def baseStart_343645 : Nat := 118140960795 + 343645 * 2 ^ 59
def prefixEnd_343645 : Nat := 4983230072969 + 3 ^ 40 * 343645 * 2
def baseEnd_343645 : Nat := 11618440132636261468781

theorem tailTrace_343645 : CollatzResearch.WordTrace tailWord_343645 prefixEnd_343645 11618440132636261468781 := by
  unfold tailWord_343645
  simp only [CollatzResearch.WordTrace]
  refine ⟨12533762840040329738568389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8355841893360219825712259 12533762840040329738568389)
  ·
    refine ⟨2350080532507561825981573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12533762840040329738568389 2350080532507561825981573)
    ·
      refine ⟨440640099845167842371545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2350080532507561825981573 440640099845167842371545)
      ·
        refine ⟨330480074883875881778659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440640099845167842371545 330480074883875881778659)
        ·
          refine ⟨495720112325813822667989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330480074883875881778659 495720112325813822667989)
          ·
            refine ⟨11618440132636261468781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 495720112325813822667989 11618440132636261468781)
            ·
              rfl

theorem cell19_343645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 7].length) (baseStart_343645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343645 prefixEnd_343645 := by exact prefixLift 343645
  have htrace : WordTrace (prefixWord ++ tailWord_343645) baseStart_343645 baseEnd_343645 := by
    simpa [prefixWord, tailWord_343645, baseEnd_343645] using wordTrace_append hprefix tailTrace_343645
  have hstable : (prefixWord ++ tailWord_343645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343645).length < 2 ^ (prefixWord ++ tailWord_343645).sum := by decide
  have hdescent : baseEnd_343645 < baseStart_343645 := by decide
  rcases family_descends (prefixWord ++ tailWord_343645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343662 : List Nat := [4, 1, 2, 2, 4, 1, 1, 4]
def baseStart_343662 : Nat := 118140960795 + 343662 * 2 ^ 59
def prefixEnd_343662 : Nat := 4983230072969 + 3 ^ 40 * 343662 * 2
def baseEnd_343662 : Nat := 104571134035875350841205

theorem tailTrace_343662 : CollatzResearch.WordTrace tailWord_343662 prefixEnd_343662 104571134035875350841205 := by
  unfold tailWord_343662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566797860122342705242155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8356255253985827761291493 1566797860122342705242155)
  ·
    refine ⟨2350196790183514057863233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1566797860122342705242155 2350196790183514057863233)
    ·
      refine ⟨1762647592637635543397425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2350196790183514057863233 1762647592637635543397425)
      ·
        refine ⟨1321985694478226657548069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1762647592637635543397425 1321985694478226657548069)
        ·
          refine ⟨247872317714667498290263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1321985694478226657548069 247872317714667498290263)
          ·
            refine ⟨371808476572001247435395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247872317714667498290263 371808476572001247435395)
            ·
              refine ⟨557712714858001871153093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371808476572001247435395 557712714858001871153093)
              ·
                refine ⟨104571134035875350841205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557712714858001871153093 104571134035875350841205)
                ·
                  rfl

theorem cell19_343662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_343662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343662 prefixEnd_343662 := by exact prefixLift 343662
  have htrace : WordTrace (prefixWord ++ tailWord_343662) baseStart_343662 baseEnd_343662 := by
    simpa [prefixWord, tailWord_343662, baseEnd_343662] using wordTrace_append hprefix tailTrace_343662
  have hstable : (prefixWord ++ tailWord_343662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343662).length < 2 ^ (prefixWord ++ tailWord_343662).sum := by decide
  have hdescent : baseEnd_343662 < baseStart_343662 := by decide
  rcases family_descends (prefixWord ++ tailWord_343662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343666 : List Nat := [3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_343666 : Nat := 118140960795 + 343666 * 2 ^ 59
def prefixEnd_343666 : Nat := 4983230072969 + 3 ^ 40 * 343666 * 2
def baseEnd_343666 : Nat := 104572351175204526752305

theorem tailTrace_343666 : CollatzResearch.WordTrace tailWord_343666 prefixEnd_343666 104572351175204526752305 := by
  unfold tailWord_343666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133632193241062581270713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8356352515309500216721901 3133632193241062581270713)
  ·
    refine ⟨2350224144930796935953035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3133632193241062581270713 2350224144930796935953035)
    ·
      refine ⟨3525336217396195403929553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2350224144930796935953035 3525336217396195403929553)
      ·
        refine ⟨2644002163047146552947165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3525336217396195403929553 2644002163047146552947165)
        ·
          refine ⟨991500811142679957355187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2644002163047146552947165 991500811142679957355187)
          ·
            refine ⟨1487251216714019936032781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991500811142679957355187 1487251216714019936032781)
            ·
              refine ⟨557719206267757476012293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1487251216714019936032781 557719206267757476012293)
              ·
                refine ⟨104572351175204526752305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557719206267757476012293 104572351175204526752305)
                ·
                  rfl

theorem cell19_343666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_343666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343666 prefixEnd_343666 := by exact prefixLift 343666
  have htrace : WordTrace (prefixWord ++ tailWord_343666) baseStart_343666 baseEnd_343666 := by
    simpa [prefixWord, tailWord_343666, baseEnd_343666] using wordTrace_append hprefix tailTrace_343666
  have hstable : (prefixWord ++ tailWord_343666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343666).length < 2 ^ (prefixWord ++ tailWord_343666).sum := by decide
  have hdescent : baseEnd_343666 < baseStart_343666 := by decide
  rcases family_descends (prefixWord ++ tailWord_343666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343685 : List Nat := [1, 3, 1, 1, 4, 1, 5, 3]
def baseStart_343685 : Nat := 118140960795 + 343685 * 2 ^ 59
def prefixEnd_343685 : Nat := 4983230072969 + 3 ^ 40 * 343685 * 2
def baseEnd_343685 : Nat := 104578132587018112330031

theorem tailTrace_343685 : CollatzResearch.WordTrace tailWord_343685 prefixEnd_343685 104578132587018112330031 := by
  unfold tailWord_343685
  simp only [CollatzResearch.WordTrace]
  refine ⟨12535221759895416570024509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8356814506596944380016339 12535221759895416570024509)
  ·
    refine ⟨4700708159960781213759191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12535221759895416570024509 4700708159960781213759191)
    ·
      refine ⟨7051062239941171820638787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700708159960781213759191 7051062239941171820638787)
      ·
        refine ⟨10576593359911757730958181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7051062239941171820638787 10576593359911757730958181)
        ·
          refine ⟨1983111254983454574554659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10576593359911757730958181 1983111254983454574554659)
          ·
            refine ⟨2974666882475181861831989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983111254983454574554659 2974666882475181861831989)
            ·
              refine ⟨278875020232048299546749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2974666882475181861831989 278875020232048299546749)
              ·
                refine ⟨104578132587018112330031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278875020232048299546749 104578132587018112330031)
                ·
                  rfl

theorem cell19_343685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_343685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343685 prefixEnd_343685 := by exact prefixLift 343685
  have htrace : WordTrace (prefixWord ++ tailWord_343685) baseStart_343685 baseEnd_343685 := by
    simpa [prefixWord, tailWord_343685, baseEnd_343685] using wordTrace_append hprefix tailTrace_343685
  have hstable : (prefixWord ++ tailWord_343685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343685).length < 2 ^ (prefixWord ++ tailWord_343685).sum := by decide
  have hdescent : baseEnd_343685 < baseStart_343685 := by decide
  rcases family_descends (prefixWord ++ tailWord_343685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343740 : List Nat := [2, 2, 2, 3, 1, 4, 2, 3]
def baseStart_343740 : Nat := 118140960795 + 343740 * 2 ^ 59
def prefixEnd_343740 : Nat := 4983230072969 + 3 ^ 40 * 343740 * 2
def baseEnd_343740 : Nat := 104594868252794281107659

theorem tailTrace_343740 : CollatzResearch.WordTrace tailWord_343740 prefixEnd_343740 104594868252794281107659 := by
  unfold tailWord_343740
  simp only [CollatzResearch.WordTrace]
  refine ⟨6268613887348080481638337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8358151849797440642184449 6268613887348080481638337)
  ·
    refine ⟨4701460415511060361228753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6268613887348080481638337 4701460415511060361228753)
    ·
      refine ⟨3526095311633295270921565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4701460415511060361228753 3526095311633295270921565)
      ·
        refine ⟨1322285741862485726595587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3526095311633295270921565 1322285741862485726595587)
        ·
          refine ⟨1983428612793728589893381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322285741862485726595587 1983428612793728589893381)
          ·
            refine ⟨371892864898824110605009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1983428612793728589893381 371892864898824110605009)
            ·
              refine ⟨278919648674118082953757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371892864898824110605009 278919648674118082953757)
              ·
                refine ⟨104594868252794281107659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278919648674118082953757 104594868252794281107659)
                ·
                  rfl

theorem cell19_343740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_343740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343740 prefixEnd_343740 := by exact prefixLift 343740
  have htrace : WordTrace (prefixWord ++ tailWord_343740) baseStart_343740 baseEnd_343740 := by
    simpa [prefixWord, tailWord_343740, baseEnd_343740] using wordTrace_append hprefix tailTrace_343740
  have hstable : (prefixWord ++ tailWord_343740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343740).length < 2 ^ (prefixWord ++ tailWord_343740).sum := by decide
  have hdescent : baseEnd_343740 < baseStart_343740 := by decide
  rcases family_descends (prefixWord ++ tailWord_343740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343742 : List Nat := [4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_343742 : Nat := 118140960795 + 343742 * 2 ^ 59
def prefixEnd_343742 : Nat := 4983230072969 + 3 ^ 40 * 343742 * 2
def baseEnd_343742 : Nat := 104595476822458869063209

theorem tailTrace_343742 : CollatzResearch.WordTrace tailWord_343742 prefixEnd_343742 104595476822458869063209 := by
  unfold tailWord_343742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567162590086114413106185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8358200480459276869899653 1567162590086114413106185)
  ·
    refine ⟨1175371942564585809829639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1567162590086114413106185 1175371942564585809829639)
    ·
      refine ⟨1763057913846878714744459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175371942564585809829639 1763057913846878714744459)
      ·
        refine ⟨2644586870770318072116689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763057913846878714744459 2644586870770318072116689)
        ·
          refine ⟨1983440153077738554087517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2644586870770318072116689 1983440153077738554087517)
          ·
            refine ⟨743790057404151957782819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1983440153077738554087517 743790057404151957782819)
            ·
              refine ⟨1115685086106227936674229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743790057404151957782819 1115685086106227936674229)
              ·
                refine ⟨104595476822458869063209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1115685086106227936674229 104595476822458869063209)
                ·
                  rfl

theorem cell19_343742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_343742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343742 prefixEnd_343742 := by exact prefixLift 343742
  have htrace : WordTrace (prefixWord ++ tailWord_343742) baseStart_343742 baseEnd_343742 := by
    simpa [prefixWord, tailWord_343742, baseEnd_343742] using wordTrace_append hprefix tailTrace_343742
  have hstable : (prefixWord ++ tailWord_343742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343742).length < 2 ^ (prefixWord ++ tailWord_343742).sum := by decide
  have hdescent : baseEnd_343742 < baseStart_343742 := by decide
  rcases family_descends (prefixWord ++ tailWord_343742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343744 : List Nat := [2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_343744 : Nat := 118140960795 + 343744 * 2 ^ 59
def prefixEnd_343744 : Nat := 4983230072969 + 3 ^ 40 * 343744 * 2
def baseEnd_343744 : Nat := 104596085392123457018759

theorem tailTrace_343744 : CollatzResearch.WordTrace tailWord_343744 prefixEnd_343744 104596085392123457018759 := by
  unfold tailWord_343744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6268686833340834823211143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8358249111121113097614857 6268686833340834823211143)
  ·
    refine ⟨9403030250011252234816715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6268686833340834823211143 9403030250011252234816715)
    ·
      refine ⟨14104545375016878352225073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9403030250011252234816715 14104545375016878352225073)
      ·
        refine ⟨10578409031262658764168805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14104545375016878352225073 10578409031262658764168805)
        ·
          refine ⟨1983451693361748518281651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10578409031262658764168805 1983451693361748518281651)
          ·
            refine ⟨2975177540042622777422477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983451693361748518281651 2975177540042622777422477)
            ·
              refine ⟨1115691577515983541533429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2975177540042622777422477 1115691577515983541533429)
              ·
                refine ⟨104596085392123457018759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1115691577515983541533429 104596085392123457018759)
                ·
                  rfl

theorem cell19_343744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_343744 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343744 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343744 prefixEnd_343744 := by exact prefixLift 343744
  have htrace : WordTrace (prefixWord ++ tailWord_343744) baseStart_343744 baseEnd_343744 := by
    simpa [prefixWord, tailWord_343744, baseEnd_343744] using wordTrace_append hprefix tailTrace_343744
  have hstable : (prefixWord ++ tailWord_343744).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343744).length < 2 ^ (prefixWord ++ tailWord_343744).sum := by decide
  have hdescent : baseEnd_343744 < baseStart_343744 := by decide
  rcases family_descends (prefixWord ++ tailWord_343744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343972 : List Nat := [2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_343972 : Nat := 118140960795 + 343972 * 2 ^ 59
def prefixEnd_343972 : Nat := 4983230072969 + 3 ^ 40 * 343972 * 2
def baseEnd_343972 : Nat := 104665462333886483951471

theorem tailTrace_343972 : CollatzResearch.WordTrace tailWord_343972 prefixEnd_343972 104665462333886483951471 := by
  unfold tailWord_343972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6272844754927832292861085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8363793006570443057148113 6272844754927832292861085)
  ·
    refine ⟨2352316783097937109822907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6272844754927832292861085 2352316783097937109822907)
    ·
      refine ⟨3528475174646905664734361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2352316783097937109822907 3528475174646905664734361)
      ·
        refine ⟨2646356380985179248550771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3528475174646905664734361 2646356380985179248550771)
        ·
          refine ⟨3969534571477768872826157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646356380985179248550771 3969534571477768872826157)
          ·
            refine ⟨1488575464304163327309809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3969534571477768872826157 1488575464304163327309809)
            ·
              refine ⟨1116431598228122495482357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1488575464304163327309809 1116431598228122495482357)
              ·
                refine ⟨104665462333886483951471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1116431598228122495482357 104665462333886483951471)
                ·
                  rfl

theorem cell19_343972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_343972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_343972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_343972 prefixEnd_343972 := by exact prefixLift 343972
  have htrace : WordTrace (prefixWord ++ tailWord_343972) baseStart_343972 baseEnd_343972 := by
    simpa [prefixWord, tailWord_343972, baseEnd_343972] using wordTrace_append hprefix tailTrace_343972
  have hstable : (prefixWord ++ tailWord_343972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343972).length < 2 ^ (prefixWord ++ tailWord_343972).sum := by decide
  have hdescent : baseEnd_343972 < baseStart_343972 := by decide
  rcases family_descends (prefixWord ++ tailWord_343972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344008 : List Nat := [2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_344008 : Nat := 118140960795 + 344008 * 2 ^ 59
def prefixEnd_344008 : Nat := 4983230072969 + 3 ^ 40 * 344008 * 2
def baseEnd_344008 : Nat := 104676416587849067151373

theorem tailTrace_344008 : CollatzResearch.WordTrace tailWord_344008 prefixEnd_344008 104676416587849067151373 := by
  unfold tailWord_344008
  simp only [CollatzResearch.WordTrace]
  refine ⟨6273501268862621367016339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8364668358483495156021785 6273501268862621367016339)
  ·
    refine ⟨9410251903293932050524509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6273501268862621367016339 9410251903293932050524509)
    ·
      refine ⟨3528844463735224518946691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9410251903293932050524509 3528844463735224518946691)
      ·
        refine ⟨5293266695602836778420037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528844463735224518946691 5293266695602836778420037)
        ·
          refine ⟨992487505425531895953757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5293266695602836778420037 992487505425531895953757)
          ·
            refine ⟨372182814534574460982659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 992487505425531895953757 372182814534574460982659)
            ·
              refine ⟨558274221801861691473989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372182814534574460982659 558274221801861691473989)
              ·
                refine ⟨104676416587849067151373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558274221801861691473989 104676416587849067151373)
                ·
                  rfl

theorem cell19_344008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_344008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344008 prefixEnd_344008 := by exact prefixLift 344008
  have htrace : WordTrace (prefixWord ++ tailWord_344008) baseStart_344008 baseEnd_344008 := by
    simpa [prefixWord, tailWord_344008, baseEnd_344008] using wordTrace_append hprefix tailTrace_344008
  have hstable : (prefixWord ++ tailWord_344008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344008).length < 2 ^ (prefixWord ++ tailWord_344008).sum := by decide
  have hdescent : baseEnd_344008 < baseStart_344008 := by decide
  rcases family_descends (prefixWord ++ tailWord_344008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344010 : List Nat := [3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_344010 : Nat := 118140960795 + 344010 * 2 ^ 59
def prefixEnd_344010 : Nat := 4983230072969 + 3 ^ 40 * 344010 * 2
def baseEnd_344010 : Nat := 104677025157513655106923

theorem tailTrace_344010 : CollatzResearch.WordTrace tailWord_344010 prefixEnd_344010 104677025157513655106923 := by
  unfold tailWord_344010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136768870929499268901371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8364716989145331383736989 3136768870929499268901371)
  ·
    refine ⟨4705153306394248903352057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3136768870929499268901371 4705153306394248903352057)
    ·
      refine ⟨3528864979795686677514043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4705153306394248903352057 3528864979795686677514043)
      ·
        refine ⟨5293297469693530016271065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528864979795686677514043 5293297469693530016271065)
        ·
          refine ⟨3969973102270147512203299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5293297469693530016271065 3969973102270147512203299)
          ·
            refine ⟨5954959653405221268304949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969973102270147512203299 5954959653405221268304949)
            ·
              refine ⟨558277467506739493903589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5954959653405221268304949 558277467506739493903589)
              ·
                refine ⟨104677025157513655106923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558277467506739493903589 104677025157513655106923)
                ·
                  rfl

theorem cell19_344010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_344010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344010 prefixEnd_344010 := by exact prefixLift 344010
  have htrace : WordTrace (prefixWord ++ tailWord_344010) baseStart_344010 baseEnd_344010 := by
    simpa [prefixWord, tailWord_344010, baseEnd_344010] using wordTrace_append hprefix tailTrace_344010
  have hstable : (prefixWord ++ tailWord_344010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344010).length < 2 ^ (prefixWord ++ tailWord_344010).sum := by decide
  have hdescent : baseEnd_344010 < baseStart_344010 := by decide
  rcases family_descends (prefixWord ++ tailWord_344010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344124 : List Nat := [2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_344124 : Nat := 118140960795 + 344124 * 2 ^ 59
def prefixEnd_344124 : Nat := 4983230072969 + 3 ^ 40 * 344124 * 2
def baseEnd_344124 : Nat := 104711713628395168573279

theorem tailTrace_344124 : CollatzResearch.WordTrace tailWord_344124 prefixEnd_344124 104711713628395168573279 := by
  unfold tailWord_344124
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275616702652497272627713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8367488936869996363503617 6275616702652497272627713)
  ·
    refine ⟨4706712526989372954470785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6275616702652497272627713 4706712526989372954470785)
    ·
      refine ⟨3530034395242029715853089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4706712526989372954470785 3530034395242029715853089)
      ·
        refine ⟨2647525796431522286889817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3530034395242029715853089 2647525796431522286889817)
        ·
          refine ⟨1985644347323641715167363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2647525796431522286889817 1985644347323641715167363)
          ·
            refine ⟨2978466520985462572751045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985644347323641715167363 2978466520985462572751045)
            ·
              refine ⟨558462472684774232390821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2978466520985462572751045 558462472684774232390821)
              ·
                refine ⟨104711713628395168573279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558462472684774232390821 104711713628395168573279)
                ·
                  rfl

theorem cell19_344124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_344124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344124 prefixEnd_344124 := by exact prefixLift 344124
  have htrace : WordTrace (prefixWord ++ tailWord_344124) baseStart_344124 baseEnd_344124 := by
    simpa [prefixWord, tailWord_344124, baseEnd_344124] using wordTrace_append hprefix tailTrace_344124
  have hstable : (prefixWord ++ tailWord_344124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344124).length < 2 ^ (prefixWord ++ tailWord_344124).sum := by decide
  have hdescent : baseEnd_344124 < baseStart_344124 := by decide
  rcases family_descends (prefixWord ++ tailWord_344124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344158 : List Nat := [4, 4, 1, 1, 2, 7]
def baseStart_344158 : Nat := 118140960795 + 344158 * 2 ^ 59
def prefixEnd_344158 : Nat := 4983230072969 + 3 ^ 40 * 344158 * 2
def baseEnd_344158 : Nat := 11635784368077018201959

theorem tailTrace_344158 : CollatzResearch.WordTrace tailWord_344158 prefixEnd_344158 11635784368077018201959 := by
  unfold tailWord_344158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569059185897727293999141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8368315658121212234662085 1569059185897727293999141)
  ·
    refine ⟨294198597355823867624839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1569059185897727293999141 294198597355823867624839)
    ·
      refine ⟨441297896033735801437259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294198597355823867624839 441297896033735801437259)
      ·
        refine ⟨661946844050603702155889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441297896033735801437259 661946844050603702155889)
        ·
          refine ⟨496460133037952776616917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661946844050603702155889 496460133037952776616917)
          ·
            refine ⟨11635784368077018201959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 496460133037952776616917 11635784368077018201959)
            ·
              rfl

theorem cell19_344158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 7].length) (baseStart_344158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344158 prefixEnd_344158 := by exact prefixLift 344158
  have htrace : WordTrace (prefixWord ++ tailWord_344158) baseStart_344158 baseEnd_344158 := by
    simpa [prefixWord, tailWord_344158, baseEnd_344158] using wordTrace_append hprefix tailTrace_344158
  have hstable : (prefixWord ++ tailWord_344158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344158).length < 2 ^ (prefixWord ++ tailWord_344158).sum := by decide
  have hdescent : baseEnd_344158 < baseStart_344158 := by decide
  rcases family_descends (prefixWord ++ tailWord_344158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344162 : List Nat := [3, 3, 2, 2, 9]
def baseStart_344162 : Nat := 118140960795 + 344162 * 2 ^ 59
def prefixEnd_344162 : Nat := 4983230072969 + 3 ^ 40 * 344162 * 2
def baseEnd_344162 : Nat := 3878639868593419989953

theorem tailTrace_344162 : CollatzResearch.WordTrace tailWord_344162 prefixEnd_344162 3878639868593419989953 := by
  unfold tailWord_344162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138154844791831758784685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8368412919444884690092493 3138154844791831758784685)
  ·
    refine ⟨1176808066796936909544257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3138154844791831758784685 1176808066796936909544257)
    ·
      refine ⟨882606050097702682158193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1176808066796936909544257 882606050097702682158193)
      ·
        refine ⟨661954537573277011618645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 882606050097702682158193 661954537573277011618645)
        ·
          refine ⟨3878639868593419989953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 661954537573277011618645 3878639868593419989953)
          ·
            rfl

theorem cell19_344162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 9].length) (baseStart_344162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344162 prefixEnd_344162 := by exact prefixLift 344162
  have htrace : WordTrace (prefixWord ++ tailWord_344162) baseStart_344162 baseEnd_344162 := by
    simpa [prefixWord, tailWord_344162, baseEnd_344162] using wordTrace_append hprefix tailTrace_344162
  have hstable : (prefixWord ++ tailWord_344162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344162).length < 2 ^ (prefixWord ++ tailWord_344162).sum := by decide
  have hdescent : baseEnd_344162 < baseStart_344162 := by decide
  rcases family_descends (prefixWord ++ tailWord_344162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344295 : List Nat := [1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_344295 : Nat := 118140960795 + 344295 * 2 ^ 59
def prefixEnd_344295 : Nat := 4983230072969 + 3 ^ 40 * 344295 * 2
def baseEnd_344295 : Nat := 104763746334717438772813

theorem tailTrace_344295 : CollatzResearch.WordTrace tailWord_344295 prefixEnd_344295 104763746334717438772813 := by
  unfold tailWord_344295
  simp only [CollatzResearch.WordTrace]
  refine ⟨12557470287685490749730339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8371646858456993833153559 12557470287685490749730339)
  ·
    refine ⟨18836205431528236124595509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12557470287685490749730339 18836205431528236124595509)
    ·
      refine ⟨1765894259205772136680829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18836205431528236124595509 1765894259205772136680829)
      ·
        refine ⟨662210347202164551255311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1765894259205772136680829 662210347202164551255311)
        ·
          refine ⟨993315520803246826882967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662210347202164551255311 993315520803246826882967)
          ·
            refine ⟨1489973281204870240324451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993315520803246826882967 1489973281204870240324451)
            ·
              refine ⟨2234959921807305360486677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489973281204870240324451 2234959921807305360486677)
              ·
                refine ⟨104763746334717438772813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2234959921807305360486677 104763746334717438772813)
                ·
                  rfl

theorem cell19_344295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_344295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344295 prefixEnd_344295 := by exact prefixLift 344295
  have htrace : WordTrace (prefixWord ++ tailWord_344295) baseStart_344295 baseEnd_344295 := by
    simpa [prefixWord, tailWord_344295, baseEnd_344295] using wordTrace_append hprefix tailTrace_344295
  have hstable : (prefixWord ++ tailWord_344295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344295).length < 2 ^ (prefixWord ++ tailWord_344295).sum := by decide
  have hdescent : baseEnd_344295 < baseStart_344295 := by decide
  rcases family_descends (prefixWord ++ tailWord_344295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344352 : List Nat := [2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_344352 : Nat := 118140960795 + 344352 * 2 ^ 59
def prefixEnd_344352 : Nat := 4983230072969 + 3 ^ 40 * 344352 * 2
def baseEnd_344352 : Nat := 104781090570158195505991

theorem tailTrace_344352 : CollatzResearch.WordTrace tailWord_344352 prefixEnd_344352 104781090570158195505991 := by
  unfold tailWord_344352
  simp only [CollatzResearch.WordTrace]
  refine ⟨6279774624239494742277655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8373032832319326323036873 6279774624239494742277655)
  ·
    refine ⟨9419661936359242113416483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6279774624239494742277655 9419661936359242113416483)
    ·
      refine ⟨14129492904538863170124725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9419661936359242113416483 14129492904538863170124725)
      ·
        refine ⟨1324639959800518422199193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14129492904538863170124725 1324639959800518422199193)
        ·
          refine ⟨993479969850388816649395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324639959800518422199193 993479969850388816649395)
          ·
            refine ⟨1490219954775583224974093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993479969850388816649395 1490219954775583224974093)
            ·
              refine ⟨558832483040843709365285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1490219954775583224974093 558832483040843709365285)
              ·
                refine ⟨104781090570158195505991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558832483040843709365285 104781090570158195505991)
                ·
                  rfl

theorem cell19_344352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_344352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344352 prefixEnd_344352 := by exact prefixLift 344352
  have htrace : WordTrace (prefixWord ++ tailWord_344352) baseStart_344352 baseEnd_344352 := by
    simpa [prefixWord, tailWord_344352, baseEnd_344352] using wordTrace_append hprefix tailTrace_344352
  have hstable : (prefixWord ++ tailWord_344352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344352).length < 2 ^ (prefixWord ++ tailWord_344352).sum := by decide
  have hdescent : baseEnd_344352 < baseStart_344352 := by decide
  rcases family_descends (prefixWord ++ tailWord_344352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344369 : List Nat := [1, 2, 2, 3, 4, 1, 3, 3]
def baseStart_344369 : Nat := 118140960795 + 344369 * 2 ^ 59
def prefixEnd_344369 : Nat := 4983230072969 + 3 ^ 40 * 344369 * 2
def baseEnd_344369 : Nat := 104786263412307193128167

theorem tailTrace_344369 : CollatzResearch.WordTrace tailWord_344369 prefixEnd_344369 104786263412307193128167 := by
  unfold tailWord_344369
  simp only [CollatzResearch.WordTrace]
  refine ⟨12560169289417401387924161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8373446192944934258616107 12560169289417401387924161)
  ·
    refine ⟨9420126967063051040943121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12560169289417401387924161 9420126967063051040943121)
    ·
      refine ⟨7065095225297288280707341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9420126967063051040943121 7065095225297288280707341)
      ·
        refine ⟨2649410709486483105265253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7065095225297288280707341 2649410709486483105265253)
        ·
          refine ⟨496764508028715582237235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2649410709486483105265253 496764508028715582237235)
          ·
            refine ⟨745146762043073373355853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496764508028715582237235 745146762043073373355853)
            ·
              refine ⟨279430035766152515008445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 745146762043073373355853 279430035766152515008445)
              ·
                refine ⟨104786263412307193128167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279430035766152515008445 104786263412307193128167)
                ·
                  rfl

theorem cell19_344369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_344369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344369 prefixEnd_344369 := by exact prefixLift 344369
  have htrace : WordTrace (prefixWord ++ tailWord_344369) baseStart_344369 baseEnd_344369 := by
    simpa [prefixWord, tailWord_344369, baseEnd_344369] using wordTrace_append hprefix tailTrace_344369
  have hstable : (prefixWord ++ tailWord_344369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344369).length < 2 ^ (prefixWord ++ tailWord_344369).sum := by decide
  have hdescent : baseEnd_344369 < baseStart_344369 := by decide
  rcases family_descends (prefixWord ++ tailWord_344369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344371 : List Nat := [1, 1, 1, 2, 5, 1, 5, 3]
def baseStart_344371 : Nat := 118140960795 + 344371 * 2 ^ 59
def prefixEnd_344371 : Nat := 4983230072969 + 3 ^ 40 * 344371 * 2
def baseEnd_344371 : Nat := 104786871981971781083717

theorem tailTrace_344371 : CollatzResearch.WordTrace tailWord_344371 prefixEnd_344371 104786871981971781083717 := by
  unfold tailWord_344371
  simp only [CollatzResearch.WordTrace]
  refine ⟨12560242235410155729496967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8373494823606770486331311 12560242235410155729496967)
  ·
    refine ⟨18840363353115233594245451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12560242235410155729496967 18840363353115233594245451)
    ·
      refine ⟨28260545029672850391368177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18840363353115233594245451 28260545029672850391368177)
      ·
        refine ⟨21195408772254637793526133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28260545029672850391368177 21195408772254637793526133)
        ·
          refine ⟨1987069572398872293143075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21195408772254637793526133 1987069572398872293143075)
          ·
            refine ⟨2980604358598308439714613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987069572398872293143075 2980604358598308439714613)
            ·
              refine ⟨279431658618591416223245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2980604358598308439714613 279431658618591416223245)
              ·
                refine ⟨104786871981971781083717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279431658618591416223245 104786871981971781083717)
                ·
                  rfl

theorem cell19_344371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_344371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344371 prefixEnd_344371 := by exact prefixLift 344371
  have htrace : WordTrace (prefixWord ++ tailWord_344371) baseStart_344371 baseEnd_344371 := by
    simpa [prefixWord, tailWord_344371, baseEnd_344371] using wordTrace_append hprefix tailTrace_344371
  have hstable : (prefixWord ++ tailWord_344371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344371).length < 2 ^ (prefixWord ++ tailWord_344371).sum := by decide
  have hdescent : baseEnd_344371 < baseStart_344371 := by decide
  rcases family_descends (prefixWord ++ tailWord_344371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344388 : List Nat := [2, 3, 4, 1, 2, 1, 6]
def baseStart_344388 : Nat := 118140960795 + 344388 * 2 ^ 59
def prefixEnd_344388 : Nat := 4983230072969 + 3 ^ 40 * 344388 * 2
def baseEnd_344388 : Nat := 34930681608040259568631

theorem tailTrace_344388 : CollatzResearch.WordTrace tailWord_344388 prefixEnd_344388 34930681608040259568631 := by
  unfold tailWord_344388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280431138174283816432909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8373908184232378421910545 6280431138174283816432909)
  ·
    refine ⟨2355161676815356431162341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6280431138174283816432909 2355161676815356431162341)
    ·
      refine ⟨441592814402879330842939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2355161676815356431162341 441592814402879330842939)
      ·
        refine ⟨662389221604318996264409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441592814402879330842939 662389221604318996264409)
        ·
          refine ⟨496791916203239247198307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662389221604318996264409 496791916203239247198307)
          ·
            refine ⟨745187874304858870797461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496791916203239247198307 745187874304858870797461)
            ·
              refine ⟨34930681608040259568631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 745187874304858870797461 34930681608040259568631)
              ·
                rfl

theorem cell19_344388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_344388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344388 prefixEnd_344388 := by exact prefixLift 344388
  have htrace : WordTrace (prefixWord ++ tailWord_344388) baseStart_344388 baseEnd_344388 := by
    simpa [prefixWord, tailWord_344388, baseEnd_344388] using wordTrace_append hprefix tailTrace_344388
  have hstable : (prefixWord ++ tailWord_344388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344388).length < 2 ^ (prefixWord ++ tailWord_344388).sum := by decide
  have hdescent : baseEnd_344388 < baseStart_344388 := by decide
  rcases family_descends (prefixWord ++ tailWord_344388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344426 : List Nat := [3, 1, 3, 3, 1, 1, 4, 3]
def baseStart_344426 : Nat := 118140960795 + 344426 * 2 ^ 59
def prefixEnd_344426 : Nat := 4983230072969 + 3 ^ 40 * 344426 * 2
def baseEnd_344426 : Nat := 104803607647747949861345

theorem tailTrace_344426 : CollatzResearch.WordTrace tailWord_344426 prefixEnd_344426 104803607647747949861345 := by
  unfold tailWord_344426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3140562062552725030687283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8374832166807266748499421 3140562062552725030687283)
  ·
    refine ⟨4710843093829087546030925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3140562062552725030687283 4710843093829087546030925)
    ·
      refine ⟨1766566160185907829761597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4710843093829087546030925 1766566160185907829761597)
      ·
        refine ⟨662462310069715436160599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1766566160185907829761597 662462310069715436160599)
        ·
          refine ⟨993693465104573154240899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662462310069715436160599 993693465104573154240899)
          ·
            refine ⟨1490540197656859731361349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993693465104573154240899 1490540197656859731361349)
            ·
              refine ⟨279476287060661199630253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1490540197656859731361349 279476287060661199630253)
              ·
                refine ⟨104803607647747949861345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279476287060661199630253 104803607647747949861345)
                ·
                  rfl

theorem cell19_344426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_344426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344426 prefixEnd_344426 := by exact prefixLift 344426
  have htrace : WordTrace (prefixWord ++ tailWord_344426) baseStart_344426 baseEnd_344426 := by
    simpa [prefixWord, tailWord_344426, baseEnd_344426] using wordTrace_append hprefix tailTrace_344426
  have hstable : (prefixWord ++ tailWord_344426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344426).length < 2 ^ (prefixWord ++ tailWord_344426).sum := by decide
  have hdescent : baseEnd_344426 < baseStart_344426 := by decide
  rcases family_descends (prefixWord ++ tailWord_344426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344428 : List Nat := [2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_344428 : Nat := 118140960795 + 344428 * 2 ^ 59
def prefixEnd_344428 : Nat := 4983230072969 + 3 ^ 40 * 344428 * 2
def baseEnd_344428 : Nat := 104804216217412537816895

theorem tailTrace_344428 : CollatzResearch.WordTrace tailWord_344428 prefixEnd_344428 104804216217412537816895 := by
  unfold tailWord_344428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281160598101827232160969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8374880797469102976214625 6281160598101827232160969)
  ·
    refine ⟨4710870448576370424120727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6281160598101827232160969 4710870448576370424120727)
    ·
      refine ⟨7066305672864555636181091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4710870448576370424120727 7066305672864555636181091)
      ·
        refine ⟨10599458509296833454271637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7066305672864555636181091 10599458509296833454271637)
        ·
          refine ⟨496849617623289068168983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10599458509296833454271637 496849617623289068168983)
          ·
            refine ⟨745274426434933602253475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496849617623289068168983 745274426434933602253475)
            ·
              refine ⟨1117911639652400403380213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745274426434933602253475 1117911639652400403380213)
              ·
                refine ⟨104804216217412537816895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1117911639652400403380213 104804216217412537816895)
                ·
                  rfl

theorem cell19_344428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_344428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344428 prefixEnd_344428 := by exact prefixLift 344428
  have htrace : WordTrace (prefixWord ++ tailWord_344428) baseStart_344428 baseEnd_344428 := by
    simpa [prefixWord, tailWord_344428, baseEnd_344428] using wordTrace_append hprefix tailTrace_344428
  have hstable : (prefixWord ++ tailWord_344428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344428).length < 2 ^ (prefixWord ++ tailWord_344428).sum := by decide
  have hdescent : baseEnd_344428 < baseStart_344428 := by decide
  rcases family_descends (prefixWord ++ tailWord_344428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344500 : List Nat := [2, 5, 2, 2, 2, 6]
def baseStart_344500 : Nat := 118140960795 + 344500 * 2 ^ 59
def prefixEnd_344500 : Nat := 4983230072969 + 3 ^ 40 * 344500 * 2
def baseEnd_344500 : Nat := 11647347191704189357411

theorem tailTrace_344500 : CollatzResearch.WordTrace tailWord_344500 prefixEnd_344500 11647347191704189357411 := by
  unfold tailWord_344500
  simp only [CollatzResearch.WordTrace]
  refine ⟨6282473625971405380471477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8376631501295207173961969 6282473625971405380471477)
  ·
    refine ⟨588981902434819254419201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6282473625971405380471477 588981902434819254419201)
    ·
      refine ⟨441736426826114440814401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 588981902434819254419201 441736426826114440814401)
      ·
        refine ⟨331302320119585830610801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441736426826114440814401 331302320119585830610801)
        ·
          refine ⟨248476740089689372958101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331302320119585830610801 248476740089689372958101)
          ·
            refine ⟨11647347191704189357411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248476740089689372958101 11647347191704189357411)
            ·
              rfl

theorem cell19_344500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 6].length) (baseStart_344500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344500 prefixEnd_344500 := by exact prefixLift 344500
  have htrace : WordTrace (prefixWord ++ tailWord_344500) baseStart_344500 baseEnd_344500 := by
    simpa [prefixWord, tailWord_344500, baseEnd_344500] using wordTrace_append hprefix tailTrace_344500
  have hstable : (prefixWord ++ tailWord_344500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344500).length < 2 ^ (prefixWord ++ tailWord_344500).sum := by decide
  have hdescent : baseEnd_344500 < baseStart_344500 := by decide
  rcases family_descends (prefixWord ++ tailWord_344500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344618 : List Nat := [3, 1, 4, 1, 1, 4, 5]
def baseStart_344618 : Nat := 118140960795 + 344618 * 2 ^ 59
def prefixEnd_344618 : Nat := 4983230072969 + 3 ^ 40 * 344618 * 2
def baseEnd_344618 : Nat := 34954010111849464531385

theorem tailTrace_344618 : CollatzResearch.WordTrace tailWord_344618 prefixEnd_344618 34954010111849464531385 := by
  unfold tailWord_344618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142312766378829228434627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8379500710343544609159005 3142312766378829228434627)
  ·
    refine ⟨4713469149568243842651941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3142312766378829228434627 4713469149568243842651941)
    ·
      refine ⟨883775465544045720497239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4713469149568243842651941 883775465544045720497239)
      ·
        refine ⟨1325663198316068580745859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883775465544045720497239 1325663198316068580745859)
        ·
          refine ⟨1988494797474102871118789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325663198316068580745859 1988494797474102871118789)
          ·
            refine ⟨372842774526394288334773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1988494797474102871118789 372842774526394288334773)
            ·
              refine ⟨34954010111849464531385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 372842774526394288334773 34954010111849464531385)
              ·
                rfl

theorem cell19_344618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_344618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344618 prefixEnd_344618 := by exact prefixLift 344618
  have htrace : WordTrace (prefixWord ++ tailWord_344618) baseStart_344618 baseEnd_344618 := by
    simpa [prefixWord, tailWord_344618, baseEnd_344618] using wordTrace_append hprefix tailTrace_344618
  have hstable : (prefixWord ++ tailWord_344618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344618).length < 2 ^ (prefixWord ++ tailWord_344618).sum := by decide
  have hdescent : baseEnd_344618 < baseStart_344618 := by decide
  rcases family_descends (prefixWord ++ tailWord_344618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344637 : List Nat := [1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_344637 : Nat := 118140960795 + 344637 * 2 ^ 59
def prefixEnd_344637 : Nat := 4983230072969 + 3 ^ 40 * 344637 * 2
def baseEnd_344637 : Nat := 104867811747361979171881

theorem tailTrace_344637 : CollatzResearch.WordTrace tailWord_344637 prefixEnd_344637 104867811747361979171881 := by
  unfold tailWord_344637
  simp only [CollatzResearch.WordTrace]
  refine ⟨12569944052446483158680165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8379962701630988772453443 12569944052446483158680165)
  ·
    refine ⟨2356864509833715592252531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12569944052446483158680165 2356864509833715592252531)
    ·
      refine ⟨3535296764750573388378797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2356864509833715592252531 3535296764750573388378797)
      ·
        refine ⟨1325736286781465020642049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3535296764750573388378797 1325736286781465020642049)
        ·
          refine ⟨994302215086098765481537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1325736286781465020642049 994302215086098765481537)
          ·
            refine ⟨745726661314574074111153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994302215086098765481537 745726661314574074111153)
            ·
              refine ⟨559294995985930555583365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745726661314574074111153 559294995985930555583365)
              ·
                refine ⟨104867811747361979171881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559294995985930555583365 104867811747361979171881)
                ·
                  rfl

theorem cell19_344637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_344637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344637 prefixEnd_344637 := by exact prefixLift 344637
  have htrace : WordTrace (prefixWord ++ tailWord_344637) baseStart_344637 baseEnd_344637 := by
    simpa [prefixWord, tailWord_344637, baseEnd_344637] using wordTrace_append hprefix tailTrace_344637
  have hstable : (prefixWord ++ tailWord_344637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344637).length < 2 ^ (prefixWord ++ tailWord_344637).sum := by decide
  have hdescent : baseEnd_344637 < baseStart_344637 := by decide
  rcases family_descends (prefixWord ++ tailWord_344637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344639 : List Nat := [1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_344639 : Nat := 118140960795 + 344639 * 2 ^ 59
def prefixEnd_344639 : Nat := 4983230072969 + 3 ^ 40 * 344639 * 2
def baseEnd_344639 : Nat := 104868420317026567127431

theorem tailTrace_344639 : CollatzResearch.WordTrace tailWord_344639 prefixEnd_344639 104868420317026567127431 := by
  unfold tailWord_344639
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570016998439237500252971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8380011332292825000168647 12570016998439237500252971)
  ·
    refine ⟨18855025497658856250379457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12570016998439237500252971 18855025497658856250379457)
    ·
      refine ⟨14141269123244142187784593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18855025497658856250379457 14141269123244142187784593)
      ·
        refine ⟨10605951842433106640838445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14141269123244142187784593 10605951842433106640838445)
        ·
          refine ⟨3977231940912414990314417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10605951842433106640838445 3977231940912414990314417)
          ·
            refine ⟨2982923955684311242735813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3977231940912414990314417 2982923955684311242735813)
            ·
              refine ⟨559298241690808358012965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2982923955684311242735813 559298241690808358012965)
              ·
                refine ⟨104868420317026567127431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559298241690808358012965 104868420317026567127431)
                ·
                  rfl

theorem cell19_344639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_344639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344639 prefixEnd_344639 := by exact prefixLift 344639
  have htrace : WordTrace (prefixWord ++ tailWord_344639) baseStart_344639 baseEnd_344639 := by
    simpa [prefixWord, tailWord_344639, baseEnd_344639] using wordTrace_append hprefix tailTrace_344639
  have hstable : (prefixWord ++ tailWord_344639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344639).length < 2 ^ (prefixWord ++ tailWord_344639).sum := by decide
  have hdescent : baseEnd_344639 < baseStart_344639 := by decide
  rcases family_descends (prefixWord ++ tailWord_344639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344658 : List Nat := [3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_344658 : Nat := 118140960795 + 344658 * 2 ^ 59
def prefixEnd_344658 : Nat := 4983230072969 + 3 ^ 40 * 344658 * 2
def baseEnd_344658 : Nat := 104874201728840152705157

theorem tailTrace_344658 : CollatzResearch.WordTrace tailWord_344658 prefixEnd_344658 104874201728840152705157 := by
  unfold tailWord_344658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142677496342600936298657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8380473323580269163463085 3142677496342600936298657)
  ·
    refine ⟨2357008122256950702223993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3142677496342600936298657 2357008122256950702223993)
    ·
      refine ⟨1767756091692713026667995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2357008122256950702223993 1767756091692713026667995)
      ·
        refine ⟨2651634137539069540001993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767756091692713026667995 2651634137539069540001993)
        ·
          refine ⟨1988725603154302155001495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2651634137539069540001993 1988725603154302155001495)
          ·
            refine ⟨2983088404731453232502243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988725603154302155001495 2983088404731453232502243)
            ·
              refine ⟨4474632607097179848753365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983088404731453232502243 4474632607097179848753365)
              ·
                refine ⟨104874201728840152705157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4474632607097179848753365 104874201728840152705157)
                ·
                  rfl

theorem cell19_344658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_344658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344658 prefixEnd_344658 := by exact prefixLift 344658
  have htrace : WordTrace (prefixWord ++ tailWord_344658) baseStart_344658 baseEnd_344658 := by
    simpa [prefixWord, tailWord_344658, baseEnd_344658] using wordTrace_append hprefix tailTrace_344658
  have hstable : (prefixWord ++ tailWord_344658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344658).length < 2 ^ (prefixWord ++ tailWord_344658).sum := by decide
  have hdescent : baseEnd_344658 < baseStart_344658 := by decide
  rcases family_descends (prefixWord ++ tailWord_344658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344677 : List Nat := [1, 3, 1, 3, 4, 7]
def baseStart_344677 : Nat := 118140960795 + 344677 * 2 ^ 59
def prefixEnd_344677 : Nat := 4983230072969 + 3 ^ 40 * 344677 * 2
def baseEnd_344677 : Nat := 11653331460072637586987

theorem tailTrace_344677 : CollatzResearch.WordTrace tailWord_344677 prefixEnd_344677 11653331460072637586987 := by
  unfold tailWord_344677
  simp only [CollatzResearch.WordTrace]
  refine ⟨12571402972301569990136285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8380935314867713326757523 12571402972301569990136285)
  ·
    refine ⟨4714276114613088746301107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12571402972301569990136285 4714276114613088746301107)
    ·
      refine ⟨7071414171919633119451661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4714276114613088746301107 7071414171919633119451661)
      ·
        refine ⟨2651780314469862419794373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7071414171919633119451661 2651780314469862419794373)
        ·
          refine ⟨497208808963099203711445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2651780314469862419794373 497208808963099203711445)
          ·
            refine ⟨11653331460072637586987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 497208808963099203711445 11653331460072637586987)
            ·
              rfl

theorem cell19_344677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 7].length) (baseStart_344677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344677 prefixEnd_344677 := by exact prefixLift 344677
  have htrace : WordTrace (prefixWord ++ tailWord_344677) baseStart_344677 baseEnd_344677 := by
    simpa [prefixWord, tailWord_344677, baseEnd_344677] using wordTrace_append hprefix tailTrace_344677
  have hstable : (prefixWord ++ tailWord_344677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344677).length < 2 ^ (prefixWord ++ tailWord_344677).sum := by decide
  have hdescent : baseEnd_344677 < baseStart_344677 := by decide
  rcases family_descends (prefixWord ++ tailWord_344677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344791 : List Nat := [1, 1, 3, 2, 1, 6, 5]
def baseStart_344791 : Nat := 118140960795 + 344791 * 2 ^ 59
def prefixEnd_344791 : Nat := 4983230072969 + 3 ^ 40 * 344791 * 2
def baseEnd_344791 : Nat := 34971557203845083916413

theorem tailTrace_344791 : CollatzResearch.WordTrace tailWord_344791 prefixEnd_344791 34971557203845083916413 := by
  unfold tailWord_344791
  simp only [CollatzResearch.WordTrace]
  refine ⟨12575560893888567459786227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8383707262592378306524151 12575560893888567459786227)
  ·
    refine ⟨18863341340832851189679341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12575560893888567459786227 18863341340832851189679341)
    ·
      refine ⟨7073753002812319196129753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18863341340832851189679341 7073753002812319196129753)
      ·
        refine ⟨5305314752109239397097315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7073753002812319196129753 5305314752109239397097315)
        ·
          refine ⟨7957972128163859095645973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5305314752109239397097315 7957972128163859095645973)
          ·
            refine ⟨373029943507680895108405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7957972128163859095645973 373029943507680895108405)
            ·
              refine ⟨34971557203845083916413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373029943507680895108405 34971557203845083916413)
              ·
                rfl

theorem cell19_344791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_344791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344791 prefixEnd_344791 := by exact prefixLift 344791
  have htrace : WordTrace (prefixWord ++ tailWord_344791) baseStart_344791 baseEnd_344791 := by
    simpa [prefixWord, tailWord_344791, baseEnd_344791] using wordTrace_append hprefix tailTrace_344791
  have hstable : (prefixWord ++ tailWord_344791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344791).length < 2 ^ (prefixWord ++ tailWord_344791).sum := by decide
  have hdescent : baseEnd_344791 < baseStart_344791 := by decide
  rcases family_descends (prefixWord ++ tailWord_344791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344808 : List Nat := [2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_344808 : Nat := 118140960795 + 344808 * 2 ^ 59
def prefixEnd_344808 : Nat := 4983230072969 + 3 ^ 40 * 344808 * 2
def baseEnd_344808 : Nat := 104919844453684249371415

theorem tailTrace_344808 : CollatzResearch.WordTrace tailWord_344808 prefixEnd_344808 104919844453684249371415 := by
  unfold tailWord_344808
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288090467413489681577539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8384120623217986242103385 6288090467413489681577539)
  ·
    refine ⟨9432135701120234522366309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6288090467413489681577539 9432135701120234522366309)
    ·
      refine ⟨1768525443960043972943683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9432135701120234522366309 1768525443960043972943683)
      ·
        refine ⟨2652788165940065959415525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768525443960043972943683 2652788165940065959415525)
        ·
          refine ⟨497397781113762367390411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2652788165940065959415525 497397781113762367390411)
          ·
            refine ⟨746096671670643551085617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497397781113762367390411 746096671670643551085617)
            ·
              refine ⟨559572503752982663314213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746096671670643551085617 559572503752982663314213)
              ·
                refine ⟨104919844453684249371415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559572503752982663314213 104919844453684249371415)
                ·
                  rfl

theorem cell19_344808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_344808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344808 prefixEnd_344808 := by exact prefixLift 344808
  have htrace : WordTrace (prefixWord ++ tailWord_344808) baseStart_344808 baseEnd_344808 := by
    simpa [prefixWord, tailWord_344808, baseEnd_344808] using wordTrace_append hprefix tailTrace_344808
  have hstable : (prefixWord ++ tailWord_344808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344808).length < 2 ^ (prefixWord ++ tailWord_344808).sum := by decide
  have hdescent : baseEnd_344808 < baseStart_344808 := by decide
  rcases family_descends (prefixWord ++ tailWord_344808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344861 : List Nat := [1, 4, 2, 4, 2, 1, 1, 4]
def baseStart_344861 : Nat := 118140960795 + 344861 * 2 ^ 59
def prefixEnd_344861 : Nat := 4983230072969 + 3 ^ 40 * 344861 * 2
def baseEnd_344861 : Nat := 104935971549795830193493

theorem tailTrace_344861 : CollatzResearch.WordTrace tailWord_344861 prefixEnd_344861 104935971549795830193493 := by
  unfold tailWord_344861
  simp only [CollatzResearch.WordTrace]
  refine ⟨12578114003634969414834437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8385409335756646276556291 12578114003634969414834437)
  ·
    refine ⟨2358396375681556765281457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12578114003634969414834437 2358396375681556765281457)
    ·
      refine ⟨1768797281761167573961093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2358396375681556765281457 1768797281761167573961093)
      ·
        refine ⟨331649490330218920117705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1768797281761167573961093 331649490330218920117705)
        ·
          refine ⟨248737117747664190088279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331649490330218920117705 248737117747664190088279)
          ·
            refine ⟨373105676621496285132419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248737117747664190088279 373105676621496285132419)
            ·
              refine ⟨559658514932244427698629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373105676621496285132419 559658514932244427698629)
              ·
                refine ⟨104935971549795830193493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559658514932244427698629 104935971549795830193493)
                ·
                  rfl

theorem cell19_344861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 4].length) (baseStart_344861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344861 prefixEnd_344861 := by exact prefixLift 344861
  have htrace : WordTrace (prefixWord ++ tailWord_344861) baseStart_344861 baseEnd_344861 := by
    simpa [prefixWord, tailWord_344861, baseEnd_344861] using wordTrace_append hprefix tailTrace_344861
  have hstable : (prefixWord ++ tailWord_344861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344861).length < 2 ^ (prefixWord ++ tailWord_344861).sum := by decide
  have hdescent : baseEnd_344861 < baseStart_344861 := by decide
  rcases family_descends (prefixWord ++ tailWord_344861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344958 : List Nat := [4, 2, 3, 1, 2, 2, 5]
def baseStart_344958 : Nat := 118140960795 + 344958 * 2 ^ 59
def prefixEnd_344958 : Nat := 4983230072969 + 3 ^ 40 * 344958 * 2
def baseEnd_344958 : Nat := 34988495726176115345891

theorem tailTrace_344958 : CollatzResearch.WordTrace tailWord_344958 prefixEnd_344958 34988495726176115345891 := by
  unfold tailWord_344958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572706485535444372639441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8387767922855703320743685 1572706485535444372639441)
  ·
    refine ⟨1179529864151583279479581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1572706485535444372639441 1179529864151583279479581)
    ·
      refine ⟨442323699056843729804843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1179529864151583279479581 442323699056843729804843)
      ·
        refine ⟨663485548585265594707265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442323699056843729804843 663485548585265594707265)
        ·
          refine ⟨497614161438949196030449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663485548585265594707265 497614161438949196030449)
          ·
            refine ⟨373210621079211897022837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497614161438949196030449 373210621079211897022837)
            ·
              refine ⟨34988495726176115345891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373210621079211897022837 34988495726176115345891)
              ·
                rfl

theorem cell19_344958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_344958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344958 prefixEnd_344958 := by exact prefixLift 344958
  have htrace : WordTrace (prefixWord ++ tailWord_344958) baseStart_344958 baseEnd_344958 := by
    simpa [prefixWord, tailWord_344958, baseEnd_344958] using wordTrace_append hprefix tailTrace_344958
  have hstable : (prefixWord ++ tailWord_344958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344958).length < 2 ^ (prefixWord ++ tailWord_344958).sum := by decide
  have hdescent : baseEnd_344958 < baseStart_344958 := by decide
  rcases family_descends (prefixWord ++ tailWord_344958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344981 : List Nat := [1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_344981 : Nat := 118140960795 + 344981 * 2 ^ 59
def prefixEnd_344981 : Nat := 4983230072969 + 3 ^ 40 * 344981 * 2
def baseEnd_344981 : Nat := 104972485729671107526499

theorem tailTrace_344981 : CollatzResearch.WordTrace tailWord_344981 prefixEnd_344981 104972485729671107526499 := by
  unfold tailWord_344981
  simp only [CollatzResearch.WordTrace]
  refine ⟨12582490763200229909202797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8388327175466819939468531 12582490763200229909202797)
  ·
    refine ⟨4718434036200086215951049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12582490763200229909202797 4718434036200086215951049)
    ·
      refine ⟨3538825527150064661963287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4718434036200086215951049 3538825527150064661963287)
      ·
        refine ⟨5308238290725096992944931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3538825527150064661963287 5308238290725096992944931)
        ·
          refine ⟨7962357436087645489417397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308238290725096992944931 7962357436087645489417397)
          ·
            refine ⟨746471009633216764632881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7962357436087645489417397 746471009633216764632881)
            ·
              refine ⟨559853257224912573474661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746471009633216764632881 559853257224912573474661)
              ·
                refine ⟨104972485729671107526499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559853257224912573474661 104972485729671107526499)
                ·
                  rfl

theorem cell19_344981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_344981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_344981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_344981 prefixEnd_344981 := by exact prefixLift 344981
  have htrace : WordTrace (prefixWord ++ tailWord_344981) baseStart_344981 baseEnd_344981 := by
    simpa [prefixWord, tailWord_344981, baseEnd_344981] using wordTrace_append hprefix tailTrace_344981
  have hstable : (prefixWord ++ tailWord_344981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344981).length < 2 ^ (prefixWord ++ tailWord_344981).sum := by decide
  have hdescent : baseEnd_344981 < baseStart_344981 := by decide
  rcases family_descends (prefixWord ++ tailWord_344981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345021 : List Nat := [1, 4, 1, 2, 11]
def baseStart_345021 : Nat := 118140960795 + 345021 * 2 ^ 59
def prefixEnd_345021 : Nat := 4983230072969 + 3 ^ 40 * 345021 * 2
def baseEnd_345021 : Nat := 3888320634183809875463

theorem tailTrace_345021 : CollatzResearch.WordTrace tailWord_345021 prefixEnd_345021 3888320634183809875463 := by
  unfold tailWord_345021
  simp only [CollatzResearch.WordTrace]
  refine ⟨12583949683055316740658917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8389299788703544493772611 12583949683055316740658917)
  ·
    refine ⟨2359490565572871888873547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12583949683055316740658917 2359490565572871888873547)
    ·
      refine ⟨3539235848359307833310321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2359490565572871888873547 3539235848359307833310321)
      ·
        refine ⟨2654426886269480874982741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3539235848359307833310321 2654426886269480874982741)
        ·
          refine ⟨3888320634183809875463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2654426886269480874982741 3888320634183809875463)
          ·
            rfl

theorem cell19_345021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 11].length) (baseStart_345021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345021 prefixEnd_345021 := by exact prefixLift 345021
  have htrace : WordTrace (prefixWord ++ tailWord_345021) baseStart_345021 baseEnd_345021 := by
    simpa [prefixWord, tailWord_345021, baseEnd_345021] using wordTrace_append hprefix tailTrace_345021
  have hstable : (prefixWord ++ tailWord_345021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345021).length < 2 ^ (prefixWord ++ tailWord_345021).sum := by decide
  have hdescent : baseEnd_345021 < baseStart_345021 := by decide
  rcases family_descends (prefixWord ++ tailWord_345021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345038 : List Nat := [4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_345038 : Nat := 118140960795 + 345038 * 2 ^ 59
def prefixEnd_345038 : Nat := 4983230072969 + 3 ^ 40 * 345038 * 2
def baseEnd_345038 : Nat := 104989829965111864259677

theorem tailTrace_345038 : CollatzResearch.WordTrace tailWord_345038 prefixEnd_345038 104989829965111864259677 := by
  unfold tailWord_345038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573071215499216080503471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8389713149329152429351845 1573071215499216080503471)
  ·
    refine ⟨2359606823248824120755207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1573071215499216080503471 2359606823248824120755207)
    ·
      refine ⟨3539410234873236181132811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2359606823248824120755207 3539410234873236181132811)
      ·
        refine ⟨5309115352309854271699217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539410234873236181132811 5309115352309854271699217)
        ·
          refine ⟨3981836514232390703774413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5309115352309854271699217 3981836514232390703774413)
          ·
            refine ⟨1493188692837146513915405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3981836514232390703774413 1493188692837146513915405)
            ·
              refine ⟨559945759813929942718277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493188692837146513915405 559945759813929942718277)
              ·
                refine ⟨104989829965111864259677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 559945759813929942718277 104989829965111864259677)
                ·
                  rfl

theorem cell19_345038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_345038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345038 prefixEnd_345038 := by exact prefixLift 345038
  have htrace : WordTrace (prefixWord ++ tailWord_345038) baseStart_345038 baseEnd_345038 := by
    simpa [prefixWord, tailWord_345038, baseEnd_345038] using wordTrace_append hprefix tailTrace_345038
  have hstable : (prefixWord ++ tailWord_345038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345038).length < 2 ^ (prefixWord ++ tailWord_345038).sum := by decide
  have hdescent : baseEnd_345038 < baseStart_345038 := by decide
  rcases family_descends (prefixWord ++ tailWord_345038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345055 : List Nat := [1, 1, 2, 3, 5, 1, 3, 3]
def baseStart_345055 : Nat := 118140960795 + 345055 * 2 ^ 59
def prefixEnd_345055 : Nat := 4983230072969 + 3 ^ 40 * 345055 * 2
def baseEnd_345055 : Nat := 104995002807260861881853

theorem tailTrace_345055 : CollatzResearch.WordTrace tailWord_345055 prefixEnd_345055 104995002807260861881853 := by
  unfold tailWord_345055
  simp only [CollatzResearch.WordTrace]
  refine ⟨12585189764932140547396619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8390126509954760364931079 12585189764932140547396619)
  ·
    refine ⟨18877784647398210821094929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12585189764932140547396619 18877784647398210821094929)
    ·
      refine ⟨14158338485548658115821197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18877784647398210821094929 14158338485548658115821197)
      ·
        refine ⟨5309376932080746793432949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14158338485548658115821197 5309376932080746793432949)
        ·
          refine ⟨497754087382570011884339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5309376932080746793432949 497754087382570011884339)
          ·
            refine ⟨746631131073855017826509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497754087382570011884339 746631131073855017826509)
            ·
              refine ⟨279986674152695631684941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 746631131073855017826509 279986674152695631684941)
              ·
                refine ⟨104995002807260861881853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279986674152695631684941 104995002807260861881853)
                ·
                  rfl

theorem cell19_345055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_345055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345055 prefixEnd_345055 := by exact prefixLift 345055
  have htrace : WordTrace (prefixWord ++ tailWord_345055) baseStart_345055 baseEnd_345055 := by
    simpa [prefixWord, tailWord_345055, baseEnd_345055] using wordTrace_append hprefix tailTrace_345055
  have hstable : (prefixWord ++ tailWord_345055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345055).length < 2 ^ (prefixWord ++ tailWord_345055).sum := by decide
  have hdescent : baseEnd_345055 < baseStart_345055 := by decide
  rcases family_descends (prefixWord ++ tailWord_345055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345074 : List Nat := [3, 2, 1, 5, 1, 1, 6]
def baseStart_345074 : Nat := 118140960795 + 345074 * 2 ^ 59
def prefixEnd_345074 : Nat := 4983230072969 + 3 ^ 40 * 345074 * 2
def baseEnd_345074 : Nat := 35000261406358149153193

theorem tailTrace_345074 : CollatzResearch.WordTrace tailWord_345074 prefixEnd_345074 35000261406358149153193 := by
  unfold tailWord_345074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146470687965826698084569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8390588501242204528225517 3146470687965826698084569)
  ·
    refine ⟨2359853015974370023563427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3146470687965826698084569 2359853015974370023563427)
    ·
      refine ⟨3539779523961555035345141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2359853015974370023563427 3539779523961555035345141)
      ·
        refine ⟨331854330371395784563607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3539779523961555035345141 331854330371395784563607)
        ·
          refine ⟨497781495557093676845411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331854330371395784563607 497781495557093676845411)
          ·
            refine ⟨746672243335640515268117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497781495557093676845411 746672243335640515268117)
            ·
              refine ⟨35000261406358149153193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 746672243335640515268117 35000261406358149153193)
              ·
                rfl

theorem cell19_345074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_345074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345074 prefixEnd_345074 := by exact prefixLift 345074
  have htrace : WordTrace (prefixWord ++ tailWord_345074) baseStart_345074 baseEnd_345074 := by
    simpa [prefixWord, tailWord_345074, baseEnd_345074] using wordTrace_append hprefix tailTrace_345074
  have hstable : (prefixWord ++ tailWord_345074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345074).length < 2 ^ (prefixWord ++ tailWord_345074).sum := by decide
  have hdescent : baseEnd_345074 < baseStart_345074 := by decide
  rcases family_descends (prefixWord ++ tailWord_345074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345106 : List Nat := [3, 2, 5, 1, 1, 2, 2, 3]
def baseStart_345106 : Nat := 118140960795 + 345106 * 2 ^ 59
def prefixEnd_345106 : Nat := 4983230072969 + 3 ^ 40 * 345106 * 2
def baseEnd_345106 : Nat := 105010521333707854748381

theorem tailTrace_345106 : CollatzResearch.WordTrace tailWord_345106 prefixEnd_345106 105010521333707854748381 := by
  unfold tailWord_345106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146762471936844064375793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8391366591831584171668781 3146762471936844064375793)
  ·
    refine ⟨2360071853952633048281845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3146762471936844064375793 2360071853952633048281845)
    ·
      refine ⟨221256736308059348276423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2360071853952633048281845 221256736308059348276423)
      ·
        refine ⟨331885104462089022414635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221256736308059348276423 331885104462089022414635)
        ·
          refine ⟨497827656693133533621953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331885104462089022414635 497827656693133533621953)
          ·
            refine ⟨373370742519850150216465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497827656693133533621953 373370742519850150216465)
            ·
              refine ⟨280028056889887612662349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373370742519850150216465 280028056889887612662349)
              ·
                refine ⟨105010521333707854748381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280028056889887612662349 105010521333707854748381)
                ·
                  rfl

theorem cell19_345106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_345106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345106 prefixEnd_345106 := by exact prefixLift 345106
  have htrace : WordTrace (prefixWord ++ tailWord_345106) baseStart_345106 baseEnd_345106 := by
    simpa [prefixWord, tailWord_345106, baseEnd_345106] using wordTrace_append hprefix tailTrace_345106
  have hstable : (prefixWord ++ tailWord_345106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345106).length < 2 ^ (prefixWord ++ tailWord_345106).sum := by decide
  have hdescent : baseEnd_345106 < baseStart_345106 := by decide
  rcases family_descends (prefixWord ++ tailWord_345106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345112 : List Nat := [2, 1, 2, 3, 2, 4, 2, 3]
def baseStart_345112 : Nat := 118140960795 + 345112 * 2 ^ 59
def prefixEnd_345112 : Nat := 4983230072969 + 3 ^ 40 * 345112 * 2
def baseEnd_345112 : Nat := 105012347042701618615031

theorem tailTrace_345112 : CollatzResearch.WordTrace tailWord_345112 prefixEnd_345112 105012347042701618615031 := by
  unfold tailWord_345112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6293634362862819641110795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8391512483817092854814393 6293634362862819641110795)
  ·
    refine ⟨9440451544294229461666193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6293634362862819641110795 9440451544294229461666193)
    ·
      refine ⟨7080338658220672096249645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9440451544294229461666193 7080338658220672096249645)
      ·
        refine ⟨2655126996832752036093617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7080338658220672096249645 2655126996832752036093617)
        ·
          refine ⟨1991345247624564027070213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655126996832752036093617 1991345247624564027070213)
          ·
            refine ⟨373377233929605755075665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1991345247624564027070213 373377233929605755075665)
            ·
              refine ⟨280032925447204316306749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373377233929605755075665 280032925447204316306749)
              ·
                refine ⟨105012347042701618615031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280032925447204316306749 105012347042701618615031)
                ·
                  rfl

theorem cell19_345112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_345112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345112 prefixEnd_345112 := by exact prefixLift 345112
  have htrace : WordTrace (prefixWord ++ tailWord_345112) baseStart_345112 baseEnd_345112 := by
    simpa [prefixWord, tailWord_345112, baseEnd_345112] using wordTrace_append hprefix tailTrace_345112
  have hstable : (prefixWord ++ tailWord_345112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345112).length < 2 ^ (prefixWord ++ tailWord_345112).sum := by decide
  have hdescent : baseEnd_345112 < baseStart_345112 := by decide
  rcases family_descends (prefixWord ++ tailWord_345112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345150 : List Nat := [4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_345150 : Nat := 118140960795 + 345150 * 2 ^ 59
def prefixEnd_345150 : Nat := 4983230072969 + 3 ^ 40 * 345150 * 2
def baseEnd_345150 : Nat := 105023909866328789770483

theorem tailTrace_345150 : CollatzResearch.WordTrace tailWord_345150 prefixEnd_345150 105023909866328789770483 := by
  unfold tailWord_345150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573581837448496471513113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8392436466391981181403269 1573581837448496471513113)
  ·
    refine ⟨1180186378086372353634835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1573581837448496471513113 1180186378086372353634835)
    ·
      refine ⟨1770279567129558530452253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180186378086372353634835 1770279567129558530452253)
      ·
        refine ⟨663854837673584448919595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1770279567129558530452253 663854837673584448919595)
        ·
          refine ⟨995782256510376673379393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663854837673584448919595 995782256510376673379393)
          ·
            refine ⟨746836692382782505034545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995782256510376673379393 746836692382782505034545)
            ·
              refine ⟨560127519287086878775909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746836692382782505034545 560127519287086878775909)
              ·
                refine ⟨105023909866328789770483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560127519287086878775909 105023909866328789770483)
                ·
                  rfl

theorem cell19_345150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_345150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345150 prefixEnd_345150 := by exact prefixLift 345150
  have htrace : WordTrace (prefixWord ++ tailWord_345150) baseStart_345150 baseEnd_345150 := by
    simpa [prefixWord, tailWord_345150, baseEnd_345150] using wordTrace_append hprefix tailTrace_345150
  have hstable : (prefixWord ++ tailWord_345150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345150).length < 2 ^ (prefixWord ++ tailWord_345150).sum := by decide
  have hdescent : baseEnd_345150 < baseStart_345150 := by decide
  rcases family_descends (prefixWord ++ tailWord_345150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345173 : List Nat := [1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_345173 : Nat := 118140960795 + 345173 * 2 ^ 59
def prefixEnd_345173 : Nat := 4983230072969 + 3 ^ 40 * 345173 * 2
def baseEnd_345173 : Nat := 105030908417471551259309

theorem tailTrace_345173 : CollatzResearch.WordTrace tailWord_345173 prefixEnd_345173 105030908417471551259309 := by
  unfold tailWord_345173
  simp only [CollatzResearch.WordTrace]
  refine ⟨12589493578504646700192173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8392995719003097800128115 12589493578504646700192173)
  ·
    refine ⟨4721060091939242512572065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12589493578504646700192173 4721060091939242512572065)
    ·
      refine ⟨3540795068954431884429049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4721060091939242512572065 3540795068954431884429049)
      ·
        refine ⟨2655596301715823913321787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540795068954431884429049 2655596301715823913321787)
        ·
          refine ⟨3983394452573735869982681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655596301715823913321787 3983394452573735869982681)
          ·
            refine ⟨2987545839430301902487011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3983394452573735869982681 2987545839430301902487011)
            ·
              refine ⟨4481318759145452853730517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987545839430301902487011 4481318759145452853730517)
              ·
                refine ⟨105030908417471551259309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4481318759145452853730517 105030908417471551259309)
                ·
                  rfl

theorem cell19_345173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_345173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345173 prefixEnd_345173 := by exact prefixLift 345173
  have htrace : WordTrace (prefixWord ++ tailWord_345173) baseStart_345173 baseEnd_345173 := by
    simpa [prefixWord, tailWord_345173, baseEnd_345173] using wordTrace_append hprefix tailTrace_345173
  have hstable : (prefixWord ++ tailWord_345173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345173).length < 2 ^ (prefixWord ++ tailWord_345173).sum := by decide
  have hdescent : baseEnd_345173 < baseStart_345173 := by decide
  rcases family_descends (prefixWord ++ tailWord_345173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345205 : List Nat := [1, 3, 4, 3, 1, 2, 1, 4]
def baseStart_345205 : Nat := 118140960795 + 345205 * 2 ^ 59
def prefixEnd_345205 : Nat := 4983230072969 + 3 ^ 40 * 345205 * 2
def baseEnd_345205 : Nat := 105040645532104958548111

theorem tailTrace_345205 : CollatzResearch.WordTrace tailWord_345205 prefixEnd_345205 105040645532104958548111 := by
  unfold tailWord_345205
  simp only [CollatzResearch.WordTrace]
  refine ⟨12590660714388716165357069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8393773809592477443571379 12590660714388716165357069)
  ·
    refine ⟨4721497767895768562008901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12590660714388716165357069 4721497767895768562008901)
    ·
      refine ⟨885280831480456605376669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4721497767895768562008901 885280831480456605376669)
      ·
        refine ⟨331980311805171227016251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 885280831480456605376669 331980311805171227016251)
        ·
          refine ⟨497970467707756840524377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331980311805171227016251 497970467707756840524377)
          ·
            refine ⟨373477850780817630393283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497970467707756840524377 373477850780817630393283)
            ·
              refine ⟨560216776171226445589925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373477850780817630393283 560216776171226445589925)
              ·
                refine ⟨105040645532104958548111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560216776171226445589925 105040645532104958548111)
                ·
                  rfl

theorem cell19_345205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_345205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345205 prefixEnd_345205 := by exact prefixLift 345205
  have htrace : WordTrace (prefixWord ++ tailWord_345205) baseStart_345205 baseEnd_345205 := by
    simpa [prefixWord, tailWord_345205, baseEnd_345205] using wordTrace_append hprefix tailTrace_345205
  have hstable : (prefixWord ++ tailWord_345205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345205).length < 2 ^ (prefixWord ++ tailWord_345205).sum := by decide
  have hdescent : baseEnd_345205 < baseStart_345205 := by decide
  rcases family_descends (prefixWord ++ tailWord_345205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345247 : List Nat := [1, 1, 2, 6, 2, 1, 6]
def baseStart_345247 : Nat := 118140960795 + 345247 * 2 ^ 59
def prefixEnd_345247 : Nat := 4983230072969 + 3 ^ 40 * 345247 * 2
def baseEnd_345247 : Nat := 35017808498353768538221

theorem tailTrace_345247 : CollatzResearch.WordTrace tailWord_345247 prefixEnd_345247 35017808498353768538221 := by
  unfold tailWord_345247
  simp only [CollatzResearch.WordTrace]
  refine ⟨12592192580236557338385995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8394795053491038225590663 12592192580236557338385995)
  ·
    refine ⟨18888288870354836007578993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12592192580236557338385995 18888288870354836007578993)
    ·
      refine ⟨14166216652766127005684245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18888288870354836007578993 14166216652766127005684245)
      ·
        refine ⟨664041405598412203391449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14166216652766127005684245 664041405598412203391449)
        ·
          refine ⟨498031054198809152543587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664041405598412203391449 498031054198809152543587)
          ·
            refine ⟨747046581298213728815381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498031054198809152543587 747046581298213728815381)
            ·
              refine ⟨35017808498353768538221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 747046581298213728815381 35017808498353768538221)
              ·
                rfl

theorem cell19_345247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_345247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345247 prefixEnd_345247 := by exact prefixLift 345247
  have htrace : WordTrace (prefixWord ++ tailWord_345247) baseStart_345247 baseEnd_345247 := by
    simpa [prefixWord, tailWord_345247, baseEnd_345247] using wordTrace_append hprefix tailTrace_345247
  have hstable : (prefixWord ++ tailWord_345247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345247).length < 2 ^ (prefixWord ++ tailWord_345247).sum := by decide
  have hdescent : baseEnd_345247 < baseStart_345247 := by decide
  rcases family_descends (prefixWord ++ tailWord_345247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345249 : List Nat := [1, 2, 3, 3, 1, 1, 8]
def baseStart_345249 : Nat := 118140960795 + 345249 * 2 ^ 59
def prefixEnd_345249 : Nat := 4983230072969 + 3 ^ 40 * 345249 * 2
def baseEnd_345249 : Nat := 35018011354908631190071

theorem tailTrace_345249 : CollatzResearch.WordTrace tailWord_345249 prefixEnd_345249 35018011354908631190071 := by
  unfold tailWord_345249
  simp only [CollatzResearch.WordTrace]
  refine ⟨12592265526229311679958801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8394843684152874453305867 12592265526229311679958801)
  ·
    refine ⟨9444199144671983759969101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12592265526229311679958801 9444199144671983759969101)
    ·
      refine ⟨3541574679251993909988413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9444199144671983759969101 3541574679251993909988413)
      ·
        refine ⟨1328090504719497716245655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3541574679251993909988413 1328090504719497716245655)
        ·
          refine ⟨1992135757079246574368483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328090504719497716245655 1992135757079246574368483)
          ·
            refine ⟨2988203635618869861552725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992135757079246574368483 2988203635618869861552725)
            ·
              refine ⟨35018011354908631190071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2988203635618869861552725 35018011354908631190071)
              ·
                rfl

theorem cell19_345249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_345249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345249 prefixEnd_345249 := by exact prefixLift 345249
  have htrace : WordTrace (prefixWord ++ tailWord_345249) baseStart_345249 baseEnd_345249 := by
    simpa [prefixWord, tailWord_345249, baseEnd_345249] using wordTrace_append hprefix tailTrace_345249
  have hstable : (prefixWord ++ tailWord_345249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345249).length < 2 ^ (prefixWord ++ tailWord_345249).sum := by decide
  have hdescent : baseEnd_345249 < baseStart_345249 := by decide
  rcases family_descends (prefixWord ++ tailWord_345249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345281 : List Nat := [1, 2, 6, 1, 1, 3, 2, 3]
def baseStart_345281 : Nat := 118140960795 + 345281 * 2 ^ 59
def prefixEnd_345281 : Nat := 4983230072969 + 3 ^ 40 * 345281 * 2
def baseEnd_345281 : Nat := 105063771179359300859015

theorem tailTrace_345281 : CollatzResearch.WordTrace tailWord_345281 prefixEnd_345281 105063771179359300859015 := by
  unfold tailWord_345281
  simp only [CollatzResearch.WordTrace]
  refine ⟨12593432662113381145123697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8395621774742254096749131 12593432662113381145123697)
  ·
    refine ⟨9445074496585035858842773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12593432662113381145123697 9445074496585035858842773)
    ·
      refine ⟨442737867027423555883255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9445074496585035858842773 442737867027423555883255)
      ·
        refine ⟨664106800541135333824883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442737867027423555883255 664106800541135333824883)
        ·
          refine ⟨996160200811703000737325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664106800541135333824883 996160200811703000737325)
          ·
            refine ⟨373560075304388625276497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 996160200811703000737325 373560075304388625276497)
            ·
              refine ⟨280170056478291468957373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373560075304388625276497 280170056478291468957373)
              ·
                refine ⟨105063771179359300859015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280170056478291468957373 105063771179359300859015)
                ·
                  rfl

theorem cell19_345281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_345281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345281 prefixEnd_345281 := by exact prefixLift 345281
  have htrace : WordTrace (prefixWord ++ tailWord_345281) baseStart_345281 baseEnd_345281 := by
    simpa [prefixWord, tailWord_345281, baseEnd_345281] using wordTrace_append hprefix tailTrace_345281
  have hstable : (prefixWord ++ tailWord_345281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345281).length < 2 ^ (prefixWord ++ tailWord_345281).sum := by decide
  have hdescent : baseEnd_345281 < baseStart_345281 := by decide
  rcases family_descends (prefixWord ++ tailWord_345281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345300 : List Nat := [2, 4, 1, 4, 2, 1, 5]
def baseStart_345300 : Nat := 118140960795 + 345300 * 2 ^ 59
def prefixEnd_345300 : Nat := 4983230072969 + 3 ^ 40 * 345300 * 2
def baseEnd_345300 : Nat := 35023184197057628812247

theorem tailTrace_345300 : CollatzResearch.WordTrace tailWord_345300 prefixEnd_345300 35023184197057628812247 := by
  unfold tailWord_345300
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297062824522273695032677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8396083766029698260043569 6297062824522273695032677)
  ·
    refine ⟨1180699279597926317818627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6297062824522273695032677 1180699279597926317818627)
    ·
      refine ⟨1771048919396889476727941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180699279597926317818627 1771048919396889476727941)
      ·
        refine ⟨332071672386916776886489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1771048919396889476727941 332071672386916776886489)
        ·
          refine ⟨249053754290187582664867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332071672386916776886489 249053754290187582664867)
          ·
            refine ⟨373580631435281373997301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249053754290187582664867 373580631435281373997301)
            ·
              refine ⟨35023184197057628812247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373580631435281373997301 35023184197057628812247)
              ·
                rfl

theorem cell19_345300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_345300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345300 prefixEnd_345300 := by exact prefixLift 345300
  have htrace : WordTrace (prefixWord ++ tailWord_345300) baseStart_345300 baseEnd_345300 := by
    simpa [prefixWord, tailWord_345300, baseEnd_345300] using wordTrace_append hprefix tailTrace_345300
  have hstable : (prefixWord ++ tailWord_345300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345300).length < 2 ^ (prefixWord ++ tailWord_345300).sum := by decide
  have hdescent : baseEnd_345300 < baseStart_345300 := by decide
  rcases family_descends (prefixWord ++ tailWord_345300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345304 : List Nat := [2, 1, 2, 2, 5, 2, 5]
def baseStart_345304 : Nat := 118140960795 + 345304 * 2 ^ 59
def prefixEnd_345304 : Nat := 4983230072969 + 3 ^ 40 * 345304 * 2
def baseEnd_345304 : Nat := 35023589910167354115947

theorem tailTrace_345304 : CollatzResearch.WordTrace tailWord_345304 prefixEnd_345304 35023589910167354115947 := by
  unfold tailWord_345304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297135770515028036605483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8396181027353370715473977 6297135770515028036605483)
  ·
    refine ⟨9445703655772542054908225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6297135770515028036605483 9445703655772542054908225)
    ·
      refine ⟨7084277741829406541181169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9445703655772542054908225 7084277741829406541181169)
      ·
        refine ⟨5313208306372054905885877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7084277741829406541181169 5313208306372054905885877)
        ·
          refine ⟨498113278722380147426801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5313208306372054905885877 498113278722380147426801)
          ·
            refine ⟨373584959041785110570101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498113278722380147426801 373584959041785110570101)
            ·
              refine ⟨35023589910167354115947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373584959041785110570101 35023589910167354115947)
              ·
                rfl

theorem cell19_345304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_345304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345304 prefixEnd_345304 := by exact prefixLift 345304
  have htrace : WordTrace (prefixWord ++ tailWord_345304) baseStart_345304 baseEnd_345304 := by
    simpa [prefixWord, tailWord_345304, baseEnd_345304] using wordTrace_append hprefix tailTrace_345304
  have hstable : (prefixWord ++ tailWord_345304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345304).length < 2 ^ (prefixWord ++ tailWord_345304).sum := by decide
  have hdescent : baseEnd_345304 < baseStart_345304 := by decide
  rcases family_descends (prefixWord ++ tailWord_345304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345342 : List Nat := [4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_345342 : Nat := 118140960795 + 345342 * 2 ^ 59
def prefixEnd_345342 : Nat := 4983230072969 + 3 ^ 40 * 345342 * 2
def baseEnd_345342 : Nat := 105082332554129233503293

theorem tailTrace_345342 : CollatzResearch.WordTrace tailWord_345342 prefixEnd_345342 105082332554129233503293 := by
  unfold tailWord_345342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574457189361548570386785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8397105009928259042062853 1574457189361548570386785)
  ·
    refine ⟨1180842892021161427790089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1574457189361548570386785 1180842892021161427790089)
    ·
      refine ⟨885632169015871070842567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1180842892021161427790089 885632169015871070842567)
      ·
        refine ⟨1328448253523806606263851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885632169015871070842567 1328448253523806606263851)
        ·
          refine ⟨1992672380285709909395777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328448253523806606263851 1992672380285709909395777)
          ·
            refine ⟨1494504285214282432046833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992672380285709909395777 1494504285214282432046833)
            ·
              refine ⟨1120878213910711824035125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494504285214282432046833 1120878213910711824035125)
              ·
                refine ⟨105082332554129233503293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1120878213910711824035125 105082332554129233503293)
                ·
                  rfl

theorem cell19_345342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_345342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345342 prefixEnd_345342 := by exact prefixLift 345342
  have htrace : WordTrace (prefixWord ++ tailWord_345342) baseStart_345342 baseEnd_345342 := by
    simpa [prefixWord, tailWord_345342, baseEnd_345342] using wordTrace_append hprefix tailTrace_345342
  have hstable : (prefixWord ++ tailWord_345342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345342).length < 2 ^ (prefixWord ++ tailWord_345342).sum := by decide
  have hdescent : baseEnd_345342 < baseStart_345342 := by decide
  rcases family_descends (prefixWord ++ tailWord_345342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345374 : List Nat := [4, 3, 2, 1, 3, 1, 1, 4]
def baseStart_345374 : Nat := 118140960795 + 345374 * 2 ^ 59
def prefixEnd_345374 : Nat := 4983230072969 + 3 ^ 40 * 345374 * 2
def baseEnd_345374 : Nat := 105092069668762640792095

theorem tailTrace_345374 : CollatzResearch.WordTrace tailWord_345374 prefixEnd_345374 105092069668762640792095 := by
  unfold tailWord_345374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574603081347057253532397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8397883100517638685506117 1574603081347057253532397)
  ·
    refine ⟨590476155505146470074649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1574603081347057253532397 590476155505146470074649)
    ·
      refine ⟨442857116628859852555987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 590476155505146470074649 442857116628859852555987)
      ·
        refine ⟨664285674943289778833981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442857116628859852555987 664285674943289778833981)
        ·
          refine ⟨249107128103733667062743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 664285674943289778833981 249107128103733667062743)
          ·
            refine ⟨373660692155600500594115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249107128103733667062743 373660692155600500594115)
            ·
              refine ⟨560491038233400750891173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373660692155600500594115 560491038233400750891173)
              ·
                refine ⟨105092069668762640792095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560491038233400750891173 105092069668762640792095)
                ·
                  rfl

theorem cell19_345374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_345374 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345374 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345374 prefixEnd_345374 := by exact prefixLift 345374
  have htrace : WordTrace (prefixWord ++ tailWord_345374) baseStart_345374 baseEnd_345374 := by
    simpa [prefixWord, tailWord_345374, baseEnd_345374] using wordTrace_append hprefix tailTrace_345374
  have hstable : (prefixWord ++ tailWord_345374).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345374).length < 2 ^ (prefixWord ++ tailWord_345374).sum := by decide
  have hdescent : baseEnd_345374 < baseStart_345374 := by decide
  rcases family_descends (prefixWord ++ tailWord_345374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345378 : List Nat := [3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_345378 : Nat := 118140960795 + 345378 * 2 ^ 59
def prefixEnd_345378 : Nat := 4983230072969 + 3 ^ 40 * 345378 * 2
def baseEnd_345378 : Nat := 105093286808091816703195

theorem tailTrace_345378 : CollatzResearch.WordTrace tailWord_345378 prefixEnd_345378 105093286808091816703195 := by
  unfold tailWord_345378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149242635690491677851197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8397980361841311140936525 3149242635690491677851197)
  ·
    refine ⟨1180965988383934379194199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3149242635690491677851197 1180965988383934379194199)
    ·
      refine ⟨1771448982575901568791299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180965988383934379194199 1771448982575901568791299)
      ·
        refine ⟨2657173473863852353186949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771448982575901568791299 2657173473863852353186949)
        ·
          refine ⟨498220026349472316222553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2657173473863852353186949 498220026349472316222553)
          ·
            refine ⟨373665019762104237166915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498220026349472316222553 373665019762104237166915)
            ·
              refine ⟨560497529643156355750373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373665019762104237166915 560497529643156355750373)
              ·
                refine ⟨105093286808091816703195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560497529643156355750373 105093286808091816703195)
                ·
                  rfl

theorem cell19_345378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_345378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345378 prefixEnd_345378 := by exact prefixLift 345378
  have htrace : WordTrace (prefixWord ++ tailWord_345378) baseStart_345378 baseEnd_345378 := by
    simpa [prefixWord, tailWord_345378, baseEnd_345378] using wordTrace_append hprefix tailTrace_345378
  have hstable : (prefixWord ++ tailWord_345378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345378).length < 2 ^ (prefixWord ++ tailWord_345378).sum := by decide
  have hdescent : baseEnd_345378 < baseStart_345378 := by decide
  rcases family_descends (prefixWord ++ tailWord_345378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345414 : List Nat := [6, 1, 1, 3, 1, 1, 6]
def baseStart_345414 : Nat := 118140960795 + 345414 * 2 ^ 59
def prefixEnd_345414 : Nat := 4983230072969 + 3 ^ 40 * 345414 * 2
def baseEnd_345414 : Nat := 35034747020684799967699

theorem tailTrace_345414 : CollatzResearch.WordTrace tailWord_345414 prefixEnd_345414 35034747020684799967699 := by
  unfold tailWord_345414
  simp only [CollatzResearch.WordTrace]
  refine ⟨393696361582235776866103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8398855713754363239810197 393696361582235776866103)
  ·
    refine ⟨590544542373353665299155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393696361582235776866103 590544542373353665299155)
    ·
      refine ⟨885816813560030497948733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590544542373353665299155 885816813560030497948733)
      ·
        refine ⟨332181305085011436730775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 885816813560030497948733 332181305085011436730775)
        ·
          refine ⟨498271957627517155096163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332181305085011436730775 498271957627517155096163)
          ·
            refine ⟨747407936441275732644245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498271957627517155096163 747407936441275732644245)
            ·
              refine ⟨35034747020684799967699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 747407936441275732644245 35034747020684799967699)
              ·
                rfl

theorem cell19_345414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_345414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345414 prefixEnd_345414 := by exact prefixLift 345414
  have htrace : WordTrace (prefixWord ++ tailWord_345414) baseStart_345414 baseEnd_345414 := by
    simpa [prefixWord, tailWord_345414, baseEnd_345414] using wordTrace_append hprefix tailTrace_345414
  have hstable : (prefixWord ++ tailWord_345414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345414).length < 2 ^ (prefixWord ++ tailWord_345414).sum := by decide
  have hdescent : baseEnd_345414 < baseStart_345414 := by decide
  rcases family_descends (prefixWord ++ tailWord_345414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345420 : List Nat := [2, 2, 1, 3, 2, 3, 6]
def baseStart_345420 : Nat := 118140960795 + 345420 * 2 ^ 59
def prefixEnd_345420 : Nat := 4983230072969 + 3 ^ 40 * 345420 * 2
def baseEnd_345420 : Nat := 35035355590349387923249

theorem tailTrace_345420 : CollatzResearch.WordTrace tailWord_345420 prefixEnd_345420 35035355590349387923249 := by
  unfold tailWord_345420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6299251204304903942216857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8399001605739871922955809 6299251204304903942216857)
  ·
    refine ⟨4724438403228677956662643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6299251204304903942216857 4724438403228677956662643)
    ·
      refine ⟨7086657604843016934993965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4724438403228677956662643 7086657604843016934993965)
      ·
        refine ⟨2657496601816131350622737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7086657604843016934993965 2657496601816131350622737)
        ·
          refine ⟨1993122451362098512967053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2657496601816131350622737 1993122451362098512967053)
          ·
            refine ⟨747420919260786942362645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1993122451362098512967053 747420919260786942362645)
            ·
              refine ⟨35035355590349387923249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 747420919260786942362645 35035355590349387923249)
              ·
                rfl

theorem cell19_345420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_345420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345420 prefixEnd_345420 := by exact prefixLift 345420
  have htrace : WordTrace (prefixWord ++ tailWord_345420) baseStart_345420 baseEnd_345420 := by
    simpa [prefixWord, tailWord_345420, baseEnd_345420] using wordTrace_append hprefix tailTrace_345420
  have hstable : (prefixWord ++ tailWord_345420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345420).length < 2 ^ (prefixWord ++ tailWord_345420).sum := by decide
  have hdescent : baseEnd_345420 < baseStart_345420 := by decide
  rcases family_descends (prefixWord ++ tailWord_345420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345454 : List Nat := [4, 1, 2, 4, 1, 1, 1, 5]
def baseStart_345454 : Nat := 118140960795 + 345454 * 2 ^ 59
def prefixEnd_345454 : Nat := 4983230072969 + 3 ^ 40 * 345454 * 2
def baseEnd_345454 : Nat := 105116412455346159014099

theorem tailTrace_345454 : CollatzResearch.WordTrace tailWord_345454 prefixEnd_345454 105116412455346159014099 := by
  unfold tailWord_345454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574967811310828961396427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8399828326991087794114277 1574967811310828961396427)
  ·
    refine ⟨2362451716966243442094641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1574967811310828961396427 2362451716966243442094641)
    ·
      refine ⟨1771838787724682581570981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2362451716966243442094641 1771838787724682581570981)
      ·
        refine ⟨332219772698377984044559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1771838787724682581570981 332219772698377984044559)
        ·
          refine ⟨498329659047566976066839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332219772698377984044559 498329659047566976066839)
          ·
            refine ⟨747494488571350464100259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498329659047566976066839 747494488571350464100259)
            ·
              refine ⟨1121241732857025696150389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747494488571350464100259 1121241732857025696150389)
              ·
                refine ⟨105116412455346159014099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1121241732857025696150389 105116412455346159014099)
                ·
                  rfl

theorem cell19_345454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_345454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345454 prefixEnd_345454 := by exact prefixLift 345454
  have htrace : WordTrace (prefixWord ++ tailWord_345454) baseStart_345454 baseEnd_345454 := by
    simpa [prefixWord, tailWord_345454, baseEnd_345454] using wordTrace_append hprefix tailTrace_345454
  have hstable : (prefixWord ++ tailWord_345454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345454).length < 2 ^ (prefixWord ++ tailWord_345454).sum := by decide
  have hdescent : baseEnd_345454 < baseStart_345454 := by decide
  rcases family_descends (prefixWord ++ tailWord_345454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345458 : List Nat := [3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_345458 : Nat := 118140960795 + 345458 * 2 ^ 59
def prefixEnd_345458 : Nat := 4983230072969 + 3 ^ 40 * 345458 * 2
def baseEnd_345458 : Nat := 105117629594675334925199

theorem tailTrace_345458 : CollatzResearch.WordTrace tailWord_345458 prefixEnd_345458 105117629594675334925199 := by
  unfold tailWord_345458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149972095618035093579257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8399925588314760249544685 3149972095618035093579257)
  ·
    refine ⟨2362479071713526320184443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3149972095618035093579257 2362479071713526320184443)
    ·
      refine ⟨3543718607570289480276665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2362479071713526320184443 3543718607570289480276665)
      ·
        refine ⟨2657788955677717110207499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3543718607570289480276665 2657788955677717110207499)
        ·
          refine ⟨3986683433516575665311249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657788955677717110207499 3986683433516575665311249)
          ·
            refine ⟨2990012575137431748983437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3986683433516575665311249 2990012575137431748983437)
            ·
              refine ⟨1121254715676536905868789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2990012575137431748983437 1121254715676536905868789)
              ·
                refine ⟨105117629594675334925199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1121254715676536905868789 105117629594675334925199)
                ·
                  rfl

theorem cell19_345458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_345458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345458 prefixEnd_345458 := by exact prefixLift 345458
  have htrace : WordTrace (prefixWord ++ tailWord_345458) baseStart_345458 baseEnd_345458 := by
    simpa [prefixWord, tailWord_345458, baseEnd_345458] using wordTrace_append hprefix tailTrace_345458
  have hstable : (prefixWord ++ tailWord_345458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345458).length < 2 ^ (prefixWord ++ tailWord_345458).sum := by decide
  have hdescent : baseEnd_345458 < baseStart_345458 := by decide
  rcases family_descends (prefixWord ++ tailWord_345458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345473 : List Nat := [1, 2, 4, 3, 3, 1, 5]
def baseStart_345473 : Nat := 118140960795 + 345473 * 2 ^ 59
def prefixEnd_345473 : Nat := 4983230072969 + 3 ^ 40 * 345473 * 2
def baseEnd_345473 : Nat := 35040731289053248197275

theorem tailTrace_345473 : CollatzResearch.WordTrace tailWord_345473 prefixEnd_345473 35040731289053248197275 := by
  unfold tailWord_345473
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600435477417797936113073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8400290318278531957408715 12600435477417797936113073)
  ·
    refine ⟨9450326608063348452084805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12600435477417797936113073 9450326608063348452084805)
    ·
      refine ⟨1771936239011877834765901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9450326608063348452084805 1771936239011877834765901)
      ·
        refine ⟨664476089629454188037213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1771936239011877834765901 664476089629454188037213)
        ·
          refine ⟨249178533611045320513955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 664476089629454188037213 249178533611045320513955)
          ·
            refine ⟨373767800416567980770933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249178533611045320513955 373767800416567980770933)
            ·
              refine ⟨35040731289053248197275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373767800416567980770933 35040731289053248197275)
              ·
                rfl

theorem cell19_345473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_345473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345473 prefixEnd_345473 := by exact prefixLift 345473
  have htrace : WordTrace (prefixWord ++ tailWord_345473) baseStart_345473 baseEnd_345473 := by
    simpa [prefixWord, tailWord_345473, baseEnd_345473] using wordTrace_append hprefix tailTrace_345473
  have hstable : (prefixWord ++ tailWord_345473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345473).length < 2 ^ (prefixWord ++ tailWord_345473).sum := by decide
  have hdescent : baseEnd_345473 < baseStart_345473 := by decide
  rcases family_descends (prefixWord ++ tailWord_345473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345532 : List Nat := [2, 2, 2, 4, 3, 6]
def baseStart_345532 : Nat := 118140960795 + 345532 * 2 ^ 59
def prefixEnd_345532 : Nat := 4983230072969 + 3 ^ 40 * 345532 * 2
def baseEnd_345532 : Nat := 11682238519140565475617

theorem tailTrace_345532 : CollatzResearch.WordTrace tailWord_345532 prefixEnd_345532 11682238519140565475617 := by
  unfold tailWord_345532
  simp only [CollatzResearch.WordTrace]
  refine ⟨6301293692102025506255425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8401724922802700675007233 6301293692102025506255425)
  ·
    refine ⟨4725970269076519129691569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6301293692102025506255425 4725970269076519129691569)
    ·
      refine ⟨3544477701807389347268677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4725970269076519129691569 3544477701807389347268677)
      ·
        refine ⟨664589569088885502612877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3544477701807389347268677 664589569088885502612877)
        ·
          refine ⟨249221088408332063479829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 664589569088885502612877 249221088408332063479829)
          ·
            refine ⟨11682238519140565475617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 249221088408332063479829 11682238519140565475617)
            ·
              rfl

theorem cell19_345532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 6].length) (baseStart_345532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345532 prefixEnd_345532 := by exact prefixLift 345532
  have htrace : WordTrace (prefixWord ++ tailWord_345532) baseStart_345532 baseEnd_345532 := by
    simpa [prefixWord, tailWord_345532, baseEnd_345532] using wordTrace_append hprefix tailTrace_345532
  have hstable : (prefixWord ++ tailWord_345532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345532).length < 2 ^ (prefixWord ++ tailWord_345532).sum := by decide
  have hdescent : baseEnd_345532 < baseStart_345532 := by decide
  rcases family_descends (prefixWord ++ tailWord_345532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345589 : List Nat := [1, 3, 5, 1, 1, 2, 6]
def baseStart_345589 : Nat := 118140960795 + 345589 * 2 ^ 59
def prefixEnd_345589 : Nat := 4983230072969 + 3 ^ 40 * 345589 * 2
def baseEnd_345589 : Nat := 35052496969235282004577

theorem tailTrace_345589 : CollatzResearch.WordTrace tailWord_345589 prefixEnd_345589 35052496969235282004577 := by
  unfold tailWord_345589
  simp only [CollatzResearch.WordTrace]
  refine ⟨12604666344997549747335821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8403110896665033164890547 12604666344997549747335821)
  ·
    refine ⟨4726749879374081155250933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12604666344997549747335821 4726749879374081155250933)
    ·
      refine ⟨443132801191320108304775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4726749879374081155250933 443132801191320108304775)
      ·
        refine ⟨664699201786980162457163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443132801191320108304775 664699201786980162457163)
        ·
          refine ⟨997048802680470243685745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664699201786980162457163 997048802680470243685745)
          ·
            refine ⟨747786602010352682764309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997048802680470243685745 747786602010352682764309)
            ·
              refine ⟨35052496969235282004577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 747786602010352682764309 35052496969235282004577)
              ·
                rfl

theorem cell19_345589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_345589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345589 prefixEnd_345589 := by exact prefixLift 345589
  have htrace : WordTrace (prefixWord ++ tailWord_345589) baseStart_345589 baseEnd_345589 := by
    simpa [prefixWord, tailWord_345589, baseEnd_345589] using wordTrace_append hprefix tailTrace_345589
  have hstable : (prefixWord ++ tailWord_345589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345589).length < 2 ^ (prefixWord ++ tailWord_345589).sum := by decide
  have hdescent : baseEnd_345589 < baseStart_345589 := by decide
  rcases family_descends (prefixWord ++ tailWord_345589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345629 : List Nat := [1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_345629 : Nat := 118140960795 + 345629 * 2 ^ 59
def prefixEnd_345629 : Nat := 4983230072969 + 3 ^ 40 * 345629 * 2
def baseEnd_345629 : Nat := 105169662300997605124733

theorem tailTrace_345629 : CollatzResearch.WordTrace tailWord_345629 prefixEnd_345629 105169662300997605124733 := by
  unfold tailWord_345629
  simp only [CollatzResearch.WordTrace]
  refine ⟨12606125264852636578791941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8404083509901757719194627 12606125264852636578791941)
  ·
    refine ⟨2363648487159869358523489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12606125264852636578791941 2363648487159869358523489)
    ·
      refine ⟨1772736365369902018892617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2363648487159869358523489 1772736365369902018892617)
      ·
        refine ⟨1329552274027426514169463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1772736365369902018892617 1329552274027426514169463)
        ·
          refine ⟨1994328411041139771254195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329552274027426514169463 1994328411041139771254195)
          ·
            refine ⟨2991492616561709656881293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994328411041139771254195 2991492616561709656881293)
            ·
              refine ⟨1121809731210641121330485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2991492616561709656881293 1121809731210641121330485)
              ·
                refine ⟨105169662300997605124733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1121809731210641121330485 105169662300997605124733)
                ·
                  rfl

theorem cell19_345629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_345629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345629 prefixEnd_345629 := by exact prefixLift 345629
  have htrace : WordTrace (prefixWord ++ tailWord_345629) baseStart_345629 baseEnd_345629 := by
    simpa [prefixWord, tailWord_345629, baseEnd_345629] using wordTrace_append hprefix tailTrace_345629
  have hstable : (prefixWord ++ tailWord_345629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345629).length < 2 ^ (prefixWord ++ tailWord_345629).sum := by decide
  have hdescent : baseEnd_345629 < baseStart_345629 := by decide
  rcases family_descends (prefixWord ++ tailWord_345629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345646 : List Nat := [4, 1, 3, 1, 2, 3, 5]
def baseStart_345646 : Nat := 118140960795 + 345646 * 2 ^ 59
def prefixEnd_345646 : Nat := 4983230072969 + 3 ^ 40 * 345646 * 2
def baseEnd_345646 : Nat := 35058278381048867582303

theorem tailTrace_345646 : CollatzResearch.WordTrace tailWord_345646 prefixEnd_345646 35058278381048867582303 := by
  unfold tailWord_345646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575843163223881060270099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8404496870527365654773861 1575843163223881060270099)
  ·
    refine ⟨2363764744835821590405149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1575843163223881060270099 2363764744835821590405149)
    ·
      refine ⟨886411779313433096401931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2363764744835821590405149 886411779313433096401931)
      ·
        refine ⟨1329617668970149644602897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886411779313433096401931 1329617668970149644602897)
        ·
          refine ⟨997213251727612233452173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1329617668970149644602897 997213251727612233452173)
          ·
            refine ⟨373954969397854587544565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 997213251727612233452173 373954969397854587544565)
            ·
              refine ⟨35058278381048867582303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 373954969397854587544565 35058278381048867582303)
              ·
                rfl

theorem cell19_345646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_345646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345646 prefixEnd_345646 := by exact prefixLift 345646
  have htrace : WordTrace (prefixWord ++ tailWord_345646) baseStart_345646 baseEnd_345646 := by
    simpa [prefixWord, tailWord_345646, baseEnd_345646] using wordTrace_append hprefix tailTrace_345646
  have hstable : (prefixWord ++ tailWord_345646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345646).length < 2 ^ (prefixWord ++ tailWord_345646).sum := by decide
  have hdescent : baseEnd_345646 < baseStart_345646 := by decide
  rcases family_descends (prefixWord ++ tailWord_345646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345794 : List Nat := [3, 5, 1, 2, 1, 1, 1, 5]
def baseStart_345794 : Nat := 118140960795 + 345794 * 2 ^ 59
def prefixEnd_345794 : Nat := 4983230072969 + 3 ^ 40 * 345794 * 2
def baseEnd_345794 : Nat := 105219869298326111457617

theorem tailTrace_345794 : CollatzResearch.WordTrace tailWord_345794 prefixEnd_345794 105219869298326111457617 := by
  unfold tailWord_345794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153035827313717439637109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8408095539503246505698957 3153035827313717439637109)
  ·
    refine ⟨295597108810661009965979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3153035827313717439637109 295597108810661009965979)
    ·
      refine ⟨443395663215991514948969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295597108810661009965979 443395663215991514948969)
      ·
        refine ⟨332546747411993636211727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443395663215991514948969 332546747411993636211727)
        ·
          refine ⟨498820121117990454317591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332546747411993636211727 498820121117990454317591)
          ·
            refine ⟨748230181676985681476387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498820121117990454317591 748230181676985681476387)
            ·
              refine ⟨1122345272515478522214581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748230181676985681476387 1122345272515478522214581)
              ·
                refine ⟨105219869298326111457617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1122345272515478522214581 105219869298326111457617)
                ·
                  rfl

theorem cell19_345794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_345794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345794 prefixEnd_345794 := by exact prefixLift 345794
  have htrace : WordTrace (prefixWord ++ tailWord_345794) baseStart_345794 baseEnd_345794 := by
    simpa [prefixWord, tailWord_345794, baseEnd_345794] using wordTrace_append hprefix tailTrace_345794
  have hstable : (prefixWord ++ tailWord_345794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345794).length < 2 ^ (prefixWord ++ tailWord_345794).sum := by decide
  have hdescent : baseEnd_345794 < baseStart_345794 := by decide
  rcases family_descends (prefixWord ++ tailWord_345794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345838 : List Nat := [4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_345838 : Nat := 118140960795 + 345838 * 2 ^ 59
def prefixEnd_345838 : Nat := 4983230072969 + 3 ^ 40 * 345838 * 2
def baseEnd_345838 : Nat := 105233257830947046479719

theorem tailTrace_345838 : CollatzResearch.WordTrace tailWord_345838 prefixEnd_345838 105233257830947046479719 := by
  unfold tailWord_345838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576718515136933159143771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8409165414063643515433445 1576718515136933159143771)
  ·
    refine ⟨2365077772705399738715657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1576718515136933159143771 2365077772705399738715657)
    ·
      refine ⟨1773808329529049804036743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2365077772705399738715657 1773808329529049804036743)
      ·
        refine ⟨2660712494293574706055115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773808329529049804036743 2660712494293574706055115)
        ·
          refine ⟨3991068741440362059082673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660712494293574706055115 3991068741440362059082673)
          ·
            refine ⟨2993301556080271544312005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3991068741440362059082673 2993301556080271544312005)
            ·
              refine ⟨561244041765050914558501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2993301556080271544312005 561244041765050914558501)
              ·
                refine ⟨105233257830947046479719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561244041765050914558501 105233257830947046479719)
                ·
                  rfl

theorem cell19_345838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_345838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345838 prefixEnd_345838 := by exact prefixLift 345838
  have htrace : WordTrace (prefixWord ++ tailWord_345838) baseStart_345838 baseEnd_345838 := by
    simpa [prefixWord, tailWord_345838, baseEnd_345838] using wordTrace_append hprefix tailTrace_345838
  have hstable : (prefixWord ++ tailWord_345838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345838).length < 2 ^ (prefixWord ++ tailWord_345838).sum := by decide
  have hdescent : baseEnd_345838 < baseStart_345838 := by decide
  rcases family_descends (prefixWord ++ tailWord_345838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345859 : List Nat := [1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_345859 : Nat := 118140960795 + 345859 * 2 ^ 59
def prefixEnd_345859 : Nat := 4983230072969 + 3 ^ 40 * 345859 * 2
def baseEnd_345859 : Nat := 105239647812425220012995

theorem tailTrace_345859 : CollatzResearch.WordTrace tailWord_345859 prefixEnd_345859 105239647812425220012995 := by
  unfold tailWord_345859
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614514054019385859664631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8409676036012923906443087 12614514054019385859664631)
  ·
    refine ⟨18921771081029078789496947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12614514054019385859664631 18921771081029078789496947)
    ·
      refine ⟨28382656621543618184245421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18921771081029078789496947 28382656621543618184245421)
      ·
        refine ⟨10643496233078856819092033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28382656621543618184245421 10643496233078856819092033)
        ·
          refine ⟨7982622174809142614319025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10643496233078856819092033 7982622174809142614319025)
          ·
            refine ⟨5986966631106856960739269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7982622174809142614319025 5986966631106856960739269)
            ·
              refine ⟨1122556243332535680138613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5986966631106856960739269 1122556243332535680138613)
              ·
                refine ⟨105239647812425220012995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1122556243332535680138613 105239647812425220012995)
                ·
                  rfl

theorem cell19_345859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_345859 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345859 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345859 prefixEnd_345859 := by exact prefixLift 345859
  have htrace : WordTrace (prefixWord ++ tailWord_345859) baseStart_345859 baseEnd_345859 := by
    simpa [prefixWord, tailWord_345859, baseEnd_345859] using wordTrace_append hprefix tailTrace_345859
  have hstable : (prefixWord ++ tailWord_345859).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345859).length < 2 ^ (prefixWord ++ tailWord_345859).sum := by decide
  have hdescent : baseEnd_345859 < baseStart_345859 := by decide
  rcases family_descends (prefixWord ++ tailWord_345859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345910 : List Nat := [5, 1, 2, 2, 1, 2, 3, 3]
def baseStart_345910 : Nat := 118140960795 + 345910 * 2 ^ 59
def prefixEnd_345910 : Nat := 4983230072969 + 3 ^ 40 * 345910 * 2
def baseEnd_345910 : Nat := 105255166338872212879523

theorem tailTrace_345910 : CollatzResearch.WordTrace tailWord_345910 prefixEnd_345910 105255166338872212879523 := by
  unfold tailWord_345910
  simp only [CollatzResearch.WordTrace]
  refine ⟨788523386052163848110699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8410916117889747713180789 788523386052163848110699)
  ·
    refine ⟨1182785079078245772166049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 788523386052163848110699 1182785079078245772166049)
    ·
      refine ⟨887088809308684329124537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1182785079078245772166049 887088809308684329124537)
      ·
        refine ⟨665316606981513246843403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 887088809308684329124537 665316606981513246843403)
        ·
          refine ⟨997974910472269870265105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665316606981513246843403 997974910472269870265105)
          ·
            refine ⟨748481182854202402698829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997974910472269870265105 748481182854202402698829)
            ·
              refine ⟨280680443570325901012061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 748481182854202402698829 280680443570325901012061)
              ·
                refine ⟨105255166338872212879523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280680443570325901012061 105255166338872212879523)
                ·
                  rfl

theorem cell19_345910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_345910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345910 prefixEnd_345910 := by exact prefixLift 345910
  have htrace : WordTrace (prefixWord ++ tailWord_345910) baseStart_345910 baseEnd_345910 := by
    simpa [prefixWord, tailWord_345910, baseEnd_345910] using wordTrace_append hprefix tailTrace_345910
  have hstable : (prefixWord ++ tailWord_345910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345910).length < 2 ^ (prefixWord ++ tailWord_345910).sum := by decide
  have hdescent : baseEnd_345910 < baseStart_345910 := by decide
  rcases family_descends (prefixWord ++ tailWord_345910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345916 : List Nat := [2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_345916 : Nat := 118140960795 + 345916 * 2 ^ 59
def prefixEnd_345916 : Nat := 4983230072969 + 3 ^ 40 * 345916 * 2
def baseEnd_345916 : Nat := 105256992047865976746173

theorem tailTrace_345916 : CollatzResearch.WordTrace tailWord_345916 prefixEnd_345916 105256992047865976746173 := by
  unfold tailWord_345916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6308296507406442297244801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8411062009875256396326401 6308296507406442297244801)
  ·
    refine ⟨4731222380554831722933601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6308296507406442297244801 4731222380554831722933601)
    ·
      refine ⟨3548416785416123792200201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4731222380554831722933601 3548416785416123792200201)
      ·
        refine ⟨2661312589062092844150151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3548416785416123792200201 2661312589062092844150151)
        ·
          refine ⟨3991968883593139266225227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661312589062092844150151 3991968883593139266225227)
          ·
            refine ⟨5987953325389708899337841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991968883593139266225227 5987953325389708899337841)
            ·
              refine ⟨4490964994042281674503381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5987953325389708899337841 4490964994042281674503381)
              ·
                refine ⟨105256992047865976746173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4490964994042281674503381 105256992047865976746173)
                ·
                  rfl

theorem cell19_345916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_345916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_345916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_345916 prefixEnd_345916 := by exact prefixLift 345916
  have htrace : WordTrace (prefixWord ++ tailWord_345916) baseStart_345916 baseEnd_345916 := by
    simpa [prefixWord, tailWord_345916, baseEnd_345916] using wordTrace_append hprefix tailTrace_345916
  have hstable : (prefixWord ++ tailWord_345916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345916).length < 2 ^ (prefixWord ++ tailWord_345916).sum := by decide
  have hdescent : baseEnd_345916 < baseStart_345916 := by decide
  rcases family_descends (prefixWord ++ tailWord_345916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346140 : List Nat := [2, 2, 3, 1, 3, 3, 2, 3]
def baseStart_346140 : Nat := 118140960795 + 346140 * 2 ^ 59
def prefixEnd_346140 : Nat := 4983230072969 + 3 ^ 40 * 346140 * 2
def baseEnd_346140 : Nat := 105325151850299827767785

theorem tailTrace_346140 : CollatzResearch.WordTrace tailWord_346140 prefixEnd_346140 105325151850299827767785 := by
  unfold tailWord_346140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6312381483000685425321937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8416508644000913900429249 6312381483000685425321937)
  ·
    refine ⟨4734286112250514068991453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6312381483000685425321937 4734286112250514068991453)
    ·
      refine ⟨1775357292093942775871795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4734286112250514068991453 1775357292093942775871795)
      ·
        refine ⟨2663035938140914163807693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775357292093942775871795 2663035938140914163807693)
        ·
          refine ⟨998638476802842811427885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2663035938140914163807693 998638476802842811427885)
          ·
            refine ⟨374489428801066054285457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 998638476802842811427885 374489428801066054285457)
            ·
              refine ⟨280867071600799540714093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374489428801066054285457 280867071600799540714093)
              ·
                refine ⟨105325151850299827767785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280867071600799540714093 105325151850299827767785)
                ·
                  rfl

theorem cell19_346140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_346140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346140 prefixEnd_346140 := by exact prefixLift 346140
  have htrace : WordTrace (prefixWord ++ tailWord_346140) baseStart_346140 baseEnd_346140 := by
    simpa [prefixWord, tailWord_346140, baseEnd_346140] using wordTrace_append hprefix tailTrace_346140
  have hstable : (prefixWord ++ tailWord_346140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346140).length < 2 ^ (prefixWord ++ tailWord_346140).sum := by decide
  have hdescent : baseEnd_346140 < baseStart_346140 := by decide
  rcases family_descends (prefixWord ++ tailWord_346140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346218 : List Nat := [3, 1, 3, 2, 4, 6]
def baseStart_346218 : Nat := 118140960795 + 346218 * 2 ^ 59
def prefixEnd_346218 : Nat := 4983230072969 + 3 ^ 40 * 346218 * 2
def baseEnd_346218 : Nat := 11705431785246528670471

theorem tailTrace_346218 : CollatzResearch.WordTrace tailWord_346218 prefixEnd_346218 11705431785246528670471 := by
  unfold tailWord_346218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156901964929697542995827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8418405239812526781322205 3156901964929697542995827)
  ·
    refine ⟨4735352947394546314493741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3156901964929697542995827 4735352947394546314493741)
    ·
      refine ⟨1775757355272954867935153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4735352947394546314493741 1775757355272954867935153)
      ·
        refine ⟨1331818016454716150951365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1775757355272954867935153 1331818016454716150951365)
        ·
          refine ⟨249715878085259278303381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1331818016454716150951365 249715878085259278303381)
          ·
            refine ⟨11705431785246528670471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 249715878085259278303381 11705431785246528670471)
            ·
              rfl

theorem cell19_346218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 6].length) (baseStart_346218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346218 prefixEnd_346218 := by exact prefixLift 346218
  have htrace : WordTrace (prefixWord ++ tailWord_346218) baseStart_346218 baseEnd_346218 := by
    simpa [prefixWord, tailWord_346218, baseEnd_346218] using wordTrace_append hprefix tailTrace_346218
  have hstable : (prefixWord ++ tailWord_346218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346218).length < 2 ^ (prefixWord ++ tailWord_346218).sum := by decide
  have hdescent : baseEnd_346218 < baseStart_346218 := by decide
  rcases family_descends (prefixWord ++ tailWord_346218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346237 : List Nat := [1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_346237 : Nat := 118140960795 + 346237 * 2 ^ 59
def prefixEnd_346237 : Nat := 4983230072969 + 3 ^ 40 * 346237 * 2
def baseEnd_346237 : Nat := 105354667479032343611965

theorem tailTrace_346237 : CollatzResearch.WordTrace tailWord_346237 prefixEnd_346237 105354667479032343611965 := by
  unfold tailWord_346237
  simp only [CollatzResearch.WordTrace]
  refine ⟨12628300846649956416924965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8418867231099970944616643 12628300846649956416924965)
  ·
    refine ⟨2367806408746866828173431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12628300846649956416924965 2367806408746866828173431)
    ·
      refine ⟨3551709613120300242260147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367806408746866828173431 3551709613120300242260147)
      ·
        refine ⟨5327564419680450363390221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551709613120300242260147 5327564419680450363390221)
        ·
          refine ⟨1997836657380168886271333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5327564419680450363390221 1997836657380168886271333)
          ·
            refine ⟨374594373258781666175875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1997836657380168886271333 374594373258781666175875)
            ·
              refine ⟨561891559888172499263813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374594373258781666175875 561891559888172499263813)
              ·
                refine ⟨105354667479032343611965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561891559888172499263813 105354667479032343611965)
                ·
                  rfl

theorem cell19_346237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_346237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346237 prefixEnd_346237 := by exact prefixLift 346237
  have htrace : WordTrace (prefixWord ++ tailWord_346237) baseStart_346237 baseEnd_346237 := by
    simpa [prefixWord, tailWord_346237, baseEnd_346237] using wordTrace_append hprefix tailTrace_346237
  have hstable : (prefixWord ++ tailWord_346237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346237).length < 2 ^ (prefixWord ++ tailWord_346237).sum := by decide
  have hdescent : baseEnd_346237 < baseStart_346237 := by decide
  rcases family_descends (prefixWord ++ tailWord_346237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346254 : List Nat := [4, 1, 1, 3, 3, 1, 3, 3]
def baseStart_346254 : Nat := 118140960795 + 346254 * 2 ^ 59
def prefixEnd_346254 : Nat := 4983230072969 + 3 ^ 40 * 346254 * 2
def baseEnd_346254 : Nat := 105359840321181341234141

theorem tailTrace_346254 : CollatzResearch.WordTrace tailWord_346254 prefixEnd_346254 105359840321181341234141 := by
  unfold tailWord_346254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578615110948546040036727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8419280591725578880195877 1578615110948546040036727)
  ·
    refine ⟨2367922666422819060055091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1578615110948546040036727 2367922666422819060055091)
    ·
      refine ⟨3551883999634228590082637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367922666422819060055091 3551883999634228590082637)
      ·
        refine ⟨1331956499862835721280989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3551883999634228590082637 1331956499862835721280989)
        ·
          refine ⟨499483687448563395480371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1331956499862835721280989 499483687448563395480371)
          ·
            refine ⟨749225531172845093220557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499483687448563395480371 749225531172845093220557)
            ·
              refine ⟨280959574189816909957709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749225531172845093220557 280959574189816909957709)
              ·
                refine ⟨105359840321181341234141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280959574189816909957709 105359840321181341234141)
                ·
                  rfl

theorem cell19_346254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_346254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346254 prefixEnd_346254 := by exact prefixLift 346254
  have htrace : WordTrace (prefixWord ++ tailWord_346254) baseStart_346254 baseEnd_346254 := by
    simpa [prefixWord, tailWord_346254, baseEnd_346254] using wordTrace_append hprefix tailTrace_346254
  have hstable : (prefixWord ++ tailWord_346254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346254).length < 2 ^ (prefixWord ++ tailWord_346254).sum := by decide
  have hdescent : baseEnd_346254 < baseStart_346254 := by decide
  rcases family_descends (prefixWord ++ tailWord_346254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346370 : List Nat := [3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_346370 : Nat := 118140960795 + 346370 * 2 ^ 59
def prefixEnd_346370 : Nat := 4983230072969 + 3 ^ 40 * 346370 * 2
def baseEnd_346370 : Nat := 105395137361727442656047

theorem tailTrace_346370 : CollatzResearch.WordTrace tailWord_346370 prefixEnd_346370 105395137361727442656047 := by
  unfold tailWord_346370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3158287938792030032879141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8422101170112080087677709 3158287938792030032879141)
  ·
    refine ⟨592178988523505631164839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3158287938792030032879141 592178988523505631164839)
    ·
      refine ⟨888268482785258446747259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592178988523505631164839 888268482785258446747259)
      ·
        refine ⟨1332402724177887670120889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888268482785258446747259 1332402724177887670120889)
        ·
          refine ⟨999302043133415752590667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1332402724177887670120889 999302043133415752590667)
          ·
            refine ⟨1498953064700123628886001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999302043133415752590667 1498953064700123628886001)
            ·
              refine ⟨1124214798525092721664501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498953064700123628886001 1124214798525092721664501)
              ·
                refine ⟨105395137361727442656047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1124214798525092721664501 105395137361727442656047)
                ·
                  rfl

theorem cell19_346370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_346370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346370 prefixEnd_346370 := by exact prefixLift 346370
  have htrace : WordTrace (prefixWord ++ tailWord_346370) baseStart_346370 baseEnd_346370 := by
    simpa [prefixWord, tailWord_346370, baseEnd_346370] using wordTrace_append hprefix tailTrace_346370
  have hstable : (prefixWord ++ tailWord_346370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346370).length < 2 ^ (prefixWord ++ tailWord_346370).sum := by decide
  have hdescent : baseEnd_346370 < baseStart_346370 := by decide
  rcases family_descends (prefixWord ++ tailWord_346370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346505 : List Nat := [1, 2, 1, 1, 6, 3, 5]
def baseStart_346505 : Nat := 118140960795 + 346505 * 2 ^ 59
def prefixEnd_346505 : Nat := 4983230072969 + 3 ^ 40 * 346505 * 2
def baseEnd_346505 : Nat := 35145405271362376551893

theorem tailTrace_346505 : CollatzResearch.WordTrace tailWord_346505 prefixEnd_346505 35145405271362376551893 := by
  unfold tailWord_346505
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638075609679038187680969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8425383739786025458453979 12638075609679038187680969)
  ·
    refine ⟨9478556707259278640760727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12638075609679038187680969 9478556707259278640760727)
    ·
      refine ⟨14217835060888917961141091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9478556707259278640760727 14217835060888917961141091)
      ·
        refine ⟨21326752591333376941711637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14217835060888917961141091 21326752591333376941711637)
        ·
          refine ⟨999691527718752044142733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21326752591333376941711637 999691527718752044142733)
          ·
            refine ⟨374884322894532016553525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 999691527718752044142733 374884322894532016553525)
            ·
              refine ⟨35145405271362376551893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 374884322894532016553525 35145405271362376551893)
              ·
                rfl

theorem cell19_346505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_346505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346505 prefixEnd_346505 := by exact prefixLift 346505
  have htrace : WordTrace (prefixWord ++ tailWord_346505) baseStart_346505 baseEnd_346505 := by
    simpa [prefixWord, tailWord_346505, baseEnd_346505] using wordTrace_append hprefix tailTrace_346505
  have hstable : (prefixWord ++ tailWord_346505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346505).length < 2 ^ (prefixWord ++ tailWord_346505).sum := by decide
  have hdescent : baseEnd_346505 < baseStart_346505 := by decide
  rcases family_descends (prefixWord ++ tailWord_346505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346507 : List Nat := [1, 1, 1, 1, 4, 4, 7]
def baseStart_346507 : Nat := 118140960795 + 346507 * 2 ^ 59
def prefixEnd_346507 : Nat := 4983230072969 + 3 ^ 40 * 346507 * 2
def baseEnd_346507 : Nat := 35145608127917239203743

theorem tailTrace_346507 : CollatzResearch.WordTrace tailWord_346507 prefixEnd_346507 35145608127917239203743 := by
  unfold tailWord_346507
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638148555671792529253775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8425432370447861686169183 12638148555671792529253775)
  ·
    refine ⟨18957222833507688793880663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12638148555671792529253775 18957222833507688793880663)
    ·
      refine ⟨28435834250261533190820995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18957222833507688793880663 28435834250261533190820995)
      ·
        refine ⟨42653751375392299786231493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28435834250261533190820995 42653751375392299786231493)
        ·
          refine ⟨7997578382886056209918405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42653751375392299786231493 7997578382886056209918405)
          ·
            refine ⟨1499545946791135539359701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7997578382886056209918405 1499545946791135539359701)
            ·
              refine ⟨35145608127917239203743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1499545946791135539359701 35145608127917239203743)
              ·
                rfl

theorem cell19_346507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_346507 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346507 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346507 prefixEnd_346507 := by exact prefixLift 346507
  have htrace : WordTrace (prefixWord ++ tailWord_346507) baseStart_346507 baseEnd_346507 := by
    simpa [prefixWord, tailWord_346507, baseEnd_346507] using wordTrace_append hprefix tailTrace_346507
  have hstable : (prefixWord ++ tailWord_346507).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346507).length < 2 ^ (prefixWord ++ tailWord_346507).sum := by decide
  have hdescent : baseEnd_346507 < baseStart_346507 := by decide
  rcases family_descends (prefixWord ++ tailWord_346507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346581 : List Nat := [1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_346581 : Nat := 118140960795 + 346581 * 2 ^ 59
def prefixEnd_346581 : Nat := 4983230072969 + 3 ^ 40 * 346581 * 2
def baseEnd_346581 : Nat := 105459341461341471966583

theorem tailTrace_346581 : CollatzResearch.WordTrace tailWord_346581 prefixEnd_346581 105459341461341471966583 := by
  unfold tailWord_346581
  simp only [CollatzResearch.WordTrace]
  refine ⟨12640847557403703167447597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8427231704935802111631731 12640847557403703167447597)
  ·
    refine ⟨4740317834026388687792849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12640847557403703167447597 4740317834026388687792849)
    ·
      refine ⟨3555238375519791515844637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4740317834026388687792849 3555238375519791515844637)
      ·
        refine ⟨1333214390819921818441739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3555238375519791515844637 1333214390819921818441739)
        ·
          refine ⟨1999821586229882727662609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333214390819921818441739 1999821586229882727662609)
          ·
            refine ⟨1499866189672412045746957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1999821586229882727662609 1499866189672412045746957)
            ·
              refine ⟨562449821127154517155109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1499866189672412045746957 562449821127154517155109)
              ·
                refine ⟨105459341461341471966583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 562449821127154517155109 105459341461341471966583)
                ·
                  rfl

theorem cell19_346581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_346581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346581 prefixEnd_346581 := by exact prefixLift 346581
  have htrace : WordTrace (prefixWord ++ tailWord_346581) baseStart_346581 baseEnd_346581 := by
    simpa [prefixWord, tailWord_346581, baseEnd_346581] using wordTrace_append hprefix tailTrace_346581
  have hstable : (prefixWord ++ tailWord_346581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346581).length < 2 ^ (prefixWord ++ tailWord_346581).sum := by decide
  have hdescent : baseEnd_346581 < baseStart_346581 := by decide
  rcases family_descends (prefixWord ++ tailWord_346581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346594 : List Nat := [3, 3, 3, 2, 1, 1, 3, 3]
def baseStart_346594 : Nat := 118140960795 + 346594 * 2 ^ 59
def prefixEnd_346594 : Nat := 4983230072969 + 3 ^ 40 * 346594 * 2
def baseEnd_346594 : Nat := 105463297164161293677659

theorem tailTrace_346594 : CollatzResearch.WordTrace tailWord_346594 prefixEnd_346594 105463297164161293677659 := by
  unfold tailWord_346594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160330426589151596917709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8427547804237737591780557 3160330426589151596917709)
  ·
    refine ⟨1185123909970931848844141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3160330426589151596917709 1185123909970931848844141)
    ·
      refine ⟨444421466239099443316553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1185123909970931848844141 444421466239099443316553)
      ·
        refine ⟨333316099679324582487415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444421466239099443316553 333316099679324582487415)
        ·
          refine ⟨499974149518986873731123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333316099679324582487415 499974149518986873731123)
          ·
            refine ⟨749961224278480310596685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499974149518986873731123 749961224278480310596685)
            ·
              refine ⟨281235459104430116473757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749961224278480310596685 281235459104430116473757)
              ·
                refine ⟨105463297164161293677659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281235459104430116473757 105463297164161293677659)
                ·
                  rfl

theorem cell19_346594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_346594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346594 prefixEnd_346594 := by exact prefixLift 346594
  have htrace : WordTrace (prefixWord ++ tailWord_346594) baseStart_346594 baseEnd_346594 := by
    simpa [prefixWord, tailWord_346594, baseEnd_346594] using wordTrace_append hprefix tailTrace_346594
  have hstable : (prefixWord ++ tailWord_346594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346594).length < 2 ^ (prefixWord ++ tailWord_346594).sum := by decide
  have hdescent : baseEnd_346594 < baseStart_346594 := by decide
  rcases family_descends (prefixWord ++ tailWord_346594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346621 : List Nat := [1, 4, 1, 1, 1, 3, 8]
def baseStart_346621 : Nat := 118140960795 + 346621 * 2 ^ 59
def prefixEnd_346621 : Nat := 4983230072969 + 3 ^ 40 * 346621 * 2
def baseEnd_346621 : Nat := 35157170951544410359195

theorem tailTrace_346621 : CollatzResearch.WordTrace tailWord_346621 prefixEnd_346621 35157170951544410359195 := by
  unfold tailWord_346621
  simp only [CollatzResearch.WordTrace]
  refine ⟨12642306477258789998903717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8428204318172526665935811 12642306477258789998903717)
  ·
    refine ⟨2370432464486023124794447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12642306477258789998903717 2370432464486023124794447)
    ·
      refine ⟨3555648696729034687191671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370432464486023124794447 3555648696729034687191671)
      ·
        refine ⟨5333473045093552030787507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555648696729034687191671 5333473045093552030787507)
        ·
          refine ⟨8000209567640328046181261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5333473045093552030787507 8000209567640328046181261)
          ·
            refine ⟨3000078587865123017317973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8000209567640328046181261 3000078587865123017317973)
            ·
              refine ⟨35157170951544410359195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3000078587865123017317973 35157170951544410359195)
              ·
                rfl

theorem cell19_346621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_346621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346621 prefixEnd_346621 := by exact prefixLift 346621
  have htrace : WordTrace (prefixWord ++ tailWord_346621) baseStart_346621 baseEnd_346621 := by
    simpa [prefixWord, tailWord_346621, baseEnd_346621] using wordTrace_append hprefix tailTrace_346621
  have hstable : (prefixWord ++ tailWord_346621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346621).length < 2 ^ (prefixWord ++ tailWord_346621).sum := by decide
  have hdescent : baseEnd_346621 < baseStart_346621 := by decide
  rcases family_descends (prefixWord ++ tailWord_346621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346695 : List Nat := [1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_346695 : Nat := 118140960795 + 346695 * 2 ^ 59
def prefixEnd_346695 : Nat := 4983230072969 + 3 ^ 40 * 346695 * 2
def baseEnd_346695 : Nat := 105494029932222985432939

theorem tailTrace_346695 : CollatzResearch.WordTrace tailWord_346695 prefixEnd_346695 105494029932222985432939 := by
  unfold tailWord_346695
  simp only [CollatzResearch.WordTrace]
  refine ⟨12645005478990700637097539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8430003652660467091398359 12645005478990700637097539)
  ·
    refine ⟨18967508218486050955646309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12645005478990700637097539 18967508218486050955646309)
    ·
      refine ⟨3556407790966134554183683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18967508218486050955646309 3556407790966134554183683)
      ·
        refine ⟨5334611686449201831275525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3556407790966134554183683 5334611686449201831275525)
        ·
          refine ⟨1000239691209225343364161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5334611686449201831275525 1000239691209225343364161)
          ·
            refine ⟨750179768406919007523121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000239691209225343364161 750179768406919007523121)
            ·
              refine ⟨562634826305189255642341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750179768406919007523121 562634826305189255642341)
              ·
                refine ⟨105494029932222985432939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 562634826305189255642341 105494029932222985432939)
                ·
                  rfl

theorem cell19_346695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_346695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346695 prefixEnd_346695 := by exact prefixLift 346695
  have htrace : WordTrace (prefixWord ++ tailWord_346695) baseStart_346695 baseEnd_346695 := by
    simpa [prefixWord, tailWord_346695, baseEnd_346695] using wordTrace_append hprefix tailTrace_346695
  have hstable : (prefixWord ++ tailWord_346695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346695).length < 2 ^ (prefixWord ++ tailWord_346695).sum := by decide
  have hdescent : baseEnd_346695 < baseStart_346695 := by decide
  rcases family_descends (prefixWord ++ tailWord_346695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346752 : List Nat := [2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_346752 : Nat := 118140960795 + 346752 * 2 ^ 59
def prefixEnd_346752 : Nat := 4983230072969 + 3 ^ 40 * 346752 * 2
def baseEnd_346752 : Nat := 105511374167663742166117

theorem tailTrace_346752 : CollatzResearch.WordTrace tailWord_346752 prefixEnd_346752 105511374167663742166117 := by
  unfold tailWord_346752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323542219892099685961255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8431389626522799581281673 6323542219892099685961255)
  ·
    refine ⟨9485313329838149528941883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6323542219892099685961255 9485313329838149528941883)
    ·
      refine ⟨14227969994757224293412825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9485313329838149528941883 14227969994757224293412825)
      ·
        refine ⟨10670977496067918220059619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14227969994757224293412825 10670977496067918220059619)
        ·
          refine ⟨16006466244101877330089429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10670977496067918220059619 16006466244101877330089429)
          ·
            refine ⟨375151552596137749923971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16006466244101877330089429 375151552596137749923971)
            ·
              refine ⟨562727328894206624885957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375151552596137749923971 562727328894206624885957)
              ·
                refine ⟨105511374167663742166117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 562727328894206624885957 105511374167663742166117)
                ·
                  rfl

theorem cell19_346752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_346752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346752 prefixEnd_346752 := by exact prefixLift 346752
  have htrace : WordTrace (prefixWord ++ tailWord_346752) baseStart_346752 baseEnd_346752 := by
    simpa [prefixWord, tailWord_346752, baseEnd_346752] using wordTrace_append hprefix tailTrace_346752
  have hstable : (prefixWord ++ tailWord_346752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346752).length < 2 ^ (prefixWord ++ tailWord_346752).sum := by decide
  have hdescent : baseEnd_346752 < baseStart_346752 := by decide
  rcases family_descends (prefixWord ++ tailWord_346752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346826 : List Nat := [3, 1, 2, 1, 4, 3, 2, 3]
def baseStart_346826 : Nat := 118140960795 + 346826 * 2 ^ 59
def prefixEnd_346826 : Nat := 4983230072969 + 3 ^ 40 * 346826 * 2
def baseEnd_346826 : Nat := 105533891245253496521471

theorem tailTrace_346826 : CollatzResearch.WordTrace tailWord_346826 prefixEnd_346826 105533891245253496521471 := by
  unfold tailWord_346826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162445860379027502529083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8433188961010740006744221 3162445860379027502529083)
  ·
    refine ⟨4743668790568541253793625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162445860379027502529083 4743668790568541253793625)
    ·
      refine ⟨3557751592926405940345219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4743668790568541253793625 3557751592926405940345219)
      ·
        refine ⟨5336627389389608910517829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557751592926405940345219 5336627389389608910517829)
        ·
          refine ⟨1000617635510551670722093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5336627389389608910517829 1000617635510551670722093)
          ·
            refine ⟨375231613316456876520785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1000617635510551670722093 375231613316456876520785)
            ·
              refine ⟨281423709987342657390589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375231613316456876520785 281423709987342657390589)
              ·
                refine ⟨105533891245253496521471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281423709987342657390589 105533891245253496521471)
                ·
                  rfl

theorem cell19_346826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_346826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346826 prefixEnd_346826 := by exact prefixLift 346826
  have htrace : WordTrace (prefixWord ++ tailWord_346826) baseStart_346826 baseEnd_346826 := by
    simpa [prefixWord, tailWord_346826, baseEnd_346826] using wordTrace_append hprefix tailTrace_346826
  have hstable : (prefixWord ++ tailWord_346826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346826).length < 2 ^ (prefixWord ++ tailWord_346826).sum := by decide
  have hdescent : baseEnd_346826 < baseStart_346826 := by decide
  rcases family_descends (prefixWord ++ tailWord_346826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346828 : List Nat := [2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_346828 : Nat := 118140960795 + 346828 * 2 ^ 59
def prefixEnd_346828 : Nat := 4983230072969 + 3 ^ 40 * 346828 * 2
def baseEnd_346828 : Nat := 105534499814918084477021

theorem tailTrace_346828 : CollatzResearch.WordTrace tailWord_346828 prefixEnd_346828 105534499814918084477021 := by
  unfold tailWord_346828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6324928193754432175844569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8433237591672576234459425 6324928193754432175844569)
  ·
    refine ⟨4743696145315824131883427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6324928193754432175844569 4743696145315824131883427)
    ·
      refine ⟨7115544217973736197825141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743696145315824131883427 7115544217973736197825141)
      ·
        refine ⟨667082270435037768546107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7115544217973736197825141 667082270435037768546107)
        ·
          refine ⟨1000623405652556652819161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667082270435037768546107 1000623405652556652819161)
          ·
            refine ⟨750467554239417489614371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000623405652556652819161 750467554239417489614371)
            ·
              refine ⟨1125701331359126234421557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750467554239417489614371 1125701331359126234421557)
              ·
                refine ⟨105534499814918084477021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1125701331359126234421557 105534499814918084477021)
                ·
                  rfl

theorem cell19_346828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_346828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346828 prefixEnd_346828 := by exact prefixLift 346828
  have htrace : WordTrace (prefixWord ++ tailWord_346828) baseStart_346828 baseEnd_346828 := by
    simpa [prefixWord, tailWord_346828, baseEnd_346828] using wordTrace_append hprefix tailTrace_346828
  have hstable : (prefixWord ++ tailWord_346828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346828).length < 2 ^ (prefixWord ++ tailWord_346828).sum := by decide
  have hdescent : baseEnd_346828 < baseStart_346828 := by decide
  rcases family_descends (prefixWord ++ tailWord_346828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346849 : List Nat := [1, 2, 3, 1, 4, 1, 7]
def baseStart_346849 : Nat := 118140960795 + 346849 * 2 ^ 59
def prefixEnd_346849 : Nat := 4983230072969 + 3 ^ 40 * 346849 * 2
def baseEnd_346849 : Nat := 35180296598798752670099

theorem tailTrace_346849 : CollatzResearch.WordTrace tailWord_346849 prefixEnd_346849 35180296598798752670099 := by
  unfold tailWord_346849
  simp only [CollatzResearch.WordTrace]
  refine ⟨12650622320432784938203601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8433748213621856625469067 12650622320432784938203601)
  ·
    refine ⟨9487966740324588703652701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12650622320432784938203601 9487966740324588703652701)
    ·
      refine ⟨3557987527621720763869763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9487966740324588703652701 3557987527621720763869763)
      ·
        refine ⟨5336981291432581145804645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557987527621720763869763 5336981291432581145804645)
        ·
          refine ⟨1000683992143608964838371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5336981291432581145804645 1000683992143608964838371)
          ·
            refine ⟨1501025988215413447257557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000683992143608964838371 1501025988215413447257557)
            ·
              refine ⟨35180296598798752670099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1501025988215413447257557 35180296598798752670099)
              ·
                rfl

theorem cell19_346849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_346849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346849 prefixEnd_346849 := by exact prefixLift 346849
  have htrace : WordTrace (prefixWord ++ tailWord_346849) baseStart_346849 baseEnd_346849 := by
    simpa [prefixWord, tailWord_346849, baseEnd_346849] using wordTrace_append hprefix tailTrace_346849
  have hstable : (prefixWord ++ tailWord_346849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346849).length < 2 ^ (prefixWord ++ tailWord_346849).sum := by decide
  have hdescent : baseEnd_346849 < baseStart_346849 := by decide
  rcases family_descends (prefixWord ++ tailWord_346849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346866 : List Nat := [3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_346866 : Nat := 118140960795 + 346866 * 2 ^ 59
def prefixEnd_346866 : Nat := 4983230072969 + 3 ^ 40 * 346866 * 2
def baseEnd_346866 : Nat := 105546062638545255632473

theorem tailTrace_346866 : CollatzResearch.WordTrace tailWord_346866 prefixEnd_346866 105546062638545255632473 := by
  unfold tailWord_346866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162810590342799210393113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8434161574247464561048301 3162810590342799210393113)
  ·
    refine ⟨2372107942757099407794835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3162810590342799210393113 2372107942757099407794835)
    ·
      refine ⟨3558161914135649111692253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2372107942757099407794835 3558161914135649111692253)
      ·
        refine ⟨1334310717800868416884595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3558161914135649111692253 1334310717800868416884595)
        ·
          refine ⟨2001466076701302625326893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334310717800868416884595 2001466076701302625326893)
          ·
            refine ⟨750549778762988484497585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2001466076701302625326893 750549778762988484497585)
            ·
              refine ⟨562912334072241363373189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750549778762988484497585 562912334072241363373189)
              ·
                refine ⟨105546062638545255632473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 562912334072241363373189 105546062638545255632473)
                ·
                  rfl

theorem cell19_346866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_346866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346866 prefixEnd_346866 := by exact prefixLift 346866
  have htrace : WordTrace (prefixWord ++ tailWord_346866) baseStart_346866 baseEnd_346866 := by
    simpa [prefixWord, tailWord_346866, baseEnd_346866] using wordTrace_append hprefix tailTrace_346866
  have hstable : (prefixWord ++ tailWord_346866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346866).length < 2 ^ (prefixWord ++ tailWord_346866).sum := by decide
  have hdescent : baseEnd_346866 < baseStart_346866 := by decide
  rcases family_descends (prefixWord ++ tailWord_346866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346997 : List Nat := [1, 3, 4, 1, 1, 4, 2, 3]
def baseStart_346997 : Nat := 118140960795 + 346997 * 2 ^ 59
def prefixEnd_346997 : Nat := 4983230072969 + 3 ^ 40 * 346997 * 2
def baseEnd_346997 : Nat := 105585923951575766721005

theorem tailTrace_346997 : CollatzResearch.WordTrace tailWord_346997 prefixEnd_346997 105585923951575766721005 := by
  unfold tailWord_346997
  simp only [CollatzResearch.WordTrace]
  refine ⟨12656020323896606214591245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8437346882597737476394163 12656020323896606214591245)
  ·
    refine ⟨4746007621461227330471717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12656020323896606214591245 4746007621461227330471717)
    ·
      refine ⟨889876429023980124463447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4746007621461227330471717 889876429023980124463447)
      ·
        refine ⟨1334814643535970186695171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889876429023980124463447 1334814643535970186695171)
        ·
          refine ⟨2002221965303955280042757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334814643535970186695171 2002221965303955280042757)
          ·
            refine ⟨375416618494491615008017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2002221965303955280042757 375416618494491615008017)
            ·
              refine ⟨281562463870868711256013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375416618494491615008017 281562463870868711256013)
              ·
                refine ⟨105585923951575766721005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281562463870868711256013 105585923951575766721005)
                ·
                  rfl

theorem cell19_346997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_346997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_346997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_346997 prefixEnd_346997 := by exact prefixLift 346997
  have htrace : WordTrace (prefixWord ++ tailWord_346997) baseStart_346997 baseEnd_346997 := by
    simpa [prefixWord, tailWord_346997, baseEnd_346997] using wordTrace_append hprefix tailTrace_346997
  have hstable : (prefixWord ++ tailWord_346997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346997).length < 2 ^ (prefixWord ++ tailWord_346997).sum := by decide
  have hdescent : baseEnd_346997 < baseStart_346997 := by decide
  rcases family_descends (prefixWord ++ tailWord_346997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347001 : List Nat := [1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_347001 : Nat := 118140960795 + 347001 * 2 ^ 59
def prefixEnd_347001 : Nat := 4983230072969 + 3 ^ 40 * 347001 * 2
def baseEnd_347001 : Nat := 105587141090904942632105

theorem tailTrace_347001 : CollatzResearch.WordTrace tailWord_347001 prefixEnd_347001 105587141090904942632105 := by
  unfold tailWord_347001
  simp only [CollatzResearch.WordTrace]
  refine ⟨12656166215882114897736857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8437444143921409931824571 12656166215882114897736857)
  ·
    refine ⟨9492124661911586173302643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12656166215882114897736857 9492124661911586173302643)
    ·
      refine ⟨14238186992867379259953965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9492124661911586173302643 14238186992867379259953965)
      ·
        refine ⟨5339320122325267222482737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14238186992867379259953965 5339320122325267222482737)
        ·
          refine ⟨4004490091743950416862053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5339320122325267222482737 4004490091743950416862053)
          ·
            refine ⟨750841892201990703161635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4004490091743950416862053 750841892201990703161635)
            ·
              refine ⟨1126262838302986054742453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750841892201990703161635 1126262838302986054742453)
              ·
                refine ⟨105587141090904942632105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1126262838302986054742453 105587141090904942632105)
                ·
                  rfl

theorem cell19_347001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_347001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347001 prefixEnd_347001 := by exact prefixLift 347001
  have htrace : WordTrace (prefixWord ++ tailWord_347001) baseStart_347001 baseEnd_347001 := by
    simpa [prefixWord, tailWord_347001, baseEnd_347001] using wordTrace_append hprefix tailTrace_347001
  have hstable : (prefixWord ++ tailWord_347001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347001).length < 2 ^ (prefixWord ++ tailWord_347001).sum := by decide
  have hdescent : baseEnd_347001 < baseStart_347001 := by decide
  rcases family_descends (prefixWord ++ tailWord_347001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347018 : List Nat := [3, 1, 2, 4, 1, 3, 5]
def baseStart_347018 : Nat := 118140960795 + 347018 * 2 ^ 59
def prefixEnd_347018 : Nat := 4983230072969 + 3 ^ 40 * 347018 * 2
def baseEnd_347018 : Nat := 35197437977684646751427

theorem tailTrace_347018 : CollatzResearch.WordTrace tailWord_347018 prefixEnd_347018 35197437977684646751427 := by
  unfold tailWord_347018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3164196564205131700276427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8437857504547017867403805 3164196564205131700276427)
  ·
    refine ⟨4746294846307697550414641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3164196564205131700276427 4746294846307697550414641)
    ·
      refine ⟨3559721134730773162810981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4746294846307697550414641 3559721134730773162810981)
      ·
        refine ⟨667447712762019968027059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3559721134730773162810981 667447712762019968027059)
        ·
          refine ⟨1001171569143029952040589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667447712762019968027059 1001171569143029952040589)
          ·
            refine ⟨375439338428636232015221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1001171569143029952040589 375439338428636232015221)
            ·
              refine ⟨35197437977684646751427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 375439338428636232015221 35197437977684646751427)
              ·
                rfl

theorem cell19_347018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_347018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347018 prefixEnd_347018 := by exact prefixLift 347018
  have htrace : WordTrace (prefixWord ++ tailWord_347018) baseStart_347018 baseEnd_347018 := by
    simpa [prefixWord, tailWord_347018, baseEnd_347018] using wordTrace_append hprefix tailTrace_347018
  have hstable : (prefixWord ++ tailWord_347018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347018).length < 2 ^ (prefixWord ++ tailWord_347018).sum := by decide
  have hdescent : baseEnd_347018 < baseStart_347018 := by decide
  rcases family_descends (prefixWord ++ tailWord_347018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347039 : List Nat := [1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_347039 : Nat := 118140960795 + 347039 * 2 ^ 59
def prefixEnd_347039 : Nat := 4983230072969 + 3 ^ 40 * 347039 * 2
def baseEnd_347039 : Nat := 105598703914532113787557

theorem tailTrace_347039 : CollatzResearch.WordTrace tailWord_347039 prefixEnd_347039 105598703914532113787557 := by
  unfold tailWord_347039
  simp only [CollatzResearch.WordTrace]
  refine ⟨12657552189744447387620171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8438368126496298258413447 12657552189744447387620171)
  ·
    refine ⟨18986328284616671081430257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12657552189744447387620171 18986328284616671081430257)
    ·
      refine ⟨14239746213462503311072693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18986328284616671081430257 14239746213462503311072693)
      ·
        refine ⟨1334976207512109685413065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14239746213462503311072693 1334976207512109685413065)
        ·
          refine ⟨1001232155634082264059799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1334976207512109685413065 1001232155634082264059799)
          ·
            refine ⟨1501848233451123396089699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001232155634082264059799 1501848233451123396089699)
            ·
              refine ⟨2252772350176685094134549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501848233451123396089699 2252772350176685094134549)
              ·
                refine ⟨105598703914532113787557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2252772350176685094134549 105598703914532113787557)
                ·
                  rfl

theorem cell19_347039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_347039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347039 prefixEnd_347039 := by exact prefixLift 347039
  have htrace : WordTrace (prefixWord ++ tailWord_347039) baseStart_347039 baseEnd_347039 := by
    simpa [prefixWord, tailWord_347039, baseEnd_347039] using wordTrace_append hprefix tailTrace_347039
  have hstable : (prefixWord ++ tailWord_347039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347039).length < 2 ^ (prefixWord ++ tailWord_347039).sum := by decide
  have hdescent : baseEnd_347039 < baseStart_347039 := by decide
  rcases family_descends (prefixWord ++ tailWord_347039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347096 : List Nat := [2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_347096 : Nat := 118140960795 + 347096 * 2 ^ 59
def prefixEnd_347096 : Nat := 4983230072969 + 3 ^ 40 * 347096 * 2
def baseEnd_347096 : Nat := 105616048149972870520735

theorem tailTrace_347096 : CollatzResearch.WordTrace tailWord_347096 prefixEnd_347096 105616048149972870520735 := by
  unfold tailWord_347096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329815575268973061222571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8439754100358630748296761 6329815575268973061222571)
  ·
    refine ⟨9494723362903459591833857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6329815575268973061222571 9494723362903459591833857)
    ·
      refine ⟨7121042522177594693875393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9494723362903459591833857 7121042522177594693875393)
      ·
        refine ⟨5340781891633196020406545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7121042522177594693875393 5340781891633196020406545)
        ·
          refine ⟨4005586418724897015304909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5340781891633196020406545 4005586418724897015304909)
          ·
            refine ⟨1502094907021836380739341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4005586418724897015304909 1502094907021836380739341)
            ·
              refine ⟨563285590133188642777253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1502094907021836380739341 563285590133188642777253)
              ·
                refine ⟨105616048149972870520735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563285590133188642777253 105616048149972870520735)
                ·
                  rfl

theorem cell19_347096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_347096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347096 prefixEnd_347096 := by exact prefixLift 347096
  have htrace : WordTrace (prefixWord ++ tailWord_347096) baseStart_347096 baseEnd_347096 := by
    simpa [prefixWord, tailWord_347096, baseEnd_347096] using wordTrace_append hprefix tailTrace_347096
  have hstable : (prefixWord ++ tailWord_347096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347096).length < 2 ^ (prefixWord ++ tailWord_347096).sum := by decide
  have hdescent : baseEnd_347096 < baseStart_347096 := by decide
  rcases family_descends (prefixWord ++ tailWord_347096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347155 : List Nat := [1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_347155 : Nat := 118140960795 + 347155 * 2 ^ 59
def prefixEnd_347155 : Nat := 4983230072969 + 3 ^ 40 * 347155 * 2
def baseEnd_347155 : Nat := 105634000955078215209463

theorem tailTrace_347155 : CollatzResearch.WordTrace tailWord_347155 prefixEnd_347155 105634000955078215209463 := by
  unfold tailWord_347155
  simp only [CollatzResearch.WordTrace]
  refine ⟨12661783057324199198842919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8441188704882799465895279 12661783057324199198842919)
  ·
    refine ⟨18992674585986298798264379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12661783057324199198842919 18992674585986298798264379)
    ·
      refine ⟨28489011878979448197396569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18992674585986298798264379 28489011878979448197396569)
      ·
        refine ⟨21366758909234586148047427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28489011878979448197396569 21366758909234586148047427)
        ·
          refine ⟨32050138363851879222071141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21366758909234586148047427 32050138363851879222071141)
          ·
            refine ⟨6009400943222227354138339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32050138363851879222071141 6009400943222227354138339)
            ·
              refine ⟨9014101414833341031207509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009400943222227354138339 9014101414833341031207509)
              ·
                refine ⟨105634000955078215209463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9014101414833341031207509 105634000955078215209463)
                ·
                  rfl

theorem cell19_347155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_347155 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347155 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347155 prefixEnd_347155 := by exact prefixLift 347155
  have htrace : WordTrace (prefixWord ++ tailWord_347155) baseStart_347155 baseEnd_347155 := by
    simpa [prefixWord, tailWord_347155, baseEnd_347155] using wordTrace_append hprefix tailTrace_347155
  have hstable : (prefixWord ++ tailWord_347155).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347155).length < 2 ^ (prefixWord ++ tailWord_347155).sum := by decide
  have hdescent : baseEnd_347155 < baseStart_347155 := by decide
  rcases family_descends (prefixWord ++ tailWord_347155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347170 : List Nat := [3, 3, 1, 1, 1, 3, 4, 3]
def baseStart_347170 : Nat := 118140960795 + 347170 * 2 ^ 59
def prefixEnd_347170 : Nat := 4983230072969 + 3 ^ 40 * 347170 * 2
def baseEnd_347170 : Nat := 105638565227562624876089

theorem tailTrace_347170 : CollatzResearch.WordTrace tailWord_347170 prefixEnd_347170 105638565227562624876089 := by
  unfold tailWord_347170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165582538067464190159741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8441553434846571173759309 3165582538067464190159741)
  ·
    refine ⟨1187093451775299071309903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3165582538067464190159741 1187093451775299071309903)
    ·
      refine ⟨1780640177662948606964855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187093451775299071309903 1780640177662948606964855)
      ·
        refine ⟨2670960266494422910447283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780640177662948606964855 2670960266494422910447283)
        ·
          refine ⟨4006440399741634365670925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670960266494422910447283 4006440399741634365670925)
          ·
            refine ⟨1502415149903112887126597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4006440399741634365670925 1502415149903112887126597)
            ·
              refine ⟨281702840606833666336237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1502415149903112887126597 281702840606833666336237)
              ·
                refine ⟨105638565227562624876089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281702840606833666336237 105638565227562624876089)
                ·
                  rfl

theorem cell19_347170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_347170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347170 prefixEnd_347170 := by exact prefixLift 347170
  have htrace : WordTrace (prefixWord ++ tailWord_347170) baseStart_347170 baseEnd_347170 := by
    simpa [prefixWord, tailWord_347170, baseEnd_347170] using wordTrace_append hprefix tailTrace_347170
  have hstable : (prefixWord ++ tailWord_347170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347170).length < 2 ^ (prefixWord ++ tailWord_347170).sum := by decide
  have hdescent : baseEnd_347170 < baseStart_347170 := by decide
  rcases family_descends (prefixWord ++ tailWord_347170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347206 : List Nat := [6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_347206 : Nat := 118140960795 + 347206 * 2 ^ 59
def prefixEnd_347206 : Nat := 4983230072969 + 3 ^ 40 * 347206 * 2
def baseEnd_347206 : Nat := 105649519481525208075991

theorem tailTrace_347206 : CollatzResearch.WordTrace tailWord_347206 prefixEnd_347206 105649519481525208075991 := by
  unfold tailWord_347206
  simp only [CollatzResearch.WordTrace]
  refine ⟨395738849379357340904671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8442428786759623272632981 395738849379357340904671)
  ·
    refine ⟨593608274069036011357007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 395738849379357340904671 593608274069036011357007)
    ·
      refine ⟨890412411103554017035511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593608274069036011357007 890412411103554017035511)
      ·
        refine ⟨1335618616655331025553267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890412411103554017035511 1335618616655331025553267)
        ·
          refine ⟨2003427924982996538329901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335618616655331025553267 2003427924982996538329901)
          ·
            refine ⟨751285471868623701873713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2003427924982996538329901 751285471868623701873713)
            ·
              refine ⟨563464103901467776405285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751285471868623701873713 563464103901467776405285)
              ·
                refine ⟨105649519481525208075991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563464103901467776405285 105649519481525208075991)
                ·
                  rfl

theorem cell19_347206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_347206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347206 prefixEnd_347206 := by exact prefixLift 347206
  have htrace : WordTrace (prefixWord ++ tailWord_347206) baseStart_347206 baseEnd_347206 := by
    simpa [prefixWord, tailWord_347206, baseEnd_347206] using wordTrace_append hprefix tailTrace_347206
  have hstable : (prefixWord ++ tailWord_347206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347206).length < 2 ^ (prefixWord ++ tailWord_347206).sum := by decide
  have hdescent : baseEnd_347206 < baseStart_347206 := by decide
  rcases family_descends (prefixWord ++ tailWord_347206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347231 : List Nat := [1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_347231 : Nat := 118140960795 + 347231 * 2 ^ 59
def prefixEnd_347231 : Nat := 4983230072969 + 3 ^ 40 * 347231 * 2
def baseEnd_347231 : Nat := 105657126602332557520367

theorem tailTrace_347231 : CollatzResearch.WordTrace tailWord_347231 prefixEnd_347231 105657126602332557520367 := by
  unfold tailWord_347231
  simp only [CollatzResearch.WordTrace]
  refine ⟨12664555005048864178609547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8443036670032576119073031 12664555005048864178609547)
  ·
    refine ⟨18996832507573296267914321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12664555005048864178609547 18996832507573296267914321)
    ·
      refine ⟨14247624380679972200935741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18996832507573296267914321 14247624380679972200935741)
      ·
        refine ⟨5342859142754989575350903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14247624380679972200935741 5342859142754989575350903)
        ·
          refine ⟨8014288714132484363026355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5342859142754989575350903 8014288714132484363026355)
          ·
            refine ⟨12021433071198726544539533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014288714132484363026355 12021433071198726544539533)
            ·
              refine ⟨4508037401699522454202325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12021433071198726544539533 4508037401699522454202325)
              ·
                refine ⟨105657126602332557520367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4508037401699522454202325 105657126602332557520367)
                ·
                  rfl

theorem cell19_347231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_347231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347231 prefixEnd_347231 := by exact prefixLift 347231
  have htrace : WordTrace (prefixWord ++ tailWord_347231) baseStart_347231 baseEnd_347231 := by
    simpa [prefixWord, tailWord_347231, baseEnd_347231] using wordTrace_append hprefix tailTrace_347231
  have hstable : (prefixWord ++ tailWord_347231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347231).length < 2 ^ (prefixWord ++ tailWord_347231).sum := by decide
  have hdescent : baseEnd_347231 < baseStart_347231 := by decide
  rcases family_descends (prefixWord ++ tailWord_347231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347265 : List Nat := [1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_347265 : Nat := 118140960795 + 347265 * 2 ^ 59
def prefixEnd_347265 : Nat := 4983230072969 + 3 ^ 40 * 347265 * 2
def baseEnd_347265 : Nat := 105667472286630552764719

theorem tailTrace_347265 : CollatzResearch.WordTrace tailWord_347265 prefixEnd_347265 105667472286630552764719 := by
  unfold tailWord_347265
  simp only [CollatzResearch.WordTrace]
  refine ⟨12665795086925687985347249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8443863391283791990231499 12665795086925687985347249)
  ·
    refine ⟨9499346315194265989010437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12665795086925687985347249 9499346315194265989010437)
    ·
      refine ⟨1781127434098924872939457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9499346315194265989010437 1781127434098924872939457)
      ·
        refine ⟨1335845575574193654704593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1781127434098924872939457 1335845575574193654704593)
        ·
          refine ⟨1001884181680645241028445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335845575574193654704593 1001884181680645241028445)
          ·
            refine ⟨375706568130241965385667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1001884181680645241028445 375706568130241965385667)
            ·
              refine ⟨563559852195362948078501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375706568130241965385667 563559852195362948078501)
              ·
                refine ⟨105667472286630552764719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563559852195362948078501 105667472286630552764719)
                ·
                  rfl

theorem cell19_347265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_347265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347265 prefixEnd_347265 := by exact prefixLift 347265
  have htrace : WordTrace (prefixWord ++ tailWord_347265) baseStart_347265 baseEnd_347265 := by
    simpa [prefixWord, tailWord_347265, baseEnd_347265] using wordTrace_append hprefix tailTrace_347265
  have hstable : (prefixWord ++ tailWord_347265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347265).length < 2 ^ (prefixWord ++ tailWord_347265).sum := by decide
  have hdescent : baseEnd_347265 < baseStart_347265 := by decide
  rcases family_descends (prefixWord ++ tailWord_347265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347364 : List Nat := [2, 3, 1, 1, 1, 2, 9]
def baseStart_347364 : Nat := 118140960795 + 347364 * 2 ^ 59
def prefixEnd_347364 : Nat := 4983230072969 + 3 ^ 40 * 347364 * 2
def baseEnd_347364 : Nat := 35232532161675885521483

theorem tailTrace_347364 : CollatzResearch.WordTrace tailWord_347364 prefixEnd_347364 35232532161675885521483 := by
  unfold tailWord_347364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334702956783513946600573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8446270609044685262134097 6334702956783513946600573)
  ·
    refine ⟨2375513608793817729975215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6334702956783513946600573 2375513608793817729975215)
    ·
      refine ⟨3563270413190726594962823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2375513608793817729975215 3563270413190726594962823)
      ·
        refine ⟨5344905619786089892444235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3563270413190726594962823 5344905619786089892444235)
        ·
          refine ⟨8017358429679134838666353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344905619786089892444235 8017358429679134838666353)
          ·
            refine ⟨6013018822259351128999765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8017358429679134838666353 6013018822259351128999765)
            ·
              refine ⟨35232532161675885521483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6013018822259351128999765 35232532161675885521483)
              ·
                rfl

theorem cell19_347364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_347364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347364 prefixEnd_347364 := by exact prefixLift 347364
  have htrace : WordTrace (prefixWord ++ tailWord_347364) baseStart_347364 baseEnd_347364 := by
    simpa [prefixWord, tailWord_347364, baseEnd_347364] using wordTrace_append hprefix tailTrace_347364
  have hstable : (prefixWord ++ tailWord_347364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347364).length < 2 ^ (prefixWord ++ tailWord_347364).sum := by decide
  have hdescent : baseEnd_347364 < baseStart_347364 := by decide
  rcases family_descends (prefixWord ++ tailWord_347364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347453 : List Nat := [1, 4, 1, 5, 1, 1, 3, 3]
def baseStart_347453 : Nat := 118140960795 + 347453 * 2 ^ 59
def prefixEnd_347453 : Nat := 4983230072969 + 3 ^ 40 * 347453 * 2
def baseEnd_347453 : Nat := 105724677835101820586429

theorem tailTrace_347453 : CollatzResearch.WordTrace tailWord_347453 prefixEnd_347453 105724677835101820586429 := by
  unfold tailWord_347453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12672652010244596093191013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8448434673496397395460675 12672652010244596093191013)
  ·
    refine ⟨2376122251920861767473315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12672652010244596093191013 2376122251920861767473315)
    ·
      refine ⟨3564183377881292651209973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376122251920861767473315 3564183377881292651209973)
      ·
        refine ⟨334142191676371186050935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3564183377881292651209973 334142191676371186050935)
        ·
          refine ⟨501213287514556779076403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334142191676371186050935 501213287514556779076403)
          ·
            refine ⟨751819931271835168614605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501213287514556779076403 751819931271835168614605)
            ·
              refine ⟨281932474226938188230477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 751819931271835168614605 281932474226938188230477)
              ·
                refine ⟨105724677835101820586429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281932474226938188230477 105724677835101820586429)
                ·
                  rfl

theorem cell19_347453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_347453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347453 prefixEnd_347453 := by exact prefixLift 347453
  have htrace : WordTrace (prefixWord ++ tailWord_347453) baseStart_347453 baseEnd_347453 := by
    simpa [prefixWord, tailWord_347453, baseEnd_347453] using wordTrace_append hprefix tailTrace_347453
  have hstable : (prefixWord ++ tailWord_347453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347453).length < 2 ^ (prefixWord ++ tailWord_347453).sum := by decide
  have hdescent : baseEnd_347453 < baseStart_347453 := by decide
  rcases family_descends (prefixWord ++ tailWord_347453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347516 : List Nat := [2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_347516 : Nat := 118140960795 + 347516 * 2 ^ 59
def prefixEnd_347516 : Nat := 4983230072969 + 3 ^ 40 * 347516 * 2
def baseEnd_347516 : Nat := 105743847779536341186257

theorem tailTrace_347516 : CollatzResearch.WordTrace tailWord_347516 prefixEnd_347516 105743847779536341186257 := by
  unfold tailWord_347516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337474904508178926367201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8449966539344238568489601 6337474904508178926367201)
  ·
    refine ⟨4753106178381134194775401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6337474904508178926367201 4753106178381134194775401)
    ·
      refine ⟨3564829633785850646081551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4753106178381134194775401 3564829633785850646081551)
      ·
        refine ⟨5347244450678775969122327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564829633785850646081551 5347244450678775969122327)
        ·
          refine ⟨8020866676018163953683491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347244450678775969122327 8020866676018163953683491)
          ·
            refine ⟨12031300014027245930525237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8020866676018163953683491 12031300014027245930525237)
            ·
              refine ⟨1127934376315054305986741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12031300014027245930525237 1127934376315054305986741)
              ·
                refine ⟨105743847779536341186257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1127934376315054305986741 105743847779536341186257)
                ·
                  rfl

theorem cell19_347516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_347516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347516 prefixEnd_347516 := by exact prefixLift 347516
  have htrace : WordTrace (prefixWord ++ tailWord_347516) baseStart_347516 baseEnd_347516 := by
    simpa [prefixWord, tailWord_347516, baseEnd_347516] using wordTrace_append hprefix tailTrace_347516
  have hstable : (prefixWord ++ tailWord_347516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347516).length < 2 ^ (prefixWord ++ tailWord_347516).sum := by decide
  have hdescent : baseEnd_347516 < baseStart_347516 := by decide
  rcases family_descends (prefixWord ++ tailWord_347516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347586 : List Nat := [3, 5, 2, 1, 8]
def baseStart_347586 : Nat := 118140960795 + 347586 * 2 ^ 59
def prefixEnd_347586 : Nat := 4983230072969 + 3 ^ 40 * 347586 * 2
def baseEnd_347586 : Nat := 3917227693251737764093

theorem tailTrace_347586 : CollatzResearch.WordTrace tailWord_347586 prefixEnd_347586 3917227693251737764093 := by
  unfold tailWord_347586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3169375729690689951945653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8451668612508506538521741 3169375729690689951945653)
  ·
    refine ⟨297128974658502182994905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3169375729690689951945653 297128974658502182994905)
    ·
      refine ⟨222846730993876637246179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297128974658502182994905 222846730993876637246179)
      ·
        refine ⟨334270096490814955869269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222846730993876637246179 334270096490814955869269)
        ·
          refine ⟨3917227693251737764093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 334270096490814955869269 3917227693251737764093)
          ·
            rfl

theorem cell19_347586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 8].length) (baseStart_347586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347586 prefixEnd_347586 := by exact prefixLift 347586
  have htrace : WordTrace (prefixWord ++ tailWord_347586) baseStart_347586 baseEnd_347586 := by
    simpa [prefixWord, tailWord_347586, baseEnd_347586] using wordTrace_append hprefix tailTrace_347586
  have hstable : (prefixWord ++ tailWord_347586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347586).length < 2 ^ (prefixWord ++ tailWord_347586).sum := by decide
  have hdescent : baseEnd_347586 < baseStart_347586 := by decide
  rcases family_descends (prefixWord ++ tailWord_347586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347609 : List Nat := [1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_347609 : Nat := 118140960795 + 347609 * 2 ^ 59
def prefixEnd_347609 : Nat := 4983230072969 + 3 ^ 40 * 347609 * 2
def baseEnd_347609 : Nat := 105772146268939681119337

theorem tailTrace_347609 : CollatzResearch.WordTrace tailWord_347609 prefixEnd_347609 105772146268939681119337 := by
  unfold tailWord_347609
  simp only [CollatzResearch.WordTrace]
  refine ⟨12678341797679434735869881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8452227865119623157246587 12678341797679434735869881)
  ·
    refine ⟨9508756348259576051902411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12678341797679434735869881 9508756348259576051902411)
    ·
      refine ⟨14263134522389364077853617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9508756348259576051902411 14263134522389364077853617)
      ·
        refine ⟨10697350891792023058390213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14263134522389364077853617 10697350891792023058390213)
        ·
          refine ⟨2005753292211004323448165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10697350891792023058390213 2005753292211004323448165)
          ·
            refine ⟨376078742289563310646531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2005753292211004323448165 376078742289563310646531)
            ·
              refine ⟨564118113434344965969797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376078742289563310646531 564118113434344965969797)
              ·
                refine ⟨105772146268939681119337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564118113434344965969797 105772146268939681119337)
                ·
                  rfl

theorem cell19_347609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_347609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347609 prefixEnd_347609 := by exact prefixLift 347609
  have htrace : WordTrace (prefixWord ++ tailWord_347609) baseStart_347609 baseEnd_347609 := by
    simpa [prefixWord, tailWord_347609, baseEnd_347609] using wordTrace_append hprefix tailTrace_347609
  have hstable : (prefixWord ++ tailWord_347609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347609).length < 2 ^ (prefixWord ++ tailWord_347609).sum := by decide
  have hdescent : baseEnd_347609 < baseStart_347609 := by decide
  rcases family_descends (prefixWord ++ tailWord_347609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347626 : List Nat := [3, 1, 3, 1, 4, 1, 3, 3]
def baseStart_347626 : Nat := 118140960795 + 347626 * 2 ^ 59
def prefixEnd_347626 : Nat := 4983230072969 + 3 ^ 40 * 347626 * 2
def baseEnd_347626 : Nat := 105777319111088678741513

theorem tailTrace_347626 : CollatzResearch.WordTrace tailWord_347626 prefixEnd_347626 105777319111088678741513 := by
  unfold tailWord_347626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3169740459654461659809683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8452641225745231092825821 3169740459654461659809683)
  ·
    refine ⟨4754610689481692489714525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3169740459654461659809683 4754610689481692489714525)
    ·
      refine ⟨1782979008555634683642947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4754610689481692489714525 1782979008555634683642947)
      ·
        refine ⟨2674468512833452025464421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782979008555634683642947 2674468512833452025464421)
        ·
          refine ⟨501462846156272254774579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2674468512833452025464421 501462846156272254774579)
          ·
            refine ⟨752194269234408382161869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501462846156272254774579 752194269234408382161869)
            ·
              refine ⟨282072850962903143310701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 752194269234408382161869 282072850962903143310701)
              ·
                refine ⟨105777319111088678741513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282072850962903143310701 105777319111088678741513)
                ·
                  rfl

theorem cell19_347626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_347626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347626 prefixEnd_347626 := by exact prefixLift 347626
  have htrace : WordTrace (prefixWord ++ tailWord_347626) baseStart_347626 baseEnd_347626 := by
    simpa [prefixWord, tailWord_347626, baseEnd_347626] using wordTrace_append hprefix tailTrace_347626
  have hstable : (prefixWord ++ tailWord_347626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347626).length < 2 ^ (prefixWord ++ tailWord_347626).sum := by decide
  have hdescent : baseEnd_347626 < baseStart_347626 := by decide
  rcases family_descends (prefixWord ++ tailWord_347626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347683 : List Nat := [1, 1, 1, 4, 5, 2, 2, 3]
def baseStart_347683 : Nat := 118140960795 + 347683 * 2 ^ 59
def prefixEnd_347683 : Nat := 4983230072969 + 3 ^ 40 * 347683 * 2
def baseEnd_347683 : Nat := 105794663346529435474691

theorem tailTrace_347683 : CollatzResearch.WordTrace tailWord_347683 prefixEnd_347683 105794663346529435474691 := by
  unfold tailWord_347683
  simp only [CollatzResearch.WordTrace]
  refine ⟨12681040799411345374063703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8454027199607563582709135 12681040799411345374063703)
  ·
    refine ⟨19021561199117018061095555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12681040799411345374063703 19021561199117018061095555)
    ·
      refine ⟨28532341798675527091643333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19021561199117018061095555 28532341798675527091643333)
      ·
        refine ⟨5349814087251661329683125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28532341798675527091643333 5349814087251661329683125)
        ·
          refine ⟨501545070679843249657793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5349814087251661329683125 501545070679843249657793)
          ·
            refine ⟨376158803009882437243345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501545070679843249657793 376158803009882437243345)
            ·
              refine ⟨282119102257411827932509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376158803009882437243345 282119102257411827932509)
              ·
                refine ⟨105794663346529435474691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282119102257411827932509 105794663346529435474691)
                ·
                  rfl

theorem cell19_347683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_347683 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347683 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347683 prefixEnd_347683 := by exact prefixLift 347683
  have htrace : WordTrace (prefixWord ++ tailWord_347683) baseStart_347683 baseEnd_347683 := by
    simpa [prefixWord, tailWord_347683, baseEnd_347683] using wordTrace_append hprefix tailTrace_347683
  have hstable : (prefixWord ++ tailWord_347683).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347683).length < 2 ^ (prefixWord ++ tailWord_347683).sum := by decide
  have hdescent : baseEnd_347683 < baseStart_347683 := by decide
  rcases family_descends (prefixWord ++ tailWord_347683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347702 : List Nat := [5, 1, 2, 1, 3, 2, 5]
def baseStart_347702 : Nat := 118140960795 + 347702 * 2 ^ 59
def prefixEnd_347702 : Nat := 4983230072969 + 3 ^ 40 * 347702 * 2
def baseEnd_347702 : Nat := 35266814919447673684139

theorem tailTrace_347702 : CollatzResearch.WordTrace tailWord_347702 prefixEnd_347702 35266814919447673684139 := by
  unfold tailWord_347702
  simp only [CollatzResearch.WordTrace]
  refine ⟨792608361646406976187835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8454489190895007746003573 792608361646406976187835)
  ·
    refine ⟨1188912542469610464281753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 792608361646406976187835 1188912542469610464281753)
    ·
      refine ⟨891684406852207848211315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1188912542469610464281753 891684406852207848211315)
      ·
        refine ⟨1337526610278311772316973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891684406852207848211315 1337526610278311772316973)
        ·
          refine ⟨501572478854366914618865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1337526610278311772316973 501572478854366914618865)
          ·
            refine ⟨376179359140775185964149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501572478854366914618865 376179359140775185964149)
            ·
              refine ⟨35266814919447673684139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 376179359140775185964149 35266814919447673684139)
              ·
                rfl

theorem cell19_347702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_347702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347702 prefixEnd_347702 := by exact prefixLift 347702
  have htrace : WordTrace (prefixWord ++ tailWord_347702) baseStart_347702 baseEnd_347702 := by
    simpa [prefixWord, tailWord_347702, baseEnd_347702] using wordTrace_append hprefix tailTrace_347702
  have hstable : (prefixWord ++ tailWord_347702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347702).length < 2 ^ (prefixWord ++ tailWord_347702).sum := by decide
  have hdescent : baseEnd_347702 < baseStart_347702 := by decide
  rcases family_descends (prefixWord ++ tailWord_347702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347799 : List Nat := [1, 1, 3, 3, 2, 3, 3, 3]
def baseStart_347799 : Nat := 118140960795 + 347799 * 2 ^ 59
def prefixEnd_347799 : Nat := 4983230072969 + 3 ^ 40 * 347799 * 2
def baseEnd_347799 : Nat := 105829960387075536896597

theorem tailTrace_347799 : CollatzResearch.WordTrace tailWord_347799 prefixEnd_347799 105829960387075536896597 := by
  unfold tailWord_347799
  simp only [CollatzResearch.WordTrace]
  refine ⟨12685271666991097185286451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8456847777994064790190967 12685271666991097185286451)
  ·
    refine ⟨19027907500486645777929677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12685271666991097185286451 19027907500486645777929677)
    ·
      refine ⟨7135465312682492166723629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19027907500486645777929677 7135465312682492166723629)
      ·
        refine ⟨2675799492255934562521361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7135465312682492166723629 2675799492255934562521361)
        ·
          refine ⟨2006849619191950921891021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2675799492255934562521361 2006849619191950921891021)
          ·
            refine ⟨752568607196981595709133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2006849619191950921891021 752568607196981595709133)
            ·
              refine ⟨282213227698868098390925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 752568607196981595709133 282213227698868098390925)
              ·
                refine ⟨105829960387075536896597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282213227698868098390925 105829960387075536896597)
                ·
                  rfl

theorem cell19_347799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_347799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347799 prefixEnd_347799 := by exact prefixLift 347799
  have htrace : WordTrace (prefixWord ++ tailWord_347799) baseStart_347799 baseEnd_347799 := by
    simpa [prefixWord, tailWord_347799, baseEnd_347799] using wordTrace_append hprefix tailTrace_347799
  have hstable : (prefixWord ++ tailWord_347799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347799).length < 2 ^ (prefixWord ++ tailWord_347799).sum := by decide
  have hdescent : baseEnd_347799 < baseStart_347799 := by decide
  rcases family_descends (prefixWord ++ tailWord_347799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347852 : List Nat := [2, 2, 1, 5, 3, 1, 2, 3]
def baseStart_347852 : Nat := 118140960795 + 347852 * 2 ^ 59
def prefixEnd_347852 : Nat := 4983230072969 + 3 ^ 40 * 347852 * 2
def baseEnd_347852 : Nat := 105846087483187117718675

theorem tailTrace_347852 : CollatzResearch.WordTrace tailWord_347852 prefixEnd_347852 105846087483187117718675 := by
  unfold tailWord_347852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343602367899543618482905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8458136490532724824643873 6343602367899543618482905)
  ·
    refine ⟨4757701775924657713862179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6343602367899543618482905 4757701775924657713862179)
    ·
      refine ⟨7136552663886986570793269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757701775924657713862179 7136552663886986570793269)
      ·
        refine ⟨669051812239404991011869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7136552663886986570793269 669051812239404991011869)
        ·
          refine ⟨250894429589776871629451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 669051812239404991011869 250894429589776871629451)
          ·
            refine ⟨376341644384665307444177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250894429589776871629451 376341644384665307444177)
            ·
              refine ⟨282256233288498980583133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376341644384665307444177 282256233288498980583133)
              ·
                refine ⟨105846087483187117718675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282256233288498980583133 105846087483187117718675)
                ·
                  rfl

theorem cell19_347852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_347852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347852 prefixEnd_347852 := by exact prefixLift 347852
  have htrace : WordTrace (prefixWord ++ tailWord_347852) baseStart_347852 baseEnd_347852 := by
    simpa [prefixWord, tailWord_347852, baseEnd_347852] using wordTrace_append hprefix tailTrace_347852
  have hstable : (prefixWord ++ tailWord_347852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347852).length < 2 ^ (prefixWord ++ tailWord_347852).sum := by decide
  have hdescent : baseEnd_347852 < baseStart_347852 := by decide
  rcases family_descends (prefixWord ++ tailWord_347852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347875 : List Nat := [1, 1, 1, 7, 2, 2, 5]
def baseStart_347875 : Nat := 118140960795 + 347875 * 2 ^ 59
def prefixEnd_347875 : Nat := 4983230072969 + 3 ^ 40 * 347875 * 2
def baseEnd_347875 : Nat := 35284362011443293069167

theorem tailTrace_347875 : CollatzResearch.WordTrace tailWord_347875 prefixEnd_347875 35284362011443293069167 := by
  unfold tailWord_347875
  simp only [CollatzResearch.WordTrace]
  refine ⟨12688043614715762165053079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8458695743143841443368719 12688043614715762165053079)
  ·
    refine ⟨19032065422073643247579619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12688043614715762165053079 19032065422073643247579619)
    ·
      refine ⟨28548098133110464871369429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19032065422073643247579619 28548098133110464871369429)
      ·
        refine ⟨669096049994776520422721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28548098133110464871369429 669096049994776520422721)
        ·
          refine ⟨501822037496082390317041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669096049994776520422721 501822037496082390317041)
          ·
            refine ⟨376366528122061792737781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501822037496082390317041 376366528122061792737781)
            ·
              refine ⟨35284362011443293069167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 376366528122061792737781 35284362011443293069167)
              ·
                rfl

theorem cell19_347875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_347875 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347875 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347875 prefixEnd_347875 := by exact prefixLift 347875
  have htrace : WordTrace (prefixWord ++ tailWord_347875) baseStart_347875 baseEnd_347875 := by
    simpa [prefixWord, tailWord_347875, baseEnd_347875] using wordTrace_append hprefix tailTrace_347875
  have hstable : (prefixWord ++ tailWord_347875).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347875).length < 2 ^ (prefixWord ++ tailWord_347875).sum := by decide
  have hdescent : baseEnd_347875 < baseStart_347875 := by decide
  rcases family_descends (prefixWord ++ tailWord_347875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347892 : List Nat := [2, 6, 1, 1, 1, 1, 1, 6]
def baseStart_347892 : Nat := 118140960795 + 347892 * 2 ^ 59
def prefixEnd_347892 : Nat := 4983230072969 + 3 ^ 40 * 347892 * 2
def baseEnd_347892 : Nat := 105858258876478876829677

theorem tailTrace_347892 : CollatzResearch.WordTrace tailWord_347892 prefixEnd_347892 105858258876478876829677 := by
  unfold tailWord_347892
  simp only [CollatzResearch.WordTrace]
  refine ⟨6344331827827087034210965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8459109103769449378947953 6344331827827087034210965)
  ·
    refine ⟨297390554429394704728639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6344331827827087034210965 297390554429394704728639)
    ·
      refine ⟨446085831644092057092959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297390554429394704728639 446085831644092057092959)
      ·
        refine ⟨669128747466138085639439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446085831644092057092959 669128747466138085639439)
        ·
          refine ⟨1003693121199207128459159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669128747466138085639439 1003693121199207128459159)
          ·
            refine ⟨1505539681798810692688739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003693121199207128459159 1505539681798810692688739)
            ·
              refine ⟨2258309522698216039033109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505539681798810692688739 2258309522698216039033109)
              ·
                refine ⟨105858258876478876829677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2258309522698216039033109 105858258876478876829677)
                ·
                  rfl

theorem cell19_347892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_347892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347892 prefixEnd_347892 := by exact prefixLift 347892
  have htrace : WordTrace (prefixWord ++ tailWord_347892) baseStart_347892 baseEnd_347892 := by
    simpa [prefixWord, tailWord_347892, baseEnd_347892] using wordTrace_append hprefix tailTrace_347892
  have hstable : (prefixWord ++ tailWord_347892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347892).length < 2 ^ (prefixWord ++ tailWord_347892).sum := by decide
  have hdescent : baseEnd_347892 < baseStart_347892 := by decide
  rcases family_descends (prefixWord ++ tailWord_347892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347894 : List Nat := [5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_347894 : Nat := 118140960795 + 347894 * 2 ^ 59
def prefixEnd_347894 : Nat := 4983230072969 + 3 ^ 40 * 347894 * 2
def baseEnd_347894 : Nat := 105858867446143464785227

theorem tailTrace_347894 : CollatzResearch.WordTrace tailWord_347894 prefixEnd_347894 105858867446143464785227 := by
  unfold tailWord_347894
  simp only [CollatzResearch.WordTrace]
  refine ⟨793046037602933025624671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8459157734431285606663157 793046037602933025624671)
  ·
    refine ⟨1189569056404399538437007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 793046037602933025624671 1189569056404399538437007)
    ·
      refine ⟨1784353584606599307655511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189569056404399538437007 1784353584606599307655511)
      ·
        refine ⟨2676530376909898961483267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784353584606599307655511 2676530376909898961483267)
        ·
          refine ⟨4014795565364848442224901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676530376909898961483267 4014795565364848442224901)
          ·
            refine ⟨752774168505909082917169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4014795565364848442224901 752774168505909082917169)
            ·
              refine ⟨564580626379431812187877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752774168505909082917169 564580626379431812187877)
              ·
                refine ⟨105858867446143464785227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564580626379431812187877 105858867446143464785227)
                ·
                  rfl

theorem cell19_347894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_347894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347894 prefixEnd_347894 := by exact prefixLift 347894
  have htrace : WordTrace (prefixWord ++ tailWord_347894) baseStart_347894 baseEnd_347894 := by
    simpa [prefixWord, tailWord_347894, baseEnd_347894] using wordTrace_append hprefix tailTrace_347894
  have hstable : (prefixWord ++ tailWord_347894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347894).length < 2 ^ (prefixWord ++ tailWord_347894).sum := by decide
  have hdescent : baseEnd_347894 < baseStart_347894 := by decide
  rcases family_descends (prefixWord ++ tailWord_347894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347953 : List Nat := [1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_347953 : Nat := 118140960795 + 347953 * 2 ^ 59
def prefixEnd_347953 : Nat := 4983230072969 + 3 ^ 40 * 347953 * 2
def baseEnd_347953 : Nat := 105876820251248809473955

theorem tailTrace_347953 : CollatzResearch.WordTrace tailWord_347953 prefixEnd_347953 105876820251248809473955 := by
  unfold tailWord_347953
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690888508433181486392513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8460592338955454324261675 12690888508433181486392513)
  ·
    refine ⟨9518166381324886114794385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12690888508433181486392513 9518166381324886114794385)
    ·
      refine ⟨7138624785993664586095789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9518166381324886114794385 7138624785993664586095789)
      ·
        refine ⟨2676984294747624219785921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7138624785993664586095789 2676984294747624219785921)
        ·
          refine ⟨2007738221060718164839441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2676984294747624219785921 2007738221060718164839441)
          ·
            refine ⟨1505803665795538623629581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2007738221060718164839441 1505803665795538623629581)
            ·
              refine ⟨564676374673326983861093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1505803665795538623629581 564676374673326983861093)
              ·
                refine ⟨105876820251248809473955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564676374673326983861093 105876820251248809473955)
                ·
                  rfl

theorem cell19_347953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_347953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347953 prefixEnd_347953 := by exact prefixLift 347953
  have htrace : WordTrace (prefixWord ++ tailWord_347953) baseStart_347953 baseEnd_347953 := by
    simpa [prefixWord, tailWord_347953, baseEnd_347953] using wordTrace_append hprefix tailTrace_347953
  have hstable : (prefixWord ++ tailWord_347953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347953).length < 2 ^ (prefixWord ++ tailWord_347953).sum := by decide
  have hdescent : baseEnd_347953 < baseStart_347953 := by decide
  rcases family_descends (prefixWord ++ tailWord_347953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347991 : List Nat := [1, 1, 3, 2, 5, 1, 6]
def baseStart_347991 : Nat := 118140960795 + 347991 * 2 ^ 59
def prefixEnd_347991 : Nat := 4983230072969 + 3 ^ 40 * 347991 * 2
def baseEnd_347991 : Nat := 35296127691625326876469

theorem tailTrace_347991 : CollatzResearch.WordTrace tailWord_347991 prefixEnd_347991 35296127691625326876469 := by
  unfold tailWord_347991
  simp only [CollatzResearch.WordTrace]
  refine ⟨12692274482295513976275827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8461516321530342650850551 12692274482295513976275827)
  ·
    refine ⟨19038411723443270964413741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12692274482295513976275827 19038411723443270964413741)
    ·
      refine ⟨7139404396291226611655153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19038411723443270964413741 7139404396291226611655153)
      ·
        refine ⟨5354553297218419958741365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7139404396291226611655153 5354553297218419958741365)
        ·
          refine ⟨501989371614226871132003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5354553297218419958741365 501989371614226871132003)
          ·
            refine ⟨752984057421340306698005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501989371614226871132003 752984057421340306698005)
            ·
              refine ⟨35296127691625326876469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 752984057421340306698005 35296127691625326876469)
              ·
                rfl

theorem cell19_347991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_347991 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347991 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347991 prefixEnd_347991 := by exact prefixLift 347991
  have htrace : WordTrace (prefixWord ++ tailWord_347991) baseStart_347991 baseEnd_347991 := by
    simpa [prefixWord, tailWord_347991, baseEnd_347991] using wordTrace_append hprefix tailTrace_347991
  have hstable : (prefixWord ++ tailWord_347991).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347991).length < 2 ^ (prefixWord ++ tailWord_347991).sum := by decide
  have hdescent : baseEnd_347991 < baseStart_347991 := by decide
  rcases family_descends (prefixWord ++ tailWord_347991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347993 : List Nat := [1, 2, 1, 2, 2, 3, 8]
def baseStart_347993 : Nat := 118140960795 + 347993 * 2 ^ 59
def prefixEnd_347993 : Nat := 4983230072969 + 3 ^ 40 * 347993 * 2
def baseEnd_347993 : Nat := 35296330548180189528319

theorem tailTrace_347993 : CollatzResearch.WordTrace tailWord_347993 prefixEnd_347993 35296330548180189528319 := by
  unfold tailWord_347993
  simp only [CollatzResearch.WordTrace]
  refine ⟨12692347428288268317848633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8461564952192178878565755 12692347428288268317848633)
  ·
    refine ⟨9519260571216201238386475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12692347428288268317848633 9519260571216201238386475)
    ·
      refine ⟨14278890856824301857579713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9519260571216201238386475 14278890856824301857579713)
      ·
        refine ⟨10709168142618226393184785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14278890856824301857579713 10709168142618226393184785)
        ·
          refine ⟨8031876106963669794888589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10709168142618226393184785 8031876106963669794888589)
          ·
            refine ⟨3011953540111376173083221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8031876106963669794888589 3011953540111376173083221)
            ·
              refine ⟨35296330548180189528319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3011953540111376173083221 35296330548180189528319)
              ·
                rfl

theorem cell19_347993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_347993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_347993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_347993 prefixEnd_347993 := by exact prefixLift 347993
  have htrace : WordTrace (prefixWord ++ tailWord_347993) baseStart_347993 baseEnd_347993 := by
    simpa [prefixWord, tailWord_347993, baseEnd_347993] using wordTrace_append hprefix tailTrace_347993
  have hstable : (prefixWord ++ tailWord_347993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347993).length < 2 ^ (prefixWord ++ tailWord_347993).sum := by decide
  have hdescent : baseEnd_347993 < baseStart_347993 := by decide
  rcases family_descends (prefixWord ++ tailWord_347993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348065 : List Nat := [1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_348065 : Nat := 118140960795 + 348065 * 2 ^ 59
def prefixEnd_348065 : Nat := 4983230072969 + 3 ^ 40 * 348065 * 2
def baseEnd_348065 : Nat := 105910900152465734984761

theorem tailTrace_348065 : CollatzResearch.WordTrace tailWord_348065 prefixEnd_348065 105910900152465734984761 := by
  unfold tailWord_348065
  simp only [CollatzResearch.WordTrace]
  refine ⟨12694973484027424614469649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8463315656018283076313099 12694973484027424614469649)
  ·
    refine ⟨9521230113020568460852237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12694973484027424614469649 9521230113020568460852237)
    ·
      refine ⟨3570461292382713172819589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9521230113020568460852237 3570461292382713172819589)
      ·
        refine ⟨669461492321758719903673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3570461292382713172819589 669461492321758719903673)
        ·
          refine ⟨502096119241319039927755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669461492321758719903673 502096119241319039927755)
          ·
            refine ⟨753144178861978559891633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502096119241319039927755 753144178861978559891633)
            ·
              refine ⟨564858134146483919918725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753144178861978559891633 564858134146483919918725)
              ·
                refine ⟨105910900152465734984761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564858134146483919918725 105910900152465734984761)
                ·
                  rfl

theorem cell19_348065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_348065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348065 prefixEnd_348065 := by exact prefixLift 348065
  have htrace : WordTrace (prefixWord ++ tailWord_348065) baseStart_348065 baseEnd_348065 := by
    simpa [prefixWord, tailWord_348065, baseEnd_348065] using wordTrace_append hprefix tailTrace_348065
  have hstable : (prefixWord ++ tailWord_348065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348065).length < 2 ^ (prefixWord ++ tailWord_348065).sum := by decide
  have hdescent : baseEnd_348065 < baseStart_348065 := by decide
  rcases family_descends (prefixWord ++ tailWord_348065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348088 : List Nat := [2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_348088 : Nat := 118140960795 + 348088 * 2 ^ 59
def prefixEnd_348088 : Nat := 4983230072969 + 3 ^ 40 * 348088 * 2
def baseEnd_348088 : Nat := 105917898703608496473587

theorem tailTrace_348088 : CollatzResearch.WordTrace tailWord_348088 prefixEnd_348088 105917898703608496473587 := by
  unfold tailWord_348088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6347906181472049771278459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8463874908629399695037945 6347906181472049771278459)
  ·
    refine ⟨9521859272208074656917689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6347906181472049771278459 9521859272208074656917689)
    ·
      refine ⟨7141394454156055992688267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9521859272208074656917689 7141394454156055992688267)
      ·
        refine ⟨10712091681234083989032401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7141394454156055992688267 10712091681234083989032401)
        ·
          refine ⟨8034068760925562991774301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10712091681234083989032401 8034068760925562991774301)
          ·
            refine ⟨3012775785347086121915363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8034068760925562991774301 3012775785347086121915363)
            ·
              refine ⟨4519163678020629182873045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012775785347086121915363 4519163678020629182873045)
              ·
                refine ⟨105917898703608496473587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4519163678020629182873045 105917898703608496473587)
                ·
                  rfl

theorem cell19_348088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_348088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348088 prefixEnd_348088 := by exact prefixLift 348088
  have htrace : WordTrace (prefixWord ++ tailWord_348088) baseStart_348088 baseEnd_348088 := by
    simpa [prefixWord, tailWord_348088, baseEnd_348088] using wordTrace_append hprefix tailTrace_348088
  have hstable : (prefixWord ++ tailWord_348088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348088).length < 2 ^ (prefixWord ++ tailWord_348088).sum := by decide
  have hdescent : baseEnd_348088 < baseStart_348088 := by decide
  rcases family_descends (prefixWord ++ tailWord_348088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348118 : List Nat := [5, 2, 1, 1, 4, 1, 1, 4]
def baseStart_348118 : Nat := 118140960795 + 348118 * 2 ^ 59
def prefixEnd_348118 : Nat := 4983230072969 + 3 ^ 40 * 348118 * 2
def baseEnd_348118 : Nat := 105927027248577315806839

theorem tailTrace_348118 : CollatzResearch.WordTrace tailWord_348118 prefixEnd_348118 105927027248577315806839 := by
  unfold tailWord_348118
  simp only [CollatzResearch.WordTrace]
  refine ⟨793556659552213416634313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8464604368556943110766005 793556659552213416634313)
  ·
    refine ⟨595167494664160062475735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 793556659552213416634313 595167494664160062475735)
    ·
      refine ⟨892751241996240093713603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595167494664160062475735 892751241996240093713603)
      ·
        refine ⟨1339126862994360140570405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892751241996240093713603 1339126862994360140570405)
        ·
          refine ⟨251086286811442526356951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1339126862994360140570405 251086286811442526356951)
          ·
            refine ⟨376629430217163789535427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251086286811442526356951 376629430217163789535427)
            ·
              refine ⟨564944145325745684303141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376629430217163789535427 564944145325745684303141)
              ·
                refine ⟨105927027248577315806839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564944145325745684303141 105927027248577315806839)
                ·
                  rfl

theorem cell19_348118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_348118 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348118 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348118 prefixEnd_348118 := by exact prefixLift 348118
  have htrace : WordTrace (prefixWord ++ tailWord_348118) baseStart_348118 baseEnd_348118 := by
    simpa [prefixWord, tailWord_348118, baseEnd_348118] using wordTrace_append hprefix tailTrace_348118
  have hstable : (prefixWord ++ tailWord_348118).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348118).length < 2 ^ (prefixWord ++ tailWord_348118).sum := by decide
  have hdescent : baseEnd_348118 < baseStart_348118 := by decide
  rcases family_descends (prefixWord ++ tailWord_348118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348122 : List Nat := [3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_348122 : Nat := 118140960795 + 348122 * 2 ^ 59
def prefixEnd_348122 : Nat := 4983230072969 + 3 ^ 40 * 348122 * 2
def baseEnd_348122 : Nat := 105928244387906491717939

theorem tailTrace_348122 : CollatzResearch.WordTrace tailWord_348122 prefixEnd_348122 105928244387906491717939 := by
  unfold tailWord_348122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3174263111205230837323655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8464701629880615566196413 3174263111205230837323655)
  ·
    refine ⟨4761394666807846255985483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3174263111205230837323655 4761394666807846255985483)
    ·
      refine ⟨7142092000211769383978225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4761394666807846255985483 7142092000211769383978225)
      ·
        refine ⟨5356569000158827037983669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7142092000211769383978225 5356569000158827037983669)
        ·
          refine ⟨502178343764890034810969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5356569000158827037983669 502178343764890034810969)
          ·
            refine ⟨376633757823667526108227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502178343764890034810969 376633757823667526108227)
            ·
              refine ⟨564950636735501289162341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376633757823667526108227 564950636735501289162341)
              ·
                refine ⟨105928244387906491717939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564950636735501289162341 105928244387906491717939)
                ·
                  rfl

theorem cell19_348122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_348122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348122 prefixEnd_348122 := by exact prefixLift 348122
  have htrace : WordTrace (prefixWord ++ tailWord_348122) baseStart_348122 baseEnd_348122 := by
    simpa [prefixWord, tailWord_348122, baseEnd_348122] using wordTrace_append hprefix tailTrace_348122
  have hstable : (prefixWord ++ tailWord_348122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348122).length < 2 ^ (prefixWord ++ tailWord_348122).sum := by decide
  have hdescent : baseEnd_348122 < baseStart_348122 := by decide
  rcases family_descends (prefixWord ++ tailWord_348122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348143 : List Nat := [1, 1, 2, 1, 4, 2, 5, 3]
def baseStart_348143 : Nat := 118140960795 + 348143 * 2 ^ 59
def prefixEnd_348143 : Nat := 4983230072969 + 3 ^ 40 * 348143 * 2
def baseEnd_348143 : Nat := 105934634369384665251215

theorem tailTrace_348143 : CollatzResearch.WordTrace tailWord_348143 prefixEnd_348143 105934634369384665251215 := by
  unfold tailWord_348143
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697818377744843935809083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8465212251829895957206055 12697818377744843935809083)
  ·
    refine ⟨19046727566617265903713625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12697818377744843935809083 19046727566617265903713625)
    ·
      refine ⟨14285045674962949427785219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19046727566617265903713625 14285045674962949427785219)
      ·
        refine ⟨21427568512444424141677829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285045674962949427785219 21427568512444424141677829)
        ·
          refine ⟨4017669096083329526564593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21427568512444424141677829 4017669096083329526564593)
          ·
            refine ⟨3013251822062497144923445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4017669096083329526564593 3013251822062497144923445)
            ·
              refine ⟨282492358318359107336573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3013251822062497144923445 282492358318359107336573)
              ·
                refine ⟨105934634369384665251215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282492358318359107336573 105934634369384665251215)
                ·
                  rfl

theorem cell19_348143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_348143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348143 prefixEnd_348143 := by exact prefixLift 348143
  have htrace : WordTrace (prefixWord ++ tailWord_348143) baseStart_348143 baseEnd_348143 := by
    simpa [prefixWord, tailWord_348143, baseEnd_348143] using wordTrace_append hprefix tailTrace_348143
  have hstable : (prefixWord ++ tailWord_348143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348143).length < 2 ^ (prefixWord ++ tailWord_348143).sum := by decide
  have hdescent : baseEnd_348143 < baseStart_348143 := by decide
  rcases family_descends (prefixWord ++ tailWord_348143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348196 : List Nat := [2, 3, 1, 4, 2, 2, 2, 3]
def baseStart_348196 : Nat := 118140960795 + 348196 * 2 ^ 59
def prefixEnd_348196 : Nat := 4983230072969 + 3 ^ 40 * 348196 * 2
def baseEnd_348196 : Nat := 105950761465496246073293

theorem tailTrace_348196 : CollatzResearch.WordTrace tailWord_348196 prefixEnd_348196 105950761465496246073293 := by
  unfold tailWord_348196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349875723276416993744221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8466500964368555991658961 6349875723276416993744221)
  ·
    refine ⟨2381203396228656372654083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6349875723276416993744221 2381203396228656372654083)
    ·
      refine ⟨3571805094342984558981125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381203396228656372654083 3571805094342984558981125)
      ·
        refine ⟨669713455189309604808961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3571805094342984558981125 669713455189309604808961)
        ·
          refine ⟨502285091391982203606721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669713455189309604808961 502285091391982203606721)
          ·
            refine ⟨376713818543986652705041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502285091391982203606721 376713818543986652705041)
            ·
              refine ⟨282535363907989989528781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376713818543986652705041 282535363907989989528781)
              ·
                refine ⟨105950761465496246073293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282535363907989989528781 105950761465496246073293)
                ·
                  rfl

theorem cell19_348196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_348196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348196 prefixEnd_348196 := by exact prefixLift 348196
  have htrace : WordTrace (prefixWord ++ tailWord_348196) baseStart_348196 baseEnd_348196 := by
    simpa [prefixWord, tailWord_348196, baseEnd_348196] using wordTrace_append hprefix tailTrace_348196
  have hstable : (prefixWord ++ tailWord_348196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348196).length < 2 ^ (prefixWord ++ tailWord_348196).sum := by decide
  have hdescent : baseEnd_348196 < baseStart_348196 := by decide
  rcases family_descends (prefixWord ++ tailWord_348196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348217 : List Nat := [1, 2, 1, 5, 4, 1, 5]
def baseStart_348217 : Nat := 118140960795 + 348217 * 2 ^ 59
def prefixEnd_348217 : Nat := 4983230072969 + 3 ^ 40 * 348217 * 2
def baseEnd_348217 : Nat := 35319050482324806535523

theorem tailTrace_348217 : CollatzResearch.WordTrace tailWord_348217 prefixEnd_348217 35319050482324806535523 := by
  unfold tailWord_348217
  simp only [CollatzResearch.WordTrace]
  refine ⟨12700517379476754574002905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8467011586317836382668603 12700517379476754574002905)
  ·
    refine ⟨9525388034607565930502179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12700517379476754574002905 9525388034607565930502179)
    ·
      refine ⟨14288082051911348895753269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9525388034607565930502179 14288082051911348895753269)
      ·
        refine ⟨1339507692366688958976869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14288082051911348895753269 1339507692366688958976869)
        ·
          refine ⟨251157692318754179808163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1339507692366688958976869 251157692318754179808163)
          ·
            refine ⟨376736538478131269712245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251157692318754179808163 376736538478131269712245)
            ·
              refine ⟨35319050482324806535523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 376736538478131269712245 35319050482324806535523)
              ·
                rfl

theorem cell19_348217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_348217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348217 prefixEnd_348217 := by exact prefixLift 348217
  have htrace : WordTrace (prefixWord ++ tailWord_348217) baseStart_348217 baseEnd_348217 := by
    simpa [prefixWord, tailWord_348217, baseEnd_348217] using wordTrace_append hprefix tailTrace_348217
  have hstable : (prefixWord ++ tailWord_348217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348217).length < 2 ^ (prefixWord ++ tailWord_348217).sum := by decide
  have hdescent : baseEnd_348217 < baseStart_348217 := by decide
  rcases family_descends (prefixWord ++ tailWord_348217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348238 : List Nat := [4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_348238 : Nat := 118140960795 + 348238 * 2 ^ 59
def prefixEnd_348238 : Nat := 4983230072969 + 3 ^ 40 * 348238 * 2
def baseEnd_348238 : Nat := 105963541428452593139845

theorem tailTrace_348238 : CollatzResearch.WordTrace tailWord_348238 prefixEnd_348238 105963541428452593139845 := by
  unfold tailWord_348238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587660414050084395064671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8467522208267116773678245 1587660414050084395064671)
  ·
    refine ⟨2381490621075126592597007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587660414050084395064671 2381490621075126592597007)
    ·
      refine ⟨3572235931612689888895511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381490621075126592597007 3572235931612689888895511)
      ·
        refine ⟨5358353897419034833343267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572235931612689888895511 5358353897419034833343267)
        ·
          refine ⟨8037530846128552250014901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5358353897419034833343267 8037530846128552250014901)
          ·
            refine ⟨753518516824551773438897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8037530846128552250014901 753518516824551773438897)
            ·
              refine ⟨565138887618413830079173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753518516824551773438897 565138887618413830079173)
              ·
                refine ⟨105963541428452593139845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 565138887618413830079173 105963541428452593139845)
                ·
                  rfl

theorem cell19_348238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_348238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348238 prefixEnd_348238 := by exact prefixLift 348238
  have htrace : WordTrace (prefixWord ++ tailWord_348238) baseStart_348238 baseEnd_348238 := by
    simpa [prefixWord, tailWord_348238, baseEnd_348238] using wordTrace_append hprefix tailTrace_348238
  have hstable : (prefixWord ++ tailWord_348238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348238).length < 2 ^ (prefixWord ++ tailWord_348238).sum := by decide
  have hdescent : baseEnd_348238 < baseStart_348238 := by decide
  rcases family_descends (prefixWord ++ tailWord_348238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348259 : List Nat := [1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_348259 : Nat := 118140960795 + 348259 * 2 ^ 59
def prefixEnd_348259 : Nat := 4983230072969 + 3 ^ 40 * 348259 * 2
def baseEnd_348259 : Nat := 105969931409930766673121

theorem tailTrace_348259 : CollatzResearch.WordTrace tailWord_348259 prefixEnd_348259 105969931409930766673121 := by
  unfold tailWord_348259
  simp only [CollatzResearch.WordTrace]
  refine ⟨12702049245324595747031831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8468032830216397164687887 12702049245324595747031831)
  ·
    refine ⟨19053073867986893620547747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12702049245324595747031831 19053073867986893620547747)
    ·
      refine ⟨28579610801980340430821621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19053073867986893620547747 28579610801980340430821621)
      ·
        refine ⟨2679338512685656915389527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28579610801980340430821621 2679338512685656915389527)
        ·
          refine ⟨4019007769028485373084291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2679338512685656915389527 4019007769028485373084291)
          ·
            refine ⟨6028511653542728059626437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019007769028485373084291 6028511653542728059626437)
            ·
              refine ⟨1130345935039261511179957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6028511653542728059626437 1130345935039261511179957)
              ·
                refine ⟨105969931409930766673121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1130345935039261511179957 105969931409930766673121)
                ·
                  rfl

theorem cell19_348259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_348259 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348259 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348259 prefixEnd_348259 := by exact prefixLift 348259
  have htrace : WordTrace (prefixWord ++ tailWord_348259) baseStart_348259 baseEnd_348259 := by
    simpa [prefixWord, tailWord_348259, baseEnd_348259] using wordTrace_append hprefix tailTrace_348259
  have hstable : (prefixWord ++ tailWord_348259).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348259).length < 2 ^ (prefixWord ++ tailWord_348259).sum := by decide
  have hdescent : baseEnd_348259 < baseStart_348259 := by decide
  rcases family_descends (prefixWord ++ tailWord_348259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348312 : List Nat := [2, 1, 2, 4, 3, 1, 3, 3]
def baseStart_348312 : Nat := 118140960795 + 348312 * 2 ^ 59
def prefixEnd_348312 : Nat := 4983230072969 + 3 ^ 40 * 348312 * 2
def baseEnd_348312 : Nat := 105986058506042347495199

theorem tailTrace_348312 : CollatzResearch.WordTrace tailWord_348312 prefixEnd_348312 105986058506042347495199 := by
  unfold tailWord_348312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6351991157066292899355595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8469321542755057199140793 6351991157066292899355595)
  ·
    refine ⟨9527986735599439349033393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6351991157066292899355595 9527986735599439349033393)
    ·
      refine ⟨7145990051699579511775045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9527986735599439349033393 7145990051699579511775045)
      ·
        refine ⟨1339873134693671158457821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7145990051699579511775045 1339873134693671158457821)
        ·
          refine ⟨502452425510126684421683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1339873134693671158457821 502452425510126684421683)
          ·
            refine ⟨753678638265190026632525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502452425510126684421683 753678638265190026632525)
            ·
              refine ⟨282629489349446259987197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 753678638265190026632525 282629489349446259987197)
              ·
                refine ⟨105986058506042347495199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282629489349446259987197 105986058506042347495199)
                ·
                  rfl

theorem cell19_348312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_348312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348312 prefixEnd_348312 := by exact prefixLift 348312
  have htrace : WordTrace (prefixWord ++ tailWord_348312) baseStart_348312 baseEnd_348312 := by
    simpa [prefixWord, tailWord_348312, baseEnd_348312] using wordTrace_append hprefix tailTrace_348312
  have hstable : (prefixWord ++ tailWord_348312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348312).length < 2 ^ (prefixWord ++ tailWord_348312).sum := by decide
  have hdescent : baseEnd_348312 < baseStart_348312 := by decide
  rcases family_descends (prefixWord ++ tailWord_348312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348333 : List Nat := [1, 5, 2, 1, 2, 2, 6]
def baseStart_348333 : Nat := 118140960795 + 348333 * 2 ^ 59
def prefixEnd_348333 : Nat := 4983230072969 + 3 ^ 40 * 348333 * 2
def baseEnd_348333 : Nat := 35330816162506840342825

theorem tailTrace_348333 : CollatzResearch.WordTrace tailWord_348333 prefixEnd_348333 35330816162506840342825 := by
  unfold tailWord_348333
  simp only [CollatzResearch.WordTrace]
  refine ⟨12704748247056506385225653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8469832164704337590150435 12704748247056506385225653)
  ·
    refine ⟨1191070148161547473614905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12704748247056506385225653 1191070148161547473614905)
    ·
      refine ⟨893302611121160605211179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1191070148161547473614905 893302611121160605211179)
      ·
        refine ⟨1339953916681740907816769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893302611121160605211179 1339953916681740907816769)
        ·
          refine ⟨1004965437511305680862577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339953916681740907816769 1004965437511305680862577)
          ·
            refine ⟨753724078133479260646933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004965437511305680862577 753724078133479260646933)
            ·
              refine ⟨35330816162506840342825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 753724078133479260646933 35330816162506840342825)
              ·
                rfl

theorem cell19_348333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_348333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348333 prefixEnd_348333 := by exact prefixLift 348333
  have htrace : WordTrace (prefixWord ++ tailWord_348333) baseStart_348333 baseEnd_348333 := by
    simpa [prefixWord, tailWord_348333, baseEnd_348333] using wordTrace_append hprefix tailTrace_348333
  have hstable : (prefixWord ++ tailWord_348333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348333).length < 2 ^ (prefixWord ++ tailWord_348333).sum := by decide
  have hdescent : baseEnd_348333 < baseStart_348333 := by decide
  rcases family_descends (prefixWord ++ tailWord_348333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348392 : List Nat := [2, 1, 4, 1, 2, 2, 7]
def baseStart_348392 : Nat := 118140960795 + 348392 * 2 ^ 59
def prefixEnd_348392 : Nat := 4983230072969 + 3 ^ 40 * 348392 * 2
def baseEnd_348392 : Nat := 35336800430875288572401

theorem tailTrace_348392 : CollatzResearch.WordTrace tailWord_348392 prefixEnd_348392 35336800430875288572401 := by
  unfold tailWord_348392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353450076921379730811715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8471266769228506307748953 6353450076921379730811715)
  ·
    refine ⟨9530175115382069596217573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6353450076921379730811715 9530175115382069596217573)
    ·
      refine ⟨1786907834134138049290795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9530175115382069596217573 1786907834134138049290795)
      ·
        refine ⟨2680361751201207073936193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786907834134138049290795 2680361751201207073936193)
        ·
          refine ⟨2010271313400905305452145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2680361751201207073936193 2010271313400905305452145)
          ·
            refine ⟨1507703485050678979089109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2010271313400905305452145 1507703485050678979089109)
            ·
              refine ⟨35336800430875288572401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1507703485050678979089109 35336800430875288572401)
              ·
                rfl

theorem cell19_348392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_348392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348392 prefixEnd_348392 := by exact prefixLift 348392
  have htrace : WordTrace (prefixWord ++ tailWord_348392) baseStart_348392 baseEnd_348392 := by
    simpa [prefixWord, tailWord_348392, baseEnd_348392] using wordTrace_append hprefix tailTrace_348392
  have hstable : (prefixWord ++ tailWord_348392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348392).length < 2 ^ (prefixWord ++ tailWord_348392).sum := by decide
  have hdescent : baseEnd_348392 < baseStart_348392 := by decide
  rcases family_descends (prefixWord ++ tailWord_348392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348430 : List Nat := [4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_348430 : Nat := 118140960795 + 348430 * 2 ^ 59
def prefixEnd_348430 : Nat := 4983230072969 + 3 ^ 40 * 348430 * 2
def baseEnd_348430 : Nat := 106021964116253036872655

theorem tailTrace_348430 : CollatzResearch.WordTrace tailWord_348430 prefixEnd_348430 106021964116253036872655 := by
  unfold tailWord_348430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588535765963136493938343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8472190751803394634337829 1588535765963136493938343)
  ·
    refine ⟨2382803648944704740907515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1588535765963136493938343 2382803648944704740907515)
    ·
      refine ⟨3574205473417057111361273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2382803648944704740907515 3574205473417057111361273)
      ·
        refine ⟨2680654105062792833520955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3574205473417057111361273 2680654105062792833520955)
        ·
          refine ⟨4020981157594189250281433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680654105062792833520955 4020981157594189250281433)
          ·
            refine ⟨3015735868195641937711075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4020981157594189250281433 3015735868195641937711075)
            ·
              refine ⟨4523603802293462906566613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015735868195641937711075 4523603802293462906566613)
              ·
                refine ⟨106021964116253036872655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4523603802293462906566613 106021964116253036872655)
                ·
                  rfl

theorem cell19_348430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_348430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348430 prefixEnd_348430 := by exact prefixLift 348430
  have htrace : WordTrace (prefixWord ++ tailWord_348430) baseStart_348430 baseEnd_348430 := by
    simpa [prefixWord, tailWord_348430, baseEnd_348430] using wordTrace_append hprefix tailTrace_348430
  have hstable : (prefixWord ++ tailWord_348430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348430).length < 2 ^ (prefixWord ++ tailWord_348430).sum := by decide
  have hdescent : baseEnd_348430 < baseStart_348430 := by decide
  rcases family_descends (prefixWord ++ tailWord_348430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348462 : List Nat := [4, 1, 3, 3, 1, 2, 1, 4]
def baseStart_348462 : Nat := 118140960795 + 348462 * 2 ^ 59
def prefixEnd_348462 : Nat := 4983230072969 + 3 ^ 40 * 348462 * 2
def baseEnd_348462 : Nat := 106031701230886444161457

theorem tailTrace_348462 : CollatzResearch.WordTrace tailWord_348462 prefixEnd_348462 106031701230886444161457 := by
  unfold tailWord_348462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588681657948645177083955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8472968842392774277781093 1588681657948645177083955)
  ·
    refine ⟨2383022486922967765625933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1588681657948645177083955 2383022486922967765625933)
    ·
      refine ⟨893633432596112912109725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2383022486922967765625933 893633432596112912109725)
      ·
        refine ⟨335112537223542342041147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 893633432596112912109725 335112537223542342041147)
        ·
          refine ⟨502668805835313513061721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335112537223542342041147 502668805835313513061721)
          ·
            refine ⟨377001604376485134796291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502668805835313513061721 377001604376485134796291)
            ·
              refine ⟨565502406564727702194437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377001604376485134796291 565502406564727702194437)
              ·
                refine ⟨106031701230886444161457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 565502406564727702194437 106031701230886444161457)
                ·
                  rfl

theorem cell19_348462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_348462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348462 prefixEnd_348462 := by exact prefixLift 348462
  have htrace : WordTrace (prefixWord ++ tailWord_348462) baseStart_348462 baseEnd_348462 := by
    simpa [prefixWord, tailWord_348462, baseEnd_348462] using wordTrace_append hprefix tailTrace_348462
  have hstable : (prefixWord ++ tailWord_348462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348462).length < 2 ^ (prefixWord ++ tailWord_348462).sum := by decide
  have hdescent : baseEnd_348462 < baseStart_348462 := by decide
  rcases family_descends (prefixWord ++ tailWord_348462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348525 : List Nat := [1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_348525 : Nat := 118140960795 + 348525 * 2 ^ 59
def prefixEnd_348525 : Nat := 4983230072969 + 3 ^ 40 * 348525 * 2
def baseEnd_348525 : Nat := 106050871175320964761285

theorem tailTrace_348525 : CollatzResearch.WordTrace tailWord_348525 prefixEnd_348525 106050871175320964761285 := by
  unfold tailWord_348525
  simp only [CollatzResearch.WordTrace]
  refine ⟨12711751062360923176215029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8474500708240615450810019 12711751062360923176215029)
  ·
    refine ⟨1191726662096336547770159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12711751062360923176215029 1191726662096336547770159)
    ·
      refine ⟨1787589993144504821655239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191726662096336547770159 1787589993144504821655239)
      ·
        refine ⟨2681384989716757232482859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787589993144504821655239 2681384989716757232482859)
        ·
          refine ⟨4022077484575135848724289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681384989716757232482859 4022077484575135848724289)
          ·
            refine ⟨3016558113431351886543217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4022077484575135848724289 3016558113431351886543217)
            ·
              refine ⟨2262418585073513914907413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3016558113431351886543217 2262418585073513914907413)
              ·
                refine ⟨106050871175320964761285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2262418585073513914907413 106050871175320964761285)
                ·
                  rfl

theorem cell19_348525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_348525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348525 prefixEnd_348525 := by exact prefixLift 348525
  have htrace : WordTrace (prefixWord ++ tailWord_348525) baseStart_348525 baseEnd_348525 := by
    simpa [prefixWord, tailWord_348525, baseEnd_348525] using wordTrace_append hprefix tailTrace_348525
  have hstable : (prefixWord ++ tailWord_348525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348525).length < 2 ^ (prefixWord ++ tailWord_348525).sum := by decide
  have hdescent : baseEnd_348525 < baseStart_348525 := by decide
  rcases family_descends (prefixWord ++ tailWord_348525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348601 : List Nat := [1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_348601 : Nat := 118140960795 + 348601 * 2 ^ 59
def prefixEnd_348601 : Nat := 4983230072969 + 3 ^ 40 * 348601 * 2
def baseEnd_348601 : Nat := 106073996822575307072189

theorem tailTrace_348601 : CollatzResearch.WordTrace tailWord_348601 prefixEnd_348601 106073996822575307072189 := by
  unfold tailWord_348601
  simp only [CollatzResearch.WordTrace]
  refine ⟨12714523010085588155981657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8476348673390392103987771 12714523010085588155981657)
  ·
    refine ⟨9535892257564191116986243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12714523010085588155981657 9535892257564191116986243)
    ·
      refine ⟨14303838386346286675479365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9535892257564191116986243 14303838386346286675479365)
      ·
        refine ⟨2681969697439928751652381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14303838386346286675479365 2681969697439928751652381)
        ·
          refine ⟨1005738636539973281869643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2681969697439928751652381 1005738636539973281869643)
          ·
            refine ⟨1508607954809959922804465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005738636539973281869643 1508607954809959922804465)
            ·
              refine ⟨1131455966107469942103349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508607954809959922804465 1131455966107469942103349)
              ·
                refine ⟨106073996822575307072189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1131455966107469942103349 106073996822575307072189)
                ·
                  rfl

theorem cell19_348601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_348601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348601 prefixEnd_348601 := by exact prefixLift 348601
  have htrace : WordTrace (prefixWord ++ tailWord_348601) baseStart_348601 baseEnd_348601 := by
    simpa [prefixWord, tailWord_348601, baseEnd_348601] using wordTrace_append hprefix tailTrace_348601
  have hstable : (prefixWord ++ tailWord_348601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348601).length < 2 ^ (prefixWord ++ tailWord_348601).sum := by decide
  have hdescent : baseEnd_348601 < baseStart_348601 := by decide
  rcases family_descends (prefixWord ++ tailWord_348601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348620 : List Nat := [2, 2, 1, 4, 3, 7]
def baseStart_348620 : Nat := 118140960795 + 348620 * 2 ^ 59
def prefixEnd_348620 : Nat := 4983230072969 + 3 ^ 40 * 348620 * 2
def baseEnd_348620 : Nat := 11786642026043210294435

theorem tailTrace_348620 : CollatzResearch.WordTrace tailWord_348620 prefixEnd_348620 11786642026043210294435 := by
  unfold tailWord_348620
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357607998508377200461657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8476810664677836267282209 6357607998508377200461657)
  ·
    refine ⟨4768205998881282900346243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6357607998508377200461657 4768205998881282900346243)
    ·
      refine ⟨7152308998321924350519365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4768205998881282900346243 7152308998321924350519365)
      ·
        refine ⟨1341057937185360815722381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7152308998321924350519365 1341057937185360815722381)
        ·
          refine ⟨502896726444510305895893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1341057937185360815722381 502896726444510305895893)
          ·
            refine ⟨11786642026043210294435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 502896726444510305895893 11786642026043210294435)
            ·
              rfl

theorem cell19_348620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 7].length) (baseStart_348620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348620 prefixEnd_348620 := by exact prefixLift 348620
  have htrace : WordTrace (prefixWord ++ tailWord_348620) baseStart_348620 baseEnd_348620 := by
    simpa [prefixWord, tailWord_348620, baseEnd_348620] using wordTrace_append hprefix tailTrace_348620
  have hstable : (prefixWord ++ tailWord_348620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348620).length < 2 ^ (prefixWord ++ tailWord_348620).sum := by decide
  have hdescent : baseEnd_348620 < baseStart_348620 := by decide
  rcases family_descends (prefixWord ++ tailWord_348620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348639 : List Nat := [1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_348639 : Nat := 118140960795 + 348639 * 2 ^ 59
def prefixEnd_348639 : Nat := 4983230072969 + 3 ^ 40 * 348639 * 2
def baseEnd_348639 : Nat := 106085559646202478227641

theorem tailTrace_348639 : CollatzResearch.WordTrace tailWord_348639 prefixEnd_348639 106085559646202478227641 := by
  unfold tailWord_348639
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715908983947920645864971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8477272655965280430576647 12715908983947920645864971)
  ·
    refine ⟨19073863475921880968797457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12715908983947920645864971 19073863475921880968797457)
    ·
      refine ⟨14305397606941410726598093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19073863475921880968797457 14305397606941410726598093)
      ·
        refine ⟨5364524102603029022474285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14305397606941410726598093 5364524102603029022474285)
        ·
          refine ⟨2011696538476135883427857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5364524102603029022474285 2011696538476135883427857)
          ·
            refine ⟨1508772403857101912570893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2011696538476135883427857 1508772403857101912570893)
            ·
              refine ⟨565789651446413217214085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1508772403857101912570893 565789651446413217214085)
              ·
                refine ⟨106085559646202478227641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 565789651446413217214085 106085559646202478227641)
                ·
                  rfl

theorem cell19_348639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_348639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348639 prefixEnd_348639 := by exact prefixLift 348639
  have htrace : WordTrace (prefixWord ++ tailWord_348639) baseStart_348639 baseEnd_348639 := by
    simpa [prefixWord, tailWord_348639, baseEnd_348639] using wordTrace_append hprefix tailTrace_348639
  have hstable : (prefixWord ++ tailWord_348639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348639).length < 2 ^ (prefixWord ++ tailWord_348639).sum := by decide
  have hdescent : baseEnd_348639 < baseStart_348639 := by decide
  rcases family_descends (prefixWord ++ tailWord_348639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348711 : List Nat := [1, 1, 7, 2, 1, 1, 1, 5]
def baseStart_348711 : Nat := 118140960795 + 348711 * 2 ^ 59
def prefixEnd_348711 : Nat := 4983230072969 + 3 ^ 40 * 348711 * 2
def baseEnd_348711 : Nat := 106107468154127644627445

theorem tailTrace_348711 : CollatzResearch.WordTrace tailWord_348711 prefixEnd_348711 106107468154127644627445 := by
  unfold tailWord_348711
  simp only [CollatzResearch.WordTrace]
  refine ⟨12718535039687076942485987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8479023359791384628323991 12718535039687076942485987)
  ·
    refine ⟨19077802559530615413728981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12718535039687076942485987 19077802559530615413728981)
    ·
      refine ⟨447135997488998798759273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19077802559530615413728981 447135997488998798759273)
      ·
        refine ⟨335351998116749099069455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447135997488998798759273 335351998116749099069455)
        ·
          refine ⟨503027997175123648604183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335351998116749099069455 503027997175123648604183)
          ·
            refine ⟨754541995762685472906275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503027997175123648604183 754541995762685472906275)
            ·
              refine ⟨1131812993644028209359413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754541995762685472906275 1131812993644028209359413)
              ·
                refine ⟨106107468154127644627445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1131812993644028209359413 106107468154127644627445)
                ·
                  rfl

theorem cell19_348711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_348711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348711 prefixEnd_348711 := by exact prefixLift 348711
  have htrace : WordTrace (prefixWord ++ tailWord_348711) baseStart_348711 baseEnd_348711 := by
    simpa [prefixWord, tailWord_348711, baseEnd_348711] using wordTrace_append hprefix tailTrace_348711
  have hstable : (prefixWord ++ tailWord_348711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348711).length < 2 ^ (prefixWord ++ tailWord_348711).sum := by decide
  have hdescent : baseEnd_348711 < baseStart_348711 := by decide
  rcases family_descends (prefixWord ++ tailWord_348711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348736 : List Nat := [2, 1, 1, 2, 2, 2, 9]
def baseStart_348736 : Nat := 118140960795 + 348736 * 2 ^ 59
def prefixEnd_348736 : Nat := 4983230072969 + 3 ^ 40 * 348736 * 2
def baseEnd_348736 : Nat := 35371691758311664690607

theorem tailTrace_348736 : CollatzResearch.WordTrace tailWord_348736 prefixEnd_348736 35371691758311664690607 := by
  unfold tailWord_348736
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359723432298253106073031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8479631243064337474764041 6359723432298253106073031)
  ·
    refine ⟨9539585148447379659109547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6359723432298253106073031 9539585148447379659109547)
    ·
      refine ⟨14309377722671069488664321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9539585148447379659109547 14309377722671069488664321)
      ·
        refine ⟨10732033292003302116498241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14309377722671069488664321 10732033292003302116498241)
        ·
          refine ⟨8049024969002476587373681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10732033292003302116498241 8049024969002476587373681)
          ·
            refine ⟨6036768726751857440530261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8049024969002476587373681 6036768726751857440530261)
            ·
              refine ⟨35371691758311664690607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6036768726751857440530261 35371691758311664690607)
              ·
                rfl

theorem cell19_348736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_348736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348736 prefixEnd_348736 := by exact prefixLift 348736
  have htrace : WordTrace (prefixWord ++ tailWord_348736) baseStart_348736 baseEnd_348736 := by
    simpa [prefixWord, tailWord_348736, baseEnd_348736] using wordTrace_append hprefix tailTrace_348736
  have hstable : (prefixWord ++ tailWord_348736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348736).length < 2 ^ (prefixWord ++ tailWord_348736).sum := by decide
  have hdescent : baseEnd_348736 < baseStart_348736 := by decide
  rcases family_descends (prefixWord ++ tailWord_348736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348753 : List Nat := [1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_348753 : Nat := 118140960795 + 348753 * 2 ^ 59
def prefixEnd_348753 : Nat := 4983230072969 + 3 ^ 40 * 348753 * 2
def baseEnd_348753 : Nat := 106120248117083991693997

theorem tailTrace_348753 : CollatzResearch.WordTrace tailWord_348753 prefixEnd_348753 106120248117083991693997 := by
  unfold tailWord_348753
  simp only [CollatzResearch.WordTrace]
  refine ⟨12720066905534918115514913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8480044603689945410343275 12720066905534918115514913)
  ·
    refine ⟨9540050179151188586636185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12720066905534918115514913 9540050179151188586636185)
    ·
      refine ⟨7155037634363391439977139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9540050179151188586636185 7155037634363391439977139)
      ·
        refine ⟨10732556451545087159965709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7155037634363391439977139 10732556451545087159965709)
        ·
          refine ⟨4024708669329407684987141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10732556451545087159965709 4024708669329407684987141)
          ·
            refine ⟨754632875499263940935089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4024708669329407684987141 754632875499263940935089)
            ·
              refine ⟨565974656624447955701317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754632875499263940935089 565974656624447955701317)
              ·
                refine ⟨106120248117083991693997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 565974656624447955701317 106120248117083991693997)
                ·
                  rfl

theorem cell19_348753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_348753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348753 prefixEnd_348753 := by exact prefixLift 348753
  have htrace : WordTrace (prefixWord ++ tailWord_348753) baseStart_348753 baseEnd_348753 := by
    simpa [prefixWord, tailWord_348753, baseEnd_348753] using wordTrace_append hprefix tailTrace_348753
  have hstable : (prefixWord ++ tailWord_348753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348753).length < 2 ^ (prefixWord ++ tailWord_348753).sum := by decide
  have hdescent : baseEnd_348753 < baseStart_348753 := by decide
  rcases family_descends (prefixWord ++ tailWord_348753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348789 : List Nat := [1, 3, 4, 2, 3, 6]
def baseStart_348789 : Nat := 118140960795 + 348789 * 2 ^ 59
def prefixEnd_348789 : Nat := 4983230072969 + 3 ^ 40 * 348789 * 2
def baseEnd_348789 : Nat := 11792355819005174988211

theorem tailTrace_348789 : CollatzResearch.WordTrace tailWord_348789 prefixEnd_348789 11792355819005174988211 := by
  unfold tailWord_348789
  simp only [CollatzResearch.WordTrace]
  refine ⟨12721379933404496263825421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8480919955602997509216947 12721379933404496263825421)
  ·
    refine ⟨4770517475026686098934533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12721379933404496263825421 4770517475026686098934533)
    ·
      refine ⟨894472026567503643550225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4770517475026686098934533 894472026567503643550225)
      ·
        refine ⟨670854019925627732662669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 894472026567503643550225 670854019925627732662669)
        ·
          refine ⟨251570257472110399748501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 670854019925627732662669 251570257472110399748501)
          ·
            refine ⟨11792355819005174988211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 251570257472110399748501 11792355819005174988211)
            ·
              rfl

theorem cell19_348789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 6].length) (baseStart_348789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348789 prefixEnd_348789 := by exact prefixLift 348789
  have htrace : WordTrace (prefixWord ++ tailWord_348789) baseStart_348789 baseEnd_348789 := by
    simpa [prefixWord, tailWord_348789, baseEnd_348789] using wordTrace_append hprefix tailTrace_348789
  have hstable : (prefixWord ++ tailWord_348789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348789).length < 2 ^ (prefixWord ++ tailWord_348789).sum := by decide
  have hdescent : baseEnd_348789 < baseStart_348789 := by decide
  rcases family_descends (prefixWord ++ tailWord_348789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348793 : List Nat := [1, 2, 1, 3, 3, 9]
def baseStart_348793 : Nat := 118140960795 + 348793 * 2 ^ 59
def prefixEnd_348793 : Nat := 4983230072969 + 3 ^ 40 * 348793 * 2
def baseEnd_348793 : Nat := 11792491056708416756111

theorem tailTrace_348793 : CollatzResearch.WordTrace tailWord_348793 prefixEnd_348793 11792491056708416756111 := by
  unfold tailWord_348793
  simp only [CollatzResearch.WordTrace]
  refine ⟨12721525825390004946971033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8481017216926669964647355 12721525825390004946971033)
  ·
    refine ⟨9541144369042503710228275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12721525825390004946971033 9541144369042503710228275)
    ·
      refine ⟨14311716553563755565342413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9541144369042503710228275 14311716553563755565342413)
      ·
        refine ⟨5366893707586408337003405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14311716553563755565342413 5366893707586408337003405)
        ·
          refine ⟨2012585140344903126376277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5366893707586408337003405 2012585140344903126376277)
          ·
            refine ⟨11792491056708416756111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2012585140344903126376277 11792491056708416756111)
            ·
              rfl

theorem cell19_348793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 9].length) (baseStart_348793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348793 prefixEnd_348793 := by exact prefixLift 348793
  have htrace : WordTrace (prefixWord ++ tailWord_348793) baseStart_348793 baseEnd_348793 := by
    simpa [prefixWord, tailWord_348793, baseEnd_348793] using wordTrace_append hprefix tailTrace_348793
  have hstable : (prefixWord ++ tailWord_348793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348793).length < 2 ^ (prefixWord ++ tailWord_348793).sum := by decide
  have hdescent : baseEnd_348793 < baseStart_348793 := by decide
  rcases family_descends (prefixWord ++ tailWord_348793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348802 : List Nat := [3, 4, 3, 1, 1, 2, 1, 4]
def baseStart_348802 : Nat := 118140960795 + 348802 * 2 ^ 59
def prefixEnd_348802 : Nat := 4983230072969 + 3 ^ 40 * 348802 * 2
def baseEnd_348802 : Nat := 106135158073866396604975

theorem tailTrace_348802 : CollatzResearch.WordTrace tailWord_348802 prefixEnd_348802 106135158073866396604975 := by
  unfold tailWord_348802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180463520589349871012165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8481236054904932989365773 3180463520589349871012165)
  ·
    refine ⟨596336910110503100814781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3180463520589349871012165 596336910110503100814781)
    ·
      refine ⟨223626341291438662805543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 596336910110503100814781 223626341291438662805543)
      ·
        refine ⟨335439511937157994208315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223626341291438662805543 335439511937157994208315)
        ·
          refine ⟨503159267905736991312473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335439511937157994208315 503159267905736991312473)
          ·
            refine ⟨377369450929302743484355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503159267905736991312473 377369450929302743484355)
            ·
              refine ⟨566054176393954115226533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377369450929302743484355 566054176393954115226533)
              ·
                refine ⟨106135158073866396604975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566054176393954115226533 106135158073866396604975)
                ·
                  rfl

theorem cell19_348802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_348802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348802 prefixEnd_348802 := by exact prefixLift 348802
  have htrace : WordTrace (prefixWord ++ tailWord_348802) baseStart_348802 baseEnd_348802 := by
    simpa [prefixWord, tailWord_348802, baseEnd_348802] using wordTrace_append hprefix tailTrace_348802
  have hstable : (prefixWord ++ tailWord_348802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348802).length < 2 ^ (prefixWord ++ tailWord_348802).sum := by decide
  have hdescent : baseEnd_348802 < baseStart_348802 := by decide
  rcases family_descends (prefixWord ++ tailWord_348802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348812 : List Nat := [2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_348812 : Nat := 118140960795 + 348812 * 2 ^ 59
def prefixEnd_348812 : Nat := 4983230072969 + 3 ^ 40 * 348812 * 2
def baseEnd_348812 : Nat := 106138200922189336382725

theorem tailTrace_348812 : CollatzResearch.WordTrace tailWord_348812 prefixEnd_348812 106138200922189336382725 := by
  unfold tailWord_348812
  simp only [CollatzResearch.WordTrace]
  refine ⟨6361109406160585595956345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8481479208214114127941793 6361109406160585595956345)
  ·
    refine ⟨4770832054620439196967259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6361109406160585595956345 4770832054620439196967259)
    ·
      refine ⟨7156248081930658795450889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4770832054620439196967259 7156248081930658795450889)
      ·
        refine ⟨5367186061447994096588167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7156248081930658795450889 5367186061447994096588167)
        ·
          refine ⟨8050779092171991144882251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367186061447994096588167 8050779092171991144882251)
          ·
            refine ⟨12076168638257986717323377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050779092171991144882251 12076168638257986717323377)
            ·
              refine ⟨9057126478693490037992533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12076168638257986717323377 9057126478693490037992533)
              ·
                refine ⟨106138200922189336382725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9057126478693490037992533 106138200922189336382725)
                ·
                  rfl

theorem cell19_348812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_348812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348812 prefixEnd_348812 := by exact prefixLift 348812
  have htrace : WordTrace (prefixWord ++ tailWord_348812) baseStart_348812 baseEnd_348812 := by
    simpa [prefixWord, tailWord_348812, baseEnd_348812] using wordTrace_append hprefix tailTrace_348812
  have hstable : (prefixWord ++ tailWord_348812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348812).length < 2 ^ (prefixWord ++ tailWord_348812).sum := by decide
  have hdescent : baseEnd_348812 < baseStart_348812 := by decide
  rcases family_descends (prefixWord ++ tailWord_348812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348846 : List Nat := [4, 1, 4, 1, 1, 2, 6]
def baseStart_348846 : Nat := 118140960795 + 348846 * 2 ^ 59
def prefixEnd_348846 : Nat := 4983230072969 + 3 ^ 40 * 348846 * 2
def baseEnd_348846 : Nat := 35382848868829110542359

theorem tailTrace_348846 : CollatzResearch.WordTrace tailWord_348846 prefixEnd_348846 35382848868829110542359 := by
  unfold tailWord_348846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1590432361774749374831299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8482305929465329999100261 1590432361774749374831299)
  ·
    refine ⟨2385648542662124062246949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1590432361774749374831299 2385648542662124062246949)
    ·
      refine ⟨447309101749148261671303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2385648542662124062246949 447309101749148261671303)
      ·
        refine ⟨670963652623722392506955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447309101749148261671303 670963652623722392506955)
        ·
          refine ⟨1006445478935583588760433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670963652623722392506955 1006445478935583588760433)
          ·
            refine ⟨754834109201687691570325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006445478935583588760433 754834109201687691570325)
            ·
              refine ⟨35382848868829110542359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 754834109201687691570325 35382848868829110542359)
              ·
                rfl

theorem cell19_348846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_348846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348846 prefixEnd_348846 := by exact prefixLift 348846
  have htrace : WordTrace (prefixWord ++ tailWord_348846) baseStart_348846 baseEnd_348846 := by
    simpa [prefixWord, tailWord_348846, baseEnd_348846] using wordTrace_append hprefix tailTrace_348846
  have hstable : (prefixWord ++ tailWord_348846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348846).length < 2 ^ (prefixWord ++ tailWord_348846).sum := by decide
  have hdescent : baseEnd_348846 < baseStart_348846 := by decide
  rcases family_descends (prefixWord ++ tailWord_348846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348882 : List Nat := [3, 2, 2, 2, 3, 2, 2, 3]
def baseStart_348882 : Nat := 118140960795 + 348882 * 2 ^ 59
def prefixEnd_348882 : Nat := 4983230072969 + 3 ^ 40 * 348882 * 2
def baseEnd_348882 : Nat := 106159500860449914826979

theorem tailTrace_348882 : CollatzResearch.WordTrace tailWord_348882 prefixEnd_348882 106159500860449914826979 := by
  unfold tailWord_348882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3181192980516893286740225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8483181281378382097973933 3181192980516893286740225)
  ·
    refine ⟨2385894735387669965055169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3181192980516893286740225 2385894735387669965055169)
    ·
      refine ⟨1789421051540752473791377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2385894735387669965055169 1789421051540752473791377)
      ·
        refine ⟨1342065788655564355343533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1789421051540752473791377 1342065788655564355343533)
        ·
          refine ⟨503274670745836633253825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1342065788655564355343533 503274670745836633253825)
          ·
            refine ⟨377456003059377474940369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503274670745836633253825 377456003059377474940369)
            ·
              refine ⟨283092002294533106205277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377456003059377474940369 283092002294533106205277)
              ·
                refine ⟨106159500860449914826979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283092002294533106205277 106159500860449914826979)
                ·
                  rfl

theorem cell19_348882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_348882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348882 prefixEnd_348882 := by exact prefixLift 348882
  have htrace : WordTrace (prefixWord ++ tailWord_348882) baseStart_348882 baseEnd_348882 := by
    simpa [prefixWord, tailWord_348882, baseEnd_348882] using wordTrace_append hprefix tailTrace_348882
  have hstable : (prefixWord ++ tailWord_348882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348882).length < 2 ^ (prefixWord ++ tailWord_348882).sum := by decide
  have hdescent : baseEnd_348882 < baseStart_348882 := by decide
  rcases family_descends (prefixWord ++ tailWord_348882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348884 : List Nat := [2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_348884 : Nat := 118140960795 + 348884 * 2 ^ 59
def prefixEnd_348884 : Nat := 4983230072969 + 3 ^ 40 * 348884 * 2
def baseEnd_348884 : Nat := 106160109430114502782529

theorem tailTrace_348884 : CollatzResearch.WordTrace tailWord_348884 prefixEnd_348884 106160109430114502782529 := by
  unfold tailWord_348884
  simp only [CollatzResearch.WordTrace]
  refine ⟨6362422434030163744266853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8483229912040218325689137 6362422434030163744266853)
  ·
    refine ⟨1192954206380655702050035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6362422434030163744266853 1192954206380655702050035)
    ·
      refine ⟨1789431309570983553075053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1192954206380655702050035 1789431309570983553075053)
      ·
        refine ⟨671036741089118832403145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1789431309570983553075053 671036741089118832403145)
        ·
          refine ⟨503277555816839124302359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671036741089118832403145 503277555816839124302359)
          ·
            refine ⟨754916333725258686453539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503277555816839124302359 754916333725258686453539)
            ·
              refine ⟨1132374500587888029680309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754916333725258686453539 1132374500587888029680309)
              ·
                refine ⟨106160109430114502782529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1132374500587888029680309 106160109430114502782529)
                ·
                  rfl

theorem cell19_348884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_348884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348884 prefixEnd_348884 := by exact prefixLift 348884
  have htrace : WordTrace (prefixWord ++ tailWord_348884) baseStart_348884 baseEnd_348884 := by
    simpa [prefixWord, tailWord_348884, baseEnd_348884] using wordTrace_append hprefix tailTrace_348884
  have hstable : (prefixWord ++ tailWord_348884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348884).length < 2 ^ (prefixWord ++ tailWord_348884).sum := by decide
  have hdescent : baseEnd_348884 < baseStart_348884 := by decide
  rcases family_descends (prefixWord ++ tailWord_348884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348924 : List Nat := [2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_348924 : Nat := 118140960795 + 348924 * 2 ^ 59
def prefixEnd_348924 : Nat := 4983230072969 + 3 ^ 40 * 348924 * 2
def baseEnd_348924 : Nat := 106172280823406261893531

theorem tailTrace_348924 : CollatzResearch.WordTrace tailWord_348924 prefixEnd_348924 106172280823406261893531 := by
  unfold tailWord_348924
  simp only [CollatzResearch.WordTrace]
  refine ⟨6363151893957707159994913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8484202525276942879993217 6363151893957707159994913)
  ·
    refine ⟨4772363920468280369996185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6363151893957707159994913 4772363920468280369996185)
    ·
      refine ⟨3579272940351210277497139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4772363920468280369996185 3579272940351210277497139)
      ·
        refine ⟨5368909410526815416245709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579272940351210277497139 5368909410526815416245709)
        ·
          refine ⟨2013341028947555781092141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5368909410526815416245709 2013341028947555781092141)
          ·
            refine ⟨755002885855333417909553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2013341028947555781092141 755002885855333417909553)
            ·
              refine ⟨566252164391500063432165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755002885855333417909553 566252164391500063432165)
              ·
                refine ⟨106172280823406261893531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566252164391500063432165 106172280823406261893531)
                ·
                  rfl

theorem cell19_348924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_348924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348924 prefixEnd_348924 := by exact prefixLift 348924
  have htrace : WordTrace (prefixWord ++ tailWord_348924) baseStart_348924 baseEnd_348924 := by
    simpa [prefixWord, tailWord_348924, baseEnd_348924] using wordTrace_append hprefix tailTrace_348924
  have hstable : (prefixWord ++ tailWord_348924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348924).length < 2 ^ (prefixWord ++ tailWord_348924).sum := by decide
  have hdescent : baseEnd_348924 < baseStart_348924 := by decide
  rcases family_descends (prefixWord ++ tailWord_348924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348945 : List Nat := [1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_348945 : Nat := 118140960795 + 348945 * 2 ^ 59
def prefixEnd_348945 : Nat := 4983230072969 + 3 ^ 40 * 348945 * 2
def baseEnd_348945 : Nat := 106178670804884435426807

theorem tailTrace_348945 : CollatzResearch.WordTrace tailWord_348945 prefixEnd_348945 106178670804884435426807 := by
  unfold tailWord_348945
  simp only [CollatzResearch.WordTrace]
  refine ⟨12727069720839334906504289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8484713147226223271002859 12727069720839334906504289)
  ·
    refine ⟨9545302290629501179878217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12727069720839334906504289 9545302290629501179878217)
    ·
      refine ⟨7158976717972125884908663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9545302290629501179878217 7158976717972125884908663)
      ·
        refine ⟨10738465076958188827362995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7158976717972125884908663 10738465076958188827362995)
        ·
          refine ⟨16107697615437283241044493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10738465076958188827362995 16107697615437283241044493)
          ·
            refine ⟨6040386605788981215391685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16107697615437283241044493 6040386605788981215391685)
            ·
              refine ⟨1132572488585433977885941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6040386605788981215391685 1132572488585433977885941)
              ·
                refine ⟨106178670804884435426807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1132572488585433977885941 106178670804884435426807)
                ·
                  rfl

theorem cell19_348945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_348945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348945 prefixEnd_348945 := by exact prefixLift 348945
  have htrace : WordTrace (prefixWord ++ tailWord_348945) baseStart_348945 baseEnd_348945 := by
    simpa [prefixWord, tailWord_348945, baseEnd_348945] using wordTrace_append hprefix tailTrace_348945
  have hstable : (prefixWord ++ tailWord_348945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348945).length < 2 ^ (prefixWord ++ tailWord_348945).sum := by decide
  have hdescent : baseEnd_348945 < baseStart_348945 := by decide
  rcases family_descends (prefixWord ++ tailWord_348945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348964 : List Nat := [2, 3, 1, 3, 10]
def baseStart_348964 : Nat := 118140960795 + 348964 * 2 ^ 59
def prefixEnd_348964 : Nat := 4983230072969 + 3 ^ 40 * 348964 * 2
def baseEnd_348964 : Nat := 3932757489507334111279

theorem tailTrace_348964 : CollatzResearch.WordTrace tailWord_348964 prefixEnd_348964 3932757489507334111279 := by
  unfold tailWord_348964
  simp only [CollatzResearch.WordTrace]
  refine ⟨6363881353885250575722973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8485175138513667434297297 6363881353885250575722973)
  ·
    refine ⟨2386455507706968965896115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6363881353885250575722973 2386455507706968965896115)
    ·
      refine ⟨3579683261560453448844173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386455507706968965896115 3579683261560453448844173)
      ·
        refine ⟨1342381223085170043316565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3579683261560453448844173 1342381223085170043316565)
        ·
          refine ⟨3932757489507334111279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1342381223085170043316565 3932757489507334111279)
          ·
            rfl

theorem cell19_348964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 10].length) (baseStart_348964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348964 prefixEnd_348964 := by exact prefixLift 348964
  have htrace : WordTrace (prefixWord ++ tailWord_348964) baseStart_348964 baseEnd_348964 := by
    simpa [prefixWord, tailWord_348964, baseEnd_348964] using wordTrace_append hprefix tailTrace_348964
  have hstable : (prefixWord ++ tailWord_348964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348964).length < 2 ^ (prefixWord ++ tailWord_348964).sum := by decide
  have hdescent : baseEnd_348964 < baseStart_348964 := by decide
  rcases family_descends (prefixWord ++ tailWord_348964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348981 : List Nat := [1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_348981 : Nat := 118140960795 + 348981 * 2 ^ 59
def prefixEnd_348981 : Nat := 4983230072969 + 3 ^ 40 * 348981 * 2
def baseEnd_348981 : Nat := 106189625058847018626709

theorem tailTrace_348981 : CollatzResearch.WordTrace tailWord_348981 prefixEnd_348981 106189625058847018626709 := by
  unfold tailWord_348981
  simp only [CollatzResearch.WordTrace]
  refine ⟨12728382748708913054814797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8485588499139275369876531 12728382748708913054814797)
  ·
    refine ⟨4773143530765842395555549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12728382748708913054814797 4773143530765842395555549)
    ·
      refine ⟨1789928824037190898333331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4773143530765842395555549 1789928824037190898333331)
      ·
        refine ⟨2684893236055786347499997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789928824037190898333331 2684893236055786347499997)
        ·
          refine ⟨1006834963520919880312499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2684893236055786347499997 1006834963520919880312499)
          ·
            refine ⟨1510252445281379820468749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006834963520919880312499 1510252445281379820468749)
            ·
              refine ⟨566344666980517432675781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1510252445281379820468749 566344666980517432675781)
              ·
                refine ⟨106189625058847018626709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566344666980517432675781 106189625058847018626709)
                ·
                  rfl

theorem cell19_348981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_348981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_348981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_348981 prefixEnd_348981 := by exact prefixLift 348981
  have htrace : WordTrace (prefixWord ++ tailWord_348981) baseStart_348981 baseEnd_348981 := by
    simpa [prefixWord, tailWord_348981, baseEnd_348981] using wordTrace_append hprefix tailTrace_348981
  have hstable : (prefixWord ++ tailWord_348981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348981).length < 2 ^ (prefixWord ++ tailWord_348981).sum := by decide
  have hdescent : baseEnd_348981 < baseStart_348981 := by decide
  rcases family_descends (prefixWord ++ tailWord_348981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349000 : List Nat := [2, 1, 3, 1, 1, 3, 5, 3]
def baseStart_349000 : Nat := 118140960795 + 349000 * 2 ^ 59
def prefixEnd_349000 : Nat := 4983230072969 + 3 ^ 40 * 349000 * 2
def baseEnd_349000 : Nat := 106195406470660604204435

theorem tailTrace_349000 : CollatzResearch.WordTrace tailWord_349000 prefixEnd_349000 106195406470660604204435 := by
  unfold tailWord_349000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6364537867820039649878227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8486050490426719533170969 6364537867820039649878227)
  ·
    refine ⟨9546806801730059474817341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6364537867820039649878227 9546806801730059474817341)
    ·
      refine ⟨3580052550648772303056503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9546806801730059474817341 3580052550648772303056503)
      ·
        refine ⟨5370078825973158454584755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580052550648772303056503 5370078825973158454584755)
        ·
          refine ⟨8055118238959737681877133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370078825973158454584755 8055118238959737681877133)
          ·
            refine ⟨3020669339609901630703925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8055118238959737681877133 3020669339609901630703925)
            ·
              refine ⟨283187750588428277878493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3020669339609901630703925 283187750588428277878493)
              ·
                refine ⟨106195406470660604204435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283187750588428277878493 106195406470660604204435)
                ·
                  rfl

theorem cell19_349000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_349000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349000 prefixEnd_349000 := by exact prefixLift 349000
  have htrace : WordTrace (prefixWord ++ tailWord_349000) baseStart_349000 baseEnd_349000 := by
    simpa [prefixWord, tailWord_349000, baseEnd_349000] using wordTrace_append hprefix tailTrace_349000
  have hstable : (prefixWord ++ tailWord_349000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349000).length < 2 ^ (prefixWord ++ tailWord_349000).sum := by decide
  have hdescent : baseEnd_349000 < baseStart_349000 := by decide
  rcases family_descends (prefixWord ++ tailWord_349000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349059 : List Nat := [1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_349059 : Nat := 118140960795 + 349059 * 2 ^ 59
def prefixEnd_349059 : Nat := 4983230072969 + 3 ^ 40 * 349059 * 2
def baseEnd_349059 : Nat := 106213359275765948893163

theorem tailTrace_349059 : CollatzResearch.WordTrace tailWord_349059 prefixEnd_349059 106213359275765948893163 := by
  unfold tailWord_349059
  simp only [CollatzResearch.WordTrace]
  refine ⟨12731227642426332376154231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8487485094950888250769487 12731227642426332376154231)
  ·
    refine ⟨19096841463639498564231347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12731227642426332376154231 19096841463639498564231347)
    ·
      refine ⟨28645262195459247846347021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19096841463639498564231347 28645262195459247846347021)
      ·
        refine ⟨10741973323297217942380133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28645262195459247846347021 10741973323297217942380133)
        ·
          refine ⟨2014119998118228364196275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10741973323297217942380133 2014119998118228364196275)
          ·
            refine ⟨3021179997177342546294413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014119998118228364196275 3021179997177342546294413)
            ·
              refine ⟨1132942498941503454860405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3021179997177342546294413 1132942498941503454860405)
              ·
                refine ⟨106213359275765948893163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1132942498941503454860405 106213359275765948893163)
                ·
                  rfl

theorem cell19_349059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_349059 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349059 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349059 prefixEnd_349059 := by exact prefixLift 349059
  have htrace : WordTrace (prefixWord ++ tailWord_349059) baseStart_349059 baseEnd_349059 := by
    simpa [prefixWord, tailWord_349059, baseEnd_349059] using wordTrace_append hprefix tailTrace_349059
  have hstable : (prefixWord ++ tailWord_349059).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349059).length < 2 ^ (prefixWord ++ tailWord_349059).sum := by decide
  have hdescent : baseEnd_349059 < baseStart_349059 := by decide
  rcases family_descends (prefixWord ++ tailWord_349059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349074 : List Nat := [3, 2, 3, 2, 2, 2, 5]
def baseStart_349074 : Nat := 118140960795 + 349074 * 2 ^ 59
def prefixEnd_349074 : Nat := 4983230072969 + 3 ^ 40 * 349074 * 2
def baseEnd_349074 : Nat := 35405974516083452853263

theorem tailTrace_349074 : CollatzResearch.WordTrace tailWord_349074 prefixEnd_349074 35405974516083452853263 := by
  unfold tailWord_349074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182943684342997484487569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8487849824914659958633517 3182943684342997484487569)
  ·
    refine ⟨2387207763257248113365677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3182943684342997484487569 2387207763257248113365677)
    ·
      refine ⟨895202911221468042512129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2387207763257248113365677 895202911221468042512129)
      ·
        refine ⟨671402183416101031884097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 895202911221468042512129 671402183416101031884097)
        ·
          refine ⟨503551637562075773913073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671402183416101031884097 503551637562075773913073)
          ·
            refine ⟨377663728171556830434805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503551637562075773913073 377663728171556830434805)
            ·
              refine ⟨35405974516083452853263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 377663728171556830434805 35405974516083452853263)
              ·
                rfl

theorem cell19_349074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_349074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349074 prefixEnd_349074 := by exact prefixLift 349074
  have htrace : WordTrace (prefixWord ++ tailWord_349074) baseStart_349074 baseEnd_349074 := by
    simpa [prefixWord, tailWord_349074, baseEnd_349074] using wordTrace_append hprefix tailTrace_349074
  have hstable : (prefixWord ++ tailWord_349074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349074).length < 2 ^ (prefixWord ++ tailWord_349074).sum := by decide
  have hdescent : baseEnd_349074 < baseStart_349074 := by decide
  rcases family_descends (prefixWord ++ tailWord_349074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349097 : List Nat := [1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_349097 : Nat := 118140960795 + 349097 * 2 ^ 59
def prefixEnd_349097 : Nat := 4983230072969 + 3 ^ 40 * 349097 * 2
def baseEnd_349097 : Nat := 106224922099393120048615

theorem tailTrace_349097 : CollatzResearch.WordTrace tailWord_349097 prefixEnd_349097 106224922099393120048615 := by
  unfold tailWord_349097
  simp only [CollatzResearch.WordTrace]
  refine ⟨12732613616288664866037545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8488409077525776577358363 12732613616288664866037545)
  ·
    refine ⟨9549460212216498649528159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12732613616288664866037545 9549460212216498649528159)
    ·
      refine ⟨14324190318324747974292239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9549460212216498649528159 14324190318324747974292239)
      ·
        refine ⟨21486285477487121961438359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14324190318324747974292239 21486285477487121961438359)
        ·
          refine ⟨32229428216230682942157539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21486285477487121961438359 32229428216230682942157539)
          ·
            refine ⟨48344142324346024413236309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32229428216230682942157539 48344142324346024413236309)
            ·
              refine ⟨566532917863429973592613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 48344142324346024413236309 566532917863429973592613)
              ·
                refine ⟨106224922099393120048615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566532917863429973592613 106224922099393120048615)
                ·
                  rfl

theorem cell19_349097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_349097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349097 prefixEnd_349097 := by exact prefixLift 349097
  have htrace : WordTrace (prefixWord ++ tailWord_349097) baseStart_349097 baseEnd_349097 := by
    simpa [prefixWord, tailWord_349097, baseEnd_349097] using wordTrace_append hprefix tailTrace_349097
  have hstable : (prefixWord ++ tailWord_349097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349097).length < 2 ^ (prefixWord ++ tailWord_349097).sum := by decide
  have hdescent : baseEnd_349097 < baseStart_349097 := by decide
  rcases family_descends (prefixWord ++ tailWord_349097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349192 : List Nat := [2, 1, 3, 2, 1, 4, 6]
def baseStart_349192 : Nat := 118140960795 + 349192 * 2 ^ 59
def prefixEnd_349192 : Nat := 4983230072969 + 3 ^ 40 * 349192 * 2
def baseEnd_349192 : Nat := 35417943052820349312415

theorem tailTrace_349192 : CollatzResearch.WordTrace tailWord_349192 prefixEnd_349192 35417943052820349312415 := by
  unfold tailWord_349192
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368039275472248045372915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8490719033962997393830553 6368039275472248045372915)
  ·
    refine ⟨9552058913208372068059373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6368039275472248045372915 9552058913208372068059373)
    ·
      refine ⟨3582022092453139525522265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9552058913208372068059373 3582022092453139525522265)
      ·
        refine ⟨2686516569339854644141699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3582022092453139525522265 2686516569339854644141699)
        ·
          refine ⟨4029774854009781966212549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686516569339854644141699 4029774854009781966212549)
          ·
            refine ⟨755582785126834118664853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4029774854009781966212549 755582785126834118664853)
            ·
              refine ⟨35417943052820349312415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 755582785126834118664853 35417943052820349312415)
              ·
                rfl

theorem cell19_349192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_349192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349192 prefixEnd_349192 := by exact prefixLift 349192
  have htrace : WordTrace (prefixWord ++ tailWord_349192) baseStart_349192 baseEnd_349192 := by
    simpa [prefixWord, tailWord_349192, baseEnd_349192] using wordTrace_append hprefix tailTrace_349192
  have hstable : (prefixWord ++ tailWord_349192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349192).length < 2 ^ (prefixWord ++ tailWord_349192).sum := by decide
  have hdescent : baseEnd_349192 < baseStart_349192 := by decide
  rcases family_descends (prefixWord ++ tailWord_349192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349266 : List Nat := [3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_349266 : Nat := 118140960795 + 349266 * 2 ^ 59
def prefixEnd_349266 : Nat := 4983230072969 + 3 ^ 40 * 349266 * 2
def baseEnd_349266 : Nat := 106276346236050802292599

theorem tailTrace_349266 : CollatzResearch.WordTrace tailWord_349266 prefixEnd_349266 106276346236050802292599 := by
  unfold tailWord_349266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184694388169101682234913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8492518368450937819293101 3184694388169101682234913)
  ·
    refine ⟨2388520791126826261676185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3184694388169101682234913 2388520791126826261676185)
    ·
      refine ⟨1791390593345119696257139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2388520791126826261676185 1791390593345119696257139)
      ·
        refine ⟨2687085890017679544385709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791390593345119696257139 2687085890017679544385709)
        ·
          refine ⟨1007657208756629829144641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2687085890017679544385709 1007657208756629829144641)
          ·
            refine ⟨755742906567472371858481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007657208756629829144641 755742906567472371858481)
            ·
              refine ⟨566807179925604278893861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755742906567472371858481 566807179925604278893861)
              ·
                refine ⟨106276346236050802292599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566807179925604278893861 106276346236050802292599)
                ·
                  rfl

theorem cell19_349266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_349266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349266 prefixEnd_349266 := by exact prefixLift 349266
  have htrace : WordTrace (prefixWord ++ tailWord_349266) baseStart_349266 baseEnd_349266 := by
    simpa [prefixWord, tailWord_349266, baseEnd_349266] using wordTrace_append hprefix tailTrace_349266
  have hstable : (prefixWord ++ tailWord_349266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349266).length < 2 ^ (prefixWord ++ tailWord_349266).sum := by decide
  have hdescent : baseEnd_349266 < baseStart_349266 := by decide
  rcases family_descends (prefixWord ++ tailWord_349266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349268 : List Nat := [2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_349268 : Nat := 118140960795 + 349268 * 2 ^ 59
def prefixEnd_349268 : Nat := 4983230072969 + 3 ^ 40 * 349268 * 2
def baseEnd_349268 : Nat := 106276954805715390248149

theorem tailTrace_349268 : CollatzResearch.WordTrace tailWord_349268 prefixEnd_349268 106276954805715390248149 := by
  unfold tailWord_349268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6369425249334580535256229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8492566999112774047008305 6369425249334580535256229)
  ·
    refine ⟨1194267234250233850360543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6369425249334580535256229 1194267234250233850360543)
    ·
      refine ⟨1791400851375350775540815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194267234250233850360543 1791400851375350775540815)
      ·
        refine ⟨2687101277063026163311223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791400851375350775540815 2687101277063026163311223)
        ·
          refine ⟨4030651915594539244966835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687101277063026163311223 4030651915594539244966835)
          ·
            refine ⟨6045977873391808867450253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030651915594539244966835 6045977873391808867450253)
            ·
              refine ⟨2267241702521928325293845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6045977873391808867450253 2267241702521928325293845)
              ·
                refine ⟨106276954805715390248149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2267241702521928325293845 106276954805715390248149)
                ·
                  rfl

theorem cell19_349268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_349268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349268 prefixEnd_349268 := by exact prefixLift 349268
  have htrace : WordTrace (prefixWord ++ tailWord_349268) baseStart_349268 baseEnd_349268 := by
    simpa [prefixWord, tailWord_349268, baseEnd_349268] using wordTrace_append hprefix tailTrace_349268
  have hstable : (prefixWord ++ tailWord_349268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349268).length < 2 ^ (prefixWord ++ tailWord_349268).sum := by decide
  have hdescent : baseEnd_349268 < baseStart_349268 := by decide
  rcases family_descends (prefixWord ++ tailWord_349268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349287 : List Nat := [1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_349287 : Nat := 118140960795 + 349287 * 2 ^ 59
def prefixEnd_349287 : Nat := 4983230072969 + 3 ^ 40 * 349287 * 2
def baseEnd_349287 : Nat := 106282736217528975825875

theorem tailTrace_349287 : CollatzResearch.WordTrace tailWord_349287 prefixEnd_349287 106282736217528975825875 := by
  unfold tailWord_349287
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739543485600327315454115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8493028990400218210302743 12739543485600327315454115)
  ·
    refine ⟨19109315228400490973181173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12739543485600327315454115 19109315228400490973181173)
    ·
      refine ⟨1791498302662546028735735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19109315228400490973181173 1791498302662546028735735)
      ·
        refine ⟨2687247453993819043103603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791498302662546028735735 2687247453993819043103603)
        ·
          refine ⟨4030871180990728564655405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687247453993819043103603 4030871180990728564655405)
          ·
            refine ⟨1511576692871523211745777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4030871180990728564655405 1511576692871523211745777)
            ·
              refine ⟨1133682519653642408809333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511576692871523211745777 1133682519653642408809333)
              ·
                refine ⟨106282736217528975825875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133682519653642408809333 106282736217528975825875)
                ·
                  rfl

theorem cell19_349287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_349287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349287 prefixEnd_349287 := by exact prefixLift 349287
  have htrace : WordTrace (prefixWord ++ tailWord_349287) baseStart_349287 baseEnd_349287 := by
    simpa [prefixWord, tailWord_349287, baseEnd_349287] using wordTrace_append hprefix tailTrace_349287
  have hstable : (prefixWord ++ tailWord_349287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349287).length < 2 ^ (prefixWord ++ tailWord_349287).sum := by decide
  have hdescent : baseEnd_349287 < baseStart_349287 := by decide
  rcases family_descends (prefixWord ++ tailWord_349287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349397 : List Nat := [1, 3, 2, 4, 1, 3, 2, 3]
def baseStart_349397 : Nat := 118140960795 + 349397 * 2 ^ 59
def prefixEnd_349397 : Nat := 4983230072969 + 3 ^ 40 * 349397 * 2
def baseEnd_349397 : Nat := 106316207549081313381131

theorem tailTrace_349397 : CollatzResearch.WordTrace tailWord_349397 prefixEnd_349397 106316207549081313381131 := by
  unfold tailWord_349397
  simp only [CollatzResearch.WordTrace]
  refine ⟨12743555515201816101958445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8495703676801210734638963 12743555515201816101958445)
  ·
    refine ⟨4778833318200681038234417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12743555515201816101958445 4778833318200681038234417)
    ·
      refine ⟨3584124988650510778675813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4778833318200681038234417 3584124988650510778675813)
      ·
        refine ⟨672023435371970771001715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3584124988650510778675813 672023435371970771001715)
        ·
          refine ⟨1008035153057956156502573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672023435371970771001715 1008035153057956156502573)
          ·
            refine ⟨378013182396733558688465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1008035153057956156502573 378013182396733558688465)
            ·
              refine ⟨283509886797550169016349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378013182396733558688465 283509886797550169016349)
              ·
                refine ⟨106316207549081313381131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283509886797550169016349 106316207549081313381131)
                ·
                  rfl

theorem cell19_349397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_349397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349397 prefixEnd_349397 := by exact prefixLift 349397
  have htrace : WordTrace (prefixWord ++ tailWord_349397) baseStart_349397 baseEnd_349397 := by
    simpa [prefixWord, tailWord_349397, baseEnd_349397] using wordTrace_append hprefix tailTrace_349397
  have hstable : (prefixWord ++ tailWord_349397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349397).length < 2 ^ (prefixWord ++ tailWord_349397).sum := by decide
  have hdescent : baseEnd_349397 < baseStart_349397 := by decide
  rcases family_descends (prefixWord ++ tailWord_349397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349420 : List Nat := [2, 2, 1, 1, 2, 6, 5]
def baseStart_349420 : Nat := 118140960795 + 349420 * 2 ^ 59
def prefixEnd_349420 : Nat := 4983230072969 + 3 ^ 40 * 349420 * 2
def baseEnd_349420 : Nat := 35441068700074691623319

theorem tailTrace_349420 : CollatzResearch.WordTrace tailWord_349420 prefixEnd_349420 35441068700074691623319 := by
  unfold tailWord_349420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6372197197059245515022857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8496262929412327353363809 6372197197059245515022857)
  ·
    refine ⟨4779147897794434136267143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6372197197059245515022857 4779147897794434136267143)
    ·
      refine ⟨7168721846691651204400715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779147897794434136267143 7168721846691651204400715)
      ·
        refine ⟨10753082770037476806601073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7168721846691651204400715 10753082770037476806601073)
        ·
          refine ⟨8064812077528107604950805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10753082770037476806601073 8064812077528107604950805)
          ·
            refine ⟨378038066134130043982069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8064812077528107604950805 378038066134130043982069)
            ·
              refine ⟨35441068700074691623319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 378038066134130043982069 35441068700074691623319)
              ·
                rfl

theorem cell19_349420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_349420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349420 prefixEnd_349420 := by exact prefixLift 349420
  have htrace : WordTrace (prefixWord ++ tailWord_349420) baseStart_349420 baseEnd_349420 := by
    simpa [prefixWord, tailWord_349420, baseEnd_349420] using wordTrace_append hprefix tailTrace_349420
  have hstable : (prefixWord ++ tailWord_349420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349420).length < 2 ^ (prefixWord ++ tailWord_349420).sum := by decide
  have hdescent : baseEnd_349420 < baseStart_349420 := by decide
  rcases family_descends (prefixWord ++ tailWord_349420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349439 : List Nat := [1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_349439 : Nat := 118140960795 + 349439 * 2 ^ 59
def prefixEnd_349439 : Nat := 4983230072969 + 3 ^ 40 * 349439 * 2
def baseEnd_349439 : Nat := 106328987512037660447683

theorem tailTrace_349439 : CollatzResearch.WordTrace tailWord_349439 prefixEnd_349439 106328987512037660447683 := by
  unfold tailWord_349439
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745087381049657274987371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8496724920699771516658247 12745087381049657274987371)
  ·
    refine ⟨19117631071574485912481057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12745087381049657274987371 19117631071574485912481057)
    ·
      refine ⟨14338223303680864434360793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19117631071574485912481057 14338223303680864434360793)
      ·
        refine ⟨10753667477760648325770595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14338223303680864434360793 10753667477760648325770595)
        ·
          refine ⟨16130501216640972488655893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10753667477760648325770595 16130501216640972488655893)
          ·
            refine ⟨756117244530045585405745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16130501216640972488655893 756117244530045585405745)
            ·
              refine ⟨567087933397534189054309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756117244530045585405745 567087933397534189054309)
              ·
                refine ⟨106328987512037660447683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 567087933397534189054309 106328987512037660447683)
                ·
                  rfl

theorem cell19_349439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_349439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349439 prefixEnd_349439 := by exact prefixLift 349439
  have htrace : WordTrace (prefixWord ++ tailWord_349439) baseStart_349439 baseEnd_349439 := by
    simpa [prefixWord, tailWord_349439, baseEnd_349439] using wordTrace_append hprefix tailTrace_349439
  have hstable : (prefixWord ++ tailWord_349439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349439).length < 2 ^ (prefixWord ++ tailWord_349439).sum := by decide
  have hdescent : baseEnd_349439 < baseStart_349439 := by decide
  rcases family_descends (prefixWord ++ tailWord_349439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349572 : List Nat := [2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_349572 : Nat := 118140960795 + 349572 * 2 ^ 59
def prefixEnd_349572 : Nat := 4983230072969 + 3 ^ 40 * 349572 * 2
def baseEnd_349572 : Nat := 106369457394732759491765

theorem tailTrace_349572 : CollatzResearch.WordTrace tailWord_349572 prefixEnd_349572 106369457394732759491765 := by
  unfold tailWord_349572
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374969144783910494789485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8499958859711880659719313 6374969144783910494789485)
  ·
    refine ⟨2390613429293966435546057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6374969144783910494789485 2390613429293966435546057)
    ·
      refine ⟨1792960071970474826659543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2390613429293966435546057 1792960071970474826659543)
      ·
        refine ⟨2689440107955712239989315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792960071970474826659543 2689440107955712239989315)
        ·
          refine ⟨4034160161933568359983973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689440107955712239989315 4034160161933568359983973)
          ·
            refine ⟨756405030362544067496995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4034160161933568359983973 756405030362544067496995)
            ·
              refine ⟨1134607545543816101245493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756405030362544067496995 1134607545543816101245493)
              ·
                refine ⟨106369457394732759491765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1134607545543816101245493 106369457394732759491765)
                ·
                  rfl

theorem cell19_349572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_349572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349572 prefixEnd_349572 := by exact prefixLift 349572
  have htrace : WordTrace (prefixWord ++ tailWord_349572) baseStart_349572 baseEnd_349572 := by
    simpa [prefixWord, tailWord_349572, baseEnd_349572] using wordTrace_append hprefix tailTrace_349572
  have hstable : (prefixWord ++ tailWord_349572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349572).length < 2 ^ (prefixWord ++ tailWord_349572).sum := by decide
  have hdescent : baseEnd_349572 < baseStart_349572 := by decide
  rcases family_descends (prefixWord ++ tailWord_349572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349593 : List Nat := [1, 2, 1, 2, 1, 5, 7]
def baseStart_349593 : Nat := 118140960795 + 349593 * 2 ^ 59
def prefixEnd_349593 : Nat := 4983230072969 + 3 ^ 40 * 349593 * 2
def baseEnd_349593 : Nat := 35458615792070311008347

theorem tailTrace_349593 : CollatzResearch.WordTrace tailWord_349593 prefixEnd_349593 35458615792070311008347 := by
  unfold tailWord_349593
  simp only [CollatzResearch.WordTrace]
  refine ⟨12750704222491741576093433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8500469481661161050728955 12750704222491741576093433)
  ·
    refine ⟨9563028166868806182070075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12750704222491741576093433 9563028166868806182070075)
    ·
      refine ⟨14344542250303209273105113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9563028166868806182070075 14344542250303209273105113)
      ·
        refine ⟨10758406687727406954828835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14344542250303209273105113 10758406687727406954828835)
        ·
          refine ⟨16137610031591110432243253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10758406687727406954828835 16137610031591110432243253)
          ·
            refine ⟨1512900940461666603022805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16137610031591110432243253 1512900940461666603022805)
            ·
              refine ⟨35458615792070311008347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1512900940461666603022805 35458615792070311008347)
              ·
                rfl

theorem cell19_349593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_349593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349593 prefixEnd_349593 := by exact prefixLift 349593
  have htrace : WordTrace (prefixWord ++ tailWord_349593) baseStart_349593 baseEnd_349593 := by
    simpa [prefixWord, tailWord_349593, baseEnd_349593] using wordTrace_append hprefix tailTrace_349593
  have hstable : (prefixWord ++ tailWord_349593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349593).length < 2 ^ (prefixWord ++ tailWord_349593).sum := by decide
  have hdescent : baseEnd_349593 < baseStart_349593 := by decide
  rcases family_descends (prefixWord ++ tailWord_349593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349612 : List Nat := [2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_349612 : Nat := 118140960795 + 349612 * 2 ^ 59
def prefixEnd_349612 : Nat := 4983230072969 + 3 ^ 40 * 349612 * 2
def baseEnd_349612 : Nat := 106381628788024518602767

theorem tailTrace_349612 : CollatzResearch.WordTrace tailWord_349612 prefixEnd_349612 106381628788024518602767 := by
  unfold tailWord_349612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375698604711453910517545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8500931472948605214023393 6375698604711453910517545)
  ·
    refine ⟨4781773953533590432888159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6375698604711453910517545 4781773953533590432888159)
    ·
      refine ⟨7172660930300385649332239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4781773953533590432888159 7172660930300385649332239)
      ·
        refine ⟨10758991395450578473998359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7172660930300385649332239 10758991395450578473998359)
        ·
          refine ⟨16138487093175867710997539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10758991395450578473998359 16138487093175867710997539)
          ·
            refine ⟨24207730639763801566496309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16138487093175867710997539 24207730639763801566496309)
            ·
              refine ⟨2269474747477856396859029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24207730639763801566496309 2269474747477856396859029)
              ·
                refine ⟨106381628788024518602767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2269474747477856396859029 106381628788024518602767)
                ·
                  rfl

theorem cell19_349612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_349612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349612 prefixEnd_349612 := by exact prefixLift 349612
  have htrace : WordTrace (prefixWord ++ tailWord_349612) baseStart_349612 baseEnd_349612 := by
    simpa [prefixWord, tailWord_349612, baseEnd_349612] using wordTrace_append hprefix tailTrace_349612
  have hstable : (prefixWord ++ tailWord_349612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349612).length < 2 ^ (prefixWord ++ tailWord_349612).sum := by decide
  have hdescent : baseEnd_349612 < baseStart_349612 := by decide
  rcases family_descends (prefixWord ++ tailWord_349612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349650 : List Nat := [3, 2, 2, 12]
def baseStart_349650 : Nat := 118140960795 + 349650 * 2 ^ 59
def prefixEnd_349650 : Nat := 4983230072969 + 3 ^ 40 * 349650 * 2
def baseEnd_349650 : Nat := 1313496192736440614299

theorem tailTrace_349650 : CollatzResearch.WordTrace tailWord_349650 prefixEnd_349650 1313496192736440614299 := by
  unfold tailWord_349650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188195795821310077729601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8501855455523493540612269 3188195795821310077729601)
  ·
    refine ⟨2391146846865982558297201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3188195795821310077729601 2391146846865982558297201)
    ·
      refine ⟨1793360135149486918722901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2391146846865982558297201 1793360135149486918722901)
      ·
        refine ⟨1313496192736440614299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1793360135149486918722901 1313496192736440614299)
        ·
          rfl

theorem cell19_349650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 12].length) (baseStart_349650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349650 prefixEnd_349650 := by exact prefixLift 349650
  have htrace : WordTrace (prefixWord ++ tailWord_349650) baseStart_349650 baseEnd_349650 := by
    simpa [prefixWord, tailWord_349650, baseEnd_349650] using wordTrace_append hprefix tailTrace_349650
  have hstable : (prefixWord ++ tailWord_349650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349650).length < 2 ^ (prefixWord ++ tailWord_349650).sum := by decide
  have hdescent : baseEnd_349650 < baseStart_349650 := by decide
  rcases family_descends (prefixWord ++ tailWord_349650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349667 : List Nat := [1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_349667 : Nat := 118140960795 + 349667 * 2 ^ 59
def prefixEnd_349667 : Nat := 4983230072969 + 3 ^ 40 * 349667 * 2
def baseEnd_349667 : Nat := 106398364453800687380395

theorem tailTrace_349667 : CollatzResearch.WordTrace tailWord_349667 prefixEnd_349667 106398364453800687380395 := by
  unfold tailWord_349667
  simp only [CollatzResearch.WordTrace]
  refine ⟨12753403224223652214287255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8502268816149101476191503 12753403224223652214287255)
  ·
    refine ⟨19130104836335478321430883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12753403224223652214287255 19130104836335478321430883)
    ·
      refine ⟨28695157254503217482146325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19130104836335478321430883 28695157254503217482146325)
      ·
        refine ⟨1345085496304838319475609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28695157254503217482146325 1345085496304838319475609)
        ·
          refine ⟨1008814122228628739606707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345085496304838319475609 1008814122228628739606707)
          ·
            refine ⟨1513221183342943109410061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008814122228628739606707 1513221183342943109410061)
            ·
              refine ⟨567457943753603666028773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1513221183342943109410061 567457943753603666028773)
              ·
                refine ⟨106398364453800687380395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 567457943753603666028773 106398364453800687380395)
                ·
                  rfl

theorem cell19_349667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_349667 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349667 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349667 prefixEnd_349667 := by exact prefixLift 349667
  have htrace : WordTrace (prefixWord ++ tailWord_349667) baseStart_349667 baseEnd_349667 := by
    simpa [prefixWord, tailWord_349667, baseEnd_349667] using wordTrace_append hprefix tailTrace_349667
  have hstable : (prefixWord ++ tailWord_349667).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349667).length < 2 ^ (prefixWord ++ tailWord_349667).sum := by decide
  have hdescent : baseEnd_349667 < baseStart_349667 := by decide
  rcases family_descends (prefixWord ++ tailWord_349667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349783 : List Nat := [1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_349783 : Nat := 118140960795 + 349783 * 2 ^ 59
def prefixEnd_349783 : Nat := 4983230072969 + 3 ^ 40 * 349783 * 2
def baseEnd_349783 : Nat := 106433661494346788802301

theorem tailTrace_349783 : CollatzResearch.WordTrace tailWord_349783 prefixEnd_349783 106433661494346788802301 := by
  unfold tailWord_349783
  simp only [CollatzResearch.WordTrace]
  refine ⟨12757634091803404025510003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8505089394535602683673335 12757634091803404025510003)
  ·
    refine ⟨19136451137705106038265005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12757634091803404025510003 19136451137705106038265005)
    ·
      refine ⟨7176169176639414764349377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19136451137705106038265005 7176169176639414764349377)
      ·
        refine ⟨5382126882479561073262033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7176169176639414764349377 5382126882479561073262033)
        ·
          refine ⟨4036595161859670804946525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5382126882479561073262033 4036595161859670804946525)
          ·
            refine ⟨1513723185697376551854947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4036595161859670804946525 1513723185697376551854947)
            ·
              refine ⟨2270584778546064827782421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513723185697376551854947 2270584778546064827782421)
              ·
                refine ⟨106433661494346788802301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2270584778546064827782421 106433661494346788802301)
                ·
                  rfl

theorem cell19_349783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_349783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349783 prefixEnd_349783 := by exact prefixLift 349783
  have htrace : WordTrace (prefixWord ++ tailWord_349783) baseStart_349783 baseEnd_349783 := by
    simpa [prefixWord, tailWord_349783, baseEnd_349783] using wordTrace_append hprefix tailTrace_349783
  have hstable : (prefixWord ++ tailWord_349783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349783).length < 2 ^ (prefixWord ++ tailWord_349783).sum := by decide
  have hdescent : baseEnd_349783 < baseStart_349783 := by decide
  rcases family_descends (prefixWord ++ tailWord_349783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349800 : List Nat := [2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_349800 : Nat := 118140960795 + 349800 * 2 ^ 59
def prefixEnd_349800 : Nat := 4983230072969 + 3 ^ 40 * 349800 * 2
def baseEnd_349800 : Nat := 106438834336495786424477

theorem tailTrace_349800 : CollatzResearch.WordTrace tailWord_349800 prefixEnd_349800 106438834336495786424477 := by
  unfold tailWord_349800
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379127066370907964439427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8505502755161210619252569 6379127066370907964439427)
  ·
    refine ⟨9568690599556361946659141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6379127066370907964439427 9568690599556361946659141)
    ·
      refine ⟨1794129487416817864998589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9568690599556361946659141 1794129487416817864998589)
      ·
        refine ⟨672798557781306699374471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1794129487416817864998589 672798557781306699374471)
        ·
          refine ⟨1009197836671960049061707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672798557781306699374471 1009197836671960049061707)
          ·
            refine ⟨1513796755007940073592561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009197836671960049061707 1513796755007940073592561)
            ·
              refine ⟨1135347566255955055194421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1513796755007940073592561 1135347566255955055194421)
              ·
                refine ⟨106438834336495786424477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1135347566255955055194421 106438834336495786424477)
                ·
                  rfl

theorem cell19_349800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_349800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349800 prefixEnd_349800 := by exact prefixLift 349800
  have htrace : WordTrace (prefixWord ++ tailWord_349800) baseStart_349800 baseEnd_349800 := by
    simpa [prefixWord, tailWord_349800, baseEnd_349800] using wordTrace_append hprefix tailTrace_349800
  have hstable : (prefixWord ++ tailWord_349800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349800).length < 2 ^ (prefixWord ++ tailWord_349800).sum := by decide
  have hdescent : baseEnd_349800 < baseStart_349800 := by decide
  rcases family_descends (prefixWord ++ tailWord_349800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349821 : List Nat := [1, 4, 1, 1, 4, 8]
def baseStart_349821 : Nat := 118140960795 + 349821 * 2 ^ 59
def prefixEnd_349821 : Nat := 4983230072969 + 3 ^ 40 * 349821 * 2
def baseEnd_349821 : Nat := 11827247146441551106417

theorem tailTrace_349821 : CollatzResearch.WordTrace tailWord_349821 prefixEnd_349821 11827247146441551106417 := by
  unfold tailWord_349821
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759020065665736515393317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8506013377110491010262211 12759020065665736515393317)
  ·
    refine ⟨2392316262312325596636247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12759020065665736515393317 2392316262312325596636247)
    ·
      refine ⟨3588474393468488394954371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392316262312325596636247 3588474393468488394954371)
      ·
        refine ⟨5382711590202732592431557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588474393468488394954371 5382711590202732592431557)
        ·
          refine ⟨1009258423163012361080917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5382711590202732592431557 1009258423163012361080917)
          ·
            refine ⟨11827247146441551106417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1009258423163012361080917 11827247146441551106417)
            ·
              rfl

theorem cell19_349821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 8].length) (baseStart_349821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349821 prefixEnd_349821 := by exact prefixLift 349821
  have htrace : WordTrace (prefixWord ++ tailWord_349821) baseStart_349821 baseEnd_349821 := by
    simpa [prefixWord, tailWord_349821, baseEnd_349821] using wordTrace_append hprefix tailTrace_349821
  have hstable : (prefixWord ++ tailWord_349821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349821).length < 2 ^ (prefixWord ++ tailWord_349821).sum := by decide
  have hdescent : baseEnd_349821 < baseStart_349821 := by decide
  rcases family_descends (prefixWord ++ tailWord_349821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349838 : List Nat := [4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_349838 : Nat := 118140960795 + 349838 * 2 ^ 59
def prefixEnd_349838 : Nat := 4983230072969 + 3 ^ 40 * 349838 * 2
def baseEnd_349838 : Nat := 106450397160122957579929

theorem tailTrace_349838 : CollatzResearch.WordTrace tailWord_349838 prefixEnd_349838 106450397160122957579929 := by
  unfold tailWord_349838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594955013325518552345271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8506426737736098945841445 1594955013325518552345271)
  ·
    refine ⟨2392432519988277828517907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1594955013325518552345271 2392432519988277828517907)
    ·
      refine ⟨3588648779982416742776861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392432519988277828517907 3588648779982416742776861)
      ·
        refine ⟨1345743292493406278541323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3588648779982416742776861 1345743292493406278541323)
        ·
          refine ⟨2018614938740109417811985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345743292493406278541323 2018614938740109417811985)
          ·
            refine ⟨1513961204055082063358989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2018614938740109417811985 1513961204055082063358989)
            ·
              refine ⟨567735451520655773759621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1513961204055082063358989 567735451520655773759621)
              ·
                refine ⟨106450397160122957579929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 567735451520655773759621 106450397160122957579929)
                ·
                  rfl

theorem cell19_349838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_349838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349838 prefixEnd_349838 := by exact prefixLift 349838
  have htrace : WordTrace (prefixWord ++ tailWord_349838) baseStart_349838 baseEnd_349838 := by
    simpa [prefixWord, tailWord_349838, baseEnd_349838] using wordTrace_append hprefix tailTrace_349838
  have hstable : (prefixWord ++ tailWord_349838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349838).length < 2 ^ (prefixWord ++ tailWord_349838).sum := by decide
  have hdescent : baseEnd_349838 < baseStart_349838 := by decide
  rcases family_descends (prefixWord ++ tailWord_349838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349910 : List Nat := [5, 2, 1, 3, 1, 1, 1, 5]
def baseStart_349910 : Nat := 118140960795 + 349910 * 2 ^ 59
def prefixEnd_349910 : Nat := 4983230072969 + 3 ^ 40 * 349910 * 2
def baseEnd_349910 : Nat := 106472305668048123979733

theorem tailTrace_349910 : CollatzResearch.WordTrace tailWord_349910 prefixEnd_349910 106472305668048123979733 := by
  unfold tailWord_349910
  simp only [CollatzResearch.WordTrace]
  refine ⟨797641635146456544711449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8508177441562203143588789 797641635146456544711449)
  ·
    refine ⟨598231226359842408533587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 797641635146456544711449 598231226359842408533587)
    ·
      refine ⟨897346839539763612800381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598231226359842408533587 897346839539763612800381)
      ·
        refine ⟨336505064827411354800143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 897346839539763612800381 336505064827411354800143)
        ·
          refine ⟨504757597241117032200215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336505064827411354800143 504757597241117032200215)
          ·
            refine ⟨757136395861675548300323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504757597241117032200215 757136395861675548300323)
            ·
              refine ⟨1135704593792513322450485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757136395861675548300323 1135704593792513322450485)
              ·
                refine ⟨106472305668048123979733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1135704593792513322450485 106472305668048123979733)
                ·
                  rfl

theorem cell19_349910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_349910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349910 prefixEnd_349910 := by exact prefixLift 349910
  have htrace : WordTrace (prefixWord ++ tailWord_349910) baseStart_349910 baseEnd_349910 := by
    simpa [prefixWord, tailWord_349910, baseEnd_349910] using wordTrace_append hprefix tailTrace_349910
  have hstable : (prefixWord ++ tailWord_349910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349910).length < 2 ^ (prefixWord ++ tailWord_349910).sum := by decide
  have hdescent : baseEnd_349910 < baseStart_349910 := by decide
  rcases family_descends (prefixWord ++ tailWord_349910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349914 : List Nat := [3, 1, 1, 2, 2, 3, 4, 3]
def baseStart_349914 : Nat := 118140960795 + 349914 * 2 ^ 59
def prefixEnd_349914 : Nat := 4983230072969 + 3 ^ 40 * 349914 * 2
def baseEnd_349914 : Nat := 106473522807377299890833

theorem tailTrace_349914 : CollatzResearch.WordTrace tailWord_349914 prefixEnd_349914 106473522807377299890833 := by
  unfold tailWord_349914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190603013582203349632199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8508274702885875599019197 3190603013582203349632199)
  ·
    refine ⟨4785904520373305024448299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190603013582203349632199 4785904520373305024448299)
    ·
      refine ⟨7178856780559957536672449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4785904520373305024448299 7178856780559957536672449)
      ·
        refine ⟨5384142585419968152504337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7178856780559957536672449 5384142585419968152504337)
        ·
          refine ⟨4038106939064976114378253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5384142585419968152504337 4038106939064976114378253)
          ·
            refine ⟨1514290102149366042891845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4038106939064976114378253 1514290102149366042891845)
            ·
              refine ⟨283929394153006133042221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1514290102149366042891845 283929394153006133042221)
              ·
                refine ⟨106473522807377299890833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283929394153006133042221 106473522807377299890833)
                ·
                  rfl

theorem cell19_349914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_349914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349914 prefixEnd_349914 := by exact prefixLift 349914
  have htrace : WordTrace (prefixWord ++ tailWord_349914) baseStart_349914 baseEnd_349914 := by
    simpa [prefixWord, tailWord_349914, baseEnd_349914] using wordTrace_append hprefix tailTrace_349914
  have hstable : (prefixWord ++ tailWord_349914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349914).length < 2 ^ (prefixWord ++ tailWord_349914).sum := by decide
  have hdescent : baseEnd_349914 < baseStart_349914 := by decide
  rcases family_descends (prefixWord ++ tailWord_349914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349933 : List Nat := [1, 5, 1, 2, 1, 4, 5]
def baseStart_349933 : Nat := 118140960795 + 349933 * 2 ^ 59
def prefixEnd_349933 : Nat := 4983230072969 + 3 ^ 40 * 349933 * 2
def baseEnd_349933 : Nat := 35493101406396961822853

theorem tailTrace_349933 : CollatzResearch.WordTrace tailWord_349933 prefixEnd_349933 35493101406396961822853 := by
  unfold tailWord_349933
  simp only [CollatzResearch.WordTrace]
  refine ⟨12763105041259979643470453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8508736694173319762313635 12763105041259979643470453)
  ·
    refine ⟨1196541097618123091575355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12763105041259979643470453 1196541097618123091575355)
    ·
      refine ⟨1794811646427184637363033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196541097618123091575355 1794811646427184637363033)
      ·
        refine ⟨1346108734820388478022275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1794811646427184637363033 1346108734820388478022275)
        ·
          refine ⟨2019163102230582717033413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346108734820388478022275 2019163102230582717033413)
          ·
            refine ⟨378593081668234259443765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2019163102230582717033413 378593081668234259443765)
            ·
              refine ⟨35493101406396961822853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 378593081668234259443765 35493101406396961822853)
              ·
                rfl

theorem cell19_349933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_349933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349933 prefixEnd_349933 := by exact prefixLift 349933
  have htrace : WordTrace (prefixWord ++ tailWord_349933) baseStart_349933 baseEnd_349933 := by
    simpa [prefixWord, tailWord_349933, baseEnd_349933] using wordTrace_append hprefix tailTrace_349933
  have hstable : (prefixWord ++ tailWord_349933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349933).length < 2 ^ (prefixWord ++ tailWord_349933).sum := by decide
  have hdescent : baseEnd_349933 < baseStart_349933 := by decide
  rcases family_descends (prefixWord ++ tailWord_349933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349950 : List Nat := [4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_349950 : Nat := 118140960795 + 349950 * 2 ^ 59
def prefixEnd_349950 : Nat := 4983230072969 + 3 ^ 40 * 349950 * 2
def baseEnd_349950 : Nat := 106484477061339883090735

theorem tailTrace_349950 : CollatzResearch.WordTrace tailWord_349950 prefixEnd_349950 106484477061339883090735 := by
  unfold tailWord_349950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595465635274798943354913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8509150054798927697892869 1595465635274798943354913)
  ·
    refine ⟨1196599226456099207516185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1595465635274798943354913 1196599226456099207516185)
    ·
      refine ⟨897449419842074405637139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1196599226456099207516185 897449419842074405637139)
      ·
        refine ⟨1346174129763111608455709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897449419842074405637139 1346174129763111608455709)
        ·
          refine ⟨504815298661166853170891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1346174129763111608455709 504815298661166853170891)
          ·
            refine ⟨757222947991750279756337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504815298661166853170891 757222947991750279756337)
            ·
              refine ⟨567917210993812709817253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757222947991750279756337 567917210993812709817253)
              ·
                refine ⟨106484477061339883090735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 567917210993812709817253 106484477061339883090735)
                ·
                  rfl

theorem cell19_349950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_349950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349950 prefixEnd_349950 := by exact prefixLift 349950
  have htrace : WordTrace (prefixWord ++ tailWord_349950) baseStart_349950 baseEnd_349950 := by
    simpa [prefixWord, tailWord_349950, baseEnd_349950] using wordTrace_append hprefix tailTrace_349950
  have hstable : (prefixWord ++ tailWord_349950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349950).length < 2 ^ (prefixWord ++ tailWord_349950).sum := by decide
  have hdescent : baseEnd_349950 < baseStart_349950 := by decide
  rcases family_descends (prefixWord ++ tailWord_349950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349973 : List Nat := [1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_349973 : Nat := 118140960795 + 349973 * 2 ^ 59
def prefixEnd_349973 : Nat := 4983230072969 + 3 ^ 40 * 349973 * 2
def baseEnd_349973 : Nat := 106491475612482644579561

theorem tailTrace_349973 : CollatzResearch.WordTrace tailWord_349973 prefixEnd_349973 106491475612482644579561 := by
  unfold tailWord_349973
  simp only [CollatzResearch.WordTrace]
  refine ⟨12764563961115066474926573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8509709307410044316617715 12764563961115066474926573)
  ·
    refine ⟨4786711485418149928097465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12764563961115066474926573 4786711485418149928097465)
    ·
      refine ⟨3590033614063612446073099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4786711485418149928097465 3590033614063612446073099)
      ·
        refine ⟨5385050421095418669109649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590033614063612446073099 5385050421095418669109649)
        ·
          refine ⟨4038787815821564001832237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5385050421095418669109649 4038787815821564001832237)
          ·
            refine ⟨1514545430933086500687089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4038787815821564001832237 1514545430933086500687089)
            ·
              refine ⟨1135909073199814875515317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514545430933086500687089 1135909073199814875515317)
              ·
                refine ⟨106491475612482644579561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1135909073199814875515317 106491475612482644579561)
                ·
                  rfl

theorem cell19_349973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_349973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349973 prefixEnd_349973 := by exact prefixLift 349973
  have htrace : WordTrace (prefixWord ++ tailWord_349973) baseStart_349973 baseEnd_349973 := by
    simpa [prefixWord, tailWord_349973, baseEnd_349973] using wordTrace_append hprefix tailTrace_349973
  have hstable : (prefixWord ++ tailWord_349973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349973).length < 2 ^ (prefixWord ++ tailWord_349973).sum := by decide
  have hdescent : baseEnd_349973 < baseStart_349973 := by decide
  rcases family_descends (prefixWord ++ tailWord_349973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349992 : List Nat := [2, 1, 5, 1, 1, 9]
def baseStart_349992 : Nat := 118140960795 + 349992 * 2 ^ 59
def prefixEnd_349992 : Nat := 4983230072969 + 3 ^ 40 * 349992 * 2
def baseEnd_349992 : Nat := 11833028558255136684143

theorem tailTrace_349992 : CollatzResearch.WordTrace tailWord_349992 prefixEnd_349992 11833028558255136684143 := by
  unfold tailWord_349992
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382628474023116359934115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8510171298697488479912153 6382628474023116359934115)
  ·
    refine ⟨9573942711034674539901173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6382628474023116359934115 9573942711034674539901173)
    ·
      refine ⟨897557129159500738115735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9573942711034674539901173 897557129159500738115735)
      ·
        refine ⟨1346335693739251107173603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897557129159500738115735 1346335693739251107173603)
        ·
          refine ⟨2019503540608876660760405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346335693739251107173603 2019503540608876660760405)
          ·
            refine ⟨11833028558255136684143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2019503540608876660760405 11833028558255136684143)
            ·
              rfl

theorem cell19_349992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 9].length) (baseStart_349992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_349992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_349992 prefixEnd_349992 := by exact prefixLift 349992
  have htrace : WordTrace (prefixWord ++ tailWord_349992) baseStart_349992 baseEnd_349992 := by
    simpa [prefixWord, tailWord_349992, baseEnd_349992] using wordTrace_append hprefix tailTrace_349992
  have hstable : (prefixWord ++ tailWord_349992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349992).length < 2 ^ (prefixWord ++ tailWord_349992).sum := by decide
  have hdescent : baseEnd_349992 < baseStart_349992 := by decide
  rcases family_descends (prefixWord ++ tailWord_349992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350081 : List Nat := [1, 2, 4, 4, 1, 2, 2, 3]
def baseStart_350081 : Nat := 118140960795 + 350081 * 2 ^ 59
def prefixEnd_350081 : Nat := 4983230072969 + 3 ^ 40 * 350081 * 2
def baseEnd_350081 : Nat := 106524338374370394179267

theorem tailTrace_350081 : CollatzResearch.WordTrace tailWord_350081 prefixEnd_350081 106524338374370394179267 := by
  unfold tailWord_350081
  simp only [CollatzResearch.WordTrace]
  refine ⟨12768503044723800919858097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8512335363149200613238731 12768503044723800919858097)
  ·
    refine ⟨9576377283542850689893573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12768503044723800919858097 9576377283542850689893573)
    ·
      refine ⟨1795570740664284504355045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9576377283542850689893573 1795570740664284504355045)
      ·
        refine ⟨336669513874553344566571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1795570740664284504355045 336669513874553344566571)
        ·
          refine ⟨505004270811830016849857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336669513874553344566571 505004270811830016849857)
          ·
            refine ⟨378753203108872512637393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505004270811830016849857 378753203108872512637393)
            ·
              refine ⟨284064902331654384478045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378753203108872512637393 284064902331654384478045)
              ·
                refine ⟨106524338374370394179267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284064902331654384478045 106524338374370394179267)
                ·
                  rfl

theorem cell19_350081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_350081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350081 prefixEnd_350081 := by exact prefixLift 350081
  have htrace : WordTrace (prefixWord ++ tailWord_350081) baseStart_350081 baseEnd_350081 := by
    simpa [prefixWord, tailWord_350081, baseEnd_350081] using wordTrace_append hprefix tailTrace_350081
  have hstable : (prefixWord ++ tailWord_350081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350081).length < 2 ^ (prefixWord ++ tailWord_350081).sum := by decide
  have hdescent : baseEnd_350081 < baseStart_350081 := by decide
  rcases family_descends (prefixWord ++ tailWord_350081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350106 : List Nat := [3, 1, 1, 4, 2, 1, 7]
def baseStart_350106 : Nat := 118140960795 + 350106 * 2 ^ 59
def prefixEnd_350106 : Nat := 4983230072969 + 3 ^ 40 * 350106 * 2
def baseEnd_350106 : Nat := 35510648498392581207881

theorem tailTrace_350106 : CollatzResearch.WordTrace tailWord_350106 prefixEnd_350106 35510648498392581207881 := by
  unfold tailWord_350106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192353717408307547379543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8512943246422153459678781 3192353717408307547379543)
  ·
    refine ⟨4788530576112461321069315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3192353717408307547379543 4788530576112461321069315)
    ·
      refine ⟨7182795864168691981603973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4788530576112461321069315 7182795864168691981603973)
      ·
        refine ⟨1346774224531629746550745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7182795864168691981603973 1346774224531629746550745)
        ·
          refine ⟨1010080668398722309913059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1346774224531629746550745 1010080668398722309913059)
          ·
            refine ⟨1515121002598083464869589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010080668398722309913059 1515121002598083464869589)
            ·
              refine ⟨35510648498392581207881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1515121002598083464869589 35510648498392581207881)
              ·
                rfl

theorem cell19_350106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_350106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350106 prefixEnd_350106 := by exact prefixLift 350106
  have htrace : WordTrace (prefixWord ++ tailWord_350106) baseStart_350106 baseEnd_350106 := by
    simpa [prefixWord, tailWord_350106, baseEnd_350106] using wordTrace_append hprefix tailTrace_350106
  have hstable : (prefixWord ++ tailWord_350106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350106).length < 2 ^ (prefixWord ++ tailWord_350106).sum := by decide
  have hdescent : baseEnd_350106 < baseStart_350106 := by decide
  rcases family_descends (prefixWord ++ tailWord_350106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350203 : List Nat := [1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_350203 : Nat := 118140960795 + 350203 * 2 ^ 59
def prefixEnd_350203 : Nat := 4983230072969 + 3 ^ 40 * 350203 * 2
def baseEnd_350203 : Nat := 106561461123910259467823

theorem tailTrace_350203 : CollatzResearch.WordTrace tailWord_350203 prefixEnd_350203 106561461123910259467823 := by
  unfold tailWord_350203
  simp only [CollatzResearch.WordTrace]
  refine ⟨12772952750281815755799263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8515301833521210503866175 12772952750281815755799263)
  ·
    refine ⟨19159429125422723633698895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12772952750281815755799263 19159429125422723633698895)
    ·
      refine ⟨28739143688134085450548343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19159429125422723633698895 28739143688134085450548343)
      ·
        refine ⟨43108715532201128175822515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28739143688134085450548343 43108715532201128175822515)
        ·
          refine ⟨64663073298301692263733773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43108715532201128175822515 64663073298301692263733773)
          ·
            refine ⟨24248652486863134598900165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64663073298301692263733773 24248652486863134598900165)
            ·
              refine ⟨4546622341286837737293781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24248652486863134598900165 4546622341286837737293781)
              ·
                refine ⟨106561461123910259467823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4546622341286837737293781 106561461123910259467823)
                ·
                  rfl

theorem cell19_350203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_350203 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350203 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350203 prefixEnd_350203 := by exact prefixLift 350203
  have htrace : WordTrace (prefixWord ++ tailWord_350203) baseStart_350203 baseEnd_350203 := by
    simpa [prefixWord, tailWord_350203, baseEnd_350203] using wordTrace_append hprefix tailTrace_350203
  have hstable : (prefixWord ++ tailWord_350203).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350203).length < 2 ^ (prefixWord ++ tailWord_350203).sum := by decide
  have hdescent : baseEnd_350203 < baseStart_350203 := by decide
  rcases family_descends (prefixWord ++ tailWord_350203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350254 : List Nat := [4, 1, 3, 1, 1, 4, 2, 3]
def baseStart_350254 : Nat := 118140960795 + 350254 * 2 ^ 59
def prefixEnd_350254 : Nat := 4983230072969 + 3 ^ 40 * 350254 * 2
def baseEnd_350254 : Nat := 106576979650357252334351

theorem tailTrace_350254 : CollatzResearch.WordTrace tailWord_350254 prefixEnd_350254 106576979650357252334351 := by
  unfold tailWord_350254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596851609137131433238227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8516541915398034310603877 1596851609137131433238227)
  ·
    refine ⟨2395277413705697149857341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1596851609137131433238227 2395277413705697149857341)
    ·
      refine ⟨898229030139636431196503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2395277413705697149857341 898229030139636431196503)
      ·
        refine ⟨1347343545209454646794755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898229030139636431196503 1347343545209454646794755)
        ·
          refine ⟨2021015317814181970192133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347343545209454646794755 2021015317814181970192133)
          ·
            refine ⟨378940372090159119411025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2021015317814181970192133 378940372090159119411025)
            ·
              refine ⟨284205279067619339558269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378940372090159119411025 284205279067619339558269)
              ·
                refine ⟨106576979650357252334351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284205279067619339558269 106576979650357252334351)
                ·
                  rfl

theorem cell19_350254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_350254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350254 prefixEnd_350254 := by exact prefixLift 350254
  have htrace : WordTrace (prefixWord ++ tailWord_350254) baseStart_350254 baseEnd_350254 := by
    simpa [prefixWord, tailWord_350254, baseEnd_350254] using wordTrace_append hprefix tailTrace_350254
  have hstable : (prefixWord ++ tailWord_350254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350254).length < 2 ^ (prefixWord ++ tailWord_350254).sum := by decide
  have hdescent : baseEnd_350254 < baseStart_350254 := by decide
  rcases family_descends (prefixWord ++ tailWord_350254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350256 : List Nat := [2, 1, 1, 1, 2, 7, 2, 3]
def baseStart_350256 : Nat := 118140960795 + 350256 * 2 ^ 59
def prefixEnd_350256 : Nat := 4983230072969 + 3 ^ 40 * 350256 * 2
def baseEnd_350256 : Nat := 106577588220021840289901

theorem tailTrace_350256 : CollatzResearch.WordTrace tailWord_350256 prefixEnd_350256 106577588220021840289901 := by
  unfold tailWord_350256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387442909544902903739311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8516590546059870538319081 6387442909544902903739311)
  ·
    refine ⟨9581164364317354355608967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6387442909544902903739311 9581164364317354355608967)
    ·
      refine ⟨14371746546476031533413451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9581164364317354355608967 14371746546476031533413451)
      ·
        refine ⟨21557619819714047300120177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14371746546476031533413451 21557619819714047300120177)
        ·
          refine ⟨16168214864785535475090133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21557619819714047300120177 16168214864785535475090133)
          ·
            refine ⟨378942535893410987697425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16168214864785535475090133 378942535893410987697425)
            ·
              refine ⟨284206901920058240773069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378942535893410987697425 284206901920058240773069)
              ·
                refine ⟨106577588220021840289901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284206901920058240773069 106577588220021840289901)
                ·
                  rfl

theorem cell19_350256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_350256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350256 prefixEnd_350256 := by exact prefixLift 350256
  have htrace : WordTrace (prefixWord ++ tailWord_350256) baseStart_350256 baseEnd_350256 := by
    simpa [prefixWord, tailWord_350256, baseEnd_350256] using wordTrace_append hprefix tailTrace_350256
  have hstable : (prefixWord ++ tailWord_350256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350256).length < 2 ^ (prefixWord ++ tailWord_350256).sum := by decide
  have hdescent : baseEnd_350256 < baseStart_350256 := by decide
  rcases family_descends (prefixWord ++ tailWord_350256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350258 : List Nat := [3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_350258 : Nat := 118140960795 + 350258 * 2 ^ 59
def prefixEnd_350258 : Nat := 4983230072969 + 3 ^ 40 * 350258 * 2
def baseEnd_350258 : Nat := 106578196789686428245451

theorem tailTrace_350258 : CollatzResearch.WordTrace tailWord_350258 prefixEnd_350258 106578196789686428245451 := by
  unfold tailWord_350258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3193739691270640037262857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8516639176721706766034285 3193739691270640037262857)
  ·
    refine ⟨2395304768452980027947143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3193739691270640037262857 2395304768452980027947143)
    ·
      refine ⟨3592957152679470041920715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395304768452980027947143 3592957152679470041920715)
      ·
        refine ⟨5389435729019205062881073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3592957152679470041920715 5389435729019205062881073)
        ·
          refine ⟨4042076796764403797160805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5389435729019205062881073 4042076796764403797160805)
          ·
            refine ⟨757889399393325711967651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4042076796764403797160805 757889399393325711967651)
            ·
              refine ⟨1136834099089988567951477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757889399393325711967651 1136834099089988567951477)
              ·
                refine ⟨106578196789686428245451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1136834099089988567951477 106578196789686428245451)
                ·
                  rfl

theorem cell19_350258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_350258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350258 prefixEnd_350258 := by exact prefixLift 350258
  have htrace : WordTrace (prefixWord ++ tailWord_350258) baseStart_350258 baseEnd_350258 := by
    simpa [prefixWord, tailWord_350258, baseEnd_350258] using wordTrace_append hprefix tailTrace_350258
  have hstable : (prefixWord ++ tailWord_350258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350258).length < 2 ^ (prefixWord ++ tailWord_350258).sum := by decide
  have hdescent : baseEnd_350258 < baseStart_350258 := by decide
  rcases family_descends (prefixWord ++ tailWord_350258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350296 : List Nat := [2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_350296 : Nat := 118140960795 + 350296 * 2 ^ 59
def prefixEnd_350296 : Nat := 4983230072969 + 3 ^ 40 * 350296 * 2
def baseEnd_350296 : Nat := 106589759613313599400903

theorem tailTrace_350296 : CollatzResearch.WordTrace tailWord_350296 prefixEnd_350296 106589759613313599400903 := by
  unfold tailWord_350296
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388172369472446319467371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8517563159296595092623161 6388172369472446319467371)
  ·
    refine ⟨9582258554208669479201057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6388172369472446319467371 9582258554208669479201057)
    ·
      refine ⟨7186693915656502109400793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9582258554208669479201057 7186693915656502109400793)
      ·
        refine ⟨5390020436742376582050595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7186693915656502109400793 5390020436742376582050595)
        ·
          refine ⟨8085030655113564873075893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390020436742376582050595 8085030655113564873075893)
          ·
            refine ⟨757971623916896706850865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8085030655113564873075893 757971623916896706850865)
            ·
              refine ⟨568478717937672530138149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757971623916896706850865 568478717937672530138149)
              ·
                refine ⟨106589759613313599400903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568478717937672530138149 106589759613313599400903)
                ·
                  rfl

theorem cell19_350296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_350296 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350296 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350296 prefixEnd_350296 := by exact prefixLift 350296
  have htrace : WordTrace (prefixWord ++ tailWord_350296) baseStart_350296 baseEnd_350296 := by
    simpa [prefixWord, tailWord_350296, baseEnd_350296] using wordTrace_append hprefix tailTrace_350296
  have hstable : (prefixWord ++ tailWord_350296).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350296).length < 2 ^ (prefixWord ++ tailWord_350296).sum := by decide
  have hdescent : baseEnd_350296 < baseStart_350296 := by decide
  rcases family_descends (prefixWord ++ tailWord_350296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350389 : List Nat := [1, 3, 3, 4, 1, 1, 6]
def baseStart_350389 : Nat := 118140960795 + 350389 * 2 ^ 59
def prefixEnd_350389 : Nat := 4983230072969 + 3 ^ 40 * 350389 * 2
def baseEnd_350389 : Nat := 35539352700905646444661

theorem tailTrace_350389 : CollatzResearch.WordTrace tailWord_350389 prefixEnd_350389 35539352700905646444661 := by
  unfold tailWord_350389
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779736727607969522070221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8519824485071979681380147 12779736727607969522070221)
  ·
    refine ⟨4792401272852988570776333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12779736727607969522070221 4792401272852988570776333)
    ·
      refine ⟨1797150477319870714041125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4792401272852988570776333 1797150477319870714041125)
      ·
        refine ⟨336965714497475758882711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1797150477319870714041125 336965714497475758882711)
        ·
          refine ⟨505448571746213638324067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336965714497475758882711 505448571746213638324067)
          ·
            refine ⟨758172857619320457486101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505448571746213638324067 758172857619320457486101)
            ·
              refine ⟨35539352700905646444661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 758172857619320457486101 35539352700905646444661)
              ·
                rfl

theorem cell19_350389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_350389 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350389 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350389 prefixEnd_350389 := by exact prefixLift 350389
  have htrace : WordTrace (prefixWord ++ tailWord_350389) baseStart_350389 baseEnd_350389 := by
    simpa [prefixWord, tailWord_350389, baseEnd_350389] using wordTrace_append hprefix tailTrace_350389
  have hstable : (prefixWord ++ tailWord_350389).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350389).length < 2 ^ (prefixWord ++ tailWord_350389).sum := by decide
  have hdescent : baseEnd_350389 < baseStart_350389 := by decide
  rcases family_descends (prefixWord ++ tailWord_350389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350393 : List Nat := [1, 2, 1, 4, 1, 2, 8]
def baseStart_350393 : Nat := 118140960795 + 350393 * 2 ^ 59
def prefixEnd_350393 : Nat := 4983230072969 + 3 ^ 40 * 350393 * 2
def baseEnd_350393 : Nat := 35539758414015371748361

theorem tailTrace_350393 : CollatzResearch.WordTrace tailWord_350393 prefixEnd_350393 35539758414015371748361 := by
  unfold tailWord_350393
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779882619593478205215833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8519921746395652136810555 12779882619593478205215833)
  ·
    refine ⟨9584911964695108653911875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12779882619593478205215833 9584911964695108653911875)
    ·
      refine ⟨14377367947042662980867813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9584911964695108653911875 14377367947042662980867813)
      ·
        refine ⟨2695756490070499308912715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14377367947042662980867813 2695756490070499308912715)
        ·
          refine ⟨4043634735105748963369073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695756490070499308912715 4043634735105748963369073)
          ·
            refine ⟨3032726051329311722526805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4043634735105748963369073 3032726051329311722526805)
            ·
              refine ⟨35539758414015371748361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3032726051329311722526805 35539758414015371748361)
              ·
                rfl

theorem cell19_350393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_350393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350393 prefixEnd_350393 := by exact prefixLift 350393
  have htrace : WordTrace (prefixWord ++ tailWord_350393) baseStart_350393 baseEnd_350393 := by
    simpa [prefixWord, tailWord_350393, baseEnd_350393] using wordTrace_append hprefix tailTrace_350393
  have hstable : (prefixWord ++ tailWord_350393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350393).length < 2 ^ (prefixWord ++ tailWord_350393).sum := by decide
  have hdescent : baseEnd_350393 < baseStart_350393 := by decide
  rcases family_descends (prefixWord ++ tailWord_350393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350488 : List Nat := [2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_350488 : Nat := 118140960795 + 350488 * 2 ^ 59
def prefixEnd_350488 : Nat := 4983230072969 + 3 ^ 40 * 350488 * 2
def baseEnd_350488 : Nat := 106648182301114043133713

theorem tailTrace_350488 : CollatzResearch.WordTrace tailWord_350488 prefixEnd_350488 106648182301114043133713 := by
  unfold tailWord_350488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391673777124654714962059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8522231702832872953282745 6391673777124654714962059)
  ·
    refine ⟨9587510665686982072443089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6391673777124654714962059 9587510665686982072443089)
    ·
      refine ⟨7190632999265236554332317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9587510665686982072443089 7190632999265236554332317)
      ·
        refine ⟨2696487374724463707874619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7190632999265236554332317 2696487374724463707874619)
        ·
          refine ⟨4044731062086695561811929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696487374724463707874619 4044731062086695561811929)
          ·
            refine ⟨3033548296565021671358947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4044731062086695561811929 3033548296565021671358947)
            ·
              refine ⟨4550322444847532507038421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3033548296565021671358947 4550322444847532507038421)
              ·
                refine ⟨106648182301114043133713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4550322444847532507038421 106648182301114043133713)
                ·
                  rfl

theorem cell19_350488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_350488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350488 prefixEnd_350488 := by exact prefixLift 350488
  have htrace : WordTrace (prefixWord ++ tailWord_350488) baseStart_350488 baseEnd_350488 := by
    simpa [prefixWord, tailWord_350488, baseEnd_350488] using wordTrace_append hprefix tailTrace_350488
  have hstable : (prefixWord ++ tailWord_350488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350488).length < 2 ^ (prefixWord ++ tailWord_350488).sum := by decide
  have hdescent : baseEnd_350488 < baseStart_350488 := by decide
  rcases family_descends (prefixWord ++ tailWord_350488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350503 : List Nat := [1, 1, 8, 1, 8]
def baseStart_350503 : Nat := 118140960795 + 350503 * 2 ^ 59
def prefixEnd_350503 : Nat := 4983230072969 + 3 ^ 40 * 350503 * 2
def baseEnd_350503 : Nat := 3950101724948090844457

theorem tailTrace_350503 : CollatzResearch.WordTrace tailWord_350503 prefixEnd_350503 3950101724948090844457 := by
  unfold tailWord_350503
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783894649194966991720163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8522596432796644661146775 12783894649194966991720163)
  ·
    refine ⟨19175841973792450487580245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12783894649194966991720163 19175841973792450487580245)
    ·
      refine ⟨224716898130380279151331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 19175841973792450487580245 224716898130380279151331)
      ·
        refine ⟨337075347195570418726997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224716898130380279151331 337075347195570418726997)
        ·
          refine ⟨3950101724948090844457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 337075347195570418726997 3950101724948090844457)
          ·
            rfl

theorem cell19_350503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 8].length) (baseStart_350503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350503 prefixEnd_350503 := by exact prefixLift 350503
  have htrace : WordTrace (prefixWord ++ tailWord_350503) baseStart_350503 baseEnd_350503 := by
    simpa [prefixWord, tailWord_350503, baseEnd_350503] using wordTrace_append hprefix tailTrace_350503
  have hstable : (prefixWord ++ tailWord_350503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350503).length < 2 ^ (prefixWord ++ tailWord_350503).sum := by decide
  have hdescent : baseEnd_350503 < baseStart_350503 := by decide
  rcases family_descends (prefixWord ++ tailWord_350503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350562 : List Nat := [3, 3, 2, 1, 1, 3, 6]
def baseStart_350562 : Nat := 118140960795 + 350562 * 2 ^ 59
def prefixEnd_350562 : Nat := 4983230072969 + 3 ^ 40 * 350562 * 2
def baseEnd_350562 : Nat := 35556899792901265829689

theorem tailTrace_350562 : CollatzResearch.WordTrace tailWord_350562 prefixEnd_350562 35556899792901265829689 := by
  unfold tailWord_350562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196511638995305017029485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8524031037320813378745293 3196511638995305017029485)
  ·
    refine ⟨1198691864623239381386057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3196511638995305017029485 1198691864623239381386057)
    ·
      refine ⟨899018898467429536039543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1198691864623239381386057 899018898467429536039543)
      ·
        refine ⟨1348528347701144304059315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899018898467429536039543 1348528347701144304059315)
        ·
          refine ⟨2022792521551716456088973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348528347701144304059315 2022792521551716456088973)
          ·
            refine ⟨758547195581893671033365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2022792521551716456088973 758547195581893671033365)
            ·
              refine ⟨35556899792901265829689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 758547195581893671033365 35556899792901265829689)
              ·
                rfl

theorem cell19_350562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_350562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350562 prefixEnd_350562 := by exact prefixLift 350562
  have htrace : WordTrace (prefixWord ++ tailWord_350562) baseStart_350562 baseEnd_350562 := by
    simpa [prefixWord, tailWord_350562, baseEnd_350562] using wordTrace_append hprefix tailTrace_350562
  have hstable : (prefixWord ++ tailWord_350562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350562).length < 2 ^ (prefixWord ++ tailWord_350562).sum := by decide
  have hdescent : baseEnd_350562 < baseStart_350562 := by decide
  rcases family_descends (prefixWord ++ tailWord_350562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350564 : List Nat := [2, 3, 1, 1, 3, 1, 8]
def baseStart_350564 : Nat := 118140960795 + 350564 * 2 ^ 59
def prefixEnd_350564 : Nat := 4983230072969 + 3 ^ 40 * 350564 * 2
def baseEnd_350564 : Nat := 35557102649456128481539

theorem tailTrace_350564 : CollatzResearch.WordTrace tailWord_350564 prefixEnd_350564 35557102649456128481539 := by
  unfold tailWord_350564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6393059750986987204845373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8524079667982649606460497 6393059750986987204845373)
  ·
    refine ⟨2397397406620120201817015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6393059750986987204845373 2397397406620120201817015)
    ·
      refine ⟨3596096109930180302725523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397397406620120201817015 3596096109930180302725523)
      ·
        refine ⟨5394144164895270454088285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596096109930180302725523 5394144164895270454088285)
        ·
          refine ⟨2022804061835726420283107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5394144164895270454088285 2022804061835726420283107)
          ·
            refine ⟨3034206092753589630424661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022804061835726420283107 3034206092753589630424661)
            ·
              refine ⟨35557102649456128481539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3034206092753589630424661 35557102649456128481539)
              ·
                rfl

theorem cell19_350564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_350564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350564 prefixEnd_350564 := by exact prefixLift 350564
  have htrace : WordTrace (prefixWord ++ tailWord_350564) baseStart_350564 baseEnd_350564 := by
    simpa [prefixWord, tailWord_350564, baseEnd_350564] using wordTrace_append hprefix tailTrace_350564
  have hstable : (prefixWord ++ tailWord_350564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350564).length < 2 ^ (prefixWord ++ tailWord_350564).sum := by decide
  have hdescent : baseEnd_350564 < baseStart_350564 := by decide
  rcases family_descends (prefixWord ++ tailWord_350564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350594 : List Nat := [3, 4, 2, 1, 2, 2, 2, 3]
def baseStart_350594 : Nat := 118140960795 + 350594 * 2 ^ 59
def prefixEnd_350594 : Nat := 4983230072969 + 3 ^ 40 * 350594 * 2
def baseEnd_350594 : Nat := 106680436493337204777869

theorem tailTrace_350594 : CollatzResearch.WordTrace tailWord_350594 prefixEnd_350594 106680436493337204777869 := by
  unfold tailWord_350594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196803422966322383320709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8524809127910193022188557 3196803422966322383320709)
  ·
    refine ⟨599400641806185446872633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3196803422966322383320709 599400641806185446872633)
    ·
      refine ⟨449550481354639085154475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 599400641806185446872633 449550481354639085154475)
      ·
        refine ⟨674325722031958627731713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449550481354639085154475 674325722031958627731713)
        ·
          refine ⟨505744291523968970798785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674325722031958627731713 505744291523968970798785)
          ·
            refine ⟨379308218642976728099089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505744291523968970798785 379308218642976728099089)
            ·
              refine ⟨284481163982232546074317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379308218642976728099089 284481163982232546074317)
              ·
                refine ⟨106680436493337204777869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284481163982232546074317 106680436493337204777869)
                ·
                  rfl

theorem cell19_350594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_350594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350594 prefixEnd_350594 := by exact prefixLift 350594
  have htrace : WordTrace (prefixWord ++ tailWord_350594) baseStart_350594 baseEnd_350594 := by
    simpa [prefixWord, tailWord_350594, baseEnd_350594] using wordTrace_append hprefix tailTrace_350594
  have hstable : (prefixWord ++ tailWord_350594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350594).length < 2 ^ (prefixWord ++ tailWord_350594).sum := by decide
  have hdescent : baseEnd_350594 < baseStart_350594 := by decide
  rcases family_descends (prefixWord ++ tailWord_350594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350674 : List Nat := [3, 2, 2, 4, 2, 6]
def baseStart_350674 : Nat := 118140960795 + 350674 * 2 ^ 59
def prefixEnd_350674 : Nat := 4983230072969 + 3 ^ 40 * 350674 * 2
def baseEnd_350674 : Nat := 11856086586657858111097

theorem tailTrace_350674 : CollatzResearch.WordTrace tailWord_350674 prefixEnd_350674 11856086586657858111097 := by
  unfold tailWord_350674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197532882893865799048769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8526754354383642130796717 3197532882893865799048769)
  ·
    refine ⟨2398149662170399349286577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3197532882893865799048769 2398149662170399349286577)
    ·
      refine ⟨1798612246627799511964933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2398149662170399349286577 1798612246627799511964933)
      ·
        refine ⟨337239796242712408493425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1798612246627799511964933 337239796242712408493425)
        ·
          refine ⟨252929847182034306370069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337239796242712408493425 252929847182034306370069)
          ·
            refine ⟨11856086586657858111097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 252929847182034306370069 11856086586657858111097)
            ·
              rfl

theorem cell19_350674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 6].length) (baseStart_350674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350674 prefixEnd_350674 := by exact prefixLift 350674
  have htrace : WordTrace (prefixWord ++ tailWord_350674) baseStart_350674 baseEnd_350674 := by
    simpa [prefixWord, tailWord_350674, baseEnd_350674] using wordTrace_append hprefix tailTrace_350674
  have hstable : (prefixWord ++ tailWord_350674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350674).length < 2 ^ (prefixWord ++ tailWord_350674).sum := by decide
  have hdescent : baseEnd_350674 < baseStart_350674 := by decide
  rcases family_descends (prefixWord ++ tailWord_350674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350693 : List Nat := [1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_350693 : Nat := 118140960795 + 350693 * 2 ^ 59
def prefixEnd_350693 : Nat := 4983230072969 + 3 ^ 40 * 350693 * 2
def baseEnd_350693 : Nat := 106710560691734308577599

theorem tailTrace_350693 : CollatzResearch.WordTrace tailWord_350693 prefixEnd_350693 106710560691734308577599 := by
  unfold tailWord_350693
  simp only [CollatzResearch.WordTrace]
  refine ⟨12790824518506629441136733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8527216345671086294091155 12790824518506629441136733)
  ·
    refine ⟨4796559194439986040426275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12790824518506629441136733 4796559194439986040426275)
    ·
      refine ⟨7194838791659979060639413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796559194439986040426275 7194838791659979060639413)
      ·
        refine ⟨674516136718123036934945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7194838791659979060639413 674516136718123036934945)
        ·
          refine ⟨505887102538592277701209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674516136718123036934945 505887102538592277701209)
          ·
            refine ⟨379415326903944208275907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505887102538592277701209 379415326903944208275907)
            ·
              refine ⟨569122990355916312413861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379415326903944208275907 569122990355916312413861)
              ·
                refine ⟨106710560691734308577599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569122990355916312413861 106710560691734308577599)
                ·
                  rfl

theorem cell19_350693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_350693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350693 prefixEnd_350693 := by exact prefixLift 350693
  have htrace : WordTrace (prefixWord ++ tailWord_350693) baseStart_350693 baseEnd_350693 := by
    simpa [prefixWord, tailWord_350693, baseEnd_350693] using wordTrace_append hprefix tailTrace_350693
  have hstable : (prefixWord ++ tailWord_350693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350693).length < 2 ^ (prefixWord ++ tailWord_350693).sum := by decide
  have hdescent : baseEnd_350693 < baseStart_350693 := by decide
  rcases family_descends (prefixWord ++ tailWord_350693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350754 : List Nat := [3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_350754 : Nat := 118140960795 + 350754 * 2 ^ 59
def prefixEnd_350754 : Nat := 4983230072969 + 3 ^ 40 * 350754 * 2
def baseEnd_350754 : Nat := 106729122066504241221877

theorem tailTrace_350754 : CollatzResearch.WordTrace tailWord_350754 prefixEnd_350754 106729122066504241221877 := by
  unfold tailWord_350754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198262342821409214776829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8528699580857091239404877 3198262342821409214776829)
  ·
    refine ⟨1199348378558028455541311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3198262342821409214776829 1199348378558028455541311)
    ·
      refine ⟨1799022567837042683311967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199348378558028455541311 1799022567837042683311967)
      ·
        refine ⟨2698533851755564024967951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799022567837042683311967 2698533851755564024967951)
        ·
          refine ⟨4047800777633346037451927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698533851755564024967951 4047800777633346037451927)
          ·
            refine ⟨6071701166450019056177891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047800777633346037451927 6071701166450019056177891)
            ·
              refine ⟨9107551749675028584266837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071701166450019056177891 9107551749675028584266837)
              ·
                refine ⟨106729122066504241221877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9107551749675028584266837 106729122066504241221877)
                ·
                  rfl

theorem cell19_350754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_350754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350754 prefixEnd_350754 := by exact prefixLift 350754
  have htrace : WordTrace (prefixWord ++ tailWord_350754) baseStart_350754 baseEnd_350754 := by
    simpa [prefixWord, tailWord_350754, baseEnd_350754] using wordTrace_append hprefix tailTrace_350754
  have hstable : (prefixWord ++ tailWord_350754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350754).length < 2 ^ (prefixWord ++ tailWord_350754).sum := by decide
  have hdescent : baseEnd_350754 < baseStart_350754 := by decide
  rcases family_descends (prefixWord ++ tailWord_350754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350773 : List Nat := [1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_350773 : Nat := 118140960795 + 350773 * 2 ^ 59
def prefixEnd_350773 : Nat := 4983230072969 + 3 ^ 40 * 350773 * 2
def baseEnd_350773 : Nat := 106734903478317826799603

theorem tailTrace_350773 : CollatzResearch.WordTrace tailWord_350773 prefixEnd_350773 106734903478317826799603 := by
  unfold tailWord_350773
  simp only [CollatzResearch.WordTrace]
  refine ⟨12793742358216803104048973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8529161572144535402699315 12793742358216803104048973)
  ·
    refine ⟨4797653384331301164018365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12793742358216803104048973 4797653384331301164018365)
    ·
      refine ⟨1799120019124237936506887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4797653384331301164018365 1799120019124237936506887)
      ·
        refine ⟨2698680028686356904760331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799120019124237936506887 2698680028686356904760331)
        ·
          refine ⟨4048020043029535357140497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698680028686356904760331 4048020043029535357140497)
          ·
            refine ⟨3036015032272151517855373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4048020043029535357140497 3036015032272151517855373)
            ·
              refine ⟨1138505637102056819195765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3036015032272151517855373 1138505637102056819195765)
              ·
                refine ⟨106734903478317826799603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1138505637102056819195765 106734903478317826799603)
                ·
                  rfl

theorem cell19_350773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_350773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350773 prefixEnd_350773 := by exact prefixLift 350773
  have htrace : WordTrace (prefixWord ++ tailWord_350773) baseStart_350773 baseEnd_350773 := by
    simpa [prefixWord, tailWord_350773, baseEnd_350773] using wordTrace_append hprefix tailTrace_350773
  have hstable : (prefixWord ++ tailWord_350773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350773).length < 2 ^ (prefixWord ++ tailWord_350773).sum := by decide
  have hdescent : baseEnd_350773 < baseStart_350773 := by decide
  rcases family_descends (prefixWord ++ tailWord_350773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350866 : List Nat := [3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_350866 : Nat := 118140960795 + 350866 * 2 ^ 59
def prefixEnd_350866 : Nat := 4983230072969 + 3 ^ 40 * 350866 * 2
def baseEnd_350866 : Nat := 106763201967721166732683

theorem tailTrace_350866 : CollatzResearch.WordTrace tailWord_350866 prefixEnd_350866 106763201967721166732683 := by
  unfold tailWord_350866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199283586719969996796113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8531422897919919991456301 3199283586719969996796113)
  ·
    refine ⟨2399462690039977497597085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3199283586719969996796113 2399462690039977497597085)
    ·
      refine ⟨899798508764991561598907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2399462690039977497597085 899798508764991561598907)
      ·
        refine ⟨1349697763147487342398361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899798508764991561598907 1349697763147487342398361)
        ·
          refine ⟨1012273322360615506798771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1349697763147487342398361 1012273322360615506798771)
          ·
            refine ⟨1518409983540923260198157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012273322360615506798771 1518409983540923260198157)
            ·
              refine ⟨569403743827846222574309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1518409983540923260198157 569403743827846222574309)
              ·
                refine ⟨106763201967721166732683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569403743827846222574309 106763201967721166732683)
                ·
                  rfl

theorem cell19_350866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_350866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350866 prefixEnd_350866 := by exact prefixLift 350866
  have htrace : WordTrace (prefixWord ++ tailWord_350866) baseStart_350866 baseEnd_350866 := by
    simpa [prefixWord, tailWord_350866, baseEnd_350866] using wordTrace_append hprefix tailTrace_350866
  have hstable : (prefixWord ++ tailWord_350866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350866).length < 2 ^ (prefixWord ++ tailWord_350866).sum := by decide
  have hdescent : baseEnd_350866 < baseStart_350866 := by decide
  rcases family_descends (prefixWord ++ tailWord_350866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350902 : List Nat := [5, 1, 3, 1, 2, 1, 6]
def baseStart_350902 : Nat := 118140960795 + 350902 * 2 ^ 59
def prefixEnd_350902 : Nat := 4983230072969 + 3 ^ 40 * 350902 * 2
def baseEnd_350902 : Nat := 35591385407227916644195

theorem tailTrace_350902 : CollatzResearch.WordTrace tailWord_350902 prefixEnd_350902 35591385407227916644195 := by
  unfold tailWord_350902
  simp only [CollatzResearch.WordTrace]
  refine ⟨799902960921841133468435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8532298249832972090329973 799902960921841133468435)
  ·
    refine ⟨1199854441382761700202653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 799902960921841133468435 1199854441382761700202653)
    ·
      refine ⟨449945415518535637575995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1199854441382761700202653 449945415518535637575995)
      ·
        refine ⟨674918123277803456363993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449945415518535637575995 674918123277803456363993)
        ·
          refine ⟨506188592458352592272995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674918123277803456363993 506188592458352592272995)
          ·
            refine ⟨759282888687528888409493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506188592458352592272995 759282888687528888409493)
            ·
              refine ⟨35591385407227916644195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 759282888687528888409493 35591385407227916644195)
              ·
                rfl

theorem cell19_350902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_350902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350902 prefixEnd_350902 := by exact prefixLift 350902
  have htrace : WordTrace (prefixWord ++ tailWord_350902) baseStart_350902 baseEnd_350902 := by
    simpa [prefixWord, tailWord_350902, baseEnd_350902] using wordTrace_append hprefix tailTrace_350902
  have hstable : (prefixWord ++ tailWord_350902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350902).length < 2 ^ (prefixWord ++ tailWord_350902).sum := by decide
  have hdescent : baseEnd_350902 < baseStart_350902 := by decide
  rcases family_descends (prefixWord ++ tailWord_350902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350940 : List Nat := [2, 2, 5, 1, 1, 1, 4, 3]
def baseStart_350940 : Nat := 118140960795 + 350940 * 2 ^ 59
def prefixEnd_350940 : Nat := 4983230072969 + 3 ^ 40 * 350940 * 2
def baseEnd_350940 : Nat := 106785719045310921088037

theorem tailTrace_350940 : CollatzResearch.WordTrace tailWord_350940 prefixEnd_350940 106785719045310921088037 := by
  unfold tailWord_350940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399916674305895312689137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8533222232407860416918849 6399916674305895312689137)
  ·
    refine ⟨4799937505729421484516853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6399916674305895312689137 4799937505729421484516853)
    ·
      refine ⟨449994141162133264173455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4799937505729421484516853 449994141162133264173455)
      ·
        refine ⟨674991211743199896260183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449994141162133264173455 674991211743199896260183)
        ·
          refine ⟨1012486817614799844390275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674991211743199896260183 1012486817614799844390275)
          ·
            refine ⟨1518730226422199766585413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012486817614799844390275 1518730226422199766585413)
            ·
              refine ⟨284761917454162456234765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1518730226422199766585413 284761917454162456234765)
              ·
                refine ⟨106785719045310921088037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284761917454162456234765 106785719045310921088037)
                ·
                  rfl

theorem cell19_350940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_350940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_350940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_350940 prefixEnd_350940 := by exact prefixLift 350940
  have htrace : WordTrace (prefixWord ++ tailWord_350940) baseStart_350940 baseEnd_350940 := by
    simpa [prefixWord, tailWord_350940, baseEnd_350940] using wordTrace_append hprefix tailTrace_350940
  have hstable : (prefixWord ++ tailWord_350940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350940).length < 2 ^ (prefixWord ++ tailWord_350940).sum := by decide
  have hdescent : baseEnd_350940 < baseStart_350940 := by decide
  rcases family_descends (prefixWord ++ tailWord_350940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351018 : List Nat := [3, 1, 4, 3, 1, 7]
def baseStart_351018 : Nat := 118140960795 + 351018 * 2 ^ 59
def prefixEnd_351018 : Nat := 4983230072969 + 3 ^ 40 * 351018 * 2
def baseEnd_351018 : Nat := 11867717029136650150499

theorem tailTrace_351018 : CollatzResearch.WordTrace tailWord_351018 prefixEnd_351018 11867717029136650150499 := by
  unfold tailWord_351018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3200669560582302486679427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8535118828219473297811805 3200669560582302486679427)
  ·
    refine ⟨4801004340873453730019141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3200669560582302486679427 4801004340873453730019141)
    ·
      refine ⟨900188313913772574378589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4801004340873453730019141 900188313913772574378589)
      ·
        refine ⟨337570617717664715391971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 900188313913772574378589 337570617717664715391971)
        ·
          refine ⟨506355926576497073087957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337570617717664715391971 506355926576497073087957)
          ·
            refine ⟨11867717029136650150499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 506355926576497073087957 11867717029136650150499)
            ·
              rfl

theorem cell19_351018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 7].length) (baseStart_351018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351018 prefixEnd_351018 := by exact prefixLift 351018
  have htrace : WordTrace (prefixWord ++ tailWord_351018) baseStart_351018 baseEnd_351018 := by
    simpa [prefixWord, tailWord_351018, baseEnd_351018] using wordTrace_append hprefix tailTrace_351018
  have hstable : (prefixWord ++ tailWord_351018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351018).length < 2 ^ (prefixWord ++ tailWord_351018).sum := by decide
  have hdescent : baseEnd_351018 < baseStart_351018 := by decide
  rcases family_descends (prefixWord ++ tailWord_351018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351039 : List Nat := [1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_351039 : Nat := 118140960795 + 351039 * 2 ^ 59
def prefixEnd_351039 : Nat := 4983230072969 + 3 ^ 40 * 351039 * 2
def baseEnd_351039 : Nat := 106815843243708024887767

theorem tailTrace_351039 : CollatzResearch.WordTrace tailWord_351039 prefixEnd_351039 106815843243708024887767 := by
  unfold tailWord_351039
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803444175253130533232171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8535629450168753688821447 12803444175253130533232171)
  ·
    refine ⟨19205166262879695799848257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12803444175253130533232171 19205166262879695799848257)
    ·
      refine ⟨14403874697159771849886193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19205166262879695799848257 14403874697159771849886193)
      ·
        refine ⟨10802906022869828887414645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14403874697159771849886193 10802906022869828887414645)
        ·
          refine ⟨1012772439644046458195123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10802906022869828887414645 1012772439644046458195123)
          ·
            refine ⟨1519158659466069687292685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012772439644046458195123 1519158659466069687292685)
            ·
              refine ⟨569684497299776132734757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1519158659466069687292685 569684497299776132734757)
              ·
                refine ⟨106815843243708024887767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569684497299776132734757 106815843243708024887767)
                ·
                  rfl

theorem cell19_351039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_351039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351039 prefixEnd_351039 := by exact prefixLift 351039
  have htrace : WordTrace (prefixWord ++ tailWord_351039) baseStart_351039 baseEnd_351039 := by
    simpa [prefixWord, tailWord_351039, baseEnd_351039] using wordTrace_append hprefix tailTrace_351039
  have hstable : (prefixWord ++ tailWord_351039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351039).length < 2 ^ (prefixWord ++ tailWord_351039).sum := by decide
  have hdescent : baseEnd_351039 < baseStart_351039 := by decide
  rcases family_descends (prefixWord ++ tailWord_351039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351098 : List Nat := [3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_351098 : Nat := 118140960795 + 351098 * 2 ^ 59
def prefixEnd_351098 : Nat := 4983230072969 + 3 ^ 40 * 351098 * 2
def baseEnd_351098 : Nat := 106833796048813369576495

theorem tailTrace_351098 : CollatzResearch.WordTrace tailWord_351098 prefixEnd_351098 106833796048813369576495 := by
  unfold tailWord_351098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201399020509845902407487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8537064054692922406419965 3201399020509845902407487)
  ·
    refine ⟨4802098530764768853611231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3201399020509845902407487 4802098530764768853611231)
    ·
      refine ⟨7203147796147153280416847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802098530764768853611231 7203147796147153280416847)
      ·
        refine ⟨10804721694220729920625271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7203147796147153280416847 10804721694220729920625271)
        ·
          refine ⟨16207082541331094880937907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10804721694220729920625271 16207082541331094880937907)
          ·
            refine ⟨24310623811996642321406861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16207082541331094880937907 24310623811996642321406861)
            ·
              refine ⟨9116483929498740870527573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24310623811996642321406861 9116483929498740870527573)
              ·
                refine ⟨106833796048813369576495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9116483929498740870527573 106833796048813369576495)
                ·
                  rfl

theorem cell19_351098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_351098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351098 prefixEnd_351098 := by exact prefixLift 351098
  have htrace : WordTrace (prefixWord ++ tailWord_351098) baseStart_351098 baseEnd_351098 := by
    simpa [prefixWord, tailWord_351098, baseEnd_351098] using wordTrace_append hprefix tailTrace_351098
  have hstable : (prefixWord ++ tailWord_351098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351098).length < 2 ^ (prefixWord ++ tailWord_351098).sum := by decide
  have hdescent : baseEnd_351098 < baseStart_351098 := by decide
  rcases family_descends (prefixWord ++ tailWord_351098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351113 : List Nat := [1, 2, 1, 1, 5, 4, 2, 3]
def baseStart_351113 : Nat := 118140960795 + 351113 * 2 ^ 59
def prefixEnd_351113 : Nat := 4983230072969 + 3 ^ 40 * 351113 * 2
def baseEnd_351113 : Nat := 106838360321297779243121

theorem tailTrace_351113 : CollatzResearch.WordTrace tailWord_351113 prefixEnd_351113 106838360321297779243121 := by
  unfold tailWord_351113
  simp only [CollatzResearch.WordTrace]
  refine ⟨12806143176985041171425993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8537428784656694114283995 12806143176985041171425993)
  ·
    refine ⟨9604607382738780878569495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12806143176985041171425993 9604607382738780878569495)
    ·
      refine ⟨14406911074108171317854243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9604607382738780878569495 14406911074108171317854243)
      ·
        refine ⟨21610366611162256976781365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14406911074108171317854243 21610366611162256976781365)
        ·
          refine ⟨2025971869796461591573253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21610366611162256976781365 2025971869796461591573253)
          ·
            refine ⟨379869725586836548419985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2025971869796461591573253 379869725586836548419985)
            ·
              refine ⟨284902294190127411314989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379869725586836548419985 284902294190127411314989)
              ·
                refine ⟨106838360321297779243121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284902294190127411314989 106838360321297779243121)
                ·
                  rfl

theorem cell19_351113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_351113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351113 prefixEnd_351113 := by exact prefixLift 351113
  have htrace : WordTrace (prefixWord ++ tailWord_351113) baseStart_351113 baseEnd_351113 := by
    simpa [prefixWord, tailWord_351113, baseEnd_351113] using wordTrace_append hprefix tailTrace_351113
  have hstable : (prefixWord ++ tailWord_351113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351113).length < 2 ^ (prefixWord ++ tailWord_351113).sum := by decide
  have hdescent : baseEnd_351113 < baseStart_351113 := by decide
  rcases family_descends (prefixWord ++ tailWord_351113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351115 : List Nat := [1, 1, 1, 1, 4, 2, 6, 3]
def baseStart_351115 : Nat := 118140960795 + 351115 * 2 ^ 59
def prefixEnd_351115 : Nat := 4983230072969 + 3 ^ 40 * 351115 * 2
def baseEnd_351115 : Nat := 106838968890962367198671

theorem tailTrace_351115 : CollatzResearch.WordTrace tailWord_351115 prefixEnd_351115 106838968890962367198671 := by
  unfold tailWord_351115
  simp only [CollatzResearch.WordTrace]
  refine ⟨12806216122977795512998799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8537477415318530341999199 12806216122977795512998799)
  ·
    refine ⟨19209324184466693269498199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12806216122977795512998799 19209324184466693269498199)
    ·
      refine ⟨28813986276700039904247299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19209324184466693269498199 28813986276700039904247299)
      ·
        refine ⟨43220979415050059856370949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28813986276700039904247299 43220979415050059856370949)
        ·
          refine ⟨8103933640321886223069553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43220979415050059856370949 8103933640321886223069553)
          ·
            refine ⟨6077950230241414667302165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8103933640321886223069553 6077950230241414667302165)
            ·
              refine ⟨284903917042566312529789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6077950230241414667302165 284903917042566312529789)
              ·
                refine ⟨106838968890962367198671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284903917042566312529789 106838968890962367198671)
                ·
                  rfl

theorem cell19_351115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_351115 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351115 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351115 prefixEnd_351115 := by exact prefixLift 351115
  have htrace : WordTrace (prefixWord ++ tailWord_351115) baseStart_351115 baseEnd_351115 := by
    simpa [prefixWord, tailWord_351115, baseEnd_351115] using wordTrace_append hprefix tailTrace_351115
  have hstable : (prefixWord ++ tailWord_351115).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351115).length < 2 ^ (prefixWord ++ tailWord_351115).sum := by decide
  have hdescent : baseEnd_351115 < baseStart_351115 := by decide
  rcases family_descends (prefixWord ++ tailWord_351115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351132 : List Nat := [2, 2, 3, 3, 2, 2, 5]
def baseStart_351132 : Nat := 118140960795 + 351132 * 2 ^ 59
def prefixEnd_351132 : Nat := 4983230072969 + 3 ^ 40 * 351132 * 2
def baseEnd_351132 : Nat := 35614713911037121606949

theorem tailTrace_351132 : CollatzResearch.WordTrace tailWord_351132 prefixEnd_351132 35614713911037121606949 := by
  unfold tailWord_351132
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403418081958103708183825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8537890775944138277578433 6403418081958103708183825)
  ·
    refine ⟨4802563561468577781137869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6403418081958103708183825 4802563561468577781137869)
    ·
      refine ⟨1800961335550716667926701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4802563561468577781137869 1800961335550716667926701)
      ·
        refine ⟨675360500831518750472513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1800961335550716667926701 675360500831518750472513)
        ·
          refine ⟨506520375623639062854385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675360500831518750472513 506520375623639062854385)
          ·
            refine ⟨379890281717729297140789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506520375623639062854385 379890281717729297140789)
            ·
              refine ⟨35614713911037121606949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 379890281717729297140789 35614713911037121606949)
              ·
                rfl

theorem cell19_351132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_351132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351132 prefixEnd_351132 := by exact prefixLift 351132
  have htrace : WordTrace (prefixWord ++ tailWord_351132) baseStart_351132 baseEnd_351132 := by
    simpa [prefixWord, tailWord_351132, baseEnd_351132] using wordTrace_append hprefix tailTrace_351132
  have hstable : (prefixWord ++ tailWord_351132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351132).length < 2 ^ (prefixWord ++ tailWord_351132).sum := by decide
  have hdescent : baseEnd_351132 < baseStart_351132 := by decide
  rcases family_descends (prefixWord ++ tailWord_351132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351136 : List Nat := [2, 1, 1, 4, 1, 1, 9]
def baseStart_351136 : Nat := 118140960795 + 351136 * 2 ^ 59
def prefixEnd_351136 : Nat := 4983230072969 + 3 ^ 40 * 351136 * 2
def baseEnd_351136 : Nat := 35615119624146846910649

theorem tailTrace_351136 : CollatzResearch.WordTrace tailWord_351136 prefixEnd_351136 35615119624146846910649 := by
  unfold tailWord_351136
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403491027950858049756631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8537988037267810733008841 6403491027950858049756631)
  ·
    refine ⟨9605236541926287074634947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6403491027950858049756631 9605236541926287074634947)
    ·
      refine ⟨14407854812889430611952421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9605236541926287074634947 14407854812889430611952421)
      ·
        refine ⟨2701472777416768239741079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14407854812889430611952421 2701472777416768239741079)
        ·
          refine ⟨4052209166125152359611619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701472777416768239741079 4052209166125152359611619)
          ·
            refine ⟨6078313749187728539417429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4052209166125152359611619 6078313749187728539417429)
            ·
              refine ⟨35615119624146846910649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6078313749187728539417429 35615119624146846910649)
              ·
                rfl

theorem cell19_351136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_351136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351136 prefixEnd_351136 := by exact prefixLift 351136
  have htrace : WordTrace (prefixWord ++ tailWord_351136) baseStart_351136 baseEnd_351136 := by
    simpa [prefixWord, tailWord_351136, baseEnd_351136] using wordTrace_append hprefix tailTrace_351136
  have hstable : (prefixWord ++ tailWord_351136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351136).length < 2 ^ (prefixWord ++ tailWord_351136).sum := by decide
  have hdescent : baseEnd_351136 < baseStart_351136 := by decide
  rcases family_descends (prefixWord ++ tailWord_351136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351149 : List Nat := [1, 5, 2, 3, 1, 1, 2, 4]
def baseStart_351149 : Nat := 118140960795 + 351149 * 2 ^ 59
def prefixEnd_351149 : Nat := 4983230072969 + 3 ^ 40 * 351149 * 2
def baseEnd_351149 : Nat := 106849314575260362443023

theorem tailTrace_351149 : CollatzResearch.WordTrace tailWord_351149 prefixEnd_351149 106849314575260362443023 := by
  unfold tailWord_351149
  simp only [CollatzResearch.WordTrace]
  refine ⟨12807456204854619319736501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8538304136569746213157667 12807456204854619319736501)
  ·
    refine ⟨1200699019205120561225297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12807456204854619319736501 1200699019205120561225297)
    ·
      refine ⟨900524264403840420918973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1200699019205120561225297 900524264403840420918973)
      ·
        refine ⟨337696599151440157844615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 900524264403840420918973 337696599151440157844615)
        ·
          refine ⟨506544898727160236766923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337696599151440157844615 506544898727160236766923)
          ·
            refine ⟨759817348090740355150385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506544898727160236766923 759817348090740355150385)
            ·
              refine ⟨569863011068055266362789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759817348090740355150385 569863011068055266362789)
              ·
                refine ⟨106849314575260362443023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569863011068055266362789 106849314575260362443023)
                ·
                  rfl

theorem cell19_351149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_351149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351149 prefixEnd_351149 := by exact prefixLift 351149
  have htrace : WordTrace (prefixWord ++ tailWord_351149) baseStart_351149 baseEnd_351149 := by
    simpa [prefixWord, tailWord_351149, baseEnd_351149] using wordTrace_append hprefix tailTrace_351149
  have hstable : (prefixWord ++ tailWord_351149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351149).length < 2 ^ (prefixWord ++ tailWord_351149).sum := by decide
  have hdescent : baseEnd_351149 < baseStart_351149 := by decide
  rcases family_descends (prefixWord ++ tailWord_351149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351193 : List Nat := [1, 2, 1, 2, 5, 8]
def baseStart_351193 : Nat := 118140960795 + 351193 * 2 ^ 59
def prefixEnd_351193 : Nat := 4983230072969 + 3 ^ 40 * 351193 * 2
def baseEnd_351193 : Nat := 11873633678653477496125

theorem tailTrace_351193 : CollatzResearch.WordTrace tailWord_351193 prefixEnd_351193 11873633678653477496125 := by
  unfold tailWord_351193
  simp only [CollatzResearch.WordTrace]
  refine ⟨12809061016695214834338233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8539374011130143222892155 12809061016695214834338233)
  ·
    refine ⟨9606795762521411125753675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12809061016695214834338233 9606795762521411125753675)
    ·
      refine ⟨14410193643782116688630513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9606795762521411125753675 14410193643782116688630513)
      ·
        refine ⟨10807645232836587516472885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14410193643782116688630513 10807645232836587516472885)
        ·
          refine ⟨1013216740578430079669333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10807645232836587516472885 1013216740578430079669333)
          ·
            refine ⟨11873633678653477496125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1013216740578430079669333 11873633678653477496125)
            ·
              rfl

theorem cell19_351193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 8].length) (baseStart_351193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351193 prefixEnd_351193 := by exact prefixLift 351193
  have htrace : WordTrace (prefixWord ++ tailWord_351193) baseStart_351193 baseEnd_351193 := by
    simpa [prefixWord, tailWord_351193, baseEnd_351193] using wordTrace_append hprefix tailTrace_351193
  have hstable : (prefixWord ++ tailWord_351193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351193).length < 2 ^ (prefixWord ++ tailWord_351193).sum := by decide
  have hdescent : baseEnd_351193 < baseStart_351193 := by decide
  rcases family_descends (prefixWord ++ tailWord_351193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351210 : List Nat := [3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_351210 : Nat := 118140960795 + 351210 * 2 ^ 59
def prefixEnd_351210 : Nat := 4983230072969 + 3 ^ 40 * 351210 * 2
def baseEnd_351210 : Nat := 106867875950030295087301

theorem tailTrace_351210 : CollatzResearch.WordTrace tailWord_351210 prefixEnd_351210 106867875950030295087301 := by
  unfold tailWord_351210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202420264408406684426771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8539787371755751158471389 3202420264408406684426771)
  ·
    refine ⟨4803630396612610026640157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3202420264408406684426771 4803630396612610026640157)
    ·
      refine ⟨1801361398729728759990059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4803630396612610026640157 1801361398729728759990059)
      ·
        refine ⟨2702042098094593139985089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801361398729728759990059 2702042098094593139985089)
        ·
          refine ⟨2026531573570944854988817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2702042098094593139985089 2026531573570944854988817)
          ·
            refine ⟨1519898680178208641241613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2026531573570944854988817 1519898680178208641241613)
            ·
              refine ⟨569962005066828240465605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1519898680178208641241613 569962005066828240465605)
              ·
                refine ⟨106867875950030295087301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569962005066828240465605 106867875950030295087301)
                ·
                  rfl

theorem cell19_351210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_351210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351210 prefixEnd_351210 := by exact prefixLift 351210
  have htrace : WordTrace (prefixWord ++ tailWord_351210) baseStart_351210 baseEnd_351210 := by
    simpa [prefixWord, tailWord_351210, baseEnd_351210] using wordTrace_append hprefix tailTrace_351210
  have hstable : (prefixWord ++ tailWord_351210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351210).length < 2 ^ (prefixWord ++ tailWord_351210).sum := by decide
  have hdescent : baseEnd_351210 < baseStart_351210 := by decide
  rcases family_descends (prefixWord ++ tailWord_351210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351269 : List Nat := [1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_351269 : Nat := 118140960795 + 351269 * 2 ^ 59
def prefixEnd_351269 : Nat := 4983230072969 + 3 ^ 40 * 351269 * 2
def baseEnd_351269 : Nat := 106885828755135639776029

theorem tailTrace_351269 : CollatzResearch.WordTrace tailWord_351269 prefixEnd_351269 106885828755135639776029 := by
  unfold tailWord_351269
  simp only [CollatzResearch.WordTrace]
  refine ⟨12811832964419879814104861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8541221976279919876069907 12811832964419879814104861)
  ·
    refine ⟨4804437361657454930289323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12811832964419879814104861 4804437361657454930289323)
    ·
      refine ⟨7206656042486182395433985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804437361657454930289323 7206656042486182395433985)
      ·
        refine ⟨5404992031864636796575489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7206656042486182395433985 5404992031864636796575489)
        ·
          refine ⟨4053744023898477597431617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5404992031864636796575489 4053744023898477597431617)
          ·
            refine ⟨3040308017923858198073713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4053744023898477597431617 3040308017923858198073713)
            ·
              refine ⟨2280231013442893648555285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040308017923858198073713 2280231013442893648555285)
              ·
                refine ⟨106885828755135639776029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2280231013442893648555285 106885828755135639776029)
                ·
                  rfl

theorem cell19_351269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_351269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351269 prefixEnd_351269 := by exact prefixLift 351269
  have htrace : WordTrace (prefixWord ++ tailWord_351269) baseStart_351269 baseEnd_351269 := by
    simpa [prefixWord, tailWord_351269, baseEnd_351269] using wordTrace_append hprefix tailTrace_351269
  have hstable : (prefixWord ++ tailWord_351269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351269).length < 2 ^ (prefixWord ++ tailWord_351269).sum := by decide
  have hdescent : baseEnd_351269 < baseStart_351269 := by decide
  rcases family_descends (prefixWord ++ tailWord_351269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351284 : List Nat := [2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_351284 : Nat := 118140960795 + 351284 * 2 ^ 59
def prefixEnd_351284 : Nat := 4983230072969 + 3 ^ 40 * 351284 * 2
def baseEnd_351284 : Nat := 106890393027620049442655

theorem tailTrace_351284 : CollatzResearch.WordTrace tailWord_351284 prefixEnd_351284 106890393027620049442655 := by
  unfold tailWord_351284
  simp only [CollatzResearch.WordTrace]
  refine ⟨6406190029682768687950453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8541586706243691583933937 6406190029682768687950453)
  ·
    refine ⟨600580315282759564495355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6406190029682768687950453 600580315282759564495355)
    ·
      refine ⟨900870472924139346743033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600580315282759564495355 900870472924139346743033)
      ·
        refine ⟨675652854693104510057275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 900870472924139346743033 675652854693104510057275)
        ·
          refine ⟨1013479282039656765085913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675652854693104510057275 1013479282039656765085913)
          ·
            refine ⟨760109461529742573814435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013479282039656765085913 760109461529742573814435)
            ·
              refine ⟨1140164192294613860721653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760109461529742573814435 1140164192294613860721653)
              ·
                refine ⟨106890393027620049442655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1140164192294613860721653 106890393027620049442655)
                ·
                  rfl

theorem cell19_351284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_351284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351284 prefixEnd_351284 := by exact prefixLift 351284
  have htrace : WordTrace (prefixWord ++ tailWord_351284) baseStart_351284 baseEnd_351284 := by
    simpa [prefixWord, tailWord_351284, baseEnd_351284] using wordTrace_append hprefix tailTrace_351284
  have hstable : (prefixWord ++ tailWord_351284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351284).length < 2 ^ (prefixWord ++ tailWord_351284).sum := by decide
  have hdescent : baseEnd_351284 < baseStart_351284 := by decide
  rcases family_descends (prefixWord ++ tailWord_351284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351324 : List Nat := [2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_351324 : Nat := 118140960795 + 351324 * 2 ^ 59
def prefixEnd_351324 : Nat := 4983230072969 + 3 ^ 40 * 351324 * 2
def baseEnd_351324 : Nat := 106902564420911808553657

theorem tailTrace_351324 : CollatzResearch.WordTrace tailWord_351324 prefixEnd_351324 106902564420911808553657 := by
  unfold tailWord_351324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6406919489610312103678513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8542559319480416138238017 6406919489610312103678513)
  ·
    refine ⟨4805189617207734077758885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6406919489610312103678513 4805189617207734077758885)
    ·
      refine ⟨900973053226450139579791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4805189617207734077758885 900973053226450139579791)
      ·
        refine ⟨1351459579839675209369687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900973053226450139579791 1351459579839675209369687)
        ·
          refine ⟨2027189369759512814054531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351459579839675209369687 2027189369759512814054531)
          ·
            refine ⟨3040784054639269221081797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027189369759512814054531 3040784054639269221081797)
            ·
              refine ⟨570147010244862978952837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3040784054639269221081797 570147010244862978952837)
              ·
                refine ⟨106902564420911808553657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 570147010244862978952837 106902564420911808553657)
                ·
                  rfl

theorem cell19_351324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_351324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351324 prefixEnd_351324 := by exact prefixLift 351324
  have htrace : WordTrace (prefixWord ++ tailWord_351324) baseStart_351324 baseEnd_351324 := by
    simpa [prefixWord, tailWord_351324, baseEnd_351324] using wordTrace_append hprefix tailTrace_351324
  have hstable : (prefixWord ++ tailWord_351324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351324).length < 2 ^ (prefixWord ++ tailWord_351324).sum := by decide
  have hdescent : baseEnd_351324 < baseStart_351324 := by decide
  rcases family_descends (prefixWord ++ tailWord_351324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351358 : List Nat := [4, 2, 4, 1, 1, 7]
def baseStart_351358 : Nat := 118140960795 + 351358 * 2 ^ 59
def prefixEnd_351358 : Nat := 4983230072969 + 3 ^ 40 * 351358 * 2
def baseEnd_351358 : Nat := 11879212233912200422001

theorem tailTrace_351358 : CollatzResearch.WordTrace tailWord_351358 prefixEnd_351358 11879212233912200422001 := by
  unfold tailWord_351358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601884882637181001761841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8543386040731632009396485 1601884882637181001761841)
  ·
    refine ⟨1201413661977885751321381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1601884882637181001761841 1201413661977885751321381)
    ·
      refine ⟨225265061620853578372759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1201413661977885751321381 225265061620853578372759)
      ·
        refine ⟨337897592431280367559139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225265061620853578372759 337897592431280367559139)
        ·
          refine ⟨506846388646920551338709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337897592431280367559139 506846388646920551338709)
          ·
            refine ⟨11879212233912200422001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 506846388646920551338709 11879212233912200422001)
            ·
              rfl

theorem cell19_351358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 7].length) (baseStart_351358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351358 prefixEnd_351358 := by exact prefixLift 351358
  have htrace : WordTrace (prefixWord ++ tailWord_351358) baseStart_351358 baseEnd_351358 := by
    simpa [prefixWord, tailWord_351358, baseEnd_351358] using wordTrace_append hprefix tailTrace_351358
  have hstable : (prefixWord ++ tailWord_351358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351358).length < 2 ^ (prefixWord ++ tailWord_351358).sum := by decide
  have hdescent : baseEnd_351358 < baseStart_351358 := by decide
  rcases family_descends (prefixWord ++ tailWord_351358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351364 : List Nat := [2, 3, 2, 1, 2, 9]
def baseStart_351364 : Nat := 118140960795 + 351364 * 2 ^ 59
def prefixEnd_351364 : Nat := 4983230072969 + 3 ^ 40 * 351364 * 2
def baseEnd_351364 : Nat := 11879415090467063073851

theorem tailTrace_351364 : CollatzResearch.WordTrace tailWord_351364 prefixEnd_351364 11879415090467063073851 := by
  unfold tailWord_351364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6407648949537855519406573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8543531932717140692542097 6407648949537855519406573)
  ·
    refine ⟨2402868356076695819777465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6407648949537855519406573 2402868356076695819777465)
    ·
      refine ⟨1802151267057521864833099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2402868356076695819777465 1802151267057521864833099)
      ·
        refine ⟨2703226900586282797249649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802151267057521864833099 2703226900586282797249649)
        ·
          refine ⟨2027420175439712097937237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2703226900586282797249649 2027420175439712097937237)
          ·
            refine ⟨11879415090467063073851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2027420175439712097937237 11879415090467063073851)
            ·
              rfl

theorem cell19_351364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 9].length) (baseStart_351364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351364 prefixEnd_351364 := by exact prefixLift 351364
  have htrace : WordTrace (prefixWord ++ tailWord_351364) baseStart_351364 baseEnd_351364 := by
    simpa [prefixWord, tailWord_351364, baseEnd_351364] using wordTrace_append hprefix tailTrace_351364
  have hstable : (prefixWord ++ tailWord_351364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351364).length < 2 ^ (prefixWord ++ tailWord_351364).sum := by decide
  have hdescent : baseEnd_351364 < baseStart_351364 := by decide
  rcases family_descends (prefixWord ++ tailWord_351364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351453 : List Nat := [1, 4, 3, 2, 2, 2, 2, 3]
def baseStart_351453 : Nat := 118140960795 + 351453 * 2 ^ 59
def prefixEnd_351453 : Nat := 4983230072969 + 3 ^ 40 * 351453 * 2
def baseEnd_351453 : Nat := 106941817164277731686639

theorem tailTrace_351453 : CollatzResearch.WordTrace tailWord_351453 prefixEnd_351453 106941817164277731686639 := by
  unfold tailWord_351453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818543995753279238803013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8545695997168852825868675 12818543995753279238803013)
  ·
    refine ⟨2403476999203739857275565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12818543995753279238803013 2403476999203739857275565)
    ·
      refine ⟨901303874701402446478337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2403476999203739857275565 901303874701402446478337)
      ·
        refine ⟨675977906026051834858753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 901303874701402446478337 675977906026051834858753)
        ·
          refine ⟨506983429519538876144065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675977906026051834858753 506983429519538876144065)
          ·
            refine ⟨380237572139654157108049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506983429519538876144065 380237572139654157108049)
            ·
              refine ⟨285178179104740617831037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380237572139654157108049 285178179104740617831037)
              ·
                refine ⟨106941817164277731686639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285178179104740617831037 106941817164277731686639)
                ·
                  rfl

theorem cell19_351453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_351453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351453 prefixEnd_351453 := by exact prefixLift 351453
  have htrace : WordTrace (prefixWord ++ tailWord_351453) baseStart_351453 baseEnd_351453 := by
    simpa [prefixWord, tailWord_351453, baseEnd_351453] using wordTrace_append hprefix tailTrace_351453
  have hstable : (prefixWord ++ tailWord_351453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351453).length < 2 ^ (prefixWord ++ tailWord_351453).sum := by decide
  have hdescent : baseEnd_351453 < baseStart_351453 := by decide
  rcases family_descends (prefixWord ++ tailWord_351453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351457 : List Nat := [1, 2, 3, 1, 3, 2, 4, 3]
def baseStart_351457 : Nat := 118140960795 + 351457 * 2 ^ 59
def prefixEnd_351457 : Nat := 4983230072969 + 3 ^ 40 * 351457 * 2
def baseEnd_351457 : Nat := 106943034303606907597739

theorem tailTrace_351457 : CollatzResearch.WordTrace tailWord_351457 prefixEnd_351457 106943034303606907597739 := by
  unfold tailWord_351457
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818689887738787921948625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8545793258492525281299083 12818689887738787921948625)
  ·
    refine ⟨9614017415804090941461469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12818689887738787921948625 9614017415804090941461469)
    ·
      refine ⟨3605256530926534103048051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9614017415804090941461469 3605256530926534103048051)
      ·
        refine ⟨5407884796389801154572077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605256530926534103048051 5407884796389801154572077)
        ·
          refine ⟨2027956798646175432964529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5407884796389801154572077 2027956798646175432964529)
          ·
            refine ⟨1520967598984631574723397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2027956798646175432964529 1520967598984631574723397)
            ·
              refine ⟨285181424809618420260637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1520967598984631574723397 285181424809618420260637)
              ·
                refine ⟨106943034303606907597739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285181424809618420260637 106943034303606907597739)
                ·
                  rfl

theorem cell19_351457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_351457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351457 prefixEnd_351457 := by exact prefixLift 351457
  have htrace : WordTrace (prefixWord ++ tailWord_351457) baseStart_351457 baseEnd_351457 := by
    simpa [prefixWord, tailWord_351457, baseEnd_351457] using wordTrace_append hprefix tailTrace_351457
  have hstable : (prefixWord ++ tailWord_351457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351457).length < 2 ^ (prefixWord ++ tailWord_351457).sum := by decide
  have hdescent : baseEnd_351457 < baseStart_351457 := by decide
  rcases family_descends (prefixWord ++ tailWord_351457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
