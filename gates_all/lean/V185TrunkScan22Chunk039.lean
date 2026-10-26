import V185TrunkScan22Chunk038

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_349233 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_349233 : Nat := 118140960795 + 349233 * 2 ^ 59
def prefixEnd_349233 : Nat := 4983230072969 + 3 ^ 40 * 349233 * 2
def baseEnd_349233 : Nat := 119549592941158238654275

theorem tailTrace_349233 : CollatzResearch.WordTrace tailWord_349233 prefixEnd_349233 119549592941158238654275 := by
  unfold tailWord_349233
  simp only [CollatzResearch.WordTrace]
  refine ⟨12737573943795960092988353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8491715962530640061992235 12737573943795960092988353)
  ·
    refine ⟨9553180457846970069741265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12737573943795960092988353 9553180457846970069741265)
    ·
      refine ⟨7164885343385227552305949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9553180457846970069741265 7164885343385227552305949)
      ·
        refine ⟨2686832003769460332114731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7164885343385227552305949 2686832003769460332114731)
        ·
          refine ⟨4030248005654190498172097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686832003769460332114731 4030248005654190498172097)
          ·
            refine ⟨3022686004240642873629073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4030248005654190498172097 3022686004240642873629073)
            ·
              refine ⟨2267014503180482155221805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022686004240642873629073 2267014503180482155221805)
              ·
                refine ⟨850130438692680808208177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2267014503180482155221805 850130438692680808208177)
                ·
                  refine ⟨637597829019510606156133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 850130438692680808208177 637597829019510606156133)
                  ·
                    refine ⟨119549592941158238654275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 637597829019510606156133 119549592941158238654275)
                    ·
                      rfl

theorem cell22_349233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_349233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349233 prefixEnd_349233 := by exact prefixLift 349233
  have htrace : WordTrace (prefixWord ++ tailWord_349233) baseStart_349233 baseEnd_349233 := by
    simpa [prefixWord, tailWord_349233, baseEnd_349233] using wordTrace_append hprefix tailTrace_349233
  have hstable : (prefixWord ++ tailWord_349233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349233).length < 2 ^ (prefixWord ++ tailWord_349233).sum := by decide
  have hdescent : baseEnd_349233 < baseStart_349233 := by decide
  rcases family_descends (prefixWord ++ tailWord_349233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349308 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_349308 : Nat := 118140960795 + 349308 * 2 ^ 59
def prefixEnd_349308 : Nat := 4983230072969 + 3 ^ 40 * 349308 * 2
def baseEnd_349308 : Nat := 119575266973883043029045

theorem tailTrace_349308 : CollatzResearch.WordTrace tailWord_349308 prefixEnd_349308 119575266973883043029045 := by
  unfold tailWord_349308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370154709262123950984289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8493539612349498601312385 6370154709262123950984289)
  ·
    refine ⟨4777616031946592963238217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6370154709262123950984289 4777616031946592963238217)
    ·
      refine ⟨3583212023959944722428663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4777616031946592963238217 3583212023959944722428663)
      ·
        refine ⟨5374818035939917083642995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583212023959944722428663 5374818035939917083642995)
        ·
          refine ⟨8062227053909875625464493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374818035939917083642995 8062227053909875625464493)
          ·
            refine ⟨3023335145216203359549185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8062227053909875625464493 3023335145216203359549185)
            ·
              refine ⟨2267501358912152519661889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3023335145216203359549185 2267501358912152519661889)
              ·
                refine ⟨1700626019184114389746417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2267501358912152519661889 1700626019184114389746417)
                ·
                  refine ⟨1275469514388085792309813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1700626019184114389746417 1275469514388085792309813)
                  ·
                    refine ⟨119575266973883043029045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1275469514388085792309813 119575266973883043029045)
                    ·
                      rfl

theorem cell22_349308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_349308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349308 prefixEnd_349308 := by exact prefixLift 349308
  have htrace : WordTrace (prefixWord ++ tailWord_349308) baseStart_349308 baseEnd_349308 := by
    simpa [prefixWord, tailWord_349308, baseEnd_349308] using wordTrace_append hprefix tailTrace_349308
  have hstable : (prefixWord ++ tailWord_349308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349308).length < 2 ^ (prefixWord ++ tailWord_349308).sum := by decide
  have hdescent : baseEnd_349308 < baseStart_349308 := by decide
  rcases family_descends (prefixWord ++ tailWord_349308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349340 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_349340 : Nat := 118140960795 + 349340 * 2 ^ 59
def prefixEnd_349340 : Nat := 4983230072969 + 3 ^ 40 * 349340 * 2
def baseEnd_349340 : Nat := 119586221227845626228947

theorem tailTrace_349340 : CollatzResearch.WordTrace tailWord_349340 prefixEnd_349340 119586221227845626228947 := by
  unfold tailWord_349340
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370738277204158683566737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8494317702938878244755649 6370738277204158683566737)
  ·
    refine ⟨4778053707903119012675053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6370738277204158683566737 4778053707903119012675053)
    ·
      refine ⟨1791770140463669629753145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4778053707903119012675053 1791770140463669629753145)
      ·
        refine ⟨1343827605347752222314859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1791770140463669629753145 1343827605347752222314859)
        ·
          refine ⟨2015741408021628333472289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343827605347752222314859 2015741408021628333472289)
          ·
            refine ⟨1511806056016221250104217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2015741408021628333472289 1511806056016221250104217)
            ·
              refine ⟨1133854542012165937578163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511806056016221250104217 1133854542012165937578163)
              ·
                refine ⟨1700781813018248906367245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133854542012165937578163 1700781813018248906367245)
                ·
                  refine ⟨637793179881843339887717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1700781813018248906367245 637793179881843339887717)
                  ·
                    refine ⟨119586221227845626228947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 637793179881843339887717 119586221227845626228947)
                    ·
                      rfl

theorem cell22_349340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_349340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349340 prefixEnd_349340 := by exact prefixLift 349340
  have htrace : WordTrace (prefixWord ++ tailWord_349340) baseStart_349340 baseEnd_349340 := by
    simpa [prefixWord, tailWord_349340, baseEnd_349340] using wordTrace_append hprefix tailTrace_349340
  have hstable : (prefixWord ++ tailWord_349340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349340).length < 2 ^ (prefixWord ++ tailWord_349340).sum := by decide
  have hdescent : baseEnd_349340 < baseStart_349340 := by decide
  rcases family_descends (prefixWord ++ tailWord_349340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349372 : List Nat := [2, 2, 2, 3, 2, 1, 2, 4, 4]
def baseStart_349372 : Nat := 118140960795 + 349372 * 2 ^ 59
def prefixEnd_349372 : Nat := 4983230072969 + 3 ^ 40 * 349372 * 2
def baseEnd_349372 : Nat := 39865725160602736476283

theorem tailTrace_349372 : CollatzResearch.WordTrace tailWord_349372 prefixEnd_349372 39865725160602736476283 := by
  unfold tailWord_349372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6371321845146193416149185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8495095793528257888198913 6371321845146193416149185)
  ·
    refine ⟨4778491383859645062111889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6371321845146193416149185 4778491383859645062111889)
    ·
      refine ⟨3583868537894733796583917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4778491383859645062111889 3583868537894733796583917)
      ·
        refine ⟨1343950701710525173718969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3583868537894733796583917 1343950701710525173718969)
        ·
          refine ⟨1007963026282893880289227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343950701710525173718969 1007963026282893880289227)
          ·
            refine ⟨1511944539424340820433841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007963026282893880289227 1511944539424340820433841)
            ·
              refine ⟨1133958404568255615325381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511944539424340820433841 1133958404568255615325381)
              ·
                refine ⟨212617200856547927873509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1133958404568255615325381 212617200856547927873509)
                ·
                  refine ⟨39865725160602736476283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212617200856547927873509 39865725160602736476283)
                  ·
                    rfl

theorem cell22_349372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_349372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349372 prefixEnd_349372 := by exact prefixLift 349372
  have htrace : WordTrace (prefixWord ++ tailWord_349372) baseStart_349372 baseEnd_349372 := by
    simpa [prefixWord, tailWord_349372, baseEnd_349372] using wordTrace_append hprefix tailTrace_349372
  have hstable : (prefixWord ++ tailWord_349372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349372).length < 2 ^ (prefixWord ++ tailWord_349372).sum := by decide
  have hdescent : baseEnd_349372 < baseStart_349372 := by decide
  rcases family_descends (prefixWord ++ tailWord_349372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349400 : List Nat := [2, 1, 2, 2, 5, 1, 1, 8]
def baseStart_349400 : Nat := 118140960795 + 349400 * 2 ^ 59
def prefixEnd_349400 : Nat := 4983230072969 + 3 ^ 40 * 349400 * 2
def baseEnd_349400 : Nat := 13289640050447274414307

theorem tailTrace_349400 : CollatzResearch.WordTrace tailWord_349400 prefixEnd_349400 13289640050447274414307 := by
  unfold tailWord_349400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6371832467095473807158827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8495776622793965076211769 6371832467095473807158827)
  ·
    refine ⟨9557748700643210710738241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6371832467095473807158827 9557748700643210710738241)
    ·
      refine ⟨7168311525482408033053681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9557748700643210710738241 7168311525482408033053681)
      ·
        refine ⟨5376233644111806024790261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7168311525482408033053681 5376233644111806024790261)
        ·
          refine ⟨504021904135481814824087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5376233644111806024790261 504021904135481814824087)
          ·
            refine ⟨756032856203222722236131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504021904135481814824087 756032856203222722236131)
            ·
              refine ⟨1134049284304834083354197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756032856203222722236131 1134049284304834083354197)
              ·
                refine ⟨13289640050447274414307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1134049284304834083354197 13289640050447274414307)
                ·
                  rfl

theorem cell22_349400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 8].length) (baseStart_349400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349400 prefixEnd_349400 := by exact prefixLift 349400
  have htrace : WordTrace (prefixWord ++ tailWord_349400) baseStart_349400 baseEnd_349400 := by
    simpa [prefixWord, tailWord_349400, baseEnd_349400] using wordTrace_append hprefix tailTrace_349400
  have hstable : (prefixWord ++ tailWord_349400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349400).length < 2 ^ (prefixWord ++ tailWord_349400).sum := by decide
  have hdescent : baseEnd_349400 < baseStart_349400 := by decide
  rcases family_descends (prefixWord ++ tailWord_349400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349430 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_349430 : Nat := 118140960795 + 349430 * 2 ^ 59
def prefixEnd_349430 : Nat := 4983230072969 + 3 ^ 40 * 349430 * 2
def baseEnd_349430 : Nat := 119617030067115391478671

theorem tailTrace_349430 : CollatzResearch.WordTrace tailWord_349430 prefixEnd_349430 119617030067115391478671 := by
  unfold tailWord_349430
  simp only [CollatzResearch.WordTrace]
  refine ⟨796547445255141421119359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8496506082721508491939829 796547445255141421119359)
  ·
    refine ⟨1194821167882712131679039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 796547445255141421119359 1194821167882712131679039)
    ·
      refine ⟨1792231751824068197518559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194821167882712131679039 1792231751824068197518559)
      ·
        refine ⟨2688347627736102296277839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792231751824068197518559 2688347627736102296277839)
        ·
          refine ⟨4032521441604153444416759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688347627736102296277839 4032521441604153444416759)
          ·
            refine ⟨6048782162406230166625139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032521441604153444416759 6048782162406230166625139)
            ·
              refine ⟨9073173243609345249937709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048782162406230166625139 9073173243609345249937709)
              ·
                refine ⟨3402439966353504468726641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9073173243609345249937709 3402439966353504468726641)
                ·
                  refine ⟨2551829974765128351544981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3402439966353504468726641 2551829974765128351544981)
                  ·
                    refine ⟨119617030067115391478671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2551829974765128351544981 119617030067115391478671)
                    ·
                      rfl

theorem cell22_349430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_349430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349430 prefixEnd_349430 := by exact prefixLift 349430
  have htrace : WordTrace (prefixWord ++ tailWord_349430) baseStart_349430 baseEnd_349430 := by
    simpa [prefixWord, tailWord_349430, baseEnd_349430] using wordTrace_append hprefix tailTrace_349430
  have hstable : (prefixWord ++ tailWord_349430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349430).length < 2 ^ (prefixWord ++ tailWord_349430).sum := by decide
  have hdescent : baseEnd_349430 < baseStart_349430 := by decide
  rcases family_descends (prefixWord ++ tailWord_349430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349445 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 5]
def baseStart_349445 : Nat := 118140960795 + 349445 * 2 ^ 59
def prefixEnd_349445 : Nat := 4983230072969 + 3 ^ 40 * 349445 * 2
def baseEnd_349445 : Nat := 39874054957886784117875

theorem tailTrace_349445 : CollatzResearch.WordTrace tailWord_349445 prefixEnd_349445 39874054957886784117875 := by
  unfold tailWord_349445
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745306219027920299705789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8496870812685280199803859 12745306219027920299705789)
  ·
    refine ⟨4779489832135470112389671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12745306219027920299705789 4779489832135470112389671)
    ·
      refine ⟨7169234748203205168584507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779489832135470112389671 7169234748203205168584507)
      ·
        refine ⟨10753852122304807752876761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169234748203205168584507 10753852122304807752876761)
        ·
          refine ⟨8065389091728605814657571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10753852122304807752876761 8065389091728605814657571)
          ·
            refine ⟨12098083637592908721986357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8065389091728605814657571 12098083637592908721986357)
            ·
              refine ⟨1134195341024335192686221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12098083637592908721986357 1134195341024335192686221)
              ·
                refine ⟨425323252884125697257333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1134195341024335192686221 425323252884125697257333)
                ·
                  refine ⟨39874054957886784117875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 425323252884125697257333 39874054957886784117875)
                  ·
                    rfl

theorem cell22_349445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_349445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349445 prefixEnd_349445 := by exact prefixLift 349445
  have htrace : WordTrace (prefixWord ++ tailWord_349445) baseStart_349445 baseEnd_349445 := by
    simpa [prefixWord, tailWord_349445, baseEnd_349445] using wordTrace_append hprefix tailTrace_349445
  have hstable : (prefixWord ++ tailWord_349445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349445).length < 2 ^ (prefixWord ++ tailWord_349445).sum := by decide
  have hdescent : baseEnd_349445 < baseStart_349445 := by decide
  rcases family_descends (prefixWord ++ tailWord_349445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349492 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_349492 : Nat := 118140960795 + 349492 * 2 ^ 59
def prefixEnd_349492 : Nat := 4983230072969 + 3 ^ 40 * 349492 * 2
def baseEnd_349492 : Nat := 119638253934167896428481

theorem tailTrace_349492 : CollatzResearch.WordTrace tailWord_349492 prefixEnd_349492 119638253934167896428481 := by
  unfold tailWord_349492
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373510224928823663333365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8498013633238431551111153 6373510224928823663333365)
  ·
    refine ⟨597516583587077218437503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6373510224928823663333365 597516583587077218437503)
    ·
      refine ⟨896274875380615827656255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597516583587077218437503 896274875380615827656255)
      ·
        refine ⟨1344412313070923741484383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896274875380615827656255 1344412313070923741484383)
        ·
          refine ⟨2016618469606385612226575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344412313070923741484383 2016618469606385612226575)
          ·
            refine ⟨3024927704409578418339863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016618469606385612226575 3024927704409578418339863)
            ·
              refine ⟨4537391556614367627509795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024927704409578418339863 4537391556614367627509795)
              ·
                refine ⟨6806087334921551441264693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537391556614367627509795 6806087334921551441264693)
                ·
                  refine ⟨638070687648895447618565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6806087334921551441264693 638070687648895447618565)
                  ·
                    refine ⟨119638253934167896428481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638070687648895447618565 119638253934167896428481)
                    ·
                      rfl

theorem cell22_349492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_349492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349492 prefixEnd_349492 := by exact prefixLift 349492
  have htrace : WordTrace (prefixWord ++ tailWord_349492) baseStart_349492 baseEnd_349492 := by
    simpa [prefixWord, tailWord_349492, baseEnd_349492] using wordTrace_append hprefix tailTrace_349492
  have hstable : (prefixWord ++ tailWord_349492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349492).length < 2 ^ (prefixWord ++ tailWord_349492).sum := by decide
  have hdescent : baseEnd_349492 < baseStart_349492 := by decide
  rcases family_descends (prefixWord ++ tailWord_349492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349520 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_349520 : Nat := 118140960795 + 349520 * 2 ^ 59
def prefixEnd_349520 : Nat := 4983230072969 + 3 ^ 40 * 349520 * 2
def baseEnd_349520 : Nat := 119647838906385156728395

theorem tailTrace_349520 : CollatzResearch.WordTrace tailWord_349520 prefixEnd_349520 119647838906385156728395 := by
  unfold tailWord_349520
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374020846878104054343007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8498694462504138739124009 6374020846878104054343007)
  ·
    refine ⟨9561031270317156081514511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6374020846878104054343007 9561031270317156081514511)
    ·
      refine ⟨14341546905475734122271767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9561031270317156081514511 14341546905475734122271767)
      ·
        refine ⟨21512320358213601183407651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14341546905475734122271767 21512320358213601183407651)
        ·
          refine ⟨32268480537320401775111477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21512320358213601183407651 32268480537320401775111477)
          ·
            refine ⟨3025170050373787666416701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32268480537320401775111477 3025170050373787666416701)
            ·
              refine ⟨1134438768890170374906263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3025170050373787666416701 1134438768890170374906263)
              ·
                refine ⟨1701658153335255562359395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134438768890170374906263 1701658153335255562359395)
                ·
                  refine ⟨2552487230002883343539093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1701658153335255562359395 2552487230002883343539093)
                  ·
                    refine ⟨119647838906385156728395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2552487230002883343539093 119647838906385156728395)
                    ·
                      rfl

theorem cell22_349520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_349520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349520 prefixEnd_349520 := by exact prefixLift 349520
  have htrace : WordTrace (prefixWord ++ tailWord_349520) baseStart_349520 baseEnd_349520 := by
    simpa [prefixWord, tailWord_349520, baseEnd_349520] using wordTrace_append hprefix tailTrace_349520
  have hstable : (prefixWord ++ tailWord_349520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349520).length < 2 ^ (prefixWord ++ tailWord_349520).sum := by decide
  have hdescent : baseEnd_349520 < baseStart_349520 := by decide
  rcases family_descends (prefixWord ++ tailWord_349520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349522 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_349522 : Nat := 118140960795 + 349522 * 2 ^ 59
def prefixEnd_349522 : Nat := 4983230072969 + 3 ^ 40 * 349522 * 2
def baseEnd_349522 : Nat := 119648523547257818178389

theorem tailTrace_349522 : CollatzResearch.WordTrace tailWord_349522 prefixEnd_349522 119648523547257818178389 := by
  unfold tailWord_349522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187028659937240612564705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8498743093165974966839213 3187028659937240612564705)
  ·
    refine ⟨2390271494952930459423529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3187028659937240612564705 2390271494952930459423529)
    ·
      refine ⟨1792703621214697844567647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2390271494952930459423529 1792703621214697844567647)
      ·
        refine ⟨2689055431822046766851471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792703621214697844567647 2689055431822046766851471)
        ·
          refine ⟨4033583147733070150277207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689055431822046766851471 4033583147733070150277207)
          ·
            refine ⟨6050374721599605225415811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033583147733070150277207 6050374721599605225415811)
            ·
              refine ⟨9075562082399407838123717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6050374721599605225415811 9075562082399407838123717)
              ·
                refine ⟨1701667890449888969648197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9075562082399407838123717 1701667890449888969648197)
                ·
                  refine ⟨319062729459354181809037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701667890449888969648197 319062729459354181809037)
                  ·
                    refine ⟨119648523547257818178389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319062729459354181809037 119648523547257818178389)
                    ·
                      rfl

theorem cell22_349522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_349522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349522 prefixEnd_349522 := by exact prefixLift 349522
  have htrace : WordTrace (prefixWord ++ tailWord_349522) baseStart_349522 baseEnd_349522 := by
    simpa [prefixWord, tailWord_349522, baseEnd_349522] using wordTrace_append hprefix tailTrace_349522
  have hstable : (prefixWord ++ tailWord_349522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349522).length < 2 ^ (prefixWord ++ tailWord_349522).sum := by decide
  have hdescent : baseEnd_349522 < baseStart_349522 := by decide
  rcases family_descends (prefixWord ++ tailWord_349522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349524 : List Nat := [2, 4, 1, 1, 2, 1, 4, 3, 4]
def baseStart_349524 : Nat := 118140960795 + 349524 * 2 ^ 59
def prefixEnd_349524 : Nat := 4983230072969 + 3 ^ 40 * 349524 * 2
def baseEnd_349524 : Nat := 39883069396043493209461

theorem tailTrace_349524 : CollatzResearch.WordTrace tailWord_349524 prefixEnd_349524 39883069396043493209461 := by
  unfold tailWord_349524
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374093792870858395915813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8498791723827811194554417 6374093792870858395915813)
  ·
    refine ⟨1195142586163285949234215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6374093792870858395915813 1195142586163285949234215)
    ·
      refine ⟨1792713879244928923851323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195142586163285949234215 1792713879244928923851323)
      ·
        refine ⟨2689070818867393385776985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792713879244928923851323 2689070818867393385776985)
        ·
          refine ⟨2016803114150545039332739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2689070818867393385776985 2016803114150545039332739)
          ·
            refine ⟨3025204671225817558999109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016803114150545039332739 3025204671225817558999109)
            ·
              refine ⟨567225875854840792312333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3025204671225817558999109 567225875854840792312333)
              ·
                refine ⟨212709703445565297117125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 567225875854840792312333 212709703445565297117125)
                ·
                  refine ⟨39883069396043493209461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212709703445565297117125 39883069396043493209461)
                  ·
                    rfl

theorem cell22_349524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_349524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349524 prefixEnd_349524 := by exact prefixLift 349524
  have htrace : WordTrace (prefixWord ++ tailWord_349524) baseStart_349524 baseEnd_349524 := by
    simpa [prefixWord, tailWord_349524, baseEnd_349524] using wordTrace_append hprefix tailTrace_349524
  have hstable : (prefixWord ++ tailWord_349524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349524).length < 2 ^ (prefixWord ++ tailWord_349524).sum := by decide
  have hdescent : baseEnd_349524 < baseStart_349524 := by decide
  rcases family_descends (prefixWord ++ tailWord_349524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349539 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 2, 3]
def baseStart_349539 : Nat := 118140960795 + 349539 * 2 ^ 59
def prefixEnd_349539 : Nat := 4983230072969 + 3 ^ 40 * 349539 * 2
def baseEnd_349539 : Nat := 119654342994675440503337

theorem tailTrace_349539 : CollatzResearch.WordTrace tailWord_349539 prefixEnd_349539 119654342994675440503337 := by
  unfold tailWord_349539
  simp only [CollatzResearch.WordTrace]
  refine ⟨12748734680687374353627671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8499156453791582902418447 12748734680687374353627671)
  ·
    refine ⟨19123102021031061530441507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12748734680687374353627671 19123102021031061530441507)
    ·
      refine ⟨28684653031546592295662261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19123102021031061530441507 28684653031546592295662261)
      ·
        refine ⟨2689186221707493027718337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28684653031546592295662261 2689186221707493027718337)
        ·
          refine ⟨2016889666280619770788753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2689186221707493027718337 2016889666280619770788753)
          ·
            refine ⟨1512667249710464828091565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016889666280619770788753 1512667249710464828091565)
            ·
              refine ⟨567250218641424310534337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1512667249710464828091565 567250218641424310534337)
              ·
                refine ⟨425437663981068232900753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567250218641424310534337 425437663981068232900753)
                ·
                  refine ⟨319078247985801174675565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425437663981068232900753 319078247985801174675565)
                  ·
                    refine ⟨119654342994675440503337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319078247985801174675565 119654342994675440503337)
                    ·
                      rfl

theorem cell22_349539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 3].length) (baseStart_349539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349539 prefixEnd_349539 := by exact prefixLift 349539
  have htrace : WordTrace (prefixWord ++ tailWord_349539) baseStart_349539 baseEnd_349539 := by
    simpa [prefixWord, tailWord_349539, baseEnd_349539] using wordTrace_append hprefix tailTrace_349539
  have hstable : (prefixWord ++ tailWord_349539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349539).length < 2 ^ (prefixWord ++ tailWord_349539).sum := by decide
  have hdescent : baseEnd_349539 < baseStart_349539 := by decide
  rcases family_descends (prefixWord ++ tailWord_349539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349580 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 9]
def baseStart_349580 : Nat := 118140960795 + 349580 * 2 ^ 59
def prefixEnd_349580 : Nat := 4983230072969 + 3 ^ 40 * 349580 * 2
def baseEnd_349580 : Nat := 39889459377521666742737

theorem tailTrace_349580 : CollatzResearch.WordTrace tailWord_349580 prefixEnd_349580 39889459377521666742737 := by
  unfold tailWord_349580
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375115036769419177935097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8500153382359225570580129 6375115036769419177935097)
  ·
    refine ⟨4781336277577064383451323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6375115036769419177935097 4781336277577064383451323)
    ·
      refine ⟨7172004416365596575176985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4781336277577064383451323 7172004416365596575176985)
      ·
        refine ⟨5379003312274197431382739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7172004416365596575176985 5379003312274197431382739)
        ·
          refine ⟨8068504968411296147074109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379003312274197431382739 8068504968411296147074109)
          ·
            refine ⟨3025689363154236055152791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8068504968411296147074109 3025689363154236055152791)
            ·
              refine ⟨4538534044731354082729187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025689363154236055152791 4538534044731354082729187)
              ·
                refine ⟨6807801067097031124093781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538534044731354082729187 6807801067097031124093781)
                ·
                  refine ⟨39889459377521666742737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6807801067097031124093781 39889459377521666742737)
                  ·
                    rfl

theorem cell22_349580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_349580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349580 prefixEnd_349580 := by exact prefixLift 349580
  have htrace : WordTrace (prefixWord ++ tailWord_349580) baseStart_349580 baseEnd_349580 := by
    simpa [prefixWord, tailWord_349580, baseEnd_349580] using wordTrace_append hprefix tailTrace_349580
  have hstable : (prefixWord ++ tailWord_349580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349580).length < 2 ^ (prefixWord ++ tailWord_349580).sum := by decide
  have hdescent : baseEnd_349580 < baseStart_349580 := by decide
  rcases family_descends (prefixWord ++ tailWord_349580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349586 : List Nat := [3, 2, 3, 3, 2, 1, 8]
def baseStart_349586 : Nat := 118140960795 + 349586 * 2 ^ 59
def prefixEnd_349586 : Nat := 4983230072969 + 3 ^ 40 * 349586 * 2
def baseEnd_349586 : Nat := 4432238224266036465859

theorem tailTrace_349586 : CollatzResearch.WordTrace tailWord_349586 prefixEnd_349586 4432238224266036465859 := by
  unfold tailWord_349586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187612227879275345147153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8500299274344734253725741 3187612227879275345147153)
  ·
    refine ⟨2390709170909456508860365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3187612227879275345147153 2390709170909456508860365)
    ·
      refine ⟨896515939091046190822637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2390709170909456508860365 896515939091046190822637)
      ·
        refine ⟨336193477159142321558489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 896515939091046190822637 336193477159142321558489)
        ·
          refine ⟨252145107869356741168867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336193477159142321558489 252145107869356741168867)
          ·
            refine ⟨378217661804035111753301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252145107869356741168867 378217661804035111753301)
            ·
              refine ⟨4432238224266036465859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 378217661804035111753301 4432238224266036465859)
              ·
                rfl

theorem cell22_349586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 8].length) (baseStart_349586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349586 prefixEnd_349586 := by exact prefixLift 349586
  have htrace : WordTrace (prefixWord ++ tailWord_349586) baseStart_349586 baseEnd_349586 := by
    simpa [prefixWord, tailWord_349586, baseEnd_349586] using wordTrace_append hprefix tailTrace_349586
  have hstable : (prefixWord ++ tailWord_349586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349586).length < 2 ^ (prefixWord ++ tailWord_349586).sum := by decide
  have hdescent : baseEnd_349586 < baseStart_349586 := by decide
  rcases family_descends (prefixWord ++ tailWord_349586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349597 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 7]
def baseStart_349597 : Nat := 118140960795 + 349597 * 2 ^ 59
def prefixEnd_349597 : Nat := 4983230072969 + 3 ^ 40 * 349597 * 2
def baseEnd_349597 : Nat := 39891399193327540851053

theorem tailTrace_349597 : CollatzResearch.WordTrace tailWord_349597 prefixEnd_349597 39891399193327540851053 := by
  unfold tailWord_349597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12750850114477250259239045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8500566742984833506159363 12750850114477250259239045)
  ·
    refine ⟨2390784396464484423607321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12750850114477250259239045 2390784396464484423607321)
    ·
      refine ⟨1793088297348363317705491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2390784396464484423607321 1793088297348363317705491)
      ·
        refine ⟨2689632446022544976558237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1793088297348363317705491 2689632446022544976558237)
        ·
          refine ⟨1008612167258454366209339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2689632446022544976558237 1008612167258454366209339)
          ·
            refine ⟨1512918250887681549314009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008612167258454366209339 1512918250887681549314009)
            ·
              refine ⟨1134688688165761161985507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512918250887681549314009 1134688688165761161985507)
              ·
                refine ⟨1702033032248641742978261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134688688165761161985507 1702033032248641742978261)
                ·
                  refine ⟨39891399193327540851053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1702033032248641742978261 39891399193327540851053)
                  ·
                    rfl

theorem cell22_349597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_349597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349597 prefixEnd_349597 := by exact prefixLift 349597
  have htrace : WordTrace (prefixWord ++ tailWord_349597) baseStart_349597 baseEnd_349597 := by
    simpa [prefixWord, tailWord_349597, baseEnd_349597] using wordTrace_append hprefix tailTrace_349597
  have hstable : (prefixWord ++ tailWord_349597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349597).length < 2 ^ (prefixWord ++ tailWord_349597).sum := by decide
  have hdescent : baseEnd_349597 < baseStart_349597 := by decide
  rcases family_descends (prefixWord ++ tailWord_349597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349652 : List Nat := [2, 4, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_349652 : Nat := 118140960795 + 349652 * 2 ^ 59
def prefixEnd_349652 : Nat := 4983230072969 + 3 ^ 40 * 349652 * 2
def baseEnd_349652 : Nat := 119693025203980812427991

theorem tailTrace_349652 : CollatzResearch.WordTrace tailWord_349652 prefixEnd_349652 119693025203980812427991 := by
  unfold tailWord_349652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376428064638997326245605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8501904086185329768327473 6376428064638997326245605)
  ·
    refine ⟨1195580262119811998671051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6376428064638997326245605 1195580262119811998671051)
    ·
      refine ⟨1793370393179717998006577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195580262119811998671051 1793370393179717998006577)
      ·
        refine ⟨1345027794884788498504933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1793370393179717998006577 1345027794884788498504933)
        ·
          refine ⟨252192711540897843469675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1345027794884788498504933 252192711540897843469675)
          ·
            refine ⟨378289067311346765204513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252192711540897843469675 378289067311346765204513)
            ·
              refine ⟨283716800483510073903385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378289067311346765204513 283716800483510073903385)
              ·
                refine ⟨212787600362632555427539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283716800483510073903385 212787600362632555427539)
                ·
                  refine ⟨319181400543948833141309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212787600362632555427539 319181400543948833141309)
                  ·
                    refine ⟨119693025203980812427991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319181400543948833141309 119693025203980812427991)
                    ·
                      rfl

theorem cell22_349652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_349652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349652 prefixEnd_349652 := by exact prefixLift 349652
  have htrace : WordTrace (prefixWord ++ tailWord_349652) baseStart_349652 baseEnd_349652 := by
    simpa [prefixWord, tailWord_349652, baseEnd_349652] using wordTrace_append hprefix tailTrace_349652
  have hstable : (prefixWord ++ tailWord_349652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349652).length < 2 ^ (prefixWord ++ tailWord_349652).sum := by decide
  have hdescent : baseEnd_349652 < baseStart_349652 := by decide
  rcases family_descends (prefixWord ++ tailWord_349652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349672 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_349672 : Nat := 118140960795 + 349672 * 2 ^ 59
def prefixEnd_349672 : Nat := 4983230072969 + 3 ^ 40 * 349672 * 2
def baseEnd_349672 : Nat := 119699871612707426927929

theorem tailTrace_349672 : CollatzResearch.WordTrace tailWord_349672 prefixEnd_349672 119699871612707426927929 := by
  unfold tailWord_349672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376792794602769034109635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8502390392803692045479513 6376792794602769034109635)
  ·
    refine ⟨9565189191904153551164453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6376792794602769034109635 9565189191904153551164453)
    ·
      refine ⟨1793472973482028790843335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9565189191904153551164453 1793472973482028790843335)
      ·
        refine ⟨2690209460223043186265003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1793472973482028790843335 2690209460223043186265003)
        ·
          refine ⟨4035314190334564779397505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690209460223043186265003 4035314190334564779397505)
          ·
            refine ⟨3026485642750923584548129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4035314190334564779397505 3026485642750923584548129)
            ·
              refine ⟨2269864232063192688411097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026485642750923584548129 2269864232063192688411097)
              ·
                refine ⟨1702398174047394516308323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269864232063192688411097 1702398174047394516308323)
                ·
                  refine ⟨2553597261071091774462485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702398174047394516308323 2553597261071091774462485)
                  ·
                    refine ⟨119699871612707426927929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2553597261071091774462485 119699871612707426927929)
                    ·
                      rfl

theorem cell22_349672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_349672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349672 prefixEnd_349672 := by exact prefixLift 349672
  have htrace : WordTrace (prefixWord ++ tailWord_349672) baseStart_349672 baseEnd_349672 := by
    simpa [prefixWord, tailWord_349672, baseEnd_349672] using wordTrace_append hprefix tailTrace_349672
  have hstable : (prefixWord ++ tailWord_349672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349672).length < 2 ^ (prefixWord ++ tailWord_349672).sum := by decide
  have hdescent : baseEnd_349672 < baseStart_349672 := by decide
  rcases family_descends (prefixWord ++ tailWord_349672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349708 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_349708 : Nat := 118140960795 + 349708 * 2 ^ 59
def prefixEnd_349708 : Nat := 4983230072969 + 3 ^ 40 * 349708 * 2
def baseEnd_349708 : Nat := 119712195148415333027819

theorem tailTrace_349708 : CollatzResearch.WordTrace tailWord_349708 prefixEnd_349708 119712195148415333027819 := by
  unfold tailWord_349708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6377449308537558108264889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8503265744716744144353185 6377449308537558108264889)
  ·
    refine ⟨4783086981403168581198667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6377449308537558108264889 4783086981403168581198667)
    ·
      refine ⟨7174630472104752871798001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4783086981403168581198667 7174630472104752871798001)
      ·
        refine ⟨5380972854078564653848501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7174630472104752871798001 5380972854078564653848501)
        ·
          refine ⟨504466205069865436298297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5380972854078564653848501 504466205069865436298297)
          ·
            refine ⟨378349653802399077223723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504466205069865436298297 378349653802399077223723)
            ·
              refine ⟨567524480703598615835585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378349653802399077223723 567524480703598615835585)
              ·
                refine ⟨425643360527698961876689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567524480703598615835585 425643360527698961876689)
                ·
                  refine ⟨319232520395774221407517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425643360527698961876689 319232520395774221407517)
                  ·
                    refine ⟨119712195148415333027819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319232520395774221407517 119712195148415333027819)
                    ·
                      rfl

theorem cell22_349708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_349708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349708 prefixEnd_349708 := by exact prefixLift 349708
  have htrace : WordTrace (prefixWord ++ tailWord_349708) baseStart_349708 baseEnd_349708 := by
    simpa [prefixWord, tailWord_349708, baseEnd_349708] using wordTrace_append hprefix tailTrace_349708
  have hstable : (prefixWord ++ tailWord_349708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349708).length < 2 ^ (prefixWord ++ tailWord_349708).sum := by decide
  have hdescent : baseEnd_349708 < baseStart_349708 := by decide
  rcases family_descends (prefixWord ++ tailWord_349708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349753 : List Nat := [1, 2, 1, 5, 1, 2, 3, 3, 1, 3]
def baseStart_349753 : Nat := 118140960795 + 349753 * 2 ^ 59
def prefixEnd_349753 : Nat := 4983230072969 + 3 ^ 40 * 349753 * 2
def baseEnd_349753 : Nat := 119727599568050215652681

theorem tailTrace_349753 : CollatzResearch.WordTrace tailWord_349753 prefixEnd_349753 119727599568050215652681 := by
  unfold tailWord_349753
  simp only [CollatzResearch.WordTrace]
  refine ⟨12756539901912088901917913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8504359934608059267945275 12756539901912088901917913)
  ·
    refine ⟨9567404926434066676438435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12756539901912088901917913 9567404926434066676438435)
    ·
      refine ⟨14351107389651100014657653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9567404926434066676438435 14351107389651100014657653)
      ·
        refine ⟨1345416317779790626374155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14351107389651100014657653 1345416317779790626374155)
        ·
          refine ⟨2018124476669685939561233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345416317779790626374155 2018124476669685939561233)
          ·
            refine ⟨1513593357502264454670925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2018124476669685939561233 1513593357502264454670925)
            ·
              refine ⟨567597509063349170501597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1513593357502264454670925 567597509063349170501597)
              ·
                refine ⟨212849065898755938938099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 567597509063349170501597 212849065898755938938099)
                ·
                  refine ⟨319273598848133908407149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212849065898755938938099 319273598848133908407149)
                  ·
                    refine ⟨119727599568050215652681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319273598848133908407149 119727599568050215652681)
                    ·
                      rfl

theorem cell22_349753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 3].length) (baseStart_349753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349753 prefixEnd_349753 := by exact prefixLift 349753
  have htrace : WordTrace (prefixWord ++ tailWord_349753) baseStart_349753 baseEnd_349753 := by
    simpa [prefixWord, tailWord_349753, baseEnd_349753] using wordTrace_append hprefix tailTrace_349753
  have hstable : (prefixWord ++ tailWord_349753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349753).length < 2 ^ (prefixWord ++ tailWord_349753).sum := by decide
  have hdescent : baseEnd_349753 < baseStart_349753 := by decide
  rcases family_descends (prefixWord ++ tailWord_349753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349796 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_349796 : Nat := 118140960795 + 349796 * 2 ^ 59
def prefixEnd_349796 : Nat := 4983230072969 + 3 ^ 40 * 349796 * 2
def baseEnd_349796 : Nat := 119742319346812436827549

theorem tailTrace_349796 : CollatzResearch.WordTrace tailWord_349796 prefixEnd_349796 119742319346812436827549 := by
  unfold tailWord_349796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379054120378153622866621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8505405493837538163822161 6379054120378153622866621)
  ·
    refine ⟨2392145295141807608574983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6379054120378153622866621 2392145295141807608574983)
    ·
      refine ⟨3588217942712711412862475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392145295141807608574983 3588217942712711412862475)
      ·
        refine ⟨5382326914069067119293713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588217942712711412862475 5382326914069067119293713)
        ·
          refine ⟨4036745185551800339470285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5382326914069067119293713 4036745185551800339470285)
          ·
            refine ⟨1513779444581925127301357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4036745185551800339470285 1513779444581925127301357)
            ·
              refine ⟨567667291718221922738009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1513779444581925127301357 567667291718221922738009)
              ·
                refine ⟨425750468788666442053507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567667291718221922738009 425750468788666442053507)
                ·
                  refine ⟨638625703182999663080261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425750468788666442053507 638625703182999663080261)
                  ·
                    refine ⟨119742319346812436827549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638625703182999663080261 119742319346812436827549)
                    ·
                      rfl

theorem cell22_349796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_349796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349796 prefixEnd_349796 := by exact prefixLift 349796
  have htrace : WordTrace (prefixWord ++ tailWord_349796) baseStart_349796 baseEnd_349796 := by
    simpa [prefixWord, tailWord_349796, baseEnd_349796] using wordTrace_append hprefix tailTrace_349796
  have hstable : (prefixWord ++ tailWord_349796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349796).length < 2 ^ (prefixWord ++ tailWord_349796).sum := by decide
  have hdescent : baseEnd_349796 < baseStart_349796 := by decide
  rcases family_descends (prefixWord ++ tailWord_349796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349809 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 6, 3]
def baseStart_349809 : Nat := 118140960795 + 349809 * 2 ^ 59
def prefixEnd_349809 : Nat := 4983230072969 + 3 ^ 40 * 349809 * 2
def baseEnd_349809 : Nat := 119746769512484736252509

theorem tailTrace_349809 : CollatzResearch.WordTrace tailWord_349809 prefixEnd_349809 119746769512484736252509 := by
  unfold tailWord_349809
  simp only [CollatzResearch.WordTrace]
  refine ⟨12758582389709210465956481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8505721593139473643970987 12758582389709210465956481)
  ·
    refine ⟨9568936792281907849467361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12758582389709210465956481 9568936792281907849467361)
    ·
      refine ⟨7176702594211430887100521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9568936792281907849467361 7176702594211430887100521)
      ·
        refine ⟨5382526945658573165325391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7176702594211430887100521 5382526945658573165325391)
        ·
          refine ⟨8073790418487859747988087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382526945658573165325391 8073790418487859747988087)
          ·
            refine ⟨12110685627731789621982131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8073790418487859747988087 12110685627731789621982131)
            ·
              refine ⟨18166028441597684432973197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12110685627731789621982131 18166028441597684432973197)
              ·
                refine ⟨6812260665599131662364949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18166028441597684432973197 6812260665599131662364949)
                ·
                  refine ⟨319324718699959296673357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6812260665599131662364949 319324718699959296673357)
                  ·
                    refine ⟨119746769512484736252509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319324718699959296673357 119746769512484736252509)
                    ·
                      rfl

theorem cell22_349809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_349809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349809 prefixEnd_349809 := by exact prefixLift 349809
  have htrace : WordTrace (prefixWord ++ tailWord_349809) baseStart_349809 baseEnd_349809 := by
    simpa [prefixWord, tailWord_349809, baseEnd_349809] using wordTrace_append hprefix tailTrace_349809
  have hstable : (prefixWord ++ tailWord_349809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349809).length < 2 ^ (prefixWord ++ tailWord_349809).sum := by decide
  have hdescent : baseEnd_349809 < baseStart_349809 := by decide
  rcases family_descends (prefixWord ++ tailWord_349809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349824 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_349824 : Nat := 118140960795 + 349824 * 2 ^ 59
def prefixEnd_349824 : Nat := 4983230072969 + 3 ^ 40 * 349824 * 2
def baseEnd_349824 : Nat := 119751904319029697127463

theorem tailTrace_349824 : CollatzResearch.WordTrace tailWord_349824 prefixEnd_349824 119751904319029697127463 := by
  unfold tailWord_349824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379564742327434013876263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8506086323103245351835017 6379564742327434013876263)
  ·
    refine ⟨9569347113491151020814395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6379564742327434013876263 9569347113491151020814395)
    ·
      refine ⟨14354020670236726531221593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9569347113491151020814395 14354020670236726531221593)
      ·
        refine ⟨10765515502677544898416195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14354020670236726531221593 10765515502677544898416195)
        ·
          refine ⟨16148273254016317347624293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10765515502677544898416195 16148273254016317347624293)
          ·
            refine ⟨3027801235128059502679555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16148273254016317347624293 3027801235128059502679555)
            ·
              refine ⟨4541701852692089254019333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027801235128059502679555 4541701852692089254019333)
              ·
                refine ⟨851569097379766735128625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4541701852692089254019333 851569097379766735128625)
                ·
                  refine ⟨638676823034825051346469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 851569097379766735128625 638676823034825051346469)
                  ·
                    refine ⟨119751904319029697127463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638676823034825051346469 119751904319029697127463)
                    ·
                      rfl

theorem cell22_349824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_349824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349824 prefixEnd_349824 := by exact prefixLift 349824
  have htrace : WordTrace (prefixWord ++ tailWord_349824) baseStart_349824 baseEnd_349824 := by
    simpa [prefixWord, tailWord_349824, baseEnd_349824] using wordTrace_append hprefix tailTrace_349824
  have hstable : (prefixWord ++ tailWord_349824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349824).length < 2 ^ (prefixWord ++ tailWord_349824).sum := by decide
  have hdescent : baseEnd_349824 < baseStart_349824 := by decide
  rcases family_descends (prefixWord ++ tailWord_349824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349828 : List Nat := [2, 3, 2, 1, 4, 1, 1, 4, 4]
def baseStart_349828 : Nat := 118140960795 + 349828 * 2 ^ 59
def prefixEnd_349828 : Nat := 4983230072969 + 3 ^ 40 * 349828 * 2
def baseEnd_349828 : Nat := 39917757866925006675817

theorem tailTrace_349828 : CollatzResearch.WordTrace tailWord_349828 prefixEnd_349828 39917757866925006675817 := by
  unfold tailWord_349828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379637688320188355449069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8506183584426917807265425 6379637688320188355449069)
  ·
    refine ⟨2392364133120070633293401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6379637688320188355449069 2392364133120070633293401)
    ·
      refine ⟨1794273099840052974970051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2392364133120070633293401 1794273099840052974970051)
      ·
        refine ⟨2691409649760079462455077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794273099840052974970051 2691409649760079462455077)
        ·
          refine ⟨504639309330014899210327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2691409649760079462455077 504639309330014899210327)
          ·
            refine ⟨756958963995022348815491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504639309330014899210327 756958963995022348815491)
            ·
              refine ⟨1135438445992533523223237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756958963995022348815491 1135438445992533523223237)
              ·
                refine ⟨212894708623600035604357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1135438445992533523223237 212894708623600035604357)
                ·
                  refine ⟨39917757866925006675817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212894708623600035604357 39917757866925006675817)
                  ·
                    rfl

theorem cell22_349828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_349828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349828 prefixEnd_349828 := by exact prefixLift 349828
  have htrace : WordTrace (prefixWord ++ tailWord_349828) baseStart_349828 baseEnd_349828 := by
    simpa [prefixWord, tailWord_349828, baseEnd_349828] using wordTrace_append hprefix tailTrace_349828
  have hstable : (prefixWord ++ tailWord_349828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349828).length < 2 ^ (prefixWord ++ tailWord_349828).sum := by decide
  have hdescent : baseEnd_349828 < baseStart_349828 := by decide
  rcases family_descends (prefixWord ++ tailWord_349828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349856 : List Nat := [2, 1, 1, 4, 3, 2, 3, 6]
def baseStart_349856 : Nat := 118140960795 + 349856 * 2 ^ 59
def prefixEnd_349856 : Nat := 4983230072969 + 3 ^ 40 * 349856 * 2
def baseEnd_349856 : Nat := 13306984285888031147485

theorem tailTrace_349856 : CollatzResearch.WordTrace tailWord_349856 prefixEnd_349856 13306984285888031147485 := by
  unfold tailWord_349856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6380148310269468746458711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8506864413692624995278281 6380148310269468746458711)
  ·
    refine ⟨9570222465404203119688067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6380148310269468746458711 9570222465404203119688067)
    ·
      refine ⟨14355333698106304679532101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9570222465404203119688067 14355333698106304679532101)
      ·
        refine ⟨2691625068394932127412269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14355333698106304679532101 2691625068394932127412269)
        ·
          refine ⟨1009359400648099547779601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2691625068394932127412269 1009359400648099547779601)
          ·
            refine ⟨757019550486074660834701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1009359400648099547779601 757019550486074660834701)
            ·
              refine ⟨283882331432277997813013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 757019550486074660834701 283882331432277997813013)
              ·
                refine ⟨13306984285888031147485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 283882331432277997813013 13306984285888031147485)
                ·
                  rfl

theorem cell22_349856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 6].length) (baseStart_349856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349856 prefixEnd_349856 := by exact prefixLift 349856
  have htrace : WordTrace (prefixWord ++ tailWord_349856) baseStart_349856 baseEnd_349856 := by
    simpa [prefixWord, tailWord_349856, baseEnd_349856] using wordTrace_append hprefix tailTrace_349856
  have hstable : (prefixWord ++ tailWord_349856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349856).length < 2 ^ (prefixWord ++ tailWord_349856).sum := by decide
  have hdescent : baseEnd_349856 < baseStart_349856 := by decide
  rcases family_descends (prefixWord ++ tailWord_349856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349858 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_349858 : Nat := 118140960795 + 349858 * 2 ^ 59
def prefixEnd_349858 : Nat := 4983230072969 + 3 ^ 40 * 349858 * 2
def baseEnd_349858 : Nat := 119763543213864941777359

theorem tailTrace_349858 : CollatzResearch.WordTrace tailWord_349858 prefixEnd_349858 119763543213864941777359 := by
  unfold tailWord_349858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190092391632922958622557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8506913044354461222993485 3190092391632922958622557)
  ·
    refine ⟨1196284646862346109483459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3190092391632922958622557 1196284646862346109483459)
    ·
      refine ⟨1794426970293519164225189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196284646862346109483459 1794426970293519164225189)
      ·
        refine ⟨336455056930034843292223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1794426970293519164225189 336455056930034843292223)
        ·
          refine ⟨504682585395052264938335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336455056930034843292223 504682585395052264938335)
          ·
            refine ⟨757023878092578397407503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504682585395052264938335 757023878092578397407503)
            ·
              refine ⟨1135535817138867596111255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757023878092578397407503 1135535817138867596111255)
              ·
                refine ⟨1703303725708301394166883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135535817138867596111255 1703303725708301394166883)
                ·
                  refine ⟨2554955588562452091250325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703303725708301394166883 2554955588562452091250325)
                  ·
                    refine ⟨119763543213864941777359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2554955588562452091250325 119763543213864941777359)
                    ·
                      rfl

theorem cell22_349858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_349858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349858 prefixEnd_349858 := by exact prefixLift 349858
  have htrace : WordTrace (prefixWord ++ tailWord_349858) baseStart_349858 baseEnd_349858 := by
    simpa [prefixWord, tailWord_349858, baseEnd_349858] using wordTrace_append hprefix tailTrace_349858
  have hstable : (prefixWord ++ tailWord_349858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349858).length < 2 ^ (prefixWord ++ tailWord_349858).sum := by decide
  have hdescent : baseEnd_349858 < baseStart_349858 := by decide
  rcases family_descends (prefixWord ++ tailWord_349858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349864 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 1, 4]
def baseStart_349864 : Nat := 118140960795 + 349864 * 2 ^ 59
def prefixEnd_349864 : Nat := 4983230072969 + 3 ^ 40 * 349864 * 2
def baseEnd_349864 : Nat := 119765597136482926127341

theorem tailTrace_349864 : CollatzResearch.WordTrace tailWord_349864 prefixEnd_349864 119765597136482926127341 := by
  unfold tailWord_349864
  simp only [CollatzResearch.WordTrace]
  refine ⟨6380294202254977429604323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8507058936339969906139097 6380294202254977429604323)
  ·
    refine ⟨9570441303382466144406485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6380294202254977429604323 9570441303382466144406485)
    ·
      refine ⟨224307218048026550259527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9570441303382466144406485 224307218048026550259527)
      ·
        refine ⟨336460827072039825389291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224307218048026550259527 336460827072039825389291)
        ·
          refine ⟨504691240608059738083937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336460827072039825389291 504691240608059738083937)
          ·
            refine ⟨378518430456044803562953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504691240608059738083937 378518430456044803562953)
            ·
              refine ⟨283888822842033602672215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378518430456044803562953 283888822842033602672215)
              ·
                refine ⟨425833234263050404008323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283888822842033602672215 425833234263050404008323)
                ·
                  refine ⟨638749851394575606012485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425833234263050404008323 638749851394575606012485)
                  ·
                    refine ⟨119765597136482926127341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638749851394575606012485 119765597136482926127341)
                    ·
                      rfl

theorem cell22_349864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_349864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349864 prefixEnd_349864 := by exact prefixLift 349864
  have htrace : WordTrace (prefixWord ++ tailWord_349864) baseStart_349864 baseEnd_349864 := by
    simpa [prefixWord, tailWord_349864, baseEnd_349864] using wordTrace_append hprefix tailTrace_349864
  have hstable : (prefixWord ++ tailWord_349864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349864).length < 2 ^ (prefixWord ++ tailWord_349864).sum := by decide
  have hdescent : baseEnd_349864 < baseStart_349864 := by decide
  rcases family_descends (prefixWord ++ tailWord_349864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349877 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_349877 : Nat := 118140960795 + 349877 * 2 ^ 59
def prefixEnd_349877 : Nat := 4983230072969 + 3 ^ 40 * 349877 * 2
def baseEnd_349877 : Nat := 119770047302155225552301

theorem tailTrace_349877 : CollatzResearch.WordTrace tailWord_349877 prefixEnd_349877 119770047302155225552301 := by
  unfold tailWord_349877
  simp only [CollatzResearch.WordTrace]
  refine ⟨12761062553462858079431885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8507375035641905386287923 12761062553462858079431885)
  ·
    refine ⟨4785398457548571779786957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12761062553462858079431885 4785398457548571779786957)
    ·
      refine ⟨1794524421580714417420109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4785398457548571779786957 1794524421580714417420109)
      ·
        refine ⟨672946658092767906532541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1794524421580714417420109 672946658092767906532541)
        ·
          refine ⟨252354996784787964949703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672946658092767906532541 252354996784787964949703)
          ·
            refine ⟨378532495177181947424555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252354996784787964949703 378532495177181947424555)
            ·
              refine ⟨567798742765772921136833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378532495177181947424555 567798742765772921136833)
              ·
                refine ⟨425849057074329690852625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567798742765772921136833 425849057074329690852625)
                ·
                  refine ⟨319386792805747268139469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425849057074329690852625 319386792805747268139469)
                  ·
                    refine ⟨119770047302155225552301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319386792805747268139469 119770047302155225552301)
                    ·
                      rfl

theorem cell22_349877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_349877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349877 prefixEnd_349877 := by exact prefixLift 349877
  have htrace : WordTrace (prefixWord ++ tailWord_349877) baseStart_349877 baseEnd_349877 := by
    simpa [prefixWord, tailWord_349877, baseEnd_349877] using wordTrace_append hprefix tailTrace_349877
  have hstable : (prefixWord ++ tailWord_349877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349877).length < 2 ^ (prefixWord ++ tailWord_349877).sum := by decide
  have hdescent : baseEnd_349877 < baseStart_349877 := by decide
  rcases family_descends (prefixWord ++ tailWord_349877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349888 : List Nat := [2, 1, 1, 2, 4, 1, 1, 6, 1, 3]
def baseStart_349888 : Nat := 118140960795 + 349888 * 2 ^ 59
def prefixEnd_349888 : Nat := 4983230072969 + 3 ^ 40 * 349888 * 2
def baseEnd_349888 : Nat := 119773812826954863527267

theorem tailTrace_349888 : CollatzResearch.WordTrace tailWord_349888 prefixEnd_349888 119773812826954863527267 := by
  unfold tailWord_349888
  simp only [CollatzResearch.WordTrace]
  refine ⟨6380731878211503479041159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8507642504282004638721545 6380731878211503479041159)
  ·
    refine ⟨9571097817317255218561739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6380731878211503479041159 9571097817317255218561739)
    ·
      refine ⟨14356646725975882827842609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9571097817317255218561739 14356646725975882827842609)
      ·
        refine ⟨10767485044481912120881957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14356646725975882827842609 10767485044481912120881957)
        ·
          refine ⟨2018903445840358522665367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10767485044481912120881957 2018903445840358522665367)
          ·
            refine ⟨3028355168760537783998051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018903445840358522665367 3028355168760537783998051)
            ·
              refine ⟨4542532753140806675997077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028355168760537783998051 4542532753140806675997077)
              ·
                refine ⟨212931222803475312937363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4542532753140806675997077 212931222803475312937363)
                ·
                  refine ⟨319396834205212969406045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212931222803475312937363 319396834205212969406045)
                  ·
                    refine ⟨119773812826954863527267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319396834205212969406045 119773812826954863527267)
                    ·
                      rfl

theorem cell22_349888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 3].length) (baseStart_349888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349888 prefixEnd_349888 := by exact prefixLift 349888
  have htrace : WordTrace (prefixWord ++ tailWord_349888) baseStart_349888 baseEnd_349888 := by
    simpa [prefixWord, tailWord_349888, baseEnd_349888] using wordTrace_append hprefix tailTrace_349888
  have hstable : (prefixWord ++ tailWord_349888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349888).length < 2 ^ (prefixWord ++ tailWord_349888).sum := by decide
  have hdescent : baseEnd_349888 < baseStart_349888 := by decide
  rcases family_descends (prefixWord ++ tailWord_349888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349894 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_349894 : Nat := 118140960795 + 349894 * 2 ^ 59
def prefixEnd_349894 : Nat := 4983230072969 + 3 ^ 40 * 349894 * 2
def baseEnd_349894 : Nat := 119775866749572847877249

theorem tailTrace_349894 : CollatzResearch.WordTrace tailWord_349894 prefixEnd_349894 119775866749572847877249 := by
  unfold tailWord_349894
  simp only [CollatzResearch.WordTrace]
  refine ⟨398802581075039686962523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8507788396267513321867157 398802581075039686962523)
  ·
    refine ⟨598203871612559530443785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398802581075039686962523 598203871612559530443785)
    ·
      refine ⟨448652903709419647832839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 598203871612559530443785 448652903709419647832839)
      ·
        refine ⟨672979355564129471749259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448652903709419647832839 672979355564129471749259)
        ·
          refine ⟨1009469033346194207623889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672979355564129471749259 1009469033346194207623889)
          ·
            refine ⟨757101775009645655717917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1009469033346194207623889 757101775009645655717917)
            ·
              refine ⟨283913165628617120894219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 757101775009645655717917 283913165628617120894219)
              ·
                refine ⟨425869748442925681341329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283913165628617120894219 425869748442925681341329)
                ·
                  refine ⟨319402311332194261005997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425869748442925681341329 319402311332194261005997)
                  ·
                    refine ⟨119775866749572847877249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319402311332194261005997 119775866749572847877249)
                    ·
                      rfl

theorem cell22_349894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_349894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349894 prefixEnd_349894 := by exact prefixLift 349894
  have htrace : WordTrace (prefixWord ++ tailWord_349894) baseStart_349894 baseEnd_349894 := by
    simpa [prefixWord, tailWord_349894, baseEnd_349894] using wordTrace_append hprefix tailTrace_349894
  have hstable : (prefixWord ++ tailWord_349894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349894).length < 2 ^ (prefixWord ++ tailWord_349894).sum := by decide
  have hdescent : baseEnd_349894 < baseStart_349894 := by decide
  rcases family_descends (prefixWord ++ tailWord_349894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349931 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 1, 4]
def baseStart_349931 : Nat := 118140960795 + 349931 * 2 ^ 59
def prefixEnd_349931 : Nat := 4983230072969 + 3 ^ 40 * 349931 * 2
def baseEnd_349931 : Nat := 119788532605717084702135

theorem tailTrace_349931 : CollatzResearch.WordTrace tailWord_349931 prefixEnd_349931 119788532605717084702135 := by
  unfold tailWord_349931
  simp only [CollatzResearch.WordTrace]
  refine ⟨12763032095267225301897647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8508688063511483534598431 12763032095267225301897647)
  ·
    refine ⟨19144548142900837952846471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12763032095267225301897647 19144548142900837952846471)
    ·
      refine ⟨28716822214351256929269707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19144548142900837952846471 28716822214351256929269707)
      ·
        refine ⟨43075233321526885393904561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28716822214351256929269707 43075233321526885393904561)
        ·
          refine ⟨32306424991145164045428421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43075233321526885393904561 32306424991145164045428421)
          ·
            refine ⟨6057454685839718258517829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32306424991145164045428421 6057454685839718258517829)
            ·
              refine ⟨1135772753594947173472093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6057454685839718258517829 1135772753594947173472093)
              ·
                refine ⟨425914782598105190052035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1135772753594947173472093 425914782598105190052035)
                ·
                  refine ⟨638872173897157785078053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425914782598105190052035 638872173897157785078053)
                  ·
                    refine ⟨119788532605717084702135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638872173897157785078053 119788532605717084702135)
                    ·
                      rfl

theorem cell22_349931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 4].length) (baseStart_349931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349931 prefixEnd_349931 := by exact prefixLift 349931
  have htrace : WordTrace (prefixWord ++ tailWord_349931) baseStart_349931 baseEnd_349931 := by
    simpa [prefixWord, tailWord_349931, baseEnd_349931] using wordTrace_append hprefix tailTrace_349931
  have hstable : (prefixWord ++ tailWord_349931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349931).length < 2 ^ (prefixWord ++ tailWord_349931).sum := by decide
  have hdescent : baseEnd_349931 < baseStart_349931 := by decide
  rcases family_descends (prefixWord ++ tailWord_349931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349944 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_349944 : Nat := 118140960795 + 349944 * 2 ^ 59
def prefixEnd_349944 : Nat := 4983230072969 + 3 ^ 40 * 349944 * 2
def baseEnd_349944 : Nat := 119792982771389384127095

theorem tailTrace_349944 : CollatzResearch.WordTrace tailWord_349944 prefixEnd_349944 119792982771389384127095 := by
  unfold tailWord_349944
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381753122110064261060443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8509004162813419014747257 6381753122110064261060443)
  ·
    refine ⟨9572629683165096391590665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6381753122110064261060443 9572629683165096391590665)
    ·
      refine ⟨7179472262373822293692999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9572629683165096391590665 7179472262373822293692999)
      ·
        refine ⟨10769208393560733440539499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7179472262373822293692999 10769208393560733440539499)
        ·
          refine ⟨16153812590341100160809249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10769208393560733440539499 16153812590341100160809249)
          ·
            refine ⟨12115359442755825120606937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16153812590341100160809249 12115359442755825120606937)
            ·
              refine ⟨9086519582066868840455203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12115359442755825120606937 9086519582066868840455203)
              ·
                refine ⟨13629779373100303260682805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9086519582066868840455203 13629779373100303260682805)
                ·
                  refine ⟨1277791816228153430689013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13629779373100303260682805 1277791816228153430689013)
                  ·
                    refine ⟨119792982771389384127095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1277791816228153430689013 119792982771389384127095)
                    ·
                      rfl

theorem cell22_349944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_349944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349944 prefixEnd_349944 := by exact prefixLift 349944
  have htrace : WordTrace (prefixWord ++ tailWord_349944) baseStart_349944 baseEnd_349944 := by
    simpa [prefixWord, tailWord_349944, baseEnd_349944] using wordTrace_append hprefix tailTrace_349944
  have hstable : (prefixWord ++ tailWord_349944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349944).length < 2 ^ (prefixWord ++ tailWord_349944).sum := by decide
  have hdescent : baseEnd_349944 < baseStart_349944 := by decide
  rcases family_descends (prefixWord ++ tailWord_349944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349976 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_349976 : Nat := 118140960795 + 349976 * 2 ^ 59
def prefixEnd_349976 : Nat := 4983230072969 + 3 ^ 40 * 349976 * 2
def baseEnd_349976 : Nat := 119803937025351967326997

theorem tailTrace_349976 : CollatzResearch.WordTrace tailWord_349976 prefixEnd_349976 119803937025351967326997 := by
  unfold tailWord_349976
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382336690052098993642891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8509782253402798658190521 6382336690052098993642891)
  ·
    refine ⟨9573505035078148490464337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6382336690052098993642891 9573505035078148490464337)
    ·
      refine ⟨7180128776308611367848253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9573505035078148490464337 7180128776308611367848253)
      ·
        refine ⟨2692548291115729262943095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7180128776308611367848253 2692548291115729262943095)
        ·
          refine ⟨4038822436673593894414643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692548291115729262943095 4038822436673593894414643)
          ·
            refine ⟨6058233655010390841621965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038822436673593894414643 6058233655010390841621965)
            ·
              refine ⟨2271837620628896565608237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6058233655010390841621965 2271837620628896565608237)
              ·
                refine ⟨851939107735836212103089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2271837620628896565608237 851939107735836212103089)
                ·
                  refine ⟨638954330801877159077317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 851939107735836212103089 638954330801877159077317)
                  ·
                    refine ⟨119803937025351967326997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638954330801877159077317 119803937025351967326997)
                    ·
                      rfl

theorem cell22_349976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_349976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349976 prefixEnd_349976 := by exact prefixLift 349976
  have htrace : WordTrace (prefixWord ++ tailWord_349976) baseStart_349976 baseEnd_349976 := by
    simpa [prefixWord, tailWord_349976, baseEnd_349976] using wordTrace_append hprefix tailTrace_349976
  have hstable : (prefixWord ++ tailWord_349976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349976).length < 2 ^ (prefixWord ++ tailWord_349976).sum := by decide
  have hdescent : baseEnd_349976 < baseStart_349976 := by decide
  rcases family_descends (prefixWord ++ tailWord_349976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350083 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 1, 4]
def baseStart_350083 : Nat := 118140960795 + 350083 * 2 ^ 59
def prefixEnd_350083 : Nat := 4983230072969 + 3 ^ 40 * 350083 * 2
def baseEnd_350083 : Nat := 119840565312039354901669

theorem tailTrace_350083 : CollatzResearch.WordTrace tailWord_350083 prefixEnd_350083 119840565312039354901669 := by
  unfold tailWord_350083
  simp only [CollatzResearch.WordTrace]
  refine ⟨12768575990716555261430903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8512383993811036840953935 12768575990716555261430903)
  ·
    refine ⟨19152863986074832892146355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12768575990716555261430903 19152863986074832892146355)
    ·
      refine ⟨28729295979112249338219533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19152863986074832892146355 28729295979112249338219533)
      ·
        refine ⟨10773485992167093501832325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28729295979112249338219533 10773485992167093501832325)
        ·
          refine ⟨2020028623531330031593561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10773485992167093501832325 2020028623531330031593561)
          ·
            refine ⟨1515021467648497523695171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2020028623531330031593561 1515021467648497523695171)
            ·
              refine ⟨2272532201472746285542757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515021467648497523695171 2272532201472746285542757)
              ·
                refine ⟨426099787776139928539267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2272532201472746285542757 426099787776139928539267)
                ·
                  refine ⟨639149681664209892808901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426099787776139928539267 639149681664209892808901)
                  ·
                    refine ⟨119840565312039354901669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 639149681664209892808901 119840565312039354901669)
                    ·
                      rfl

theorem cell22_350083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 4].length) (baseStart_350083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350083 prefixEnd_350083 := by exact prefixLift 350083
  have htrace : WordTrace (prefixWord ++ tailWord_350083) baseStart_350083 baseEnd_350083 := by
    simpa [prefixWord, tailWord_350083, baseEnd_350083] using wordTrace_append hprefix tailTrace_350083
  have hstable : (prefixWord ++ tailWord_350083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350083).length < 2 ^ (prefixWord ++ tailWord_350083).sum := by decide
  have hdescent : baseEnd_350083 < baseStart_350083 := by decide
  rcases family_descends (prefixWord ++ tailWord_350083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350100 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_350100 : Nat := 118140960795 + 350100 * 2 ^ 59
def prefixEnd_350100 : Nat := 4983230072969 + 3 ^ 40 * 350100 * 2
def baseEnd_350100 : Nat := 119846384759456977226617

theorem tailTrace_350100 : CollatzResearch.WordTrace tailWord_350100 prefixEnd_350100 119846384759456977226617 := by
  unfold tailWord_350100
  simp only [CollatzResearch.WordTrace]
  refine ⟨6384598015827483582399877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8512797354436644776533169 6384598015827483582399877)
  ·
    refine ⟨1197112127967653171699977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6384598015827483582399877 1197112127967653171699977)
    ·
      refine ⟨897834095975739878774983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1197112127967653171699977 897834095975739878774983)
      ·
        refine ⟨1346751143963609818162475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897834095975739878774983 1346751143963609818162475)
        ·
          refine ⟨2020126715945414727243713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346751143963609818162475 2020126715945414727243713)
          ·
            refine ⟨1515095036959061045432785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2020126715945414727243713 1515095036959061045432785)
            ·
              refine ⟨1136321277719295784074589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1515095036959061045432785 1136321277719295784074589)
              ·
                refine ⟨426120479144735919027971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1136321277719295784074589 426120479144735919027971)
                ·
                  refine ⟨639180718717103878541957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426120479144735919027971 639180718717103878541957)
                  ·
                    refine ⟨119846384759456977226617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 639180718717103878541957 119846384759456977226617)
                    ·
                      rfl

theorem cell22_350100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_350100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350100 prefixEnd_350100 := by exact prefixLift 350100
  have htrace : WordTrace (prefixWord ++ tailWord_350100) baseStart_350100 baseEnd_350100 := by
    simpa [prefixWord, tailWord_350100, baseEnd_350100] using wordTrace_append hprefix tailTrace_350100
  have hstable : (prefixWord ++ tailWord_350100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350100).length < 2 ^ (prefixWord ++ tailWord_350100).sum := by decide
  have hdescent : baseEnd_350100 < baseStart_350100 := by decide
  rcases family_descends (prefixWord ++ tailWord_350100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350166 : List Nat := [5, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_350166 : Nat := 118140960795 + 350166 * 2 ^ 59
def prefixEnd_350166 : Nat := 4983230072969 + 3 ^ 40 * 350166 * 2
def baseEnd_350166 : Nat := 39956325969418268358805

theorem tailTrace_350166 : CollatzResearch.WordTrace tailWord_350166 prefixEnd_350166 39956325969418268358805 := by
  unfold tailWord_350166
  simp only [CollatzResearch.WordTrace]
  refine ⟨798225203088491277293897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8514402166277240291134901 798225203088491277293897)
  ·
    refine ⟨598668902316368457970423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 798225203088491277293897 598668902316368457970423)
    ·
      refine ⟨898003353474552686955635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598668902316368457970423 898003353474552686955635)
      ·
        refine ⟨1347005030211829030433453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898003353474552686955635 1347005030211829030433453)
        ·
          refine ⟨505126886329435886412545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1347005030211829030433453 505126886329435886412545)
          ·
            refine ⟨378845164747076914809409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505126886329435886412545 378845164747076914809409)
            ·
              refine ⟨284133873560307686107057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378845164747076914809409 284133873560307686107057)
              ·
                refine ⟨213100405170230764580293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284133873560307686107057 213100405170230764580293)
                ·
                  refine ⟨39956325969418268358805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213100405170230764580293 39956325969418268358805)
                  ·
                    rfl

theorem cell22_350166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_350166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350166 prefixEnd_350166 := by exact prefixLift 350166
  have htrace : WordTrace (prefixWord ++ tailWord_350166) baseStart_350166 baseEnd_350166 := by
    simpa [prefixWord, tailWord_350166, baseEnd_350166] using wordTrace_append hprefix tailTrace_350166
  have hstable : (prefixWord ++ tailWord_350166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350166).length < 2 ^ (prefixWord ++ tailWord_350166).sum := by decide
  have hdescent : baseEnd_350166 < baseStart_350166 := by decide
  rcases family_descends (prefixWord ++ tailWord_350166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350250 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_350250 : Nat := 118140960795 + 350250 * 2 ^ 59
def prefixEnd_350250 : Nat := 4983230072969 + 3 ^ 40 * 350250 * 2
def baseEnd_350250 : Nat := 39965910941635528658719

theorem tailTrace_350250 : CollatzResearch.WordTrace tailWord_350250 prefixEnd_350250 39965910941635528658719 := by
  unfold tailWord_350250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3193666745277885695690051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8516444654074361855173469 3193666745277885695690051)
  ·
    refine ⟨4790500117916828543535077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3193666745277885695690051 4790500117916828543535077)
    ·
      refine ⟨898218772109405351912827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4790500117916828543535077 898218772109405351912827)
      ·
        refine ⟨1347328158164108027869241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898218772109405351912827 1347328158164108027869241)
        ·
          refine ⟨1010496118623081020901931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1347328158164108027869241 1010496118623081020901931)
          ·
            refine ⟨1515744177934621531352897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010496118623081020901931 1515744177934621531352897)
            ·
              refine ⟨1136808133450966148514673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1515744177934621531352897 1136808133450966148514673)
              ·
                refine ⟨852606100088224611386005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136808133450966148514673 852606100088224611386005)
                ·
                  refine ⟨39965910941635528658719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 852606100088224611386005 39965910941635528658719)
                  ·
                    rfl

theorem cell22_350250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_350250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350250 prefixEnd_350250 := by exact prefixLift 350250
  have htrace : WordTrace (prefixWord ++ tailWord_350250) baseStart_350250 baseEnd_350250 := by
    simpa [prefixWord, tailWord_350250, baseEnd_350250] using wordTrace_append hprefix tailTrace_350250
  have hstable : (prefixWord ++ tailWord_350250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350250).length < 2 ^ (prefixWord ++ tailWord_350250).sum := by decide
  have hdescent : baseEnd_350250 < baseStart_350250 := by decide
  rcases family_descends (prefixWord ++ tailWord_350250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350263 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 1, 6]
def baseStart_350263 : Nat := 118140960795 + 350263 * 2 ^ 59
def prefixEnd_350263 : Nat := 4983230072969 + 3 ^ 40 * 350263 * 2
def baseEnd_350263 : Nat := 119902182990578885401117

theorem tailTrace_350263 : CollatzResearch.WordTrace tailWord_350263 prefixEnd_350263 119902182990578885401117 := by
  unfold tailWord_350263
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775141130064446002983443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8516760753376297335322295 12775141130064446002983443)
  ·
    refine ⟨19162711695096669004475165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12775141130064446002983443 19162711695096669004475165)
    ·
      refine ⟨7186016885661250876678187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19162711695096669004475165 7186016885661250876678187)
      ·
        refine ⟨10779025328491876315017281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7186016885661250876678187 10779025328491876315017281)
        ·
          refine ⟨8084268996368907236262961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10779025328491876315017281 8084268996368907236262961)
          ·
            refine ⟨6063201747276680427197221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8084268996368907236262961 6063201747276680427197221)
            ·
              refine ⟨1136850327614377580099479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6063201747276680427197221 1136850327614377580099479)
              ·
                refine ⟨1705275491421566370149219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136850327614377580099479 1705275491421566370149219)
                ·
                  refine ⟨2557913237132349555223829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705275491421566370149219 2557913237132349555223829)
                  ·
                    refine ⟨119902182990578885401117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2557913237132349555223829 119902182990578885401117)
                    ·
                      rfl

theorem cell22_350263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_350263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350263 prefixEnd_350263 := by exact prefixLift 350263
  have htrace : WordTrace (prefixWord ++ tailWord_350263) baseStart_350263 baseEnd_350263 := by
    simpa [prefixWord, tailWord_350263, baseEnd_350263] using wordTrace_append hprefix tailTrace_350263
  have hstable : (prefixWord ++ tailWord_350263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350263).length < 2 ^ (prefixWord ++ tailWord_350263).sum := by decide
  have hdescent : baseEnd_350263 < baseStart_350263 := by decide
  rcases family_descends (prefixWord ++ tailWord_350263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350378 : List Nat := [3, 1, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_350378 : Nat := 118140960795 + 350378 * 2 ^ 59
def prefixEnd_350378 : Nat := 4983230072969 + 3 ^ 40 * 350378 * 2
def baseEnd_350378 : Nat := 119941549840756918775765

theorem tailTrace_350378 : CollatzResearch.WordTrace tailWord_350378 prefixEnd_350378 119941549840756918775765 := by
  unfold tailWord_350378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194833881161955160854947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8519557016431880428946525 3194833881161955160854947)
  ·
    refine ⟨4792250821742932741282421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3194833881161955160854947 4792250821742932741282421)
    ·
      refine ⟨449273514538399944495227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4792250821742932741282421 449273514538399944495227)
      ·
        refine ⟨673910271807599916742841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449273514538399944495227 673910271807599916742841)
        ·
          refine ⟨505432703855699937557131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673910271807599916742841 505432703855699937557131)
          ·
            refine ⟨758149055783549906335697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505432703855699937557131 758149055783549906335697)
            ·
              refine ⟨568611791837662429751773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 758149055783549906335697 568611791837662429751773)
              ·
                refine ⟨213229421939123411156915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 568611791837662429751773 213229421939123411156915)
                ·
                  refine ⟨319844132908685116735373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213229421939123411156915 319844132908685116735373)
                  ·
                    refine ⟨119941549840756918775765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319844132908685116735373 119941549840756918775765)
                    ·
                      rfl

theorem cell22_350378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_350378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350378 prefixEnd_350378 := by exact prefixLift 350378
  have htrace : WordTrace (prefixWord ++ tailWord_350378) baseStart_350378 baseEnd_350378 := by
    simpa [prefixWord, tailWord_350378, baseEnd_350378] using wordTrace_append hprefix tailTrace_350378
  have hstable : (prefixWord ++ tailWord_350378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350378).length < 2 ^ (prefixWord ++ tailWord_350378).sum := by decide
  have hdescent : baseEnd_350378 < baseStart_350378 := by decide
  rcases family_descends (prefixWord ++ tailWord_350378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350417 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 2, 3]
def baseStart_350417 : Nat := 118140960795 + 350417 * 2 ^ 59
def prefixEnd_350417 : Nat := 4983230072969 + 3 ^ 40 * 350417 * 2
def baseEnd_350417 : Nat := 119954900337773817050645

theorem tailTrace_350417 : CollatzResearch.WordTrace tailWord_350417 prefixEnd_350417 119954900337773817050645 := by
  unfold tailWord_350417
  simp only [CollatzResearch.WordTrace]
  refine ⟨12780757971506530304089505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8520505314337686869393003 12780757971506530304089505)
  ·
    refine ⟨9585568478629897728067129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12780757971506530304089505 9585568478629897728067129)
    ·
      refine ⟨7189176358972423296050347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9585568478629897728067129 7189176358972423296050347)
      ·
        refine ⟨10783764538458634944075521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189176358972423296050347 10783764538458634944075521)
        ·
          refine ⟨8087823403843976208056641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10783764538458634944075521 8087823403843976208056641)
          ·
            refine ⟨6065867552882982156042481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8087823403843976208056641 6065867552882982156042481)
            ·
              refine ⟨4549400664662236617031861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6065867552882982156042481 4549400664662236617031861)
              ·
                refine ⟨426506312312084682846737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4549400664662236617031861 426506312312084682846737)
                ·
                  refine ⟨319879734234063512135053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426506312312084682846737 319879734234063512135053)
                  ·
                    refine ⟨119954900337773817050645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319879734234063512135053 119954900337773817050645)
                    ·
                      rfl

theorem cell22_350417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_350417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350417 prefixEnd_350417 := by exact prefixLift 350417
  have htrace : WordTrace (prefixWord ++ tailWord_350417) baseStart_350417 baseEnd_350417 := by
    simpa [prefixWord, tailWord_350417, baseEnd_350417] using wordTrace_append hprefix tailTrace_350417
  have hstable : (prefixWord ++ tailWord_350417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350417).length < 2 ^ (prefixWord ++ tailWord_350417).sum := by decide
  have hdescent : baseEnd_350417 < baseStart_350417 := by decide
  rcases family_descends (prefixWord ++ tailWord_350417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350468 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_350468 : Nat := 118140960795 + 350468 * 2 ^ 59
def prefixEnd_350468 : Nat := 4983230072969 + 3 ^ 40 * 350468 * 2
def baseEnd_350468 : Nat := 119972358680026684025489

theorem tailTrace_350468 : CollatzResearch.WordTrace tailWord_350468 prefixEnd_350468 119972358680026684025489 := by
  unfold tailWord_350468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391309047160883007098029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8521745396214510676130705 6391309047160883007098029)
  ·
    refine ⟨2396740892685331127661761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6391309047160883007098029 2396740892685331127661761)
    ·
      refine ⟨1797555669513998345746321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2396740892685331127661761 1797555669513998345746321)
      ·
        refine ⟨1348166752135498759309741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1797555669513998345746321 1348166752135498759309741)
        ·
          refine ⟨505562532050812034741153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1348166752135498759309741 505562532050812034741153)
          ·
            refine ⟨379171899038109026055865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505562532050812034741153 379171899038109026055865)
            ·
              refine ⟨284378924278581769541899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379171899038109026055865 284378924278581769541899)
              ·
                refine ⟨426568386417872654312849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284378924278581769541899 426568386417872654312849)
                ·
                  refine ⟨319926289813404490734637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426568386417872654312849 319926289813404490734637)
                  ·
                    refine ⟨119972358680026684025489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319926289813404490734637 119972358680026684025489)
                    ·
                      rfl

theorem cell22_350468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_350468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350468 prefixEnd_350468 := by exact prefixLift 350468
  have htrace : WordTrace (prefixWord ++ tailWord_350468) baseStart_350468 baseEnd_350468 := by
    simpa [prefixWord, tailWord_350468, baseEnd_350468] using wordTrace_append hprefix tailTrace_350468
  have hstable : (prefixWord ++ tailWord_350468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350468).length < 2 ^ (prefixWord ++ tailWord_350468).sum := by decide
  have hdescent : baseEnd_350468 < baseStart_350468 := by decide
  rcases family_descends (prefixWord ++ tailWord_350468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350522 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_350522 : Nat := 118140960795 + 350522 * 2 ^ 59
def prefixEnd_350522 : Nat := 4983230072969 + 3 ^ 40 * 350522 * 2
def baseEnd_350522 : Nat := 119990843983588543175323

theorem tailTrace_350522 : CollatzResearch.WordTrace tailWord_350522 prefixEnd_350522 119990843983588543175323 := by
  unfold tailWord_350522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196146909031533309165455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8523058424084088824441213 3196146909031533309165455)
  ·
    refine ⟨4794220363547299963748183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3196146909031533309165455 4794220363547299963748183)
    ·
      refine ⟨7191330545320949945622275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4794220363547299963748183 7191330545320949945622275)
      ·
        refine ⟨10786995817981424918433413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7191330545320949945622275 10786995817981424918433413)
        ·
          refine ⟨2022561715871517172206265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10786995817981424918433413 2022561715871517172206265)
          ·
            refine ⟨1516921286903637879154699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022561715871517172206265 1516921286903637879154699)
            ·
              refine ⟨2275381930355456818732049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516921286903637879154699 2275381930355456818732049)
              ·
                refine ⟨1706536447766592614049037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275381930355456818732049 1706536447766592614049037)
                ·
                  refine ⟨639951167912472230268389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1706536447766592614049037 639951167912472230268389)
                  ·
                    refine ⟨119990843983588543175323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 639951167912472230268389 119990843983588543175323)
                    ·
                      rfl

theorem cell22_350522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_350522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350522 prefixEnd_350522 := by exact prefixLift 350522
  have htrace : WordTrace (prefixWord ++ tailWord_350522) baseStart_350522 baseEnd_350522 := by
    simpa [prefixWord, tailWord_350522, baseEnd_350522] using wordTrace_append hprefix tailTrace_350522
  have hstable : (prefixWord ++ tailWord_350522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350522).length < 2 ^ (prefixWord ++ tailWord_350522).sum := by decide
  have hdescent : baseEnd_350522 < baseStart_350522 := by decide
  rcases family_descends (prefixWord ++ tailWord_350522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350627 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 7]
def baseStart_350627 : Nat := 118140960795 + 350627 * 2 ^ 59
def prefixEnd_350627 : Nat := 4983230072969 + 3 ^ 40 * 350627 * 2
def baseEnd_350627 : Nat := 40008929209801089766667

theorem tailTrace_350627 : CollatzResearch.WordTrace tailWord_350627 prefixEnd_350627 40008929209801089766667 := by
  unfold tailWord_350627
  simp only [CollatzResearch.WordTrace]
  refine ⟨12788417300745736169234135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8525611533830490779489423 12788417300745736169234135)
  ·
    refine ⟨19182625951118604253851203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12788417300745736169234135 19182625951118604253851203)
    ·
      refine ⟨28773938926677906380776805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19182625951118604253851203 28773938926677906380776805)
      ·
        refine ⟨5395113548752107446395651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28773938926677906380776805 5395113548752107446395651)
        ·
          refine ⟨8092670323128161169593477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5395113548752107446395651 8092670323128161169593477)
          ·
            refine ⟨1517375685586530219298777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8092670323128161169593477 1517375685586530219298777)
            ·
              refine ⟨1138031764189897664474083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517375685586530219298777 1138031764189897664474083)
              ·
                refine ⟨1707047646284846496711125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138031764189897664474083 1707047646284846496711125)
                ·
                  refine ⟨40008929209801089766667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1707047646284846496711125 40008929209801089766667)
                  ·
                    rfl

theorem cell22_350627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 7].length) (baseStart_350627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350627 prefixEnd_350627 := by exact prefixLift 350627
  have htrace : WordTrace (prefixWord ++ tailWord_350627) baseStart_350627 baseEnd_350627 := by
    simpa [prefixWord, tailWord_350627, baseEnd_350627] using wordTrace_append hprefix tailTrace_350627
  have hstable : (prefixWord ++ tailWord_350627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350627).length < 2 ^ (prefixWord ++ tailWord_350627).sum := by decide
  have hdescent : baseEnd_350627 < baseStart_350627 := by decide
  rcases family_descends (prefixWord ++ tailWord_350627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350631 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 3, 3]
def baseStart_350631 : Nat := 118140960795 + 350631 * 2 ^ 59
def prefixEnd_350631 : Nat := 4983230072969 + 3 ^ 40 * 350631 * 2
def baseEnd_350631 : Nat := 120028156911148592199989

theorem tailTrace_350631 : CollatzResearch.WordTrace tailWord_350631 prefixEnd_350631 120028156911148592199989 := by
  unfold tailWord_350631
  simp only [CollatzResearch.WordTrace]
  refine ⟨12788563192731244852379747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8525708795154163234919831 12788563192731244852379747)
  ·
    refine ⟨19182844789096867278569621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12788563192731244852379747 19182844789096867278569621)
    ·
      refine ⟨899195849488915653682951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19182844789096867278569621 899195849488915653682951)
      ·
        refine ⟨1348793774233373480524427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899195849488915653682951 1348793774233373480524427)
        ·
          refine ⟨2023190661350060220786641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348793774233373480524427 2023190661350060220786641)
          ·
            refine ⟨1517392996012545165589981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2023190661350060220786641 1517392996012545165589981)
            ·
              refine ⟨569022373504704437096243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1517392996012545165589981 569022373504704437096243)
              ·
                refine ⟨853533560257056655644365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569022373504704437096243 853533560257056655644365)
                ·
                  refine ⟨320075085096396245866637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 853533560257056655644365 320075085096396245866637)
                  ·
                    refine ⟨120028156911148592199989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320075085096396245866637 120028156911148592199989)
                    ·
                      rfl

theorem cell22_350631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_350631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350631 prefixEnd_350631 := by exact prefixLift 350631
  have htrace : WordTrace (prefixWord ++ tailWord_350631) baseStart_350631 baseEnd_350631 := by
    simpa [prefixWord, tailWord_350631, baseEnd_350631] using wordTrace_append hprefix tailTrace_350631
  have hstable : (prefixWord ++ tailWord_350631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350631).length < 2 ^ (prefixWord ++ tailWord_350631).sum := by decide
  have hdescent : baseEnd_350631 < baseStart_350631 := by decide
  rcases family_descends (prefixWord ++ tailWord_350631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350637 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_350637 : Nat := 118140960795 + 350637 * 2 ^ 59
def prefixEnd_350637 : Nat := 4983230072969 + 3 ^ 40 * 350637 * 2
def baseEnd_350637 : Nat := 120030210833766576549971

theorem tailTrace_350637 : CollatzResearch.WordTrace tailWord_350637 prefixEnd_350637 120030210833766576549971 := by
  unfold tailWord_350637
  simp only [CollatzResearch.WordTrace]
  refine ⟨12788782030709507877098165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8525854687139671918065443 12788782030709507877098165)
  ·
    refine ⟨1198948315379016363477953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12788782030709507877098165 1198948315379016363477953)
    ·
      refine ⟨899211236534262272608465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1198948315379016363477953 899211236534262272608465)
      ·
        refine ⟨674408427400696704456349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 899211236534262272608465 674408427400696704456349)
        ·
          refine ⟨252903160275261264171131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 674408427400696704456349 252903160275261264171131)
          ·
            refine ⟨379354740412891896256697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252903160275261264171131 379354740412891896256697)
            ·
              refine ⟨284516055309668922192523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379354740412891896256697 284516055309668922192523)
              ·
                refine ⟨426774082964503383288785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284516055309668922192523 426774082964503383288785)
                ·
                  refine ⟨320080562223377537466589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426774082964503383288785 320080562223377537466589)
                  ·
                    refine ⟨120030210833766576549971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320080562223377537466589 120030210833766576549971)
                    ·
                      rfl

theorem cell22_350637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_350637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350637 prefixEnd_350637 := by exact prefixLift 350637
  have htrace : WordTrace (prefixWord ++ tailWord_350637) baseStart_350637 baseEnd_350637 := by
    simpa [prefixWord, tailWord_350637, baseEnd_350637] using wordTrace_append hprefix tailTrace_350637
  have hstable : (prefixWord ++ tailWord_350637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350637).length < 2 ^ (prefixWord ++ tailWord_350637).sum := by decide
  have hdescent : baseEnd_350637 < baseStart_350637 := by decide
  rcases family_descends (prefixWord ++ tailWord_350637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350642 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_350642 : Nat := 118140960795 + 350642 * 2 ^ 59
def prefixEnd_350642 : Nat := 4983230072969 + 3 ^ 40 * 350642 * 2
def baseEnd_350642 : Nat := 120031922435948230174955

theorem tailTrace_350642 : CollatzResearch.WordTrace tailWord_350642 prefixEnd_350642 120031922435948230174955 := by
  unfold tailWord_350642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197241098922848432757545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8525976263794262487353453 3197241098922848432757545)
  ·
    refine ⟨2397930824192136324568159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3197241098922848432757545 2397930824192136324568159)
    ·
      refine ⟨3596896236288204486852239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397930824192136324568159 3596896236288204486852239)
      ·
        refine ⟨5395344354432306730278359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596896236288204486852239 5395344354432306730278359)
        ·
          refine ⟨8093016531648460095417539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5395344354432306730278359 8093016531648460095417539)
          ·
            refine ⟨12139524797472690143126309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093016531648460095417539 12139524797472690143126309)
            ·
              refine ⟨2276160899526129401836183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12139524797472690143126309 2276160899526129401836183)
              ·
                refine ⟨3414241349289194102754275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276160899526129401836183 3414241349289194102754275)
                ·
                  refine ⟨5121362023933791154131413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414241349289194102754275 5121362023933791154131413)
                  ·
                    refine ⟨120031922435948230174955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5121362023933791154131413 120031922435948230174955)
                    ·
                      rfl

theorem cell22_350642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_350642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350642 prefixEnd_350642 := by exact prefixLift 350642
  have htrace : WordTrace (prefixWord ++ tailWord_350642) baseStart_350642 baseEnd_350642 := by
    simpa [prefixWord, tailWord_350642, baseEnd_350642] using wordTrace_append hprefix tailTrace_350642
  have hstable : (prefixWord ++ tailWord_350642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350642).length < 2 ^ (prefixWord ++ tailWord_350642).sum := by decide
  have hdescent : baseEnd_350642 < baseStart_350642 := by decide
  rcases family_descends (prefixWord ++ tailWord_350642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350704 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_350704 : Nat := 118140960795 + 350704 * 2 ^ 59
def prefixEnd_350704 : Nat := 4983230072969 + 3 ^ 40 * 350704 * 2
def baseEnd_350704 : Nat := 120053146303000735124765

theorem tailTrace_350704 : CollatzResearch.WordTrace tailWord_350704 prefixEnd_350704 120053146303000735124765 := by
  unfold tailWord_350704
  simp only [CollatzResearch.WordTrace]
  refine ⟨6395612860733389159893583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8527483814311185546524777 6395612860733389159893583)
  ·
    refine ⟨9593419291100083739840375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6395612860733389159893583 9593419291100083739840375)
    ·
      refine ⟨14390128936650125609760563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9593419291100083739840375 14390128936650125609760563)
      ·
        refine ⟨21585193404975188414640845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14390128936650125609760563 21585193404975188414640845)
        ·
          refine ⟨8094447526865695655490317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21585193404975188414640845 8094447526865695655490317)
          ·
            refine ⟨3035417822574635870808869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8094447526865695655490317 3035417822574635870808869)
            ·
              refine ⟨569140841732744225776663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3035417822574635870808869 569140841732744225776663)
              ·
                refine ⟨853711262599116338664995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569140841732744225776663 853711262599116338664995)
                ·
                  refine ⟨1280566893898674507997493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853711262599116338664995 1280566893898674507997493)
                  ·
                    refine ⟨120053146303000735124765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1280566893898674507997493 120053146303000735124765)
                    ·
                      rfl

theorem cell22_350704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_350704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350704 prefixEnd_350704 := by exact prefixLift 350704
  have htrace : WordTrace (prefixWord ++ tailWord_350704) baseStart_350704 baseEnd_350704 := by
    simpa [prefixWord, tailWord_350704, baseEnd_350704] using wordTrace_append hprefix tailTrace_350704
  have hstable : (prefixWord ++ tailWord_350704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350704).length < 2 ^ (prefixWord ++ tailWord_350704).sum := by decide
  have hdescent : baseEnd_350704 < baseStart_350704 := by decide
  rcases family_descends (prefixWord ++ tailWord_350704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350706 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_350706 : Nat := 118140960795 + 350706 * 2 ^ 59
def prefixEnd_350706 : Nat := 4983230072969 + 3 ^ 40 * 350706 * 2
def baseEnd_350706 : Nat := 40017943647957798858253

theorem tailTrace_350706 : CollatzResearch.WordTrace tailWord_350706 prefixEnd_350706 40017943647957798858253 := by
  unfold tailWord_350706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197824666864883165339993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8527532444973021774239981 3197824666864883165339993)
  ·
    refine ⟨2398368500148662374004995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3197824666864883165339993 2398368500148662374004995)
    ·
      refine ⟨3597552750222993561007493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398368500148662374004995 3597552750222993561007493)
      ·
        refine ⟨674541140666811292688905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3597552750222993561007493 674541140666811292688905)
        ·
          refine ⟨505905855500108469516679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674541140666811292688905 505905855500108469516679)
          ·
            refine ⟨758858783250162704275019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505905855500108469516679 758858783250162704275019)
            ·
              refine ⟨1138288174875244056412529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758858783250162704275019 1138288174875244056412529)
              ·
                refine ⟨853716131156433042309397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138288174875244056412529 853716131156433042309397)
                ·
                  refine ⟨40017943647957798858253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 853716131156433042309397 40017943647957798858253)
                  ·
                    rfl

theorem cell22_350706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_350706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350706 prefixEnd_350706 := by exact prefixLift 350706
  have htrace : WordTrace (prefixWord ++ tailWord_350706) baseStart_350706 baseEnd_350706 := by
    simpa [prefixWord, tailWord_350706, baseEnd_350706] using wordTrace_append hprefix tailTrace_350706
  have hstable : (prefixWord ++ tailWord_350706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350706).length < 2 ^ (prefixWord ++ tailWord_350706).sum := by decide
  have hdescent : baseEnd_350706 < baseStart_350706 := by decide
  rcases family_descends (prefixWord ++ tailWord_350706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350734 : List Nat := [4, 1, 1, 2, 3, 2, 9]
def baseStart_350734 : Nat := 118140960795 + 350734 * 2 ^ 59
def prefixEnd_350734 : Nat := 4983230072969 + 3 ^ 40 * 350734 * 2
def baseEnd_350734 : Nat := 4446793182077431736099

theorem tailTrace_350734 : CollatzResearch.WordTrace tailWord_350734 prefixEnd_350734 4446793182077431736099 := by
  unfold tailWord_350734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599039988919761680422407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8528213274238728962252837 1599039988919761680422407)
  ·
    refine ⟨2398559983379642520633611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1599039988919761680422407 2398559983379642520633611)
    ·
      refine ⟨3597839975069463780950417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398559983379642520633611 3597839975069463780950417)
      ·
        refine ⟨2698379981302097835712813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3597839975069463780950417 2698379981302097835712813)
        ·
          refine ⟨1011892492988286688392305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2698379981302097835712813 1011892492988286688392305)
          ·
            refine ⟨758919369741215016294229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1011892492988286688392305 758919369741215016294229)
            ·
              refine ⟨4446793182077431736099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 758919369741215016294229 4446793182077431736099)
              ·
                rfl

theorem cell22_350734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 9].length) (baseStart_350734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350734 prefixEnd_350734 := by exact prefixLift 350734
  have htrace : WordTrace (prefixWord ++ tailWord_350734) baseStart_350734 baseEnd_350734 := by
    simpa [prefixWord, tailWord_350734, baseEnd_350734] using wordTrace_append hprefix tailTrace_350734
  have hstable : (prefixWord ++ tailWord_350734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350734).length < 2 ^ (prefixWord ++ tailWord_350734).sum := by decide
  have hdescent : baseEnd_350734 < baseStart_350734 := by decide
  rcases family_descends (prefixWord ++ tailWord_350734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350826 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_350826 : Nat := 118140960795 + 350826 * 2 ^ 59
def prefixEnd_350826 : Nat := 4983230072969 + 3 ^ 40 * 350826 * 2
def baseEnd_350826 : Nat := 120094909396233083574391

theorem tailTrace_350826 : CollatzResearch.WordTrace tailWord_350826 prefixEnd_350826 120094909396233083574391 := by
  unfold tailWord_350826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198918856756198288932083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8530450284683195437152221 3198918856756198288932083)
  ·
    refine ⟨4798378285134297433398125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3198918856756198288932083 4798378285134297433398125)
    ·
      refine ⟨1799391856925361537524297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4798378285134297433398125 1799391856925361537524297)
      ·
        refine ⟨1349543892694021153143223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1799391856925361537524297 1349543892694021153143223)
        ·
          refine ⟨2024315839041031729714835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349543892694021153143223 2024315839041031729714835)
          ·
            refine ⟨3036473758561547594572253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024315839041031729714835 3036473758561547594572253)
            ·
              refine ⟨1138677659460580347964595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3036473758561547594572253 1138677659460580347964595)
              ·
                refine ⟨1708016489190870521946893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138677659460580347964595 1708016489190870521946893)
                ·
                  refine ⟨640506183446576445730085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1708016489190870521946893 640506183446576445730085)
                  ·
                    refine ⟨120094909396233083574391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 640506183446576445730085 120094909396233083574391)
                    ·
                      rfl

theorem cell22_350826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_350826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350826 prefixEnd_350826 := by exact prefixLift 350826
  have htrace : WordTrace (prefixWord ++ tailWord_350826) baseStart_350826 baseEnd_350826 := by
    simpa [prefixWord, tailWord_350826, baseEnd_350826] using wordTrace_append hprefix tailTrace_350826
  have hstable : (prefixWord ++ tailWord_350826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350826).length < 2 ^ (prefixWord ++ tailWord_350826).sum := by decide
  have hdescent : baseEnd_350826 < baseStart_350826 := by decide
  rcases family_descends (prefixWord ++ tailWord_350826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350839 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 3, 5]
def baseStart_350839 : Nat := 118140960795 + 350839 * 2 ^ 59
def prefixEnd_350839 : Nat := 4983230072969 + 3 ^ 40 * 350839 * 2
def baseEnd_350839 : Nat := 120099359561905382999351

theorem tailTrace_350839 : CollatzResearch.WordTrace tailWord_350839 prefixEnd_350839 120099359561905382999351 := by
  unfold tailWord_350839
  simp only [CollatzResearch.WordTrace]
  refine ⟨12796149575977696375951571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8530766383985130917301047 12796149575977696375951571)
  ·
    refine ⟨19194224363966544563927357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12796149575977696375951571 19194224363966544563927357)
    ·
      refine ⟨7197834136487454211472759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19194224363966544563927357 7197834136487454211472759)
      ·
        refine ⟨10796751204731181317209139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7197834136487454211472759 10796751204731181317209139)
        ·
          refine ⟨16195126807096771975813709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10796751204731181317209139 16195126807096771975813709)
          ·
            refine ⟨6073172552661289490930141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16195126807096771975813709 6073172552661289490930141)
            ·
              refine ⟨2277439707247983559098803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6073172552661289490930141 2277439707247983559098803)
              ·
                refine ⟨3416159560871975338648205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277439707247983559098803 3416159560871975338648205)
                ·
                  refine ⟨1281059835326990751993077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3416159560871975338648205 1281059835326990751993077)
                  ·
                    refine ⟨120099359561905382999351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1281059835326990751993077 120099359561905382999351)
                    ·
                      rfl

theorem cell22_350839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_350839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350839 prefixEnd_350839 := by exact prefixLift 350839
  have htrace : WordTrace (prefixWord ++ tailWord_350839) baseStart_350839 baseEnd_350839 := by
    simpa [prefixWord, tailWord_350839, baseEnd_350839] using wordTrace_append hprefix tailTrace_350839
  have hstable : (prefixWord ++ tailWord_350839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350839).length < 2 ^ (prefixWord ++ tailWord_350839).sum := by decide
  have hdescent : baseEnd_350839 < baseStart_350839 := by decide
  rcases family_descends (prefixWord ++ tailWord_350839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350991 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 1, 5]
def baseStart_350991 : Nat := 118140960795 + 350991 * 2 ^ 59
def prefixEnd_350991 : Nat := 4983230072969 + 3 ^ 40 * 350991 * 2
def baseEnd_350991 : Nat := 120151392268227653198885

theorem tailTrace_350991 : CollatzResearch.WordTrace tailWord_350991 prefixEnd_350991 120151392268227653198885 := by
  unfold tailWord_350991
  simp only [CollatzResearch.WordTrace]
  refine ⟨12801693471427026335484827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8534462314284684223656551 12801693471427026335484827)
  ·
    refine ⟨19202540207140539503227241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12801693471427026335484827 19202540207140539503227241)
    ·
      refine ⟨14401905155355404627420431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19202540207140539503227241 14401905155355404627420431)
      ·
        refine ⟨21602857733033106941130647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14401905155355404627420431 21602857733033106941130647)
        ·
          refine ⟨32404286599549660411695971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21602857733033106941130647 32404286599549660411695971)
          ·
            refine ⟨48606429899324490617543957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32404286599549660411695971 48606429899324490617543957)
            ·
              refine ⟨2278426401530835497697373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48606429899324490617543957 2278426401530835497697373)
              ·
                refine ⟨854409900574063311636515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2278426401530835497697373 854409900574063311636515)
                ·
                  refine ⟨1281614850861094967454773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854409900574063311636515 1281614850861094967454773)
                  ·
                    refine ⟨120151392268227653198885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1281614850861094967454773 120151392268227653198885)
                    ·
                      rfl

theorem cell22_350991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_350991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_350991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_350991 prefixEnd_350991 := by exact prefixLift 350991
  have htrace : WordTrace (prefixWord ++ tailWord_350991) baseStart_350991 baseEnd_350991 := by
    simpa [prefixWord, tailWord_350991, baseEnd_350991] using wordTrace_append hprefix tailTrace_350991
  have hstable : (prefixWord ++ tailWord_350991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350991).length < 2 ^ (prefixWord ++ tailWord_350991).sum := by decide
  have hdescent : baseEnd_350991 < baseStart_350991 := by decide
  rcases family_descends (prefixWord ++ tailWord_350991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351008 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_351008 : Nat := 118140960795 + 351008 * 2 ^ 59
def prefixEnd_351008 : Nat := 4983230072969 + 3 ^ 40 * 351008 * 2
def baseEnd_351008 : Nat := 120157211715645275523833

theorem tailTrace_351008 : CollatzResearch.WordTrace tailWord_351008 prefixEnd_351008 120157211715645275523833 := by
  unfold tailWord_351008
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401156756182719119426839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8534875674910292159235785 6401156756182719119426839)
  ·
    refine ⟨9601735134274078679140259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6401156756182719119426839 9601735134274078679140259)
    ·
      refine ⟨14402602701411118018710389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9601735134274078679140259 14402602701411118018710389)
      ·
        refine ⟨1350244003257292314254099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14402602701411118018710389 1350244003257292314254099)
        ·
          refine ⟨2025366004885938471381149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350244003257292314254099 2025366004885938471381149)
          ·
            refine ⟨759512251832226926767931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2025366004885938471381149 759512251832226926767931)
            ·
              refine ⟨1139268377748340390151897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759512251832226926767931 1139268377748340390151897)
              ·
                refine ⟨854451283311255292613923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139268377748340390151897 854451283311255292613923)
                ·
                  refine ⟨1281676924966882938920885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854451283311255292613923 1281676924966882938920885)
                  ·
                    refine ⟨120157211715645275523833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1281676924966882938920885 120157211715645275523833)
                    ·
                      rfl

theorem cell22_351008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_351008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351008 prefixEnd_351008 := by exact prefixLift 351008
  have htrace : WordTrace (prefixWord ++ tailWord_351008) baseStart_351008 baseEnd_351008 := by
    simpa [prefixWord, tailWord_351008, baseEnd_351008] using wordTrace_append hprefix tailTrace_351008
  have hstable : (prefixWord ++ tailWord_351008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351008).length < 2 ^ (prefixWord ++ tailWord_351008).sum := by decide
  have hdescent : baseEnd_351008 < baseStart_351008 := by decide
  rcases family_descends (prefixWord ++ tailWord_351008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351012 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_351012 : Nat := 118140960795 + 351012 * 2 ^ 59
def prefixEnd_351012 : Nat := 4983230072969 + 3 ^ 40 * 351012 * 2
def baseEnd_351012 : Nat := 120158580997390598423821

theorem tailTrace_351012 : CollatzResearch.WordTrace tailWord_351012 prefixEnd_351012 120158580997390598423821 := by
  unfold tailWord_351012
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401229702175473460999645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8534972936233964614666193 6401229702175473460999645)
  ·
    refine ⟨2400461138315802547874867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6401229702175473460999645 2400461138315802547874867)
    ·
      refine ⟨3600691707473703821812301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2400461138315802547874867 3600691707473703821812301)
      ·
        refine ⟨1350259390302638933179613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3600691707473703821812301 1350259390302638933179613)
        ·
          refine ⟨506347271363489599942355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1350259390302638933179613 506347271363489599942355)
          ·
            refine ⟨759520907045234399913533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506347271363489599942355 759520907045234399913533)
            ·
              refine ⟨284820340141962899967575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759520907045234399913533 284820340141962899967575)
              ·
                refine ⟨427230510212944349951363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284820340141962899967575 427230510212944349951363)
                ·
                  refine ⟨640845765319416524927045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427230510212944349951363 640845765319416524927045)
                  ·
                    refine ⟨120158580997390598423821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 640845765319416524927045 120158580997390598423821)
                    ·
                      rfl

theorem cell22_351012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_351012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351012 prefixEnd_351012 := by exact prefixLift 351012
  have htrace : WordTrace (prefixWord ++ tailWord_351012) baseStart_351012 baseEnd_351012 := by
    simpa [prefixWord, tailWord_351012, baseEnd_351012] using wordTrace_append hprefix tailTrace_351012
  have hstable : (prefixWord ++ tailWord_351012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351012).length < 2 ^ (prefixWord ++ tailWord_351012).sum := by decide
  have hdescent : baseEnd_351012 < baseStart_351012 := by decide
  rcases family_descends (prefixWord ++ tailWord_351012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351025 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 2, 3]
def baseStart_351025 : Nat := 118140960795 + 351025 * 2 ^ 59
def prefixEnd_351025 : Nat := 4983230072969 + 3 ^ 40 * 351025 * 2
def baseEnd_351025 : Nat := 120163031163062897848781

theorem tailTrace_351025 : CollatzResearch.WordTrace tailWord_351025 prefixEnd_351025 120163031163062897848781 := by
  unfold tailWord_351025
  simp only [CollatzResearch.WordTrace]
  refine ⟨12802933553303850142222529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8535289035535900094815019 12802933553303850142222529)
  ·
    refine ⟨9602200164977887606666897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12802933553303850142222529 9602200164977887606666897)
    ·
      refine ⟨7201650123733415705000173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9602200164977887606666897 7201650123733415705000173)
      ·
        refine ⟨2700618796400030889375065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7201650123733415705000173 2700618796400030889375065)
        ·
          refine ⟨2025464097300023167031299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2700618796400030889375065 2025464097300023167031299)
          ·
            refine ⟨3038196145950034750546949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025464097300023167031299 3038196145950034750546949)
            ·
              refine ⟨569661777365631515727553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3038196145950034750546949 569661777365631515727553)
              ·
                refine ⟨427246333024223636795665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569661777365631515727553 427246333024223636795665)
                ·
                  refine ⟨320434749768167727596749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427246333024223636795665 320434749768167727596749)
                  ·
                    refine ⟨120163031163062897848781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320434749768167727596749 120163031163062897848781)
                    ·
                      rfl

theorem cell22_351025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_351025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351025 prefixEnd_351025 := by exact prefixLift 351025
  have htrace : WordTrace (prefixWord ++ tailWord_351025) baseStart_351025 baseEnd_351025 := by
    simpa [prefixWord, tailWord_351025, baseEnd_351025] using wordTrace_append hprefix tailTrace_351025
  have hstable : (prefixWord ++ tailWord_351025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351025).length < 2 ^ (prefixWord ++ tailWord_351025).sum := by decide
  have hdescent : baseEnd_351025 < baseStart_351025 := by decide
  rcases family_descends (prefixWord ++ tailWord_351025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351027 : List Nat := [1, 1, 1, 2, 6, 3, 2, 2, 4]
def baseStart_351027 : Nat := 118140960795 + 351027 * 2 ^ 59
def prefixEnd_351027 : Nat := 4983230072969 + 3 ^ 40 * 351027 * 2
def baseEnd_351027 : Nat := 40054571934645186432925

theorem tailTrace_351027 : CollatzResearch.WordTrace tailWord_351027 prefixEnd_351027 40054571934645186432925 := by
  unfold tailWord_351027
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803006499296604483795335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8535337666197736322530223 12803006499296604483795335)
  ·
    refine ⟨19204509748944906725693003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12803006499296604483795335 19204509748944906725693003)
    ·
      refine ⟨28806764623417360088539505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19204509748944906725693003 28806764623417360088539505)
      ·
        refine ⟨21605073467563020066404629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28806764623417360088539505 21605073467563020066404629)
        ·
          refine ⟨1012737818792016565612717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21605073467563020066404629 1012737818792016565612717)
          ·
            refine ⟨379776682047006212104769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1012737818792016565612717 379776682047006212104769)
            ·
              refine ⟨284832511535254659078577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379776682047006212104769 284832511535254659078577)
              ·
                refine ⟨213624383651440994308933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284832511535254659078577 213624383651440994308933)
                ·
                  refine ⟨40054571934645186432925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213624383651440994308933 40054571934645186432925)
                  ·
                    rfl

theorem cell22_351027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 4].length) (baseStart_351027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351027 prefixEnd_351027 := by exact prefixLift 351027
  have htrace : WordTrace (prefixWord ++ tailWord_351027) baseStart_351027 baseEnd_351027 := by
    simpa [prefixWord, tailWord_351027, baseEnd_351027] using wordTrace_append hprefix tailTrace_351027
  have hstable : (prefixWord ++ tailWord_351027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351027).length < 2 ^ (prefixWord ++ tailWord_351027).sum := by decide
  have hdescent : baseEnd_351027 < baseStart_351027 := by decide
  rcases family_descends (prefixWord ++ tailWord_351027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351036 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_351036 : Nat := 118140960795 + 351036 * 2 ^ 59
def prefixEnd_351036 : Nat := 4983230072969 + 3 ^ 40 * 351036 * 2
def baseEnd_351036 : Nat := 120166796687862535823747

theorem tailTrace_351036 : CollatzResearch.WordTrace tailWord_351036 prefixEnd_351036 120166796687862535823747 := by
  unfold tailWord_351036
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401667378131999510436481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8535556504175999347248641 6401667378131999510436481)
  ·
    refine ⟨4801250533598999632827361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6401667378131999510436481 4801250533598999632827361)
    ·
      refine ⟨3600937900199249724620521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4801250533598999632827361 3600937900199249724620521)
      ·
        refine ⟨2700703425149437293465391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3600937900199249724620521 2700703425149437293465391)
        ·
          refine ⟨4051055137724155940198087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700703425149437293465391 4051055137724155940198087)
          ·
            refine ⟨6076582706586233910297131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051055137724155940198087 6076582706586233910297131)
            ·
              refine ⟨9114874059879350865445697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076582706586233910297131 9114874059879350865445697)
              ·
                refine ⟨6836155544909513149084273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9114874059879350865445697 6836155544909513149084273)
                ·
                  refine ⟨5127116658682134861813205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6836155544909513149084273 5127116658682134861813205)
                  ·
                    refine ⟨120166796687862535823747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5127116658682134861813205 120166796687862535823747)
                    ·
                      rfl

theorem cell22_351036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_351036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351036 prefixEnd_351036 := by exact prefixLift 351036
  have htrace : WordTrace (prefixWord ++ tailWord_351036) baseStart_351036 baseEnd_351036 := by
    simpa [prefixWord, tailWord_351036, baseEnd_351036] using wordTrace_append hprefix tailTrace_351036
  have hstable : (prefixWord ++ tailWord_351036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351036).length < 2 ^ (prefixWord ++ tailWord_351036).sum := by decide
  have hdescent : baseEnd_351036 < baseStart_351036 := by decide
  rcases family_descends (prefixWord ++ tailWord_351036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351057 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 2, 4]
def baseStart_351057 : Nat := 118140960795 + 351057 * 2 ^ 59
def prefixEnd_351057 : Nat := 4983230072969 + 3 ^ 40 * 351057 * 2
def baseEnd_351057 : Nat := 120173985417025481048683

theorem tailTrace_351057 : CollatzResearch.WordTrace tailWord_351057 prefixEnd_351057 120173985417025481048683 := by
  unfold tailWord_351057
  simp only [CollatzResearch.WordTrace]
  refine ⟨12804100689187919607387425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8536067126125279738258283 12804100689187919607387425)
  ·
    refine ⟨9603075516890939705540569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12804100689187919607387425 9603075516890939705540569)
    ·
      refine ⟨7202306637668204779155427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9603075516890939705540569 7202306637668204779155427)
      ·
        refine ⟨10803459956502307168733141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7202306637668204779155427 10803459956502307168733141)
        ·
          refine ⟨253206092730522824267183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10803459956502307168733141 253206092730522824267183)
          ·
            refine ⟨379809139095784236400775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253206092730522824267183 379809139095784236400775)
            ·
              refine ⟨569713708643676354601163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379809139095784236400775 569713708643676354601163)
              ·
                refine ⟨854570562965514531901745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569713708643676354601163 854570562965514531901745)
                ·
                  refine ⟨640927922224135898926309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 854570562965514531901745 640927922224135898926309)
                  ·
                    refine ⟨120173985417025481048683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 640927922224135898926309 120173985417025481048683)
                    ·
                      rfl

theorem cell22_351057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_351057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351057 prefixEnd_351057 := by exact prefixLift 351057
  have htrace : WordTrace (prefixWord ++ tailWord_351057) baseStart_351057 baseEnd_351057 := by
    simpa [prefixWord, tailWord_351057, baseEnd_351057] using wordTrace_append hprefix tailTrace_351057
  have hstable : (prefixWord ++ tailWord_351057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351057).length < 2 ^ (prefixWord ++ tailWord_351057).sum := by decide
  have hdescent : baseEnd_351057 < baseStart_351057 := by decide
  rcases family_descends (prefixWord ++ tailWord_351057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351083 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 5]
def baseStart_351083 : Nat := 118140960795 + 351083 * 2 ^ 59
def prefixEnd_351083 : Nat := 4983230072969 + 3 ^ 40 * 351083 * 2
def baseEnd_351083 : Nat := 40060961916123359966201

theorem tailTrace_351083 : CollatzResearch.WordTrace tailWord_351083 prefixEnd_351083 40060961916123359966201 := by
  unfold tailWord_351083
  simp only [CollatzResearch.WordTrace]
  refine ⟨12805048987093726047833903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8536699324729150698555935 12805048987093726047833903)
  ·
    refine ⟨19207573480640589071750855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12805048987093726047833903 19207573480640589071750855)
    ·
      refine ⟨28811360220960883607626283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19207573480640589071750855 28811360220960883607626283)
      ·
        refine ⟨43217040331441325411439425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28811360220960883607626283 43217040331441325411439425)
        ·
          refine ⟨32412780248580994058579569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43217040331441325411439425 32412780248580994058579569)
          ·
            refine ⟨24309585186435745543934677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32412780248580994058579569 24309585186435745543934677)
            ·
              refine ⟨569755902807087786185969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24309585186435745543934677 569755902807087786185969)
              ·
                refine ⟨427316927105315839639477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569755902807087786185969 427316927105315839639477)
                ·
                  refine ⟨40060961916123359966201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 427316927105315839639477 40060961916123359966201)
                  ·
                    rfl

theorem cell22_351083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 5].length) (baseStart_351083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351083 prefixEnd_351083 := by exact prefixLift 351083
  have htrace : WordTrace (prefixWord ++ tailWord_351083) baseStart_351083 baseEnd_351083 := by
    simpa [prefixWord, tailWord_351083, baseEnd_351083] using wordTrace_append hprefix tailTrace_351083
  have hstable : (prefixWord ++ tailWord_351083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351083).length < 2 ^ (prefixWord ++ tailWord_351083).sum := by decide
  have hdescent : baseEnd_351083 < baseStart_351083 := by decide
  rcases family_descends (prefixWord ++ tailWord_351083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351096 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_351096 : Nat := 118140960795 + 351096 * 2 ^ 59
def prefixEnd_351096 : Nat := 4983230072969 + 3 ^ 40 * 351096 * 2
def baseEnd_351096 : Nat := 120187335914042379323563

theorem tailTrace_351096 : CollatzResearch.WordTrace tailWord_351096 prefixEnd_351096 120187335914042379323563 := by
  unfold tailWord_351096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402761568023314634028571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8537015424031086178704761 6402761568023314634028571)
  ·
    refine ⟨9604142352034971951042857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402761568023314634028571 9604142352034971951042857)
    ·
      refine ⟨7203106764026228963282143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9604142352034971951042857 7203106764026228963282143)
      ·
        refine ⟨10804660146039343444923215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7203106764026228963282143 10804660146039343444923215)
        ·
          refine ⟨16206990219059015167384823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10804660146039343444923215 16206990219059015167384823)
          ·
            refine ⟨24310485328588522751077235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16206990219059015167384823 24310485328588522751077235)
            ·
              refine ⟨36465727992882784126615853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24310485328588522751077235 36465727992882784126615853)
              ·
                refine ⟨13674647997331044047480945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36465727992882784126615853 13674647997331044047480945)
                ·
                  refine ⟨10255985997998283035610709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13674647997331044047480945 10255985997998283035610709)
                  ·
                    refine ⟨120187335914042379323563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10255985997998283035610709 120187335914042379323563)
                    ·
                      rfl

theorem cell22_351096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_351096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351096 prefixEnd_351096 := by exact prefixLift 351096
  have htrace : WordTrace (prefixWord ++ tailWord_351096) baseStart_351096 baseEnd_351096 := by
    simpa [prefixWord, tailWord_351096, baseEnd_351096] using wordTrace_append hprefix tailTrace_351096
  have hstable : (prefixWord ++ tailWord_351096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351096).length < 2 ^ (prefixWord ++ tailWord_351096).sum := by decide
  have hdescent : baseEnd_351096 < baseStart_351096 := by decide
  rcases family_descends (prefixWord ++ tailWord_351096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351106 : List Nat := [3, 4, 2, 2, 2, 1, 2, 6]
def baseStart_351106 : Nat := 118140960795 + 351106 * 2 ^ 59
def prefixEnd_351106 : Nat := 4983230072969 + 3 ^ 40 * 351106 * 2
def baseEnd_351106 : Nat := 13354528790933965174837

theorem tailTrace_351106 : CollatzResearch.WordTrace tailWord_351106 prefixEnd_351106 13354528790933965174837 := by
  unfold tailWord_351106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201471966502600243980293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8537258577340267317280781 3201471966502600243980293)
  ·
    refine ⟨600275993719237545746305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3201471966502600243980293 600275993719237545746305)
    ·
      refine ⟨450206995289428159309729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 600275993719237545746305 450206995289428159309729)
      ·
        refine ⟨337655246467071119482297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450206995289428159309729 337655246467071119482297)
        ·
          refine ⟨253241434850303339611723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337655246467071119482297 253241434850303339611723)
          ·
            refine ⟨379862152275455009417585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253241434850303339611723 379862152275455009417585)
            ·
              refine ⟨284896614206591257063189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379862152275455009417585 284896614206591257063189)
              ·
                refine ⟨13354528790933965174837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 284896614206591257063189 13354528790933965174837)
                ·
                  rfl

theorem cell22_351106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_351106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351106 prefixEnd_351106 := by exact prefixLift 351106
  have htrace : WordTrace (prefixWord ++ tailWord_351106) baseStart_351106 baseEnd_351106 := by
    simpa [prefixWord, tailWord_351106, baseEnd_351106] using wordTrace_append hprefix tailTrace_351106
  have hstable : (prefixWord ++ tailWord_351106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351106).length < 2 ^ (prefixWord ++ tailWord_351106).sum := by decide
  have hdescent : baseEnd_351106 < baseStart_351106 := by decide
  rcases family_descends (prefixWord ++ tailWord_351106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351190 : List Nat := [5, 2, 1, 1, 2, 11]
def baseStart_351190 : Nat := 118140960795 + 351190 * 2 ^ 59
def prefixEnd_351190 : Nat := 4983230072969 + 3 ^ 40 * 351190 * 2
def baseEnd_351190 : Nat := 1484191531297005771275

theorem tailTrace_351190 : CollatzResearch.WordTrace tailWord_351190 prefixEnd_351190 1484191531297005771275 := by
  unfold tailWord_351190
  simp only [CollatzResearch.WordTrace]
  refine ⟨800559474856630207623689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8539301065137388881319349 800559474856630207623689)
  ·
    refine ⟨600419606142472655717767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 800559474856630207623689 600419606142472655717767)
    ·
      refine ⟨900629409213708983576651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600419606142472655717767 900629409213708983576651)
      ·
        refine ⟨1350944113820563475364977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900629409213708983576651 1350944113820563475364977)
        ·
          refine ⟨1013208085365422606523733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1350944113820563475364977 1013208085365422606523733)
          ·
            refine ⟨1484191531297005771275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1013208085365422606523733 1484191531297005771275)
            ·
              rfl

theorem cell22_351190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 11].length) (baseStart_351190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351190 prefixEnd_351190 := by exact prefixLift 351190
  have htrace : WordTrace (prefixWord ++ tailWord_351190) baseStart_351190 baseEnd_351190 := by
    simpa [prefixWord, tailWord_351190, baseEnd_351190] using wordTrace_append hprefix tailTrace_351190
  have hstable : (prefixWord ++ tailWord_351190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351190).length < 2 ^ (prefixWord ++ tailWord_351190).sum := by decide
  have hdescent : baseEnd_351190 < baseStart_351190 := by decide
  rcases family_descends (prefixWord ++ tailWord_351190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351203 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 1, 8]
def baseStart_351203 : Nat := 118140960795 + 351203 * 2 ^ 59
def prefixEnd_351203 : Nat := 4983230072969 + 3 ^ 40 * 351203 * 2
def baseEnd_351203 : Nat := 120223964200729766898235

theorem tailTrace_351203 : CollatzResearch.WordTrace tailWord_351203 prefixEnd_351203 120223964200729766898235 := by
  unfold tailWord_351203
  simp only [CollatzResearch.WordTrace]
  refine ⟨12809425746658986542202263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8539617164439324361468175 12809425746658986542202263)
  ·
    refine ⟨19214138619988479813303395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12809425746658986542202263 19214138619988479813303395)
    ·
      refine ⟨28821207929982719719955093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19214138619988479813303395 28821207929982719719955093)
      ·
        refine ⟨1350994121717939986872895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28821207929982719719955093 1350994121717939986872895)
        ·
          refine ⟨2026491182576909980309343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350994121717939986872895 2026491182576909980309343)
          ·
            refine ⟨3039736773865364970464015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026491182576909980309343 3039736773865364970464015)
            ·
              refine ⟨4559605160798047455696023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3039736773865364970464015 4559605160798047455696023)
              ·
                refine ⟨6839407741197071183544035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559605160798047455696023 6839407741197071183544035)
                ·
                  refine ⟨10259111611795606775316053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6839407741197071183544035 10259111611795606775316053)
                  ·
                    refine ⟨120223964200729766898235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10259111611795606775316053 120223964200729766898235)
                    ·
                      rfl

theorem cell22_351203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_351203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351203 prefixEnd_351203 := by exact prefixLift 351203
  have htrace : WordTrace (prefixWord ++ tailWord_351203) baseStart_351203 baseEnd_351203 := by
    simpa [prefixWord, tailWord_351203, baseEnd_351203] using wordTrace_append hprefix tailTrace_351203
  have hstable : (prefixWord ++ tailWord_351203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351203).length < 2 ^ (prefixWord ++ tailWord_351203).sum := by decide
  have hdescent : baseEnd_351203 < baseStart_351203 := by decide
  rcases family_descends (prefixWord ++ tailWord_351203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351222 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_351222 : Nat := 118140960795 + 351222 * 2 ^ 59
def prefixEnd_351222 : Nat := 4983230072969 + 3 ^ 40 * 351222 * 2
def baseEnd_351222 : Nat := 120230468289020050673177

theorem tailTrace_351222 : CollatzResearch.WordTrace tailWord_351222 prefixEnd_351222 120230468289020050673177 := by
  unfold tailWord_351222
  simp only [CollatzResearch.WordTrace]
  refine ⟨800632420849384549196495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8540079155726768524762613 800632420849384549196495)
  ·
    refine ⟨1200948631274076823794743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800632420849384549196495 1200948631274076823794743)
    ·
      refine ⟨1801422946911115235692115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200948631274076823794743 1801422946911115235692115)
      ·
        refine ⟨2702134420366672853538173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801422946911115235692115 2702134420366672853538173)
        ·
          refine ⟨1013300407637502320076815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2702134420366672853538173 1013300407637502320076815)
          ·
            refine ⟨1519950611456253480115223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013300407637502320076815 1519950611456253480115223)
            ·
              refine ⟨2279925917184380220172835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519950611456253480115223 2279925917184380220172835)
              ·
                refine ⟨3419888875776570330259253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279925917184380220172835 3419888875776570330259253)
                ·
                  refine ⟨320614582104053468461805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3419888875776570330259253 320614582104053468461805)
                  ·
                    refine ⟨120230468289020050673177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320614582104053468461805 120230468289020050673177)
                    ·
                      rfl

theorem cell22_351222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_351222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351222 prefixEnd_351222 := by exact prefixLift 351222
  have htrace : WordTrace (prefixWord ++ tailWord_351222) baseStart_351222 baseEnd_351222 := by
    simpa [prefixWord, tailWord_351222, baseEnd_351222] using wordTrace_append hprefix tailTrace_351222
  have hstable : (prefixWord ++ tailWord_351222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351222).length < 2 ^ (prefixWord ++ tailWord_351222).sum := by decide
  have hdescent : baseEnd_351222 < baseStart_351222 := by decide
  rcases family_descends (prefixWord ++ tailWord_351222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351239 : List Nat := [1, 1, 4, 3, 1, 1, 4, 3, 1, 3]
def baseStart_351239 : Nat := 118140960795 + 351239 * 2 ^ 59
def prefixEnd_351239 : Nat := 4983230072969 + 3 ^ 40 * 351239 * 2
def baseEnd_351239 : Nat := 120236287736437672998125

theorem tailTrace_351239 : CollatzResearch.WordTrace tailWord_351239 prefixEnd_351239 120236287736437672998125 := by
  unfold tailWord_351239
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810738774528564690512771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8540492516352376460341847 12810738774528564690512771)
  ·
    refine ⟨19216108161792847035769157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12810738774528564690512771 19216108161792847035769157)
    ·
      refine ⟨3603020280336158819206717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19216108161792847035769157 3603020280336158819206717)
      ·
        refine ⟨1351132605126059557202519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3603020280336158819206717 1351132605126059557202519)
        ·
          refine ⟨2026698907689089335803779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351132605126059557202519 2026698907689089335803779)
          ·
            refine ⟨3040048361533634003705669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026698907689089335803779 3040048361533634003705669)
            ·
              refine ⟨570009067787556375694813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3040048361533634003705669 570009067787556375694813)
              ·
                refine ⟨213753400420333640885555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570009067787556375694813 213753400420333640885555)
                ·
                  refine ⟨320630100630500461328333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213753400420333640885555 320630100630500461328333)
                  ·
                    refine ⟨120236287736437672998125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320630100630500461328333 120236287736437672998125)
                    ·
                      rfl

theorem cell22_351239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_351239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351239 prefixEnd_351239 := by exact prefixLift 351239
  have htrace : WordTrace (prefixWord ++ tailWord_351239) baseStart_351239 baseEnd_351239 := by
    simpa [prefixWord, tailWord_351239, baseEnd_351239] using wordTrace_append hprefix tailTrace_351239
  have hstable : (prefixWord ++ tailWord_351239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351239).length < 2 ^ (prefixWord ++ tailWord_351239).sum := by decide
  have hdescent : baseEnd_351239 < baseStart_351239 := by decide
  rcases family_descends (prefixWord ++ tailWord_351239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351282 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_351282 : Nat := 118140960795 + 351282 * 2 ^ 59
def prefixEnd_351282 : Nat := 4983230072969 + 3 ^ 40 * 351282 * 2
def baseEnd_351282 : Nat := 120251007515199894172993

theorem tailTrace_351282 : CollatzResearch.WordTrace tailWord_351282 prefixEnd_351282 120251007515199894172993 := by
  unfold tailWord_351282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3203076778343195758582025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8541538075581855356218733 3203076778343195758582025)
  ·
    refine ⟨2402307583757396818936519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3203076778343195758582025 2402307583757396818936519)
    ·
      refine ⟨3603461375636095228404779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402307583757396818936519 3603461375636095228404779)
      ·
        refine ⟨5405192063454142842607169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603461375636095228404779 5405192063454142842607169)
        ·
          refine ⟨4053894047590607131955377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5405192063454142842607169 4053894047590607131955377)
          ·
            refine ⟨3040420535692955348966533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4053894047590607131955377 3040420535692955348966533)
            ·
              refine ⟨570078850442429127931225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3040420535692955348966533 570078850442429127931225)
              ·
                refine ⟨427559137831821845948419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570078850442429127931225 427559137831821845948419)
                ·
                  refine ⟨641338706747732768922629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427559137831821845948419 641338706747732768922629)
                  ·
                    refine ⟨120251007515199894172993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 641338706747732768922629 120251007515199894172993)
                    ·
                      rfl

theorem cell22_351282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_351282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351282 prefixEnd_351282 := by exact prefixLift 351282
  have htrace : WordTrace (prefixWord ++ tailWord_351282) baseStart_351282 baseEnd_351282 := by
    simpa [prefixWord, tailWord_351282, baseEnd_351282] using wordTrace_append hprefix tailTrace_351282
  have hstable : (prefixWord ++ tailWord_351282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351282).length < 2 ^ (prefixWord ++ tailWord_351282).sum := by decide
  have hdescent : baseEnd_351282 < baseStart_351282 := by decide
  rcases family_descends (prefixWord ++ tailWord_351282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351329 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 2, 3]
def baseStart_351329 : Nat := 118140960795 + 351329 * 2 ^ 59
def prefixEnd_351329 : Nat := 4983230072969 + 3 ^ 40 * 351329 * 2
def baseEnd_351329 : Nat := 120267096575707438247849

theorem tailTrace_351329 : CollatzResearch.WordTrace tailWord_351329 prefixEnd_351329 120267096575707438247849 := by
  unfold tailWord_351329
  simp only [CollatzResearch.WordTrace]
  refine ⟨12814021344202510061289041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8542680896135006707526027 12814021344202510061289041)
  ·
    refine ⟨9610516008151882545966781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12814021344202510061289041 9610516008151882545966781)
    ·
      refine ⟨3603943503056955954737543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9610516008151882545966781 3603943503056955954737543)
      ·
        refine ⟨5405915254585433932106315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603943503056955954737543 5405915254585433932106315)
        ·
          refine ⟨8108872881878150898159473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405915254585433932106315 8108872881878150898159473)
          ·
            refine ⟨6081654661408613173619605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8108872881878150898159473 6081654661408613173619605)
            ·
              refine ⟨285077562253528742513419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6081654661408613173619605 285077562253528742513419)
              ·
                refine ⟨427616343380293113770129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285077562253528742513419 427616343380293113770129)
                ·
                  refine ⟨320712257535219835327597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427616343380293113770129 320712257535219835327597)
                  ·
                    refine ⟨120267096575707438247849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320712257535219835327597 120267096575707438247849)
                    ·
                      rfl

theorem cell22_351329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_351329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351329 prefixEnd_351329 := by exact prefixLift 351329
  have htrace : WordTrace (prefixWord ++ tailWord_351329) baseStart_351329 baseEnd_351329 := by
    simpa [prefixWord, tailWord_351329, baseEnd_351329] using wordTrace_append hprefix tailTrace_351329
  have hstable : (prefixWord ++ tailWord_351329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351329).length < 2 ^ (prefixWord ++ tailWord_351329).sum := by decide
  have hdescent : baseEnd_351329 < baseStart_351329 := by decide
  rcases family_descends (prefixWord ++ tailWord_351329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351415 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 8]
def baseStart_351415 : Nat := 118140960795 + 351415 * 2 ^ 59
def prefixEnd_351415 : Nat := 4983230072969 + 3 ^ 40 * 351415 * 2
def baseEnd_351415 : Nat := 40098845377743960199195

theorem tailTrace_351415 : CollatzResearch.WordTrace tailWord_351415 prefixEnd_351415 40098845377743960199195 := by
  unfold tailWord_351415
  simp only [CollatzResearch.WordTrace]
  refine ⟨12817158021890946748919699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8544772014593964499279799 12817158021890946748919699)
  ·
    refine ⟨19225737032836420123379549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12817158021890946748919699 19225737032836420123379549)
    ·
      refine ⟨7209651387313657546267331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19225737032836420123379549 7209651387313657546267331)
      ·
        refine ⟨10814477080970486319400997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7209651387313657546267331 10814477080970486319400997)
        ·
          refine ⟨2027714452681966184887687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10814477080970486319400997 2027714452681966184887687)
          ·
            refine ⟨3041571679022949277331531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027714452681966184887687 3041571679022949277331531)
            ·
              refine ⟨4562357518534423915997297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041571679022949277331531 4562357518534423915997297)
              ·
                refine ⟨3421768138900817936997973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562357518534423915997297 3421768138900817936997973)
                ·
                  refine ⟨40098845377743960199195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3421768138900817936997973 40098845377743960199195)
                  ·
                    rfl

theorem cell22_351415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 8].length) (baseStart_351415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351415 prefixEnd_351415 := by exact prefixLift 351415
  have htrace : WordTrace (prefixWord ++ tailWord_351415) baseStart_351415 baseEnd_351415 := by
    simpa [prefixWord, tailWord_351415, baseEnd_351415] using wordTrace_append hprefix tailTrace_351415
  have hstable : (prefixWord ++ tailWord_351415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351415).length < 2 ^ (prefixWord ++ tailWord_351415).sum := by decide
  have hdescent : baseEnd_351415 < baseStart_351415 := by decide
  rcases family_descends (prefixWord ++ tailWord_351415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351447 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 1, 5]
def baseStart_351447 : Nat := 118140960795 + 351447 * 2 ^ 59
def prefixEnd_351447 : Nat := 4983230072969 + 3 ^ 40 * 351447 * 2
def baseEnd_351447 : Nat := 120307490387194463797487

theorem tailTrace_351447 : CollatzResearch.WordTrace tailWord_351447 prefixEnd_351447 120307490387194463797487 := by
  unfold tailWord_351447
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818325157775016214084595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8545550105183344142723063 12818325157775016214084595)
  ·
    refine ⟨19227487736662524321126893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12818325157775016214084595 19227487736662524321126893)
    ·
      refine ⟨7210307901248446620422585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19227487736662524321126893 7210307901248446620422585)
      ·
        refine ⟨5407730925936334965316939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7210307901248446620422585 5407730925936334965316939)
        ·
          refine ⟨8111596388904502447975409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407730925936334965316939 8111596388904502447975409)
          ·
            refine ⟨6083697291678376835981557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8111596388904502447975409 6083697291678376835981557)
            ·
              refine ⟨570346621094847828373271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6083697291678376835981557 570346621094847828373271)
              ·
                refine ⟨855519931642271742559907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570346621094847828373271 855519931642271742559907)
                ·
                  refine ⟨1283279897463407613839861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855519931642271742559907 1283279897463407613839861)
                  ·
                    refine ⟨120307490387194463797487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1283279897463407613839861 120307490387194463797487)
                    ·
                      rfl

theorem cell22_351447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_351447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351447 prefixEnd_351447 := by exact prefixLift 351447
  have htrace : WordTrace (prefixWord ++ tailWord_351447) baseStart_351447 baseEnd_351447 := by
    simpa [prefixWord, tailWord_351447, baseEnd_351447] using wordTrace_append hprefix tailTrace_351447
  have hstable : (prefixWord ++ tailWord_351447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351447).length < 2 ^ (prefixWord ++ tailWord_351447).sum := by decide
  have hdescent : baseEnd_351447 < baseStart_351447 := by decide
  rcases family_descends (prefixWord ++ tailWord_351447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351466 : List Nat := [3, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_351466 : Nat := 118140960795 + 351466 * 2 ^ 59
def prefixEnd_351466 : Nat := 4983230072969 + 3 ^ 40 * 351466 * 2
def baseEnd_351466 : Nat := 40104664825161582524143

theorem tailTrace_351466 : CollatzResearch.WordTrace tailWord_351466 prefixEnd_351466 40104664825161582524143 := by
  unfold tailWord_351466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204754536176545614756563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8546012096470788306017501 3204754536176545614756563)
  ·
    refine ⟨4807131804264818422134845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3204754536176545614756563 4807131804264818422134845)
    ·
      refine ⟨1802674426599306908300567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4807131804264818422134845 1802674426599306908300567)
      ·
        refine ⟨2704011639898960362450851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802674426599306908300567 2704011639898960362450851)
        ·
          refine ⟨4056017459848440543676277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704011639898960362450851 4056017459848440543676277)
          ·
            refine ⟨380251636860791300969651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4056017459848440543676277 380251636860791300969651)
            ·
              refine ⟨570377455291186951454477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380251636860791300969651 570377455291186951454477)
              ·
                refine ⟨213891545734195106795429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570377455291186951454477 213891545734195106795429)
                ·
                  refine ⟨40104664825161582524143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213891545734195106795429 40104664825161582524143)
                  ·
                    rfl

theorem cell22_351466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_351466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351466 prefixEnd_351466 := by exact prefixLift 351466
  have htrace : WordTrace (prefixWord ++ tailWord_351466) baseStart_351466 baseEnd_351466 := by
    simpa [prefixWord, tailWord_351466, baseEnd_351466] using wordTrace_append hprefix tailTrace_351466
  have hstable : (prefixWord ++ tailWord_351466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351466).length < 2 ^ (prefixWord ++ tailWord_351466).sum := by decide
  have hdescent : baseEnd_351466 < baseStart_351466 := by decide
  rcases family_descends (prefixWord ++ tailWord_351466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351539 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 5]
def baseStart_351539 : Nat := 118140960795 + 351539 * 2 ^ 59
def prefixEnd_351539 : Nat := 4983230072969 + 3 ^ 40 * 351539 * 2
def baseEnd_351539 : Nat := 40112994622445630165735

theorem tailTrace_351539 : CollatzResearch.WordTrace tailWord_351539 prefixEnd_351539 40112994622445630165735 := by
  unfold tailWord_351539
  simp only [CollatzResearch.WordTrace]
  refine ⟨12821680673441715926433671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8547787115627810617622447 12821680673441715926433671)
  ·
    refine ⟨19232521010162573889650507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12821680673441715926433671 19232521010162573889650507)
    ·
      refine ⟨28848781515243860834475761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19232521010162573889650507 28848781515243860834475761)
      ·
        refine ⟨21636586136432895625856821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28848781515243860834475761 21636586136432895625856821)
        ·
          refine ⟨2028429950290583964924077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21636586136432895625856821 2028429950290583964924077)
          ·
            refine ⟨760661231358968986846529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2028429950290583964924077 760661231358968986846529)
            ·
              refine ⟨570495923519226740134897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760661231358968986846529 570495923519226740134897)
              ·
                refine ⟨427871942639420055101173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570495923519226740134897 427871942639420055101173)
                ·
                  refine ⟨40112994622445630165735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 427871942639420055101173 40112994622445630165735)
                  ·
                    rfl

theorem cell22_351539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 5].length) (baseStart_351539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351539 prefixEnd_351539 := by exact prefixLift 351539
  have htrace : WordTrace (prefixWord ++ tailWord_351539) baseStart_351539 baseEnd_351539 := by
    simpa [prefixWord, tailWord_351539, baseEnd_351539] using wordTrace_append hprefix tailTrace_351539
  have hstable : (prefixWord ++ tailWord_351539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351539).length < 2 ^ (prefixWord ++ tailWord_351539).sum := by decide
  have hdescent : baseEnd_351539 < baseStart_351539 := by decide
  rcases family_descends (prefixWord ++ tailWord_351539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351552 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_351552 : Nat := 118140960795 + 351552 * 2 ^ 59
def prefixEnd_351552 : Nat := 4983230072969 + 3 ^ 40 * 351552 * 2
def baseEnd_351552 : Nat := 120343434033009189922165

theorem tailTrace_351552 : CollatzResearch.WordTrace tailWord_351552 prefixEnd_351552 120343434033009189922165 := by
  unfold tailWord_351552
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411077411197309573328455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8548103214929746097771273 6411077411197309573328455)
  ·
    refine ⟨9616616116795964359992683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6411077411197309573328455 9616616116795964359992683)
    ·
      refine ⟨14424924175193946539989025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9616616116795964359992683 14424924175193946539989025)
      ·
        refine ⟨10818693131395459904991769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14424924175193946539989025 10818693131395459904991769)
        ·
          refine ⟨8114019848546594928743827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10818693131395459904991769 8114019848546594928743827)
          ·
            refine ⟨12171029772819892393115741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8114019848546594928743827 12171029772819892393115741)
            ·
              refine ⟨4564136164807459647418403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12171029772819892393115741 4564136164807459647418403)
              ·
                refine ⟨6846204247211189471127605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4564136164807459647418403 6846204247211189471127605)
                ·
                  refine ⟨641831648176049012918213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6846204247211189471127605 641831648176049012918213)
                  ·
                    refine ⟨120343434033009189922165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 641831648176049012918213 120343434033009189922165)
                    ·
                      rfl

theorem cell22_351552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_351552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351552 prefixEnd_351552 := by exact prefixLift 351552
  have htrace : WordTrace (prefixWord ++ tailWord_351552) baseStart_351552 baseEnd_351552 := by
    simpa [prefixWord, tailWord_351552, baseEnd_351552] using wordTrace_append hprefix tailTrace_351552
  have hstable : (prefixWord ++ tailWord_351552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351552).length < 2 ^ (prefixWord ++ tailWord_351552).sum := by decide
  have hdescent : baseEnd_351552 < baseStart_351552 := by decide
  rcases family_descends (prefixWord ++ tailWord_351552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351556 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 5]
def baseStart_351556 : Nat := 118140960795 + 351556 * 2 ^ 59
def prefixEnd_351556 : Nat := 4983230072969 + 3 ^ 40 * 351556 * 2
def baseEnd_351556 : Nat := 40114934438251504274051

theorem tailTrace_351556 : CollatzResearch.WordTrace tailWord_351556 prefixEnd_351556 40114934438251504274051 := by
  unfold tailWord_351556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411150357190063914901261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8548200476253418553201681 6411150357190063914901261)
  ·
    refine ⟨2404181383946273968087973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6411150357190063914901261 2404181383946273968087973)
    ·
      refine ⟨450784009489926369016495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2404181383946273968087973 450784009489926369016495)
      ·
        refine ⟨676176014234889553524743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450784009489926369016495 676176014234889553524743)
        ·
          refine ⟨1014264021352334330287115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676176014234889553524743 1014264021352334330287115)
          ·
            refine ⟨1521396032028501495430673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014264021352334330287115 1521396032028501495430673)
            ·
              refine ⟨1141047024021376121573005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521396032028501495430673 1141047024021376121573005)
              ·
                refine ⟨427892634008016045589877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1141047024021376121573005 427892634008016045589877)
                ·
                  refine ⟨40114934438251504274051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 427892634008016045589877 40114934438251504274051)
                  ·
                    rfl

theorem cell22_351556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_351556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351556 prefixEnd_351556 := by exact prefixLift 351556
  have htrace : WordTrace (prefixWord ++ tailWord_351556) baseStart_351556 baseEnd_351556 := by
    simpa [prefixWord, tailWord_351556, baseEnd_351556] using wordTrace_append hprefix tailTrace_351556
  have hstable : (prefixWord ++ tailWord_351556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351556).length < 2 ^ (prefixWord ++ tailWord_351556).sum := by decide
  have hdescent : baseEnd_351556 < baseStart_351556 := by decide
  rcases family_descends (prefixWord ++ tailWord_351556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351569 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_351569 : Nat := 118140960795 + 351569 * 2 ^ 59
def prefixEnd_351569 : Nat := 4983230072969 + 3 ^ 40 * 351569 * 2
def baseEnd_351569 : Nat := 120349253480426812247113

theorem tailTrace_351569 : CollatzResearch.WordTrace tailWord_351569 prefixEnd_351569 120349253480426812247113 := by
  unfold tailWord_351569
  simp only [CollatzResearch.WordTrace]
  refine ⟨12822774863333031050025761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8548516575555354033350507 12822774863333031050025761)
  ·
    refine ⟨9617081147499773287519321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12822774863333031050025761 9617081147499773287519321)
    ·
      refine ⟨7212810860624829965639491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9617081147499773287519321 7212810860624829965639491)
      ·
        refine ⟨10819216290937244948459237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7212810860624829965639491 10819216290937244948459237)
        ·
          refine ⟨2028603054550733427836107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10819216290937244948459237 2028603054550733427836107)
          ·
            refine ⟨3042904581826100141754161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028603054550733427836107 3042904581826100141754161)
            ·
              refine ⟨2282178436369575106315621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042904581826100141754161 2282178436369575106315621)
              ·
                refine ⟨427908456819295332434179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2282178436369575106315621 427908456819295332434179)
                ·
                  refine ⟨641862685228942998651269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427908456819295332434179 641862685228942998651269)
                  ·
                    refine ⟨120349253480426812247113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 641862685228942998651269 120349253480426812247113)
                    ·
                      rfl

theorem cell22_351569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_351569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351569 prefixEnd_351569 := by exact prefixLift 351569
  have htrace : WordTrace (prefixWord ++ tailWord_351569) baseStart_351569 baseEnd_351569 := by
    simpa [prefixWord, tailWord_351569, baseEnd_351569] using wordTrace_append hprefix tailTrace_351569
  have hstable : (prefixWord ++ tailWord_351569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351569).length < 2 ^ (prefixWord ++ tailWord_351569).sum := by decide
  have hdescent : baseEnd_351569 < baseStart_351569 := by decide
  rcases family_descends (prefixWord ++ tailWord_351569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351586 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_351586 : Nat := 118140960795 + 351586 * 2 ^ 59
def prefixEnd_351586 : Nat := 4983230072969 + 3 ^ 40 * 351586 * 2
def baseEnd_351586 : Nat := 120355072927844434572061

theorem tailTrace_351586 : CollatzResearch.WordTrace tailWord_351586 prefixEnd_351586 120355072927844434572061 := by
  unfold tailWord_351586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3205848726067860738348653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8548929936180961968929741 3205848726067860738348653)
  ·
    refine ⟨1202193272275447776880745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3205848726067860738348653 1202193272275447776880745)
    ·
      refine ⟨901644954206585832660559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1202193272275447776880745 901644954206585832660559)
      ·
        refine ⟨1352467431309878748990839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901644954206585832660559 1352467431309878748990839)
        ·
          refine ⟨2028701146964818123486259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352467431309878748990839 2028701146964818123486259)
          ·
            refine ⟨3043051720447227185229389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028701146964818123486259 3043051720447227185229389)
            ·
              refine ⟨1141144395167710194461021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3043051720447227185229389 1141144395167710194461021)
              ·
                refine ⟨427929148187891322922883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1141144395167710194461021 427929148187891322922883)
                ·
                  refine ⟨641893722281836984384325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427929148187891322922883 641893722281836984384325)
                  ·
                    refine ⟨120355072927844434572061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 641893722281836984384325 120355072927844434572061)
                    ·
                      rfl

theorem cell22_351586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_351586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351586 prefixEnd_351586 := by exact prefixLift 351586
  have htrace : WordTrace (prefixWord ++ tailWord_351586) baseStart_351586 baseEnd_351586 := by
    simpa [prefixWord, tailWord_351586, baseEnd_351586] using wordTrace_append hprefix tailTrace_351586
  have hstable : (prefixWord ++ tailWord_351586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351586).length < 2 ^ (prefixWord ++ tailWord_351586).sum := by decide
  have hdescent : baseEnd_351586 < baseStart_351586 := by decide
  rcases family_descends (prefixWord ++ tailWord_351586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351599 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 4, 3]
def baseStart_351599 : Nat := 118140960795 + 351599 * 2 ^ 59
def prefixEnd_351599 : Nat := 4983230072969 + 3 ^ 40 * 351599 * 2
def baseEnd_351599 : Nat := 120359523093516733997021

theorem tailTrace_351599 : CollatzResearch.WordTrace tailWord_351599 prefixEnd_351599 120359523093516733997021 := by
  unfold tailWord_351599
  simp only [CollatzResearch.WordTrace]
  refine ⟨12823869053224346173617851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8549246035482897449078567 12823869053224346173617851)
  ·
    refine ⟨19235803579836519260426777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12823869053224346173617851 19235803579836519260426777)
    ·
      refine ⟨14426852684877389445320083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19235803579836519260426777 14426852684877389445320083)
      ·
        refine ⟨21640279027316084167980125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14426852684877389445320083 21640279027316084167980125)
        ·
          refine ⟨8115104635243531562992547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21640279027316084167980125 8115104635243531562992547)
          ·
            refine ⟨12172656952865297344488821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115104635243531562992547 12172656952865297344488821)
            ·
              refine ⟨1141186589331121626045827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12172656952865297344488821 1141186589331121626045827)
              ·
                refine ⟨1711779883996682439068741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141186589331121626045827 1711779883996682439068741)
                ·
                  refine ⟨320958728249377957325389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711779883996682439068741 320958728249377957325389)
                  ·
                    refine ⟨120359523093516733997021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320958728249377957325389 120359523093516733997021)
                    ·
                      rfl

theorem cell22_351599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_351599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351599 prefixEnd_351599 := by exact prefixLift 351599
  have htrace : WordTrace (prefixWord ++ tailWord_351599) baseStart_351599 baseEnd_351599 := by
    simpa [prefixWord, tailWord_351599, baseEnd_351599] using wordTrace_append hprefix tailTrace_351599
  have hstable : (prefixWord ++ tailWord_351599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351599).length < 2 ^ (prefixWord ++ tailWord_351599).sum := by decide
  have hdescent : baseEnd_351599 < baseStart_351599 := by decide
  rcases family_descends (prefixWord ++ tailWord_351599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351612 : List Nat := [2, 2, 2, 1, 1, 1, 4, 9]
def baseStart_351612 : Nat := 118140960795 + 351612 * 2 ^ 59
def prefixEnd_351612 : Nat := 4983230072969 + 3 ^ 40 * 351612 * 2
def baseEnd_351612 : Nat := 13373774806576559269109

theorem tailTrace_351612 : CollatzResearch.WordTrace tailWord_351612 prefixEnd_351612 13373774806576559269109 := by
  unfold tailWord_351612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412171601088624696920545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8549562134784832929227393 6412171601088624696920545)
  ·
    refine ⟨4809128700816468522690409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6412171601088624696920545 4809128700816468522690409)
    ·
      refine ⟨3606846525612351392017807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4809128700816468522690409 3606846525612351392017807)
      ·
        refine ⟨5410269788418527088026711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3606846525612351392017807 5410269788418527088026711)
        ·
          refine ⟨8115404682627790632040067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410269788418527088026711 8115404682627790632040067)
          ·
            refine ⟨12173107023941685948060101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115404682627790632040067 12173107023941685948060101)
            ·
              refine ⟨2282457566989066115261269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12173107023941685948060101 2282457566989066115261269)
              ·
                refine ⟨13373774806576559269109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2282457566989066115261269 13373774806576559269109)
                ·
                  rfl

theorem cell22_351612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 9].length) (baseStart_351612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351612 prefixEnd_351612 := by exact prefixLift 351612
  have htrace : WordTrace (prefixWord ++ tailWord_351612) baseStart_351612 baseEnd_351612 := by
    simpa [prefixWord, tailWord_351612, baseEnd_351612] using wordTrace_append hprefix tailTrace_351612
  have hstable : (prefixWord ++ tailWord_351612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351612).length < 2 ^ (prefixWord ++ tailWord_351612).sum := by decide
  have hdescent : baseEnd_351612 < baseStart_351612 := by decide
  rcases family_descends (prefixWord ++ tailWord_351612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351627 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 2, 7]
def baseStart_351627 : Nat := 118140960795 + 351627 * 2 ^ 59
def prefixEnd_351627 : Nat := 4983230072969 + 3 ^ 40 * 351627 * 2
def baseEnd_351627 : Nat := 120369108065733994296935

theorem tailTrace_351627 : CollatzResearch.WordTrace tailWord_351627 prefixEnd_351627 120369108065733994296935 := by
  unfold tailWord_351627
  simp only [CollatzResearch.WordTrace]
  refine ⟨12824890297122906955637135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8549926864748604637091423 12824890297122906955637135)
  ·
    refine ⟨19237335445684360433455703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12824890297122906955637135 19237335445684360433455703)
    ·
      refine ⟨28856003168526540650183555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19237335445684360433455703 28856003168526540650183555)
      ·
        refine ⟨43284004752789810975275333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28856003168526540650183555 43284004752789810975275333)
        ·
          refine ⟨8115750891148089557864125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43284004752789810975275333 8115750891148089557864125)
          ·
            refine ⟨3043406584180533584199047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8115750891148089557864125 3043406584180533584199047)
            ·
              refine ⟨4565109876270800376298571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043406584180533584199047 4565109876270800376298571)
              ·
                refine ⟨6847664814406200564447857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565109876270800376298571 6847664814406200564447857)
                ·
                  refine ⟨5135748610804650423335893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6847664814406200564447857 5135748610804650423335893)
                  ·
                    refine ⟨120369108065733994296935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5135748610804650423335893 120369108065733994296935)
                    ·
                      rfl

theorem cell22_351627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_351627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351627 prefixEnd_351627 := by exact prefixLift 351627
  have htrace : WordTrace (prefixWord ++ tailWord_351627) baseStart_351627 baseEnd_351627 := by
    simpa [prefixWord, tailWord_351627, baseEnd_351627] using wordTrace_append hprefix tailTrace_351627
  have hstable : (prefixWord ++ tailWord_351627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351627).length < 2 ^ (prefixWord ++ tailWord_351627).sum := by decide
  have hdescent : baseEnd_351627 < baseStart_351627 := by decide
  rcases family_descends (prefixWord ++ tailWord_351627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351751 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 1, 5]
def baseStart_351751 : Nat := 118140960795 + 351751 * 2 ^ 59
def prefixEnd_351751 : Nat := 4983230072969 + 3 ^ 40 * 351751 * 2
def baseEnd_351751 : Nat := 120411555799839004196555

theorem tailTrace_351751 : CollatzResearch.WordTrace tailWord_351751 prefixEnd_351751 120411555799839004196555 := by
  unfold tailWord_351751
  simp only [CollatzResearch.WordTrace]
  refine ⟨12829412948673676133151107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8552941965782450755434071 12829412948673676133151107)
  ·
    refine ⟨19244119423010514199726661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12829412948673676133151107 19244119423010514199726661)
    ·
      refine ⟨3608272391814471412448749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19244119423010514199726661 3608272391814471412448749)
      ·
        refine ⟨1353102146930426779668281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3608272391814471412448749 1353102146930426779668281)
        ·
          refine ⟨1014826610197820084751211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1353102146930426779668281 1014826610197820084751211)
          ·
            refine ⟨1522239915296730127126817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014826610197820084751211 1522239915296730127126817)
            ·
              refine ⟨1141679936472547595345113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522239915296730127126817 1141679936472547595345113)
              ·
                refine ⟨856259952354410696508835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141679936472547595345113 856259952354410696508835)
                ·
                  refine ⟨1284389928531616044763253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856259952354410696508835 1284389928531616044763253)
                  ·
                    refine ⟨120411555799839004196555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1284389928531616044763253 120411555799839004196555)
                    ·
                      rfl

theorem cell22_351751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_351751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351751 prefixEnd_351751 := by exact prefixLift 351751
  have htrace : WordTrace (prefixWord ++ tailWord_351751) baseStart_351751 baseEnd_351751 := by
    simpa [prefixWord, tailWord_351751, baseEnd_351751] using wordTrace_append hprefix tailTrace_351751
  have hstable : (prefixWord ++ tailWord_351751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351751).length < 2 ^ (prefixWord ++ tailWord_351751).sum := by decide
  have hdescent : baseEnd_351751 < baseStart_351751 := by decide
  rcases family_descends (prefixWord ++ tailWord_351751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351755 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 1, 4]
def baseStart_351755 : Nat := 118140960795 + 351755 * 2 ^ 59
def prefixEnd_351755 : Nat := 4983230072969 + 3 ^ 40 * 351755 * 2
def baseEnd_351755 : Nat := 120412925081584327096543

theorem tailTrace_351755 : CollatzResearch.WordTrace tailWord_351755 prefixEnd_351755 120412925081584327096543 := by
  unfold tailWord_351755
  simp only [CollatzResearch.WordTrace]
  refine ⟨12829558840659184816296719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8553039227106123210864479 12829558840659184816296719)
  ·
    refine ⟨19244338260988777224445079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12829558840659184816296719 19244338260988777224445079)
    ·
      refine ⟨28866507391483165836667619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19244338260988777224445079 28866507391483165836667619)
      ·
        refine ⟨43299761087224748755001429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28866507391483165836667619 43299761087224748755001429)
        ·
          refine ⟨507419075240915024472673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 43299761087224748755001429 507419075240915024472673)
          ·
            refine ⟨380564306430686268354505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507419075240915024472673 380564306430686268354505)
            ·
              refine ⟨285423229823014701265879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380564306430686268354505 285423229823014701265879)
              ·
                refine ⟨428134844734522051898819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285423229823014701265879 428134844734522051898819)
                ·
                  refine ⟨642202267101783077848229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428134844734522051898819 642202267101783077848229)
                  ·
                    refine ⟨120412925081584327096543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 642202267101783077848229 120412925081584327096543)
                    ·
                      rfl

theorem cell22_351755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 4].length) (baseStart_351755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351755 prefixEnd_351755 := by exact prefixLift 351755
  have htrace : WordTrace (prefixWord ++ tailWord_351755) baseStart_351755 baseEnd_351755 := by
    simpa [prefixWord, tailWord_351755, baseEnd_351755] using wordTrace_append hprefix tailTrace_351755
  have hstable : (prefixWord ++ tailWord_351755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351755).length < 2 ^ (prefixWord ++ tailWord_351755).sum := by decide
  have hdescent : baseEnd_351755 < baseStart_351755 := by decide
  rcases family_descends (prefixWord ++ tailWord_351755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351768 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 4, 3]
def baseStart_351768 : Nat := 118140960795 + 351768 * 2 ^ 59
def prefixEnd_351768 : Nat := 4983230072969 + 3 ^ 40 * 351768 * 2
def baseEnd_351768 : Nat := 120417375247256626521503

theorem tailTrace_351768 : CollatzResearch.WordTrace tailWord_351768 prefixEnd_351768 120417375247256626521503 := by
  unfold tailWord_351768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415016494806044018259979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8553355326408058691013305 6415016494806044018259979)
  ·
    refine ⟨9622524742209066027389969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6415016494806044018259979 9622524742209066027389969)
    ·
      refine ⟨7216893556656799520542477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9622524742209066027389969 7216893556656799520542477)
      ·
        refine ⟨2706335083746299820203429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7216893556656799520542477 2706335083746299820203429)
        ·
          refine ⟨507437828202431216288143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2706335083746299820203429 507437828202431216288143)
          ·
            refine ⟨761156742303646824432215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507437828202431216288143 761156742303646824432215)
            ·
              refine ⟨1141735113455470236648323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761156742303646824432215 1141735113455470236648323)
              ·
                refine ⟨1712602670183205354972485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141735113455470236648323 1712602670183205354972485)
                ·
                  refine ⟨321113000659351004057341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1712602670183205354972485 321113000659351004057341)
                  ·
                    refine ⟨120417375247256626521503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321113000659351004057341 120417375247256626521503)
                    ·
                      rfl

theorem cell22_351768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_351768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351768 prefixEnd_351768 := by exact prefixLift 351768
  have htrace : WordTrace (prefixWord ++ tailWord_351768) baseStart_351768 baseEnd_351768 := by
    simpa [prefixWord, tailWord_351768, baseEnd_351768] using wordTrace_append hprefix tailTrace_351768
  have hstable : (prefixWord ++ tailWord_351768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351768).length < 2 ^ (prefixWord ++ tailWord_351768).sum := by decide
  have hdescent : baseEnd_351768 < baseStart_351768 := by decide
  rcases family_descends (prefixWord ++ tailWord_351768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351798 : List Nat := [5, 1, 2, 1, 3, 1, 1, 8]
def baseStart_351798 : Nat := 118140960795 + 351798 * 2 ^ 59
def prefixEnd_351798 : Nat := 4983230072969 + 3 ^ 40 * 351798 * 2
def baseEnd_351798 : Nat := 13380849428927394252379

theorem tailTrace_351798 : CollatzResearch.WordTrace tailWord_351798 prefixEnd_351798 13380849428927394252379 := by
  unfold tailWord_351798
  simp only [CollatzResearch.WordTrace]
  refine ⟨801945448718962697507003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8554084786335602106741365 801945448718962697507003)
  ·
    refine ⟨1202918173078444046260505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 801945448718962697507003 1202918173078444046260505)
    ·
      refine ⟨902188629808833034695379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1202918173078444046260505 902188629808833034695379)
      ·
        refine ⟨1353282944713249552043069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902188629808833034695379 1353282944713249552043069)
        ·
          refine ⟨507481104267468582016151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1353282944713249552043069 507481104267468582016151)
          ·
            refine ⟨761221656401202873024227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507481104267468582016151 761221656401202873024227)
            ·
              refine ⟨1141832484601804309536341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761221656401202873024227 1141832484601804309536341)
              ·
                refine ⟨13380849428927394252379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1141832484601804309536341 13380849428927394252379)
                ·
                  rfl

theorem cell22_351798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_351798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351798 prefixEnd_351798 := by exact prefixLift 351798
  have htrace : WordTrace (prefixWord ++ tailWord_351798) baseStart_351798 baseEnd_351798 := by
    simpa [prefixWord, tailWord_351798, baseEnd_351798] using wordTrace_append hprefix tailTrace_351798
  have hstable : (prefixWord ++ tailWord_351798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351798).length < 2 ^ (prefixWord ++ tailWord_351798).sum := by decide
  have hdescent : baseEnd_351798 < baseStart_351798 := by decide
  rcases family_descends (prefixWord ++ tailWord_351798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351826 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_351826 : Nat := 118140960795 + 351826 * 2 ^ 59
def prefixEnd_351826 : Nat := 4983230072969 + 3 ^ 40 * 351826 * 2
def baseEnd_351826 : Nat := 40145743277521269523775

theorem tailTrace_351826 : CollatzResearch.WordTrace tailWord_351826 prefixEnd_351826 40145743277521269523775 := by
  unfold tailWord_351826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3208037105850490985532833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8554765615601309294754221 3208037105850490985532833)
  ·
    refine ⟨2406027829387868239149625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3208037105850490985532833 2406027829387868239149625)
    ·
      refine ⟨1804520872040901179362219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2406027829387868239149625 1804520872040901179362219)
      ·
        refine ⟨2706781308061351769043329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804520872040901179362219 2706781308061351769043329)
        ·
          refine ⟨2030085981046013826782497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2706781308061351769043329 2030085981046013826782497)
          ·
            refine ⟨1522564485784510370086873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2030085981046013826782497 1522564485784510370086873)
            ·
              refine ⟨1141923364338382777565155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522564485784510370086873 1141923364338382777565155)
              ·
                refine ⟨1712885046507574166347733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141923364338382777565155 1712885046507574166347733)
                ·
                  refine ⟨40145743277521269523775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1712885046507574166347733 40145743277521269523775)
                  ·
                    rfl

theorem cell22_351826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_351826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351826 prefixEnd_351826 := by exact prefixLift 351826
  have htrace : WordTrace (prefixWord ++ tailWord_351826) baseStart_351826 baseEnd_351826 := by
    simpa [prefixWord, tailWord_351826, baseEnd_351826] using wordTrace_append hprefix tailTrace_351826
  have hstable : (prefixWord ++ tailWord_351826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351826).length < 2 ^ (prefixWord ++ tailWord_351826).sum := by decide
  have hdescent : baseEnd_351826 < baseStart_351826 := by decide
  rcases family_descends (prefixWord ++ tailWord_351826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351839 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 10]
def baseStart_351839 : Nat := 118140960795 + 351839 * 2 ^ 59
def prefixEnd_351839 : Nat := 4983230072969 + 3 ^ 40 * 351839 * 2
def baseEnd_351839 : Nat := 120441679998236107996285

theorem tailTrace_351839 : CollatzResearch.WordTrace tailWord_351839 prefixEnd_351839 120441679998236107996285 := by
  unfold tailWord_351839
  simp only [CollatzResearch.WordTrace]
  refine ⟨12832622572354867162354571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8555081714903244774903047 12832622572354867162354571)
  ·
    refine ⟨19248933858532300743531857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12832622572354867162354571 19248933858532300743531857)
    ·
      refine ⟨14436700393899225557648893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19248933858532300743531857 14436700393899225557648893)
      ·
        refine ⟨5413762647712209584118335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14436700393899225557648893 5413762647712209584118335)
        ·
          refine ⟨8120643971568314376177503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413762647712209584118335 8120643971568314376177503)
          ·
            refine ⟨12180965957352471564266255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8120643971568314376177503 12180965957352471564266255)
            ·
              refine ⟨18271448936028707346399383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12180965957352471564266255 18271448936028707346399383)
              ·
                refine ⟨27407173404043061019599075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18271448936028707346399383 27407173404043061019599075)
                ·
                  refine ⟨41110760106064591529398613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27407173404043061019599075 41110760106064591529398613)
                  ·
                    refine ⟨120441679998236107996285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 41110760106064591529398613 120441679998236107996285)
                    ·
                      rfl

theorem cell22_351839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_351839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351839 prefixEnd_351839 := by exact prefixLift 351839
  have htrace : WordTrace (prefixWord ++ tailWord_351839) baseStart_351839 baseEnd_351839 := by
    simpa [prefixWord, tailWord_351839, baseEnd_351839] using wordTrace_append hprefix tailTrace_351839
  have hstable : (prefixWord ++ tailWord_351839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351839).length < 2 ^ (prefixWord ++ tailWord_351839).sum := by decide
  have hdescent : baseEnd_351839 < baseStart_351839 := by decide
  rcases family_descends (prefixWord ++ tailWord_351839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351843 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 5]
def baseStart_351843 : Nat := 118140960795 + 351843 * 2 ^ 59
def prefixEnd_351843 : Nat := 4983230072969 + 3 ^ 40 * 351843 * 2
def baseEnd_351843 : Nat := 40147683093327143632091

theorem tailTrace_351843 : CollatzResearch.WordTrace tailWord_351843 prefixEnd_351843 40147683093327143632091 := by
  unfold tailWord_351843
  simp only [CollatzResearch.WordTrace]
  refine ⟨12832768464340375845500183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8555178976226917230333455 12832768464340375845500183)
  ·
    refine ⟨19249152696510563768250275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12832768464340375845500183 19249152696510563768250275)
    ·
      refine ⟨28873729044765845652375413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19249152696510563768250275 28873729044765845652375413)
      ·
        refine ⟨2706912097946798029910195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28873729044765845652375413 2706912097946798029910195)
        ·
          refine ⟨4060368146920197044865293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706912097946798029910195 4060368146920197044865293)
          ·
            refine ⟨1522638055095073891824485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4060368146920197044865293 1522638055095073891824485)
            ·
              refine ⟨285494635330326354717091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1522638055095073891824485 285494635330326354717091)
              ·
                refine ⟨428241952995489532075637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285494635330326354717091 428241952995489532075637)
                ·
                  refine ⟨40147683093327143632091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428241952995489532075637 40147683093327143632091)
                  ·
                    rfl

theorem cell22_351843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 5].length) (baseStart_351843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351843 prefixEnd_351843 := by exact prefixLift 351843
  have htrace : WordTrace (prefixWord ++ tailWord_351843) baseStart_351843 baseEnd_351843 := by
    simpa [prefixWord, tailWord_351843, baseEnd_351843] using wordTrace_append hprefix tailTrace_351843
  have hstable : (prefixWord ++ tailWord_351843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351843).length < 2 ^ (prefixWord ++ tailWord_351843).sum := by decide
  have hdescent : baseEnd_351843 < baseStart_351843 := by decide
  rcases family_descends (prefixWord ++ tailWord_351843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351901 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_351901 : Nat := 118140960795 + 351901 * 2 ^ 59
def prefixEnd_351901 : Nat := 4983230072969 + 3 ^ 40 * 351901 * 2
def baseEnd_351901 : Nat := 120462903865288612946095

theorem tailTrace_351901 : CollatzResearch.WordTrace tailWord_351901 prefixEnd_351901 120462903865288612946095 := by
  unfold tailWord_351901
  simp only [CollatzResearch.WordTrace]
  refine ⟨12834883898130251751111557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8556589265420167834074371 12834883898130251751111557)
  ·
    refine ⟨2406540730899422203333417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12834883898130251751111557 2406540730899422203333417)
    ·
      refine ⟨1804905548174566652500063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2406540730899422203333417 1804905548174566652500063)
      ·
        refine ⟨2707358322261849978750095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804905548174566652500063 2707358322261849978750095)
        ·
          refine ⟨4061037483392774968125143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707358322261849978750095 4061037483392774968125143)
          ·
            refine ⟨6091556225089162452187715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4061037483392774968125143 6091556225089162452187715)
            ·
              refine ⟨9137334337633743678281573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6091556225089162452187715 9137334337633743678281573)
              ·
                refine ⟨1713250188306326939677795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9137334337633743678281573 1713250188306326939677795)
                ·
                  refine ⟨2569875282459490409516693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713250188306326939677795 2569875282459490409516693)
                  ·
                    refine ⟨120462903865288612946095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2569875282459490409516693 120462903865288612946095)
                    ·
                      rfl

theorem cell22_351901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_351901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_351901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_351901 prefixEnd_351901 := by exact prefixLift 351901
  have htrace : WordTrace (prefixWord ++ tailWord_351901) baseStart_351901 baseEnd_351901 := by
    simpa [prefixWord, tailWord_351901, baseEnd_351901] using wordTrace_append hprefix tailTrace_351901
  have hstable : (prefixWord ++ tailWord_351901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351901).length < 2 ^ (prefixWord ++ tailWord_351901).sum := by decide
  have hdescent : baseEnd_351901 < baseStart_351901 := by decide
  rcases family_descends (prefixWord ++ tailWord_351901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352008 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_352008 : Nat := 118140960795 + 352008 * 2 ^ 59
def prefixEnd_352008 : Nat := 4983230072969 + 3 ^ 40 * 352008 * 2
def baseEnd_352008 : Nat := 120499532151976000520767

theorem tailTrace_352008 : CollatzResearch.WordTrace tailWord_352008 prefixEnd_352008 120499532151976000520767 := by
  unfold tailWord_352008
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419393254371304512628339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8559191005828406016837785 6419393254371304512628339)
  ·
    refine ⟨9629089881556956768942509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6419393254371304512628339 9629089881556956768942509)
    ·
      refine ⟨3610908705583858788353441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9629089881556956768942509 3610908705583858788353441)
      ·
        refine ⟨2708181529187894091265081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3610908705583858788353441 2708181529187894091265081)
        ·
          refine ⟨2031136146890920568448811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2708181529187894091265081 2031136146890920568448811)
          ·
            refine ⟨3046704220336380852673217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031136146890920568448811 3046704220336380852673217)
            ·
              refine ⟨2285028165252285639504913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046704220336380852673217 2285028165252285639504913)
              ·
                refine ⟨1713771123939214229628685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285028165252285639504913 1713771123939214229628685)
                ·
                  refine ⟨642664171477205336110757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1713771123939214229628685 642664171477205336110757)
                  ·
                    refine ⟨120499532151976000520767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 642664171477205336110757 120499532151976000520767)
                    ·
                      rfl

theorem cell22_352008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_352008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352008 prefixEnd_352008 := by exact prefixLift 352008
  have htrace : WordTrace (prefixWord ++ tailWord_352008) baseStart_352008 baseEnd_352008 := by
    simpa [prefixWord, tailWord_352008, baseEnd_352008] using wordTrace_append hprefix tailTrace_352008
  have hstable : (prefixWord ++ tailWord_352008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352008).length < 2 ^ (prefixWord ++ tailWord_352008).sum := by decide
  have hdescent : baseEnd_352008 < baseStart_352008 := by decide
  rcases family_descends (prefixWord ++ tailWord_352008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352051 : List Nat := [1, 1, 1, 2, 17]
def baseStart_352051 : Nat := 118140960795 + 352051 * 2 ^ 59
def prefixEnd_352051 : Nat := 4983230072969 + 3 ^ 40 * 352051 * 2
def baseEnd_352051 : Nat := 495943423583284862945

theorem tailTrace_352051 : CollatzResearch.WordTrace tailWord_352051 prefixEnd_352051 495943423583284862945 := by
  unfold tailWord_352051
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840354847586827369072007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8560236565057884912714671 12840354847586827369072007)
  ·
    refine ⟨19260532271380241053608011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12840354847586827369072007 19260532271380241053608011)
    ·
      refine ⟨28890798407070361580412017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19260532271380241053608011 28890798407070361580412017)
      ·
        refine ⟨21668098805302771185309013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28890798407070361580412017 21668098805302771185309013)
        ·
          refine ⟨495943423583284862945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 21668098805302771185309013 495943423583284862945)
          ·
            rfl

theorem cell22_352051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 17].length) (baseStart_352051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352051 prefixEnd_352051 := by exact prefixLift 352051
  have htrace : WordTrace (prefixWord ++ tailWord_352051) baseStart_352051 baseEnd_352051 := by
    simpa [prefixWord, tailWord_352051, baseEnd_352051] using wordTrace_append hprefix tailTrace_352051
  have hstable : (prefixWord ++ tailWord_352051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352051).length < 2 ^ (prefixWord ++ tailWord_352051).sum := by decide
  have hdescent : baseEnd_352051 < baseStart_352051 := by decide
  rcases family_descends (prefixWord ++ tailWord_352051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352085 : List Nat := [1, 3, 2, 2, 2, 3, 3, 6]
def baseStart_352085 : Nat := 118140960795 + 352085 * 2 ^ 59
def prefixEnd_352085 : Nat := 4983230072969 + 3 ^ 40 * 352085 * 2
def baseEnd_352085 : Nat := 13391765647285940705059

theorem tailTrace_352085 : CollatzResearch.WordTrace tailWord_352085 prefixEnd_352085 13391765647285940705059 := by
  unfold tailWord_352085
  simp only [CollatzResearch.WordTrace]
  refine ⟨12841594929463651175809709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8561063286309100783873139 12841594929463651175809709)
  ·
    refine ⟨4815598098548869190928641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12841594929463651175809709 4815598098548869190928641)
    ·
      refine ⟨3611698573911651893196481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4815598098548869190928641 3611698573911651893196481)
      ·
        refine ⟨2708773930433738919897361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3611698573911651893196481 2708773930433738919897361)
        ·
          refine ⟨2031580447825304189923021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2708773930433738919897361 2031580447825304189923021)
          ·
            refine ⟨761842667934489071221133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2031580447825304189923021 761842667934489071221133)
            ·
              refine ⟨285691000475433401707925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 761842667934489071221133 285691000475433401707925)
              ·
                refine ⟨13391765647285940705059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 285691000475433401707925 13391765647285940705059)
                ·
                  rfl

theorem cell22_352085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 6].length) (baseStart_352085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352085 prefixEnd_352085 := by exact prefixLift 352085
  have htrace : WordTrace (prefixWord ++ tailWord_352085) baseStart_352085 baseEnd_352085 := by
    simpa [prefixWord, tailWord_352085, baseEnd_352085] using wordTrace_append hprefix tailTrace_352085
  have hstable : (prefixWord ++ tailWord_352085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352085).length < 2 ^ (prefixWord ++ tailWord_352085).sum := by decide
  have hdescent : baseEnd_352085 < baseStart_352085 := by decide
  rcases family_descends (prefixWord ++ tailWord_352085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352087 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 2, 4]
def baseStart_352087 : Nat := 118140960795 + 352087 * 2 ^ 59
def prefixEnd_352087 : Nat := 4983230072969 + 3 ^ 40 * 352087 * 2
def baseEnd_352087 : Nat := 120526575466446127795525

theorem tailTrace_352087 : CollatzResearch.WordTrace tailWord_352087 prefixEnd_352087 120526575466446127795525 := by
  unfold tailWord_352087
  simp only [CollatzResearch.WordTrace]
  refine ⟨12841667875456405517382515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8561111916970937011588343 12841667875456405517382515)
  ·
    refine ⟨19262501813184608276073773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12841667875456405517382515 19262501813184608276073773)
    ·
      refine ⟨7223438179944228103527665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19262501813184608276073773 7223438179944228103527665)
      ·
        refine ⟨5417578634958171077645749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7223438179944228103527665 5417578634958171077645749)
        ·
          refine ⟨507897997027328538529289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5417578634958171077645749 507897997027328538529289)
          ·
            refine ⟨380923497770496403896967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507897997027328538529289 380923497770496403896967)
            ·
              refine ⟨571385246655744605845451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380923497770496403896967 571385246655744605845451)
              ·
                refine ⟨857077869983616908768177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571385246655744605845451 857077869983616908768177)
                ·
                  refine ⟨642808402487712681576133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 857077869983616908768177 642808402487712681576133)
                  ·
                    refine ⟨120526575466446127795525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 642808402487712681576133 120526575466446127795525)
                    ·
                      rfl

theorem cell22_352087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_352087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352087 prefixEnd_352087 := by exact prefixLift 352087
  have htrace : WordTrace (prefixWord ++ tailWord_352087) baseStart_352087 baseEnd_352087 := by
    simpa [prefixWord, tailWord_352087, baseEnd_352087] using wordTrace_append hprefix tailTrace_352087
  have hstable : (prefixWord ++ tailWord_352087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352087).length < 2 ^ (prefixWord ++ tailWord_352087).sum := by decide
  have hdescent : baseEnd_352087 < baseStart_352087 := by decide
  rcases family_descends (prefixWord ++ tailWord_352087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352106 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_352106 : Nat := 118140960795 + 352106 * 2 ^ 59
def prefixEnd_352106 : Nat := 4983230072969 + 3 ^ 40 * 352106 * 2
def baseEnd_352106 : Nat := 120533079554736411570467

theorem tailTrace_352106 : CollatzResearch.WordTrace tailWord_352106 prefixEnd_352106 120533079554736411570467 := by
  unfold tailWord_352106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210590215596892940581043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8561573908258381174882781 3210590215596892940581043)
  ·
    refine ⟨4815885323395339410871565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3210590215596892940581043 4815885323395339410871565)
    ·
      refine ⟨1805956996273252279076837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4815885323395339410871565 1805956996273252279076837)
      ·
        refine ⟨338616936801234802326907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1805956996273252279076837 338616936801234802326907)
        ·
          refine ⟨507925405201852203490361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338616936801234802326907 507925405201852203490361)
          ·
            refine ⟨380944053901389152617771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507925405201852203490361 380944053901389152617771)
            ·
              refine ⟨571416080852083728926657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380944053901389152617771 571416080852083728926657)
              ·
                refine ⟨428562060639062796694993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571416080852083728926657 428562060639062796694993)
                ·
                  refine ⟨321421545479297097521245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428562060639062796694993 321421545479297097521245)
                  ·
                    refine ⟨120533079554736411570467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321421545479297097521245 120533079554736411570467)
                    ·
                      rfl

theorem cell22_352106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_352106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352106 prefixEnd_352106 := by exact prefixLift 352106
  have htrace : WordTrace (prefixWord ++ tailWord_352106) baseStart_352106 baseEnd_352106 := by
    simpa [prefixWord, tailWord_352106, baseEnd_352106] using wordTrace_append hprefix tailTrace_352106
  have hstable : (prefixWord ++ tailWord_352106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352106).length < 2 ^ (prefixWord ++ tailWord_352106).sum := by decide
  have hdescent : baseEnd_352106 < baseStart_352106 := by decide
  rcases family_descends (prefixWord ++ tailWord_352106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352113 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 7]
def baseStart_352113 : Nat := 118140960795 + 352113 * 2 ^ 59
def prefixEnd_352113 : Nat := 4983230072969 + 3 ^ 40 * 352113 * 2
def baseEnd_352113 : Nat := 40178491932596908881815

theorem tailTrace_352113 : CollatzResearch.WordTrace tailWord_352113 prefixEnd_352113 40178491932596908881815 := by
  unfold tailWord_352113
  simp only [CollatzResearch.WordTrace]
  refine ⟨12842616173362211957828993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8561744115574807971885995 12842616173362211957828993)
  ·
    refine ⟨9631962130021658968371745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12842616173362211957828993 9631962130021658968371745)
    ·
      refine ⟨7223971597516244226278809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9631962130021658968371745 7223971597516244226278809)
      ·
        refine ⟨5417978698137183169709107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7223971597516244226278809 5417978698137183169709107)
        ·
          refine ⟨8126968047205774754563661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5417978698137183169709107 8126968047205774754563661)
          ·
            refine ⟨3047613017702165532961373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8126968047205774754563661 3047613017702165532961373)
            ·
              refine ⟨1142854881638312074860515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3047613017702165532961373 1142854881638312074860515)
              ·
                refine ⟨1714282322457468112290773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142854881638312074860515 1714282322457468112290773)
                ·
                  refine ⟨40178491932596908881815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1714282322457468112290773 40178491932596908881815)
                  ·
                    rfl

theorem cell22_352113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_352113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352113 prefixEnd_352113 := by exact prefixLift 352113
  have htrace : WordTrace (prefixWord ++ tailWord_352113) baseStart_352113 baseEnd_352113 := by
    simpa [prefixWord, tailWord_352113, baseEnd_352113] using wordTrace_append hprefix tailTrace_352113
  have hstable : (prefixWord ++ tailWord_352113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352113).length < 2 ^ (prefixWord ++ tailWord_352113).sum := by decide
  have hdescent : baseEnd_352113 < baseStart_352113 := by decide
  rcases family_descends (prefixWord ++ tailWord_352113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352117 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_352117 : Nat := 118140960795 + 352117 * 2 ^ 59
def prefixEnd_352117 : Nat := 4983230072969 + 3 ^ 40 * 352117 * 2
def baseEnd_352117 : Nat := 120536845079536049545433

theorem tailTrace_352117 : CollatzResearch.WordTrace tailWord_352117 prefixEnd_352117 120536845079536049545433 := by
  unfold tailWord_352117
  simp only [CollatzResearch.WordTrace]
  refine ⟨12842762065347720640974605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8561841376898480427316403 12842762065347720640974605)
  ·
    refine ⟨4816035774505395240365477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12842762065347720640974605 4816035774505395240365477)
    ·
      refine ⟨903006707719761607568527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4816035774505395240365477 903006707719761607568527)
      ·
        refine ⟨1354510061579642411352791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903006707719761607568527 1354510061579642411352791)
        ·
          refine ⟨2031765092369463617029187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354510061579642411352791 2031765092369463617029187)
          ·
            refine ⟨3047647638554195425543781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031765092369463617029187 3047647638554195425543781)
            ·
              refine ⟨571433932228911642289459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3047647638554195425543781 571433932228911642289459)
              ·
                refine ⟨857150898343367463434189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571433932228911642289459 857150898343367463434189)
                ·
                  refine ⟨321431586878762798787821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857150898343367463434189 321431586878762798787821)
                  ·
                    refine ⟨120536845079536049545433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321431586878762798787821 120536845079536049545433)
                    ·
                      rfl

theorem cell22_352117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_352117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352117 prefixEnd_352117 := by exact prefixLift 352117
  have htrace : WordTrace (prefixWord ++ tailWord_352117) baseStart_352117 baseEnd_352117 := by
    simpa [prefixWord, tailWord_352117, baseEnd_352117] using wordTrace_append hprefix tailTrace_352117
  have hstable : (prefixWord ++ tailWord_352117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352117).length < 2 ^ (prefixWord ++ tailWord_352117).sum := by decide
  have hdescent : baseEnd_352117 < baseStart_352117 := by decide
  rcases family_descends (prefixWord ++ tailWord_352117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352128 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_352128 : Nat := 118140960795 + 352128 * 2 ^ 59
def prefixEnd_352128 : Nat := 4983230072969 + 3 ^ 40 * 352128 * 2
def baseEnd_352128 : Nat := 120540610604335687520399

theorem tailTrace_352128 : CollatzResearch.WordTrace tailWord_352128 prefixEnd_352128 120540610604335687520399 := by
  unfold tailWord_352128
  simp only [CollatzResearch.WordTrace]
  refine ⟨6421581634153934759812519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8562108845538579679750025 6421581634153934759812519)
  ·
    refine ⟨9632372451230902139718779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6421581634153934759812519 9632372451230902139718779)
    ·
      refine ⟨14448558676846353209578169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9632372451230902139718779 14448558676846353209578169)
      ·
        refine ⟨10836419007634764907183627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14448558676846353209578169 10836419007634764907183627)
        ·
          refine ⟨16254628511452147360775441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10836419007634764907183627 16254628511452147360775441)
          ·
            refine ⟨12190971383589110520581581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16254628511452147360775441 12190971383589110520581581)
            ·
              refine ⟨4571614268845916445218093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12190971383589110520581581 4571614268845916445218093)
              ·
                refine ⟨1714355350817218666956785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4571614268845916445218093 1714355350817218666956785)
                ·
                  refine ⟨1285766513112914000217589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1714355350817218666956785 1285766513112914000217589)
                  ·
                    refine ⟨120540610604335687520399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1285766513112914000217589 120540610604335687520399)
                    ·
                      rfl

theorem cell22_352128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_352128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352128 prefixEnd_352128 := by exact prefixLift 352128
  have htrace : WordTrace (prefixWord ++ tailWord_352128) baseStart_352128 baseEnd_352128 := by
    simpa [prefixWord, tailWord_352128, baseEnd_352128] using wordTrace_append hprefix tailTrace_352128
  have hstable : (prefixWord ++ tailWord_352128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352128).length < 2 ^ (prefixWord ++ tailWord_352128).sum := by decide
  have hdescent : baseEnd_352128 < baseStart_352128 := by decide
  rcases family_descends (prefixWord ++ tailWord_352128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352143 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 9, 4]
def baseStart_352143 : Nat := 118140960795 + 352143 * 2 ^ 59
def prefixEnd_352143 : Nat := 4983230072969 + 3 ^ 40 * 352143 * 2
def baseEnd_352143 : Nat := 120545745410880648395353

theorem tailTrace_352143 : CollatzResearch.WordTrace tailWord_352143 prefixEnd_352143 120545745410880648395353 := by
  unfold tailWord_352143
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843710363253527081421083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8562473575502351387614055 12843710363253527081421083)
  ·
    refine ⟨19265565544880290622131625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12843710363253527081421083 19265565544880290622131625)
    ·
      refine ⟨14449174158660217966598719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19265565544880290622131625 14449174158660217966598719)
      ·
        refine ⟨21673761237990326949898079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14449174158660217966598719 21673761237990326949898079)
        ·
          refine ⟨32510641856985490424847119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21673761237990326949898079 32510641856985490424847119)
          ·
            refine ⟨48765962785478235637270679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32510641856985490424847119 48765962785478235637270679)
            ·
              refine ⟨73148944178217353455906019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48765962785478235637270679 73148944178217353455906019)
              ·
                refine ⟨109723416267326030183859029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73148944178217353455906019 109723416267326030183859029)
                ·
                  refine ⟨642910642191363458108549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 109723416267326030183859029 642910642191363458108549)
                  ·
                    refine ⟨120545745410880648395353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 642910642191363458108549 120545745410880648395353)
                    ·
                      rfl

theorem cell22_352143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_352143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352143 prefixEnd_352143 := by exact prefixLift 352143
  have htrace : WordTrace (prefixWord ++ tailWord_352143) baseStart_352143 baseEnd_352143 := by
    simpa [prefixWord, tailWord_352143, baseEnd_352143] using wordTrace_append hprefix tailTrace_352143
  have hstable : (prefixWord ++ tailWord_352143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352143).length < 2 ^ (prefixWord ++ tailWord_352143).sum := by decide
  have hdescent : baseEnd_352143 < baseStart_352143 := by decide
  rcases family_descends (prefixWord ++ tailWord_352143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352168 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 3, 3]
def baseStart_352168 : Nat := 118140960795 + 352168 * 2 ^ 59
def prefixEnd_352168 : Nat := 4983230072969 + 3 ^ 40 * 352168 * 2
def baseEnd_352168 : Nat := 120554303421788916520277

theorem tailTrace_352168 : CollatzResearch.WordTrace tailWord_352168 prefixEnd_352168 120554303421788916520277 := by
  unfold tailWord_352168
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422311094081478175540579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8563081458775304234054105 6422311094081478175540579)
  ·
    refine ⟨9633466641122217263310869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6422311094081478175540579 9633466641122217263310869)
    ·
      refine ⟨451568748802603934217697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9633466641122217263310869 451568748802603934217697)
      ·
        refine ⟨338676561601952950663273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451568748802603934217697 338676561601952950663273)
        ·
          refine ⟨254007421201464712997455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338676561601952950663273 254007421201464712997455)
          ·
            refine ⟨381011131802197069496183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254007421201464712997455 381011131802197069496183)
            ·
              refine ⟨571516697703295604244275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381011131802197069496183 571516697703295604244275)
              ·
                refine ⟨857275046554943406366413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571516697703295604244275 857275046554943406366413)
                ·
                  refine ⟨321478142458103777387405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857275046554943406366413 321478142458103777387405)
                  ·
                    refine ⟨120554303421788916520277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321478142458103777387405 120554303421788916520277)
                    ·
                      rfl

theorem cell22_352168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_352168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352168 prefixEnd_352168 := by exact prefixLift 352168
  have htrace : WordTrace (prefixWord ++ tailWord_352168) baseStart_352168 baseEnd_352168 := by
    simpa [prefixWord, tailWord_352168, baseEnd_352168] using wordTrace_append hprefix tailTrace_352168
  have hstable : (prefixWord ++ tailWord_352168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352168).length < 2 ^ (prefixWord ++ tailWord_352168).sum := by decide
  have hdescent : baseEnd_352168 < baseStart_352168 := by decide
  rcases family_descends (prefixWord ++ tailWord_352168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352203 : List Nat := [1, 1, 1, 1, 3, 4, 1, 10]
def baseStart_352203 : Nat := 118140960795 + 352203 * 2 ^ 59
def prefixEnd_352203 : Nat := 4983230072969 + 3 ^ 40 * 352203 * 2
def baseEnd_352203 : Nat := 13396253848562276877241

theorem tailTrace_352203 : CollatzResearch.WordTrace tailWord_352203 prefixEnd_352203 13396253848562276877241 := by
  unfold tailWord_352203
  simp only [CollatzResearch.WordTrace]
  refine ⟨12845898743036157328605263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8563932495357438219070175 12845898743036157328605263)
  ·
    refine ⟨19268848114554235992907895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12845898743036157328605263 19268848114554235992907895)
    ·
      refine ⟨28903272171831353989361843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19268848114554235992907895 28903272171831353989361843)
      ·
        refine ⟨43354908257747030984042765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28903272171831353989361843 43354908257747030984042765)
        ·
          refine ⟨16258090596655136619016037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43354908257747030984042765 16258090596655136619016037)
          ·
            refine ⟨3048391986872838116065507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16258090596655136619016037 3048391986872838116065507)
            ·
              refine ⟨4572587980309257174098261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3048391986872838116065507 4572587980309257174098261)
              ·
                refine ⟨13396253848562276877241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4572587980309257174098261 13396253848562276877241)
                ·
                  rfl

theorem cell22_352203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 10].length) (baseStart_352203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352203 prefixEnd_352203 := by exact prefixLift 352203
  have htrace : WordTrace (prefixWord ++ tailWord_352203) baseStart_352203 baseEnd_352203 := by
    simpa [prefixWord, tailWord_352203, baseEnd_352203] using wordTrace_append hprefix tailTrace_352203
  have hstable : (prefixWord ++ tailWord_352203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352203).length < 2 ^ (prefixWord ++ tailWord_352203).sum := by decide
  have hdescent : baseEnd_352203 < baseStart_352203 := by decide
  rcases family_descends (prefixWord ++ tailWord_352203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352226 : List Nat := [3, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_352226 : Nat := 118140960795 + 352226 * 2 ^ 59
def prefixEnd_352226 : Nat := 4983230072969 + 3 ^ 40 * 352226 * 2
def baseEnd_352226 : Nat := 40191386002365366190033

theorem tailTrace_352226 : CollatzResearch.WordTrace tailWord_352226 prefixEnd_352226 40191386002365366190033 := by
  unfold tailWord_352226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3211684405488208064173133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8564491747968554837795021 3211684405488208064173133)
  ·
    refine ⟨1204381652058078024064925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3211684405488208064173133 1204381652058078024064925)
    ·
      refine ⟨451643119521779259024347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1204381652058078024064925 451643119521779259024347)
      ·
        refine ⟨677464679282668888536521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451643119521779259024347 677464679282668888536521)
        ·
          refine ⟨508098509462001666402391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677464679282668888536521 508098509462001666402391)
          ·
            refine ⟨762147764193002499603587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508098509462001666402391 762147764193002499603587)
            ·
              refine ⟨1143221646289503749405381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762147764193002499603587 1143221646289503749405381)
              ·
                refine ⟨214354058679281953013509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1143221646289503749405381 214354058679281953013509)
                ·
                  refine ⟨40191386002365366190033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214354058679281953013509 40191386002365366190033)
                  ·
                    rfl

theorem cell22_352226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_352226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352226 prefixEnd_352226 := by exact prefixLift 352226
  have htrace : WordTrace (prefixWord ++ tailWord_352226) baseStart_352226 baseEnd_352226 := by
    simpa [prefixWord, tailWord_352226, baseEnd_352226] using wordTrace_append hprefix tailTrace_352226
  have hstable : (prefixWord ++ tailWord_352226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352226).length < 2 ^ (prefixWord ++ tailWord_352226).sum := by decide
  have hdescent : baseEnd_352226 < baseStart_352226 := by decide
  rcases family_descends (prefixWord ++ tailWord_352226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352235 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 7, 3]
def baseStart_352235 : Nat := 118140960795 + 352235 * 2 ^ 59
def prefixEnd_352235 : Nat := 4983230072969 + 3 ^ 40 * 352235 * 2
def baseEnd_352235 : Nat := 120577238891023075095071

theorem tailTrace_352235 : CollatzResearch.WordTrace tailWord_352235 prefixEnd_352235 120577238891023075095071 := by
  unfold tailWord_352235
  simp only [CollatzResearch.WordTrace]
  refine ⟨12847065878920226793770159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8564710585946817862513439 12847065878920226793770159)
  ·
    refine ⟨19270598818380340190655239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12847065878920226793770159 19270598818380340190655239)
    ·
      refine ⟨28905898227570510285982859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19270598818380340190655239 28905898227570510285982859)
      ·
        refine ⟨43358847341355765428974289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28905898227570510285982859 43358847341355765428974289)
        ·
          refine ⟨32519135506016824071730717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43358847341355765428974289 32519135506016824071730717)
          ·
            refine ⟨12194675814756309026899019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32519135506016824071730717 12194675814756309026899019)
            ·
              refine ⟨18292013722134463540348529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12194675814756309026899019 18292013722134463540348529)
              ·
                refine ⟨13719010291600847655261397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18292013722134463540348529 13719010291600847655261397)
                ·
                  refine ⟨321539303709394866920189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13719010291600847655261397 321539303709394866920189)
                  ·
                    refine ⟨120577238891023075095071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321539303709394866920189 120577238891023075095071)
                    ·
                      rfl

theorem cell22_352235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 3].length) (baseStart_352235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352235 prefixEnd_352235 := by exact prefixLift 352235
  have htrace : WordTrace (prefixWord ++ tailWord_352235) baseStart_352235 baseEnd_352235 := by
    simpa [prefixWord, tailWord_352235, baseEnd_352235] using wordTrace_append hprefix tailTrace_352235
  have hstable : (prefixWord ++ tailWord_352235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352235).length < 2 ^ (prefixWord ++ tailWord_352235).sum := by decide
  have hdescent : baseEnd_352235 < baseStart_352235 := by decide
  rcases family_descends (prefixWord ++ tailWord_352235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352252 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_352252 : Nat := 118140960795 + 352252 * 2 ^ 59
def prefixEnd_352252 : Nat := 4983230072969 + 3 ^ 40 * 352252 * 2
def baseEnd_352252 : Nat := 120583058338440697420019

theorem tailTrace_352252 : CollatzResearch.WordTrace tailWord_352252 prefixEnd_352252 120583058338440697420019 := by
  unfold tailWord_352252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423842959929319348569505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8565123946572425798092673 6423842959929319348569505)
  ·
    refine ⟨4817882219946989511427129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6423842959929319348569505 4817882219946989511427129)
    ·
      refine ⟨3613411664960242133570347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4817882219946989511427129 3613411664960242133570347)
      ·
        refine ⟨5420117497440363200355521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3613411664960242133570347 5420117497440363200355521)
        ·
          refine ⟨4065088123080272400266641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5420117497440363200355521 4065088123080272400266641)
          ·
            refine ⟨3048816092310204300199981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4065088123080272400266641 3048816092310204300199981)
            ·
              refine ⟨1143306034616326612574993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3048816092310204300199981 1143306034616326612574993)
              ·
                refine ⟨857479525962244959431245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1143306034616326612574993 857479525962244959431245)
                ·
                  refine ⟨321554822235841859786717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 857479525962244959431245 321554822235841859786717)
                  ·
                    refine ⟨120583058338440697420019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321554822235841859786717 120583058338440697420019)
                    ·
                      rfl

theorem cell22_352252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_352252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352252 prefixEnd_352252 := by exact prefixLift 352252
  have htrace : WordTrace (prefixWord ++ tailWord_352252) baseStart_352252 baseEnd_352252 := by
    simpa [prefixWord, tailWord_352252, baseEnd_352252] using wordTrace_append hprefix tailTrace_352252
  have hstable : (prefixWord ++ tailWord_352252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352252).length < 2 ^ (prefixWord ++ tailWord_352252).sum := by decide
  have hdescent : baseEnd_352252 < baseStart_352252 := by decide
  rcases family_descends (prefixWord ++ tailWord_352252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352254 : List Nat := [4, 2, 2, 2, 1, 2, 3, 6]
def baseStart_352254 : Nat := 118140960795 + 352254 * 2 ^ 59
def prefixEnd_352254 : Nat := 4983230072969 + 3 ^ 40 * 352254 * 2
def baseEnd_352254 : Nat := 13398193664368150985557

theorem tailTrace_352254 : CollatzResearch.WordTrace tailWord_352254 prefixEnd_352254 13398193664368150985557 := by
  unfold tailWord_352254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605969858231424129838977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8565172577234262025807877 1605969858231424129838977)
  ·
    refine ⟨1204477393673568097379233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1605969858231424129838977 1204477393673568097379233)
    ·
      refine ⟨903358045255176073034425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1204477393673568097379233 903358045255176073034425)
      ·
        refine ⟨677518533941382054775819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 903358045255176073034425 677518533941382054775819)
        ·
          refine ⟨1016277800912073082163729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677518533941382054775819 1016277800912073082163729)
          ·
            refine ⟨762208350684054811622797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1016277800912073082163729 762208350684054811622797)
            ·
              refine ⟨285828131506520554358549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 762208350684054811622797 285828131506520554358549)
              ·
                refine ⟨13398193664368150985557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 285828131506520554358549 13398193664368150985557)
                ·
                  rfl

theorem cell22_352254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_352254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352254 prefixEnd_352254 := by exact prefixLift 352254
  have htrace : WordTrace (prefixWord ++ tailWord_352254) baseStart_352254 baseEnd_352254 := by
    simpa [prefixWord, tailWord_352254, baseEnd_352254] using wordTrace_append hprefix tailTrace_352254
  have hstable : (prefixWord ++ tailWord_352254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352254).length < 2 ^ (prefixWord ++ tailWord_352254).sum := by decide
  have hdescent : baseEnd_352254 < baseStart_352254 := by decide
  rcases family_descends (prefixWord ++ tailWord_352254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352262 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_352262 : Nat := 118140960795 + 352262 * 2 ^ 59
def prefixEnd_352262 : Nat := 4983230072969 + 3 ^ 40 * 352262 * 2
def baseEnd_352262 : Nat := 120586481542804004669989

theorem tailTrace_352262 : CollatzResearch.WordTrace tailWord_352262 prefixEnd_352262 120586481542804004669989 := by
  unfold tailWord_352262
  simp only [CollatzResearch.WordTrace]
  refine ⟨401501582806950325156345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8565367099881606936668693 401501582806950325156345)
  ·
    refine ⟨301126187105212743867259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 401501582806950325156345 301126187105212743867259)
    ·
      refine ⟨451689280657819115800889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301126187105212743867259 451689280657819115800889)
      ·
        refine ⟨338766960493364336850667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451689280657819115800889 338766960493364336850667)
        ·
          refine ⟨508150440740046505276001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338766960493364336850667 508150440740046505276001)
          ·
            refine ⟨381112830555034878957001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508150440740046505276001 381112830555034878957001)
            ·
              refine ⟨285834622916276159217751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381112830555034878957001 285834622916276159217751)
              ·
                refine ⟨428751934374414238826627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285834622916276159217751 428751934374414238826627)
                ·
                  refine ⟨643127901561621358239941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428751934374414238826627 643127901561621358239941)
                  ·
                    refine ⟨120586481542804004669989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 643127901561621358239941 120586481542804004669989)
                    ·
                      rfl

theorem cell22_352262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_352262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352262 prefixEnd_352262 := by exact prefixLift 352262
  have htrace : WordTrace (prefixWord ++ tailWord_352262) baseStart_352262 baseEnd_352262 := by
    simpa [prefixWord, tailWord_352262, baseEnd_352262] using wordTrace_append hprefix tailTrace_352262
  have hstable : (prefixWord ++ tailWord_352262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352262).length < 2 ^ (prefixWord ++ tailWord_352262).sum := by decide
  have hdescent : baseEnd_352262 < baseStart_352262 := by decide
  rcases family_descends (prefixWord ++ tailWord_352262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352280 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_352280 : Nat := 118140960795 + 352280 * 2 ^ 59
def prefixEnd_352280 : Nat := 4983230072969 + 3 ^ 40 * 352280 * 2
def baseEnd_352280 : Nat := 120592643310657957719933

theorem tailTrace_352280 : CollatzResearch.WordTrace tailWord_352280 prefixEnd_352280 120592643310657957719933 := by
  unfold tailWord_352280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424353581878599739579147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8565804775838132986105529 6424353581878599739579147)
  ·
    refine ⟨9636530372817899609368721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6424353581878599739579147 9636530372817899609368721)
    ·
      refine ⟨7227397779613424707026541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9636530372817899609368721 7227397779613424707026541)
      ·
        refine ⟨2710274167355034265134953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7227397779613424707026541 2710274167355034265134953)
        ·
          refine ⟨2032705625516275698851215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2710274167355034265134953 2032705625516275698851215)
          ·
            refine ⟨3049058438274413548276823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032705625516275698851215 3049058438274413548276823)
            ·
              refine ⟨4573587657411620322415235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3049058438274413548276823 4573587657411620322415235)
              ·
                refine ⟨6860381486117430483622853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573587657411620322415235 6860381486117430483622853)
                ·
                  refine ⟨1286321528647018215679285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6860381486117430483622853 1286321528647018215679285)
                  ·
                    refine ⟨120592643310657957719933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1286321528647018215679285 120592643310657957719933)
                    ·
                      rfl

theorem cell22_352280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_352280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352280 prefixEnd_352280 := by exact prefixLift 352280
  have htrace : WordTrace (prefixWord ++ tailWord_352280) baseStart_352280 baseEnd_352280 := by
    simpa [prefixWord, tailWord_352280, baseEnd_352280] using wordTrace_append hprefix tailTrace_352280
  have hstable : (prefixWord ++ tailWord_352280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352280).length < 2 ^ (prefixWord ++ tailWord_352280).sum := by decide
  have hdescent : baseEnd_352280 < baseStart_352280 := by decide
  rcases family_descends (prefixWord ++ tailWord_352280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352282 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_352282 : Nat := 118140960795 + 352282 * 2 ^ 59
def prefixEnd_352282 : Nat := 4983230072969 + 3 ^ 40 * 352282 * 2
def baseEnd_352282 : Nat := 40197775983843539723309

theorem tailTrace_352282 : CollatzResearch.WordTrace tailWord_352282 prefixEnd_352282 40197775983843539723309 := by
  unfold tailWord_352282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212195027437488455182775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8565853406499969213820733 3212195027437488455182775)
  ·
    refine ⟨4818292541156232682774163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3212195027437488455182775 4818292541156232682774163)
    ·
      refine ⟨7227438811734349024161245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4818292541156232682774163 7227438811734349024161245)
      ·
        refine ⟨2710289554400380884060467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7227438811734349024161245 2710289554400380884060467)
        ·
          refine ⟨4065434331600571326090701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710289554400380884060467 4065434331600571326090701)
          ·
            refine ⟨1524537874350214247284013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4065434331600571326090701 1524537874350214247284013)
            ·
              refine ⟨571701702881330342731505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1524537874350214247284013 571701702881330342731505)
              ·
                refine ⟨428776277160997757048629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571701702881330342731505 428776277160997757048629)
                ·
                  refine ⟨40197775983843539723309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428776277160997757048629 40197775983843539723309)
                  ·
                    rfl

theorem cell22_352282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_352282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352282 prefixEnd_352282 := by exact prefixLift 352282
  have htrace : WordTrace (prefixWord ++ tailWord_352282) baseStart_352282 baseEnd_352282 := by
    simpa [prefixWord, tailWord_352282, baseEnd_352282] using wordTrace_append hprefix tailTrace_352282
  have hstable : (prefixWord ++ tailWord_352282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352282).length < 2 ^ (prefixWord ++ tailWord_352282).sum := by decide
  have hdescent : baseEnd_352282 < baseStart_352282 := by decide
  rcases family_descends (prefixWord ++ tailWord_352282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352325 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_352325 : Nat := 118140960795 + 352325 * 2 ^ 59
def prefixEnd_352325 : Nat := 4983230072969 + 3 ^ 40 * 352325 * 2
def baseEnd_352325 : Nat := 120608047730292840344795

theorem tailTrace_352325 : CollatzResearch.WordTrace tailWord_352325 prefixEnd_352325 120608047730292840344795 := by
  unfold tailWord_352325
  simp only [CollatzResearch.WordTrace]
  refine ⟨12850348448594172164546429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8566898965729448109697619 12850348448594172164546429)
  ·
    refine ⟨4818880668222814561704911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12850348448594172164546429 4818880668222814561704911)
    ·
      refine ⟨7228321002334221842557367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4818880668222814561704911 7228321002334221842557367)
      ·
        refine ⟨10842481503501332763836051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7228321002334221842557367 10842481503501332763836051)
        ·
          refine ⟨16263722255251999145754077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10842481503501332763836051 16263722255251999145754077)
          ·
            refine ⟨6098895845719499679657779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16263722255251999145754077 6098895845719499679657779)
            ·
              refine ⟨9148343768579249519486669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6098895845719499679657779 9148343768579249519486669)
              ·
                refine ⟨3430628913217218569807501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9148343768579249519486669 3430628913217218569807501)
                ·
                  refine ⟨1286485842456456963677813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3430628913217218569807501 1286485842456456963677813)
                  ·
                    refine ⟨120608047730292840344795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1286485842456456963677813 120608047730292840344795)
                    ·
                      rfl

theorem cell22_352325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_352325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352325 prefixEnd_352325 := by exact prefixLift 352325
  have htrace : WordTrace (prefixWord ++ tailWord_352325) baseStart_352325 baseEnd_352325 := by
    simpa [prefixWord, tailWord_352325, baseEnd_352325] using wordTrace_append hprefix tailTrace_352325
  have hstable : (prefixWord ++ tailWord_352325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352325).length < 2 ^ (prefixWord ++ tailWord_352325).sum := by decide
  have hdescent : baseEnd_352325 < baseStart_352325 := by decide
  rcases family_descends (prefixWord ++ tailWord_352325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352350 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_352350 : Nat := 118140960795 + 352350 * 2 ^ 59
def prefixEnd_352350 : Nat := 4983230072969 + 3 ^ 40 * 352350 * 2
def baseEnd_352350 : Nat := 40205535247067036156573

theorem tailTrace_352350 : CollatzResearch.WordTrace tailWord_352350 prefixEnd_352350 40205535247067036156573 := by
  unfold tailWord_352350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1606407534187950179275813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8567506849002400956137669 1606407534187950179275813)
  ·
    refine ⟨301201412660240658614215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1606407534187950179275813 301201412660240658614215)
    ·
      refine ⟨451802118990360987921323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301201412660240658614215 451802118990360987921323)
      ·
        refine ⟨677703178485541481881985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451802118990360987921323 677703178485541481881985)
        ·
          refine ⟨508277383864156111411489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677703178485541481881985 508277383864156111411489)
          ·
            refine ⟨381208037898117083558617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508277383864156111411489 381208037898117083558617)
            ·
              refine ⟨285906028423587812668963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381208037898117083558617 285906028423587812668963)
              ·
                refine ⟨428859042635381719003445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285906028423587812668963 428859042635381719003445)
                ·
                  refine ⟨40205535247067036156573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 428859042635381719003445 40205535247067036156573)
                  ·
                    rfl

theorem cell22_352350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_352350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352350 prefixEnd_352350 := by exact prefixLift 352350
  have htrace : WordTrace (prefixWord ++ tailWord_352350) baseStart_352350 baseEnd_352350 := by
    simpa [prefixWord, tailWord_352350, baseEnd_352350] using wordTrace_append hprefix tailTrace_352350
  have hstable : (prefixWord ++ tailWord_352350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352350).length < 2 ^ (prefixWord ++ tailWord_352350).sum := by decide
  have hdescent : baseEnd_352350 < baseStart_352350 := by decide
  rcases family_descends (prefixWord ++ tailWord_352350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352355 : List Nat := [1, 1, 1, 5, 1, 1, 3, 9]
def baseStart_352355 : Nat := 118140960795 + 352355 * 2 ^ 59
def prefixEnd_352355 : Nat := 4983230072969 + 3 ^ 40 * 352355 * 2
def baseEnd_352355 : Nat := 13402035260375862454967

theorem tailTrace_352355 : CollatzResearch.WordTrace tailWord_352355 prefixEnd_352355 13402035260375862454967 := by
  unfold tailWord_352355
  simp only [CollatzResearch.WordTrace]
  refine ⟨12851442638485487288138519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8567628425656991525425679 12851442638485487288138519)
  ·
    refine ⟨19277163957728230932207779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12851442638485487288138519 19277163957728230932207779)
    ·
      refine ⟨28915745936592346398311669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19277163957728230932207779 28915745936592346398311669)
      ·
        refine ⟨2710851181555532474841719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28915745936592346398311669 2710851181555532474841719)
        ·
          refine ⟨4066276772333298712262579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710851181555532474841719 4066276772333298712262579)
          ·
            refine ⟨6099415158499948068393869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4066276772333298712262579 6099415158499948068393869)
            ·
              refine ⟨2287280684437480525647701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6099415158499948068393869 2287280684437480525647701)
              ·
                refine ⟨13402035260375862454967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2287280684437480525647701 13402035260375862454967)
                ·
                  rfl

theorem cell22_352355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 9].length) (baseStart_352355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352355 prefixEnd_352355 := by exact prefixLift 352355
  have htrace : WordTrace (prefixWord ++ tailWord_352355) baseStart_352355 baseEnd_352355 := by
    simpa [prefixWord, tailWord_352355, baseEnd_352355] using wordTrace_append hprefix tailTrace_352355
  have hstable : (prefixWord ++ tailWord_352355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352355).length < 2 ^ (prefixWord ++ tailWord_352355).sum := by decide
  have hdescent : baseEnd_352355 < baseStart_352355 := by decide
  rcases family_descends (prefixWord ++ tailWord_352355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352359 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 2, 3]
def baseStart_352359 : Nat := 118140960795 + 352359 * 2 ^ 59
def prefixEnd_352359 : Nat := 4983230072969 + 3 ^ 40 * 352359 * 2
def baseEnd_352359 : Nat := 120619686625128084994691

theorem tailTrace_352359 : CollatzResearch.WordTrace tailWord_352359 prefixEnd_352359 120619686625128084994691 := by
  unfold tailWord_352359
  simp only [CollatzResearch.WordTrace]
  refine ⟨12851588530470995971284131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8567725686980663980856087 12851588530470995971284131)
  ·
    refine ⟨19277382795706493956926197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12851588530470995971284131 19277382795706493956926197)
    ·
      refine ⟨1807254637097483808461831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19277382795706493956926197 1807254637097483808461831)
      ·
        refine ⟨2710881955646225712692747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807254637097483808461831 2710881955646225712692747)
        ·
          refine ⟨4066322933469338569039121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710881955646225712692747 4066322933469338569039121)
          ·
            refine ⟨3049742200102003926779341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4066322933469338569039121 3049742200102003926779341)
            ·
              refine ⟨1143653325038251472542253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3049742200102003926779341 1143653325038251472542253)
              ·
                refine ⟨428869996889344302203345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1143653325038251472542253 428869996889344302203345)
                ·
                  refine ⟨321652497667008226652509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428869996889344302203345 321652497667008226652509)
                  ·
                    refine ⟨120619686625128084994691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321652497667008226652509 120619686625128084994691)
                    ·
                      rfl

theorem cell22_352359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_352359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352359 prefixEnd_352359 := by exact prefixLift 352359
  have htrace : WordTrace (prefixWord ++ tailWord_352359) baseStart_352359 baseEnd_352359 := by
    simpa [prefixWord, tailWord_352359, baseEnd_352359] using wordTrace_append hprefix tailTrace_352359
  have hstable : (prefixWord ++ tailWord_352359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352359).length < 2 ^ (prefixWord ++ tailWord_352359).sum := by decide
  have hdescent : baseEnd_352359 < baseStart_352359 := by decide
  rcases family_descends (prefixWord ++ tailWord_352359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352374 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_352374 : Nat := 118140960795 + 352374 * 2 ^ 59
def prefixEnd_352374 : Nat := 4983230072969 + 3 ^ 40 * 352374 * 2
def baseEnd_352374 : Nat := 120624821431673045869645

theorem tailTrace_352374 : CollatzResearch.WordTrace tailWord_352374 prefixEnd_352374 120624821431673045869645 := by
  unfold tailWord_352374
  simp only [CollatzResearch.WordTrace]
  refine ⟨803258476588540845817511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8568090416944435688720117 803258476588540845817511)
  ·
    refine ⟨1204887714882811268726267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 803258476588540845817511 1204887714882811268726267)
    ·
      refine ⟨1807331572324216903089401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1204887714882811268726267 1807331572324216903089401)
      ·
        refine ⟨1355498679243162677317051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1807331572324216903089401 1355498679243162677317051)
        ·
          refine ⟨2033248018864744015975577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355498679243162677317051 2033248018864744015975577)
          ·
            refine ⟨1524936014148558011981683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2033248018864744015975577 1524936014148558011981683)
            ·
              refine ⟨2287404021222837017972525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524936014148558011981683 2287404021222837017972525)
              ·
                refine ⟨857776507958563881739697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2287404021222837017972525 857776507958563881739697)
                ·
                  refine ⟨643332380968922911304773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 857776507958563881739697 643332380968922911304773)
                  ·
                    refine ⟨120624821431673045869645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 643332380968922911304773 120624821431673045869645)
                    ·
                      rfl

theorem cell22_352374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_352374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352374 prefixEnd_352374 := by exact prefixLift 352374
  have htrace : WordTrace (prefixWord ++ tailWord_352374) baseStart_352374 baseEnd_352374 := by
    simpa [prefixWord, tailWord_352374, baseEnd_352374] using wordTrace_append hprefix tailTrace_352374
  have hstable : (prefixWord ++ tailWord_352374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352374).length < 2 ^ (prefixWord ++ tailWord_352374).sum := by decide
  have hdescent : baseEnd_352374 < baseStart_352374 := by decide
  rcases family_descends (prefixWord ++ tailWord_352374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352402 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_352402 : Nat := 118140960795 + 352402 * 2 ^ 59
def prefixEnd_352402 : Nat := 4983230072969 + 3 ^ 40 * 352402 * 2
def baseEnd_352402 : Nat := 120634406403890306169559

theorem tailTrace_352402 : CollatzResearch.WordTrace tailWord_352402 prefixEnd_352402 120634406403890306169559 := by
  unfold tailWord_352402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213289217328803578774865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8568771246210142876732973 3213289217328803578774865)
  ·
    refine ⟨2409966912996602684081149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3213289217328803578774865 2409966912996602684081149)
    ·
      refine ⟨903737592373726006530431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2409966912996602684081149 903737592373726006530431)
      ·
        refine ⟨1355606388560589009795647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903737592373726006530431 1355606388560589009795647)
        ·
          refine ⟨2033409582840883514693471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355606388560589009795647 2033409582840883514693471)
          ·
            refine ⟨3050114374261325272040207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033409582840883514693471 3050114374261325272040207)
            ·
              refine ⟨4575171561391987908060311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050114374261325272040207 4575171561391987908060311)
              ·
                refine ⟨6862757342087981862090467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575171561391987908060311 6862757342087981862090467)
                ·
                  refine ⟨10294136013131972793135701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6862757342087981862090467 10294136013131972793135701)
                  ·
                    refine ⟨120634406403890306169559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10294136013131972793135701 120634406403890306169559)
                    ·
                      rfl

theorem cell22_352402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_352402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352402 prefixEnd_352402 := by exact prefixLift 352402
  have htrace : WordTrace (prefixWord ++ tailWord_352402) baseStart_352402 baseEnd_352402 := by
    simpa [prefixWord, tailWord_352402, baseEnd_352402] using wordTrace_append hprefix tailTrace_352402
  have hstable : (prefixWord ++ tailWord_352402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352402).length < 2 ^ (prefixWord ++ tailWord_352402).sum := by decide
  have hdescent : baseEnd_352402 < baseStart_352402 := by decide
  rcases family_descends (prefixWord ++ tailWord_352402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352492 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_352492 : Nat := 118140960795 + 352492 * 2 ^ 59
def prefixEnd_352492 : Nat := 4983230072969 + 3 ^ 40 * 352492 * 2
def baseEnd_352492 : Nat := 120665215243160071419283

theorem tailTrace_352492 : CollatzResearch.WordTrace tailWord_352492 prefixEnd_352492 120665215243160071419283 := by
  unfold tailWord_352492
  simp only [CollatzResearch.WordTrace]
  refine ⟨6428219719494579842937865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8570959625992773123917153 6428219719494579842937865)
  ·
    refine ⟨4821164789620934882203399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6428219719494579842937865 4821164789620934882203399)
    ·
      refine ⟨7231747184431402323305099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4821164789620934882203399 7231747184431402323305099)
      ·
        refine ⟨10847620776647103484957649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7231747184431402323305099 10847620776647103484957649)
        ·
          refine ⟨8135715582485327613718237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10847620776647103484957649 8135715582485327613718237)
          ·
            refine ⟨3050893343431997855144339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8135715582485327613718237 3050893343431997855144339)
            ·
              refine ⟨4576340015147996782716509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050893343431997855144339 4576340015147996782716509)
              ·
                refine ⟨1716127505680498793518691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4576340015147996782716509 1716127505680498793518691)
                ·
                  refine ⟨2574191258520748190278037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716127505680498793518691 2574191258520748190278037)
                  ·
                    refine ⟨120665215243160071419283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2574191258520748190278037 120665215243160071419283)
                    ·
                      rfl

theorem cell22_352492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_352492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352492 prefixEnd_352492 := by exact prefixLift 352492
  have htrace : WordTrace (prefixWord ++ tailWord_352492) baseStart_352492 baseEnd_352492 := by
    simpa [prefixWord, tailWord_352492, baseEnd_352492] using wordTrace_append hprefix tailTrace_352492
  have hstable : (prefixWord ++ tailWord_352492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352492).length < 2 ^ (prefixWord ++ tailWord_352492).sum := by decide
  have hdescent : baseEnd_352492 < baseStart_352492 := by decide
  rcases family_descends (prefixWord ++ tailWord_352492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352539 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 3, 3]
def baseStart_352539 : Nat := 118140960795 + 352539 * 2 ^ 59
def prefixEnd_352539 : Nat := 4983230072969 + 3 ^ 40 * 352539 * 2
def baseEnd_352539 : Nat := 120681304303667615494139

theorem tailTrace_352539 : CollatzResearch.WordTrace tailWord_352539 prefixEnd_352539 120681304303667615494139 := by
  unfold tailWord_352539
  simp only [CollatzResearch.WordTrace]
  refine ⟨12858153669818886712836671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8572102446545924475224447 12858153669818886712836671)
  ·
    refine ⟨19287230504728330069255007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12858153669818886712836671 19287230504728330069255007)
    ·
      refine ⟨28930845757092495103882511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19287230504728330069255007 28930845757092495103882511)
      ·
        refine ⟨43396268635638742655823767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28930845757092495103882511 43396268635638742655823767)
        ·
          refine ⟨65094402953458113983735651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43396268635638742655823767 65094402953458113983735651)
          ·
            refine ⟨97641604430187170975603477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65094402953458113983735651 97641604430187170975603477)
            ·
              refine ⟨4576950207665023639481413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97641604430187170975603477 4576950207665023639481413)
              ·
                refine ⟨858178163937191932402765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4576950207665023639481413 858178163937191932402765)
                ·
                  refine ⟨321816811476446974651037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 858178163937191932402765 321816811476446974651037)
                  ·
                    refine ⟨120681304303667615494139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321816811476446974651037 120681304303667615494139)
                    ·
                      rfl

theorem cell22_352539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 3].length) (baseStart_352539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352539 prefixEnd_352539 := by exact prefixLift 352539
  have htrace : WordTrace (prefixWord ++ tailWord_352539) baseStart_352539 baseEnd_352539 := by
    simpa [prefixWord, tailWord_352539, baseEnd_352539] using wordTrace_append hprefix tailTrace_352539
  have hstable : (prefixWord ++ tailWord_352539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352539).length < 2 ^ (prefixWord ++ tailWord_352539).sum := by decide
  have hdescent : baseEnd_352539 < baseStart_352539 := by decide
  rcases family_descends (prefixWord ++ tailWord_352539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352567 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 3, 7]
def baseStart_352567 : Nat := 118140960795 + 352567 * 2 ^ 59
def prefixEnd_352567 : Nat := 4983230072969 + 3 ^ 40 * 352567 * 2
def baseEnd_352567 : Nat := 120690889275884875794053

theorem tailTrace_352567 : CollatzResearch.WordTrace tailWord_352567 prefixEnd_352567 120690889275884875794053 := by
  unfold tailWord_352567
  simp only [CollatzResearch.WordTrace]
  refine ⟨12859174913717447494855955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8572783275811631663237303 12859174913717447494855955)
  ·
    refine ⟨19288762370576171242283933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12859174913717447494855955 19288762370576171242283933)
    ·
      refine ⟨7233285888966064215856475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19288762370576171242283933 7233285888966064215856475)
      ·
        refine ⟨10849928833449096323784713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233285888966064215856475 10849928833449096323784713)
        ·
          refine ⟨8137446625086822242838535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10849928833449096323784713 8137446625086822242838535)
          ·
            refine ⟨12206169937630233364257803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8137446625086822242838535 12206169937630233364257803)
            ·
              refine ⟨18309254906445350046386705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12206169937630233364257803 18309254906445350046386705)
              ·
                refine ⟨13731941179834012534790029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18309254906445350046386705 13731941179834012534790029)
                ·
                  refine ⟨5149477942437754700546261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13731941179834012534790029 5149477942437754700546261)
                  ·
                    refine ⟨120690889275884875794053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5149477942437754700546261 120690889275884875794053)
                    ·
                      rfl

theorem cell22_352567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_352567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352567 prefixEnd_352567 := by exact prefixLift 352567
  have htrace : WordTrace (prefixWord ++ tailWord_352567) baseStart_352567 baseEnd_352567 := by
    simpa [prefixWord, tailWord_352567, baseEnd_352567] using wordTrace_append hprefix tailTrace_352567
  have hstable : (prefixWord ++ tailWord_352567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352567).length < 2 ^ (prefixWord ++ tailWord_352567).sum := by decide
  have hdescent : baseEnd_352567 < baseStart_352567 := by decide
  rcases family_descends (prefixWord ++ tailWord_352567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352599 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 3, 4]
def baseStart_352599 : Nat := 118140960795 + 352599 * 2 ^ 59
def prefixEnd_352599 : Nat := 4983230072969 + 3 ^ 40 * 352599 * 2
def baseEnd_352599 : Nat := 120701843529847458993955

theorem tailTrace_352599 : CollatzResearch.WordTrace tailWord_352599 prefixEnd_352599 120701843529847458993955 := by
  unfold tailWord_352599
  simp only [CollatzResearch.WordTrace]
  refine ⟨12860342049601516960020851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8573561366401011306680567 12860342049601516960020851)
  ·
    refine ⟨19290513074402275440031277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12860342049601516960020851 19290513074402275440031277)
    ·
      refine ⟨7233942402900853290011729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19290513074402275440031277 7233942402900853290011729)
      ·
        refine ⟨5425456802175639967508797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7233942402900853290011729 5425456802175639967508797)
        ·
          refine ⟨2034546300815864987815799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5425456802175639967508797 2034546300815864987815799)
          ·
            refine ⟨3051819451223797481723699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034546300815864987815799 3051819451223797481723699)
            ·
              refine ⟨4577729176835696222585549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051819451223797481723699 4577729176835696222585549)
              ·
                refine ⟨1716648441313386083469581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4577729176835696222585549 1716648441313386083469581)
                ·
                  refine ⟨643743165492519781301093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1716648441313386083469581 643743165492519781301093)
                  ·
                    refine ⟨120701843529847458993955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 643743165492519781301093 120701843529847458993955)
                    ·
                      rfl

theorem cell22_352599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_352599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352599 prefixEnd_352599 := by exact prefixLift 352599
  have htrace : WordTrace (prefixWord ++ tailWord_352599) baseStart_352599 baseEnd_352599 := by
    simpa [prefixWord, tailWord_352599, baseEnd_352599] using wordTrace_append hprefix tailTrace_352599
  have hstable : (prefixWord ++ tailWord_352599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352599).length < 2 ^ (prefixWord ++ tailWord_352599).sum := by decide
  have hdescent : baseEnd_352599 < baseStart_352599 := by decide
  rcases family_descends (prefixWord ++ tailWord_352599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352644 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_352644 : Nat := 118140960795 + 352644 * 2 ^ 59
def prefixEnd_352644 : Nat := 4983230072969 + 3 ^ 40 * 352644 * 2
def baseEnd_352644 : Nat := 120717247949482341618817

theorem tailTrace_352644 : CollatzResearch.WordTrace tailWord_352644 prefixEnd_352644 120717247949482341618817 := by
  unfold tailWord_352644
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430991667219244822704493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8574655556292326430272657 6430991667219244822704493)
  ·
    refine ⟨2411621875207216808514185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6430991667219244822704493 2411621875207216808514185)
    ·
      refine ⟨1808716406405412606385639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2411621875207216808514185 1808716406405412606385639)
      ·
        refine ⟨2713074609608118909578459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1808716406405412606385639 2713074609608118909578459)
        ·
          refine ⟨4069611914412178364367689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2713074609608118909578459 4069611914412178364367689)
          ·
            refine ⟨3052208935809133773275767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4069611914412178364367689 3052208935809133773275767)
            ·
              refine ⟨4578313403713700659913651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052208935809133773275767 4578313403713700659913651)
              ·
                refine ⟨6867470105570550989870477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578313403713700659913651 6867470105570550989870477)
                ·
                  refine ⟨2575301289588956621201429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6867470105570550989870477 2575301289588956621201429)
                  ·
                    refine ⟨120717247949482341618817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2575301289588956621201429 120717247949482341618817)
                    ·
                      rfl

theorem cell22_352644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_352644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352644 prefixEnd_352644 := by exact prefixLift 352644
  have htrace : WordTrace (prefixWord ++ tailWord_352644) baseStart_352644 baseEnd_352644 := by
    simpa [prefixWord, tailWord_352644, baseEnd_352644] using wordTrace_append hprefix tailTrace_352644
  have hstable : (prefixWord ++ tailWord_352644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352644).length < 2 ^ (prefixWord ++ tailWord_352644).sum := by decide
  have hdescent : baseEnd_352644 < baseStart_352644 := by decide
  rcases family_descends (prefixWord ++ tailWord_352644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352650 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_352650 : Nat := 118140960795 + 352650 * 2 ^ 59
def prefixEnd_352650 : Nat := 4983230072969 + 3 ^ 40 * 352650 * 2
def baseEnd_352650 : Nat := 120719301872100325968799

theorem tailTrace_352650 : CollatzResearch.WordTrace tailWord_352650 prefixEnd_352650 120719301872100325968799 := by
  unfold tailWord_352650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215550543104188167531851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8574801448277835113418269 3215550543104188167531851)
  ·
    refine ⟨4823325814656282251297777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3215550543104188167531851 4823325814656282251297777)
    ·
      refine ⟨3617494360992211688473333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4823325814656282251297777 3617494360992211688473333)
      ·
        refine ⟨339140096343019845794375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3617494360992211688473333 339140096343019845794375)
        ·
          refine ⟨508710144514529768691563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339140096343019845794375 508710144514529768691563)
          ·
            refine ⟨763065216771794653037345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508710144514529768691563 763065216771794653037345)
            ·
              refine ⟨572298912578845989778009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763065216771794653037345 572298912578845989778009)
              ·
                refine ⟨429224184434134492333507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572298912578845989778009 429224184434134492333507)
                ·
                  refine ⟨643836276651201738500261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429224184434134492333507 643836276651201738500261)
                  ·
                    refine ⟨120719301872100325968799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 643836276651201738500261 120719301872100325968799)
                    ·
                      rfl

theorem cell22_352650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_352650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352650 prefixEnd_352650 := by exact prefixLift 352650
  have htrace : WordTrace (prefixWord ++ tailWord_352650) baseStart_352650 baseEnd_352650 := by
    simpa [prefixWord, tailWord_352650, baseEnd_352650] using wordTrace_append hprefix tailTrace_352650
  have hstable : (prefixWord ++ tailWord_352650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352650).length < 2 ^ (prefixWord ++ tailWord_352650).sum := by decide
  have hdescent : baseEnd_352650 < baseStart_352650 := by decide
  rcases family_descends (prefixWord ++ tailWord_352650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352682 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_352682 : Nat := 118140960795 + 352682 * 2 ^ 59
def prefixEnd_352682 : Nat := 4983230072969 + 3 ^ 40 * 352682 * 2
def baseEnd_352682 : Nat := 40243418708687636389567

theorem tailTrace_352682 : CollatzResearch.WordTrace tailWord_352682 prefixEnd_352682 40243418708687636389567 := by
  unfold tailWord_352682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215842327075205533823075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8575579538867214756861533 3215842327075205533823075)
  ·
    refine ⟨4823763490612808300734613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3215842327075205533823075 4823763490612808300734613)
    ·
      refine ⟨226113913622475389096935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4823763490612808300734613 226113913622475389096935)
      ·
        refine ⟨339170870433713083645403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226113913622475389096935 339170870433713083645403)
        ·
          refine ⟨508756305650569625468105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339170870433713083645403 508756305650569625468105)
          ·
            refine ⟨381567229237927219101079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508756305650569625468105 381567229237927219101079)
            ·
              refine ⟨572350843856890828651619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381567229237927219101079 572350843856890828651619)
              ·
                refine ⟨858526265785336242977429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572350843856890828651619 858526265785336242977429)
                ·
                  refine ⟨40243418708687636389567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 858526265785336242977429 40243418708687636389567)
                  ·
                    rfl

theorem cell22_352682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_352682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352682 prefixEnd_352682 := by exact prefixLift 352682
  have htrace : WordTrace (prefixWord ++ tailWord_352682) baseStart_352682 baseEnd_352682 := by
    simpa [prefixWord, tailWord_352682, baseEnd_352682] using wordTrace_append hprefix tailTrace_352682
  have hstable : (prefixWord ++ tailWord_352682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352682).length < 2 ^ (prefixWord ++ tailWord_352682).sum := by decide
  have hdescent : baseEnd_352682 < baseStart_352682 := by decide
  rcases family_descends (prefixWord ++ tailWord_352682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352719 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 4, 5]
def baseStart_352719 : Nat := 118140960795 + 352719 * 2 ^ 59
def prefixEnd_352719 : Nat := 4983230072969 + 3 ^ 40 * 352719 * 2
def baseEnd_352719 : Nat := 120742921982207145993587

theorem tailTrace_352719 : CollatzResearch.WordTrace tailWord_352719 prefixEnd_352719 120742921982207145993587 := by
  unfold tailWord_352719
  simp only [CollatzResearch.WordTrace]
  refine ⟨12864718809166777454389211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8576479206111184969592807 12864718809166777454389211)
  ·
    refine ⟨19297078213750166181583817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12864718809166777454389211 19297078213750166181583817)
    ·
      refine ⟨14472808660312624636187863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19297078213750166181583817 14472808660312624636187863)
      ·
        refine ⟨21709212990468936954281795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14472808660312624636187863 21709212990468936954281795)
        ·
          refine ⟨32563819485703405431422693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21709212990468936954281795 32563819485703405431422693)
          ·
            refine ⟨6105716153569388518391755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32563819485703405431422693 6105716153569388518391755)
            ·
              refine ⟨9158574230354082777587633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105716153569388518391755 9158574230354082777587633)
              ·
                refine ⟨6868930672765562083190725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9158574230354082777587633 6868930672765562083190725)
                ·
                  refine ⟨1287924501143542890598261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6868930672765562083190725 1287924501143542890598261)
                  ·
                    refine ⟨120742921982207145993587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1287924501143542890598261 120742921982207145993587)
                    ·
                      rfl

theorem cell22_352719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_352719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352719 prefixEnd_352719 := by exact prefixLift 352719
  have htrace : WordTrace (prefixWord ++ tailWord_352719) baseStart_352719 baseEnd_352719 := by
    simpa [prefixWord, tailWord_352719, baseEnd_352719] using wordTrace_append hprefix tailTrace_352719
  have hstable : (prefixWord ++ tailWord_352719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352719).length < 2 ^ (prefixWord ++ tailWord_352719).sum := by decide
  have hdescent : baseEnd_352719 < baseStart_352719 := by decide
  rcases family_descends (prefixWord ++ tailWord_352719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352828 : List Nat := [2, 2, 2, 2, 3, 1, 4, 6]
def baseStart_352828 : Nat := 118140960795 + 352828 * 2 ^ 59
def prefixEnd_352828 : Nat := 4983230072969 + 3 ^ 40 * 352828 * 2
def baseEnd_352828 : Nat := 13420026101085243890917

theorem tailTrace_352828 : CollatzResearch.WordTrace tailWord_352828 prefixEnd_352828 13420026101085243890917 := by
  unfold tailWord_352828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434347182885944535053569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8579129577181259380071425 6434347182885944535053569)
  ·
    refine ⟨4825760387164458401290177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6434347182885944535053569 4825760387164458401290177)
    ·
      refine ⟨3619320290373343800967633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4825760387164458401290177 3619320290373343800967633)
      ·
        refine ⟨2714490217780007850725725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3619320290373343800967633 2714490217780007850725725)
        ·
          refine ⟨1017933831667502944022147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2714490217780007850725725 1017933831667502944022147)
          ·
            refine ⟨1526900747501254416033221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017933831667502944022147 1526900747501254416033221)
            ·
              refine ⟨286293890156485203006229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1526900747501254416033221 286293890156485203006229)
              ·
                refine ⟨13420026101085243890917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 286293890156485203006229 13420026101085243890917)
                ·
                  rfl

theorem cell22_352828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 6].length) (baseStart_352828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352828 prefixEnd_352828 := by exact prefixLift 352828
  have htrace : WordTrace (prefixWord ++ tailWord_352828) baseStart_352828 baseEnd_352828 := by
    simpa [prefixWord, tailWord_352828, baseEnd_352828] using wordTrace_append hprefix tailTrace_352828
  have hstable : (prefixWord ++ tailWord_352828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352828).length < 2 ^ (prefixWord ++ tailWord_352828).sum := by decide
  have hdescent : baseEnd_352828 < baseStart_352828 := by decide
  rcases family_descends (prefixWord ++ tailWord_352828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352856 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 7]
def baseStart_352856 : Nat := 118140960795 + 352856 * 2 ^ 59
def prefixEnd_352856 : Nat := 4983230072969 + 3 ^ 40 * 352856 * 2
def baseEnd_352856 : Nat := 40263273293994818439389

theorem tailTrace_352856 : CollatzResearch.WordTrace tailWord_352856 prefixEnd_352856 40263273293994818439389 := by
  unfold tailWord_352856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434857804835224926063211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8579810406446966568084281 6434857804835224926063211)
  ·
    refine ⟨9652286707252837389094817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6434857804835224926063211 9652286707252837389094817)
    ·
      refine ⟨7239215030439628041821113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9652286707252837389094817 7239215030439628041821113)
      ·
        refine ⟨5429411272829721031365835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7239215030439628041821113 5429411272829721031365835)
        ·
          refine ⟨8144116909244581547048753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429411272829721031365835 8144116909244581547048753)
          ·
            refine ⟨6108087681933436160286565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8144116909244581547048753 6108087681933436160286565)
            ·
              refine ⟨1145266440362519280053731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6108087681933436160286565 1145266440362519280053731)
              ·
                refine ⟨1717899660543778920080597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145266440362519280053731 1717899660543778920080597)
                ·
                  refine ⟨40263273293994818439389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1717899660543778920080597 40263273293994818439389)
                  ·
                    rfl

theorem cell22_352856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_352856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352856 prefixEnd_352856 := by exact prefixLift 352856
  have htrace : WordTrace (prefixWord ++ tailWord_352856) baseStart_352856 baseEnd_352856 := by
    simpa [prefixWord, tailWord_352856, baseEnd_352856] using wordTrace_append hprefix tailTrace_352856
  have hstable : (prefixWord ++ tailWord_352856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352856).length < 2 ^ (prefixWord ++ tailWord_352856).sum := by decide
  have hdescent : baseEnd_352856 < baseStart_352856 := by decide
  rcases family_descends (prefixWord ++ tailWord_352856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352866 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_352866 : Nat := 118140960795 + 352866 * 2 ^ 59
def prefixEnd_352866 : Nat := 4983230072969 + 3 ^ 40 * 352866 * 2
def baseEnd_352866 : Nat := 120793243086347762568137

theorem tailTrace_352866 : CollatzResearch.WordTrace tailWord_352866 prefixEnd_352866 120793243086347762568137 := by
  unfold tailWord_352866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217520084908555389997613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8580053559756147706660301 3217520084908555389997613)
  ·
    refine ⟨1206570031840708271249105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3217520084908555389997613 1206570031840708271249105)
    ·
      refine ⟨904927523880531203436829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1206570031840708271249105 904927523880531203436829)
      ·
        refine ⟨339347821455199201288811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 904927523880531203436829 339347821455199201288811)
        ·
          refine ⟨509021732182798801933217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339347821455199201288811 509021732182798801933217)
          ·
            refine ⟨381766299137099101449913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509021732182798801933217 381766299137099101449913)
            ·
              refine ⟨286324724352824326087435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381766299137099101449913 286324724352824326087435)
              ·
                refine ⟨429487086529236489131153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286324724352824326087435 429487086529236489131153)
                ·
                  refine ⟨322115314896927366848365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429487086529236489131153 322115314896927366848365)
                  ·
                    refine ⟨120793243086347762568137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322115314896927366848365 120793243086347762568137)
                    ·
                      rfl

theorem cell22_352866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_352866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352866 prefixEnd_352866 := by exact prefixLift 352866
  have htrace : WordTrace (prefixWord ++ tailWord_352866) baseStart_352866 baseEnd_352866 := by
    simpa [prefixWord, tailWord_352866, baseEnd_352866] using wordTrace_append hprefix tailTrace_352866
  have hstable : (prefixWord ++ tailWord_352866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352866).length < 2 ^ (prefixWord ++ tailWord_352866).sum := by decide
  have hdescent : baseEnd_352866 < baseStart_352866 := by decide
  rcases family_descends (prefixWord ++ tailWord_352866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352871 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 1, 7]
def baseStart_352871 : Nat := 118140960795 + 352871 * 2 ^ 59
def prefixEnd_352871 : Nat := 4983230072969 + 3 ^ 40 * 352871 * 2
def baseEnd_352871 : Nat := 120794954688529416193121

theorem tailTrace_352871 : CollatzResearch.WordTrace tailWord_352871 prefixEnd_352871 120794954688529416193121 := by
  unfold tailWord_352871
  simp only [CollatzResearch.WordTrace]
  refine ⟨12870262704616107413922467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8580175136410738275948311 12870262704616107413922467)
  ·
    refine ⟨19305394056924161120883701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12870262704616107413922467 19305394056924161120883701)
    ·
      refine ⟨1809880692836640105082847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19305394056924161120883701 1809880692836640105082847)
      ·
        refine ⟨2714821039254960157624271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809880692836640105082847 2714821039254960157624271)
        ·
          refine ⟨4072231558882440236436407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714821039254960157624271 4072231558882440236436407)
          ·
            refine ⟨6108347338323660354654611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072231558882440236436407 6108347338323660354654611)
            ·
              refine ⟨9162521007485490531981917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6108347338323660354654611 9162521007485490531981917)
              ·
                refine ⟨3435945377807058949493219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9162521007485490531981917 3435945377807058949493219)
                ·
                  refine ⟨5153918066710588424239829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435945377807058949493219 5153918066710588424239829)
                  ·
                    refine ⟨120794954688529416193121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5153918066710588424239829 120794954688529416193121)
                    ·
                      rfl

theorem cell22_352871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_352871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352871 prefixEnd_352871 := by exact prefixLift 352871
  have htrace : WordTrace (prefixWord ++ tailWord_352871) baseStart_352871 baseEnd_352871 := by
    simpa [prefixWord, tailWord_352871, baseEnd_352871] using wordTrace_append hprefix tailTrace_352871
  have hstable : (prefixWord ++ tailWord_352871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352871).length < 2 ^ (prefixWord ++ tailWord_352871).sum := by decide
  have hdescent : baseEnd_352871 < baseStart_352871 := by decide
  rcases family_descends (prefixWord ++ tailWord_352871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352933 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_352933 : Nat := 118140960795 + 352933 * 2 ^ 59
def prefixEnd_352933 : Nat := 4983230072969 + 3 ^ 40 * 352933 * 2
def baseEnd_352933 : Nat := 120816178555581921142931

theorem tailTrace_352933 : CollatzResearch.WordTrace tailWord_352933 prefixEnd_352933 120816178555581921142931 := by
  unfold tailWord_352933
  simp only [CollatzResearch.WordTrace]
  refine ⟨12872524030391492002679453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8581682686927661335119635 12872524030391492002679453)
  ·
    refine ⟨4827196511396809501004795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12872524030391492002679453 4827196511396809501004795)
    ·
      refine ⟨7240794767095214251507193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4827196511396809501004795 7240794767095214251507193)
      ·
        refine ⟨5430596075321410688630395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7240794767095214251507193 5430596075321410688630395)
        ·
          refine ⟨8145894112982116032945593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5430596075321410688630395 8145894112982116032945593)
          ·
            refine ⟨6109420584736587024709195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8145894112982116032945593 6109420584736587024709195)
            ·
              refine ⟨9164130877104880537063793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6109420584736587024709195 9164130877104880537063793)
              ·
                refine ⟨6873098157828660402797845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9164130877104880537063793 6873098157828660402797845)
                ·
                  refine ⟨322176476148218456381149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6873098157828660402797845 322176476148218456381149)
                  ·
                    refine ⟨120816178555581921142931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322176476148218456381149 120816178555581921142931)
                    ·
                      rfl

theorem cell22_352933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_352933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_352933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_352933 prefixEnd_352933 := by exact prefixLift 352933
  have htrace : WordTrace (prefixWord ++ tailWord_352933) baseStart_352933 baseEnd_352933 := by
    simpa [prefixWord, tailWord_352933, baseEnd_352933] using wordTrace_append hprefix tailTrace_352933
  have hstable : (prefixWord ++ tailWord_352933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352933).length < 2 ^ (prefixWord ++ tailWord_352933).sum := by decide
  have hdescent : baseEnd_352933 < baseStart_352933 := by decide
  rcases family_descends (prefixWord ++ tailWord_352933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353038 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_353038 : Nat := 118140960795 + 353038 * 2 ^ 59
def prefixEnd_353038 : Nat := 4983230072969 + 3 ^ 40 * 353038 * 2
def baseEnd_353038 : Nat := 120852122201396647267609

theorem tailTrace_353038 : CollatzResearch.WordTrace tailWord_353038 prefixEnd_353038 120852122201396647267609 := by
  unfold tailWord_353038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609544211876386866906471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8584235796674063290167845 1609544211876386866906471)
  ·
    refine ⟨2414316317814580300359707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1609544211876386866906471 2414316317814580300359707)
    ·
      refine ⟨3621474476721870450539561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414316317814580300359707 3621474476721870450539561)
      ·
        refine ⟨2716105857541402837904671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3621474476721870450539561 2716105857541402837904671)
        ·
          refine ⟨4074158786312104256857007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716105857541402837904671 4074158786312104256857007)
          ·
            refine ⟨6111238179468156385285511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074158786312104256857007 6111238179468156385285511)
            ·
              refine ⟨9166857269202234577928267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111238179468156385285511 9166857269202234577928267)
              ·
                refine ⟨13750285903803351866892401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9166857269202234577928267 13750285903803351866892401)
                ·
                  refine ⟨10312714427852513900169301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13750285903803351866892401 10312714427852513900169301)
                  ·
                    refine ⟨120852122201396647267609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10312714427852513900169301 120852122201396647267609)
                    ·
                      rfl

theorem cell22_353038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_353038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353038 prefixEnd_353038 := by exact prefixLift 353038
  have htrace : WordTrace (prefixWord ++ tailWord_353038) baseStart_353038 baseEnd_353038 := by
    simpa [prefixWord, tailWord_353038, baseEnd_353038] using wordTrace_append hprefix tailTrace_353038
  have hstable : (prefixWord ++ tailWord_353038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353038).length < 2 ^ (prefixWord ++ tailWord_353038).sum := by decide
  have hdescent : baseEnd_353038 < baseStart_353038 := by decide
  rcases family_descends (prefixWord ++ tailWord_353038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353055 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 3, 4]
def baseStart_353055 : Nat := 118140960795 + 353055 * 2 ^ 59
def prefixEnd_353055 : Nat := 4983230072969 + 3 ^ 40 * 353055 * 2
def baseEnd_353055 : Nat := 120857941648814269592557

theorem tailTrace_353055 : CollatzResearch.WordTrace tailWord_353055 prefixEnd_353055 120857941648814269592557 := by
  unfold tailWord_353055
  simp only [CollatzResearch.WordTrace]
  refine ⟨12876973735949506838620619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8584649157299671225747079 12876973735949506838620619)
  ·
    refine ⟨19315460603924260257930929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12876973735949506838620619 19315460603924260257930929)
    ·
      refine ⟨14486595452943195193448197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19315460603924260257930929 14486595452943195193448197)
      ·
        refine ⟨2716236647426849098771537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14486595452943195193448197 2716236647426849098771537)
        ·
          refine ⟨2037177485570136824078653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716236647426849098771537 2037177485570136824078653)
          ·
            refine ⟨763941557088801309029495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2037177485570136824078653 763941557088801309029495)
            ·
              refine ⟨1145912335633201963544243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763941557088801309029495 1145912335633201963544243)
              ·
                refine ⟨1718868503449802945316365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145912335633201963544243 1718868503449802945316365)
                ·
                  refine ⟨644575688793676104493637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1718868503449802945316365 644575688793676104493637)
                  ·
                    refine ⟨120857941648814269592557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 644575688793676104493637 120857941648814269592557)
                    ·
                      rfl

theorem cell22_353055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_353055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353055 prefixEnd_353055 := by exact prefixLift 353055
  have htrace : WordTrace (prefixWord ++ tailWord_353055) baseStart_353055 baseEnd_353055 := by
    simpa [prefixWord, tailWord_353055, baseEnd_353055] using wordTrace_append hprefix tailTrace_353055
  have hstable : (prefixWord ++ tailWord_353055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353055).length < 2 ^ (prefixWord ++ tailWord_353055).sum := by decide
  have hdescent : baseEnd_353055 < baseStart_353055 := by decide
  rcases family_descends (prefixWord ++ tailWord_353055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353087 : List Nat := [1, 1, 2, 2, 5, 2, 1, 4, 4]
def baseStart_353087 : Nat := 118140960795 + 353087 * 2 ^ 59
def prefixEnd_353087 : Nat := 4983230072969 + 3 ^ 40 * 353087 * 2
def baseEnd_353087 : Nat := 40289631967592284264153

theorem tailTrace_353087 : CollatzResearch.WordTrace tailWord_353087 prefixEnd_353087 40289631967592284264153 := by
  unfold tailWord_353087
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878140871833576303785515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8585427247889050869190343 12878140871833576303785515)
  ·
    refine ⟨19317211307750364455678273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12878140871833576303785515 19317211307750364455678273)
    ·
      refine ⟨14487908480812773341758705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19317211307750364455678273 14487908480812773341758705)
      ·
        refine ⟨10865931360609580006319029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14487908480812773341758705 10865931360609580006319029)
        ·
          refine ⟨1018681065057148125592409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10865931360609580006319029 1018681065057148125592409)
          ·
            refine ⟨764010798792861094194307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018681065057148125592409 764010798792861094194307)
            ·
              refine ⟨1146016198189291641291461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764010798792861094194307 1146016198189291641291461)
              ·
                refine ⟨214878037160492182742149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1146016198189291641291461 214878037160492182742149)
                ·
                  refine ⟨40289631967592284264153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214878037160492182742149 40289631967592284264153)
                  ·
                    rfl

theorem cell22_353087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 4].length) (baseStart_353087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353087 prefixEnd_353087 := by exact prefixLift 353087
  have htrace : WordTrace (prefixWord ++ tailWord_353087) baseStart_353087 baseEnd_353087 := by
    simpa [prefixWord, tailWord_353087, baseEnd_353087] using wordTrace_append hprefix tailTrace_353087
  have hstable : (prefixWord ++ tailWord_353087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353087).length < 2 ^ (prefixWord ++ tailWord_353087).sum := by decide
  have hdescent : baseEnd_353087 < baseStart_353087 := by decide
  rcases family_descends (prefixWord ++ tailWord_353087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353098 : List Nat := [3, 1, 2, 1, 1, 1, 2, 11]
def baseStart_353098 : Nat := 118140960795 + 353098 * 2 ^ 59
def prefixEnd_353098 : Nat := 4983230072969 + 3 ^ 40 * 353098 * 2
def baseEnd_353098 : Nat := 13430295714175165640825

theorem tailTrace_353098 : CollatzResearch.WordTrace tailWord_353098 prefixEnd_353098 13430295714175165640825 := by
  unfold tailWord_353098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219635518698431295608987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8585694716529150121623965 3219635518698431295608987)
  ·
    refine ⟨4829453278047646943413481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3219635518698431295608987 4829453278047646943413481)
    ·
      refine ⟨3622089958535735207560111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4829453278047646943413481 3622089958535735207560111)
      ·
        refine ⟨5433134937803602811340167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622089958535735207560111 5433134937803602811340167)
        ·
          refine ⟨8149702406705404217010251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433134937803602811340167 8149702406705404217010251)
          ·
            refine ⟨12224553610058106325515377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149702406705404217010251 12224553610058106325515377)
            ·
              refine ⟨9168415207543579744136533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12224553610058106325515377 9168415207543579744136533)
              ·
                refine ⟨13430295714175165640825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 9168415207543579744136533 13430295714175165640825)
                ·
                  rfl

theorem cell22_353098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_353098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353098 prefixEnd_353098 := by exact prefixLift 353098
  have htrace : WordTrace (prefixWord ++ tailWord_353098) baseStart_353098 baseEnd_353098 := by
    simpa [prefixWord, tailWord_353098, baseEnd_353098] using wordTrace_append hprefix tailTrace_353098
  have hstable : (prefixWord ++ tailWord_353098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353098).length < 2 ^ (prefixWord ++ tailWord_353098).sum := by decide
  have hdescent : baseEnd_353098 < baseStart_353098 := by decide
  rcases family_descends (prefixWord ++ tailWord_353098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353316 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_353316 : Nat := 118140960795 + 353316 * 2 ^ 59
def prefixEnd_353316 : Nat := 4983230072969 + 3 ^ 40 * 353316 * 2
def baseEnd_353316 : Nat := 120947287282696588816757

theorem tailTrace_353316 : CollatzResearch.WordTrace tailWord_353316 prefixEnd_353316 120947287282696588816757 := by
  unfold tailWord_353316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443246594001974206935901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8590995458669298942581201 6443246594001974206935901)
  ·
    refine ⟨2416217472750740327600963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6443246594001974206935901 2416217472750740327600963)
    ·
      refine ⟨3624326209126110491401445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416217472750740327600963 3624326209126110491401445)
      ·
        refine ⟨679561164211145717137771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3624326209126110491401445 679561164211145717137771)
        ·
          refine ⟨1019341746316718575706657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679561164211145717137771 1019341746316718575706657)
          ·
            refine ⟨764506309737538931779993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019341746316718575706657 764506309737538931779993)
            ·
              refine ⟨573379732303154198834995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 764506309737538931779993 573379732303154198834995)
              ·
                refine ⟨860069598454731298252493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573379732303154198834995 860069598454731298252493)
                ·
                  refine ⟨322526099420524236844685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860069598454731298252493 322526099420524236844685)
                  ·
                    refine ⟨120947287282696588816757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322526099420524236844685 120947287282696588816757)
                    ·
                      rfl

theorem cell22_353316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_353316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353316 prefixEnd_353316 := by exact prefixLift 353316
  have htrace : WordTrace (prefixWord ++ tailWord_353316) baseStart_353316 baseEnd_353316 := by
    simpa [prefixWord, tailWord_353316, baseEnd_353316] using wordTrace_append hprefix tailTrace_353316
  have hstable : (prefixWord ++ tailWord_353316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353316).length < 2 ^ (prefixWord ++ tailWord_353316).sum := by decide
  have hdescent : baseEnd_353316 < baseStart_353316 := by decide
  rcases family_descends (prefixWord ++ tailWord_353316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353329 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 5]
def baseStart_353329 : Nat := 118140960795 + 353329 * 2 ^ 59
def prefixEnd_353329 : Nat := 4983230072969 + 3 ^ 40 * 353329 * 2
def baseEnd_353329 : Nat := 40317245816122962747239

theorem tailTrace_353329 : CollatzResearch.WordTrace tailWord_353329 prefixEnd_353329 40317245816122962747239 := by
  unfold tailWord_353329
  simp only [CollatzResearch.WordTrace]
  refine ⟨12886967336956851634095041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8591311557971234422730027 12886967336956851634095041)
  ·
    refine ⟨9665225502717638725571281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12886967336956851634095041 9665225502717638725571281)
    ·
      refine ⟨7248919127038229044178461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9665225502717638725571281 7248919127038229044178461)
      ·
        refine ⟨2718344672639335891566923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7248919127038229044178461 2718344672639335891566923)
        ·
          refine ⟨4077517008959003837350385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718344672639335891566923 4077517008959003837350385)
          ·
            refine ⟨3058137756719252878012789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4077517008959003837350385 3058137756719252878012789)
            ·
              refine ⟨286700414692429957313699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3058137756719252878012789 286700414692429957313699)
              ·
                refine ⟨430050622038644935970549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286700414692429957313699 430050622038644935970549)
                ·
                  refine ⟨40317245816122962747239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430050622038644935970549 40317245816122962747239)
                  ·
                    rfl

theorem cell22_353329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_353329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353329 prefixEnd_353329 := by exact prefixLift 353329
  have htrace : WordTrace (prefixWord ++ tailWord_353329) baseStart_353329 baseEnd_353329 := by
    simpa [prefixWord, tailWord_353329, baseEnd_353329] using wordTrace_append hprefix tailTrace_353329
  have hstable : (prefixWord ++ tailWord_353329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353329).length < 2 ^ (prefixWord ++ tailWord_353329).sum := by decide
  have hdescent : baseEnd_353329 < baseStart_353329 := by decide
  rcases family_descends (prefixWord ++ tailWord_353329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353350 : List Nat := [6, 1, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_353350 : Nat := 118140960795 + 353350 * 2 ^ 59
def prefixEnd_353350 : Nat := 4983230072969 + 3 ^ 40 * 353350 * 2
def baseEnd_353350 : Nat := 120958926177531833466653

theorem tailTrace_353350 : CollatzResearch.WordTrace tailWord_353350 prefixEnd_353350 120958926177531833466653 := by
  unfold tailWord_353350
  simp only [CollatzResearch.WordTrace]
  refine ⟨402741664683774131894047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8591822179920514813739669 402741664683774131894047)
  ·
    refine ⟨604112497025661197841071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 402741664683774131894047 604112497025661197841071)
    ·
      refine ⟨906168745538491796761607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604112497025661197841071 906168745538491796761607)
      ·
        refine ⟨1359253118307737695142411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906168745538491796761607 1359253118307737695142411)
        ·
          refine ⟨2038879677461606542713617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359253118307737695142411 2038879677461606542713617)
          ·
            refine ⟨1529159758096204907035213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038879677461606542713617 1529159758096204907035213)
            ·
              refine ⟨573434909286076840138205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1529159758096204907035213 573434909286076840138205)
              ·
                refine ⟨215038090982278815051827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 573434909286076840138205 215038090982278815051827)
                ·
                  refine ⟨322557136473418222577741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215038090982278815051827 322557136473418222577741)
                  ·
                    refine ⟨120958926177531833466653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322557136473418222577741 120958926177531833466653)
                    ·
                      rfl

theorem cell22_353350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_353350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353350 prefixEnd_353350 := by exact prefixLift 353350
  have htrace : WordTrace (prefixWord ++ tailWord_353350) baseStart_353350 baseEnd_353350 := by
    simpa [prefixWord, tailWord_353350, baseEnd_353350] using wordTrace_append hprefix tailTrace_353350
  have hstable : (prefixWord ++ tailWord_353350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353350).length < 2 ^ (prefixWord ++ tailWord_353350).sum := by decide
  have hdescent : baseEnd_353350 < baseStart_353350 := by decide
  rcases family_descends (prefixWord ++ tailWord_353350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353404 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_353404 : Nat := 118140960795 + 353404 * 2 ^ 59
def prefixEnd_353404 : Nat := 4983230072969 + 3 ^ 40 * 353404 * 2
def baseEnd_353404 : Nat := 120977411481093692616487

theorem tailTrace_353404 : CollatzResearch.WordTrace tailWord_353404 prefixEnd_353404 120977411481093692616487 := by
  unfold tailWord_353404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444851405842569721537633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8593135207790092962050177 6444851405842569721537633)
  ·
    refine ⟨4833638554381927291153225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6444851405842569721537633 4833638554381927291153225)
    ·
      refine ⟨3625228915786445468364919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4833638554381927291153225 3625228915786445468364919)
      ·
        refine ⟨5437843373679668202547379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3625228915786445468364919 5437843373679668202547379)
        ·
          refine ⟨8156765060519502303821069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437843373679668202547379 8156765060519502303821069)
          ·
            refine ⟨3058786897694813363932901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8156765060519502303821069 3058786897694813363932901)
            ·
              refine ⟨573522543317777505737419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3058786897694813363932901 573522543317777505737419)
              ·
                refine ⟨860283814976666258606129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573522543317777505737419 860283814976666258606129)
                ·
                  refine ⟨645212861232499693954597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 860283814976666258606129 645212861232499693954597)
                  ·
                    refine ⟨120977411481093692616487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 645212861232499693954597 120977411481093692616487)
                    ·
                      rfl

theorem cell22_353404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_353404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353404 prefixEnd_353404 := by exact prefixLift 353404
  have htrace : WordTrace (prefixWord ++ tailWord_353404) baseStart_353404 baseEnd_353404 := by
    simpa [prefixWord, tailWord_353404, baseEnd_353404] using wordTrace_append hprefix tailTrace_353404
  have hstable : (prefixWord ++ tailWord_353404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353404).length < 2 ^ (prefixWord ++ tailWord_353404).sum := by decide
  have hdescent : baseEnd_353404 < baseStart_353404 := by decide
  rcases family_descends (prefixWord ++ tailWord_353404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353468 : List Nat := [2, 2, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_353468 : Nat := 118140960795 + 353468 * 2 ^ 59
def prefixEnd_353468 : Nat := 4983230072969 + 3 ^ 40 * 353468 * 2
def baseEnd_353468 : Nat := 120999319989018859016291

theorem tailTrace_353468 : CollatzResearch.WordTrace tailWord_353468 prefixEnd_353468 120999319989018859016291 := by
  unfold tailWord_353468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6446018541726639186702529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8594691388968852248936705 6446018541726639186702529)
  ·
    refine ⟨4834513906294979390026897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6446018541726639186702529 4834513906294979390026897)
    ·
      refine ⟨3625885429721234542520173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4834513906294979390026897 3625885429721234542520173)
      ·
        refine ⟨1359707036145462953445065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3625885429721234542520173 1359707036145462953445065)
        ·
          refine ⟨1019780277109097215083799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1359707036145462953445065 1019780277109097215083799)
          ·
            refine ⟨1529670415663645822625699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019780277109097215083799 1529670415663645822625699)
            ·
              refine ⟨2294505623495468733938549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529670415663645822625699 2294505623495468733938549)
              ·
                refine ⟨215109902202700193806739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2294505623495468733938549 215109902202700193806739)
                ·
                  refine ⟨322664853304050290710109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215109902202700193806739 322664853304050290710109)
                  ·
                    refine ⟨120999319989018859016291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322664853304050290710109 120999319989018859016291)
                    ·
                      rfl

theorem cell22_353468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_353468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353468 prefixEnd_353468 := by exact prefixLift 353468
  have htrace : WordTrace (prefixWord ++ tailWord_353468) baseStart_353468 baseEnd_353468 := by
    simpa [prefixWord, tailWord_353468, baseEnd_353468] using wordTrace_append hprefix tailTrace_353468
  have hstable : (prefixWord ++ tailWord_353468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353468).length < 2 ^ (prefixWord ++ tailWord_353468).sum := by decide
  have hdescent : baseEnd_353468 < baseStart_353468 := by decide
  rcases family_descends (prefixWord ++ tailWord_353468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353474 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_353474 : Nat := 118140960795 + 353474 * 2 ^ 59
def prefixEnd_353474 : Nat := 4983230072969 + 3 ^ 40 * 353474 * 2
def baseEnd_353474 : Nat := 121001373911636843366273

theorem tailTrace_353474 : CollatzResearch.WordTrace tailWord_353474 prefixEnd_353474 121001373911636843366273 := by
  unfold tailWord_353474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223063980357885349530869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8594837280954360932082317 3223063980357885349530869)
  ·
    refine ⟨302162248158551751518519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3223063980357885349530869 302162248158551751518519)
    ·
      refine ⟨453243372237827627277779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302162248158551751518519 453243372237827627277779)
      ·
        refine ⟨679865058356741440916669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453243372237827627277779 679865058356741440916669)
        ·
          refine ⟨254949396883778040343751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 679865058356741440916669 254949396883778040343751)
          ·
            refine ⟨382424095325667060515627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254949396883778040343751 382424095325667060515627)
            ·
              refine ⟨573636142988500590773441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382424095325667060515627 573636142988500590773441)
              ·
                refine ⟨430227107241375443080081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573636142988500590773441 430227107241375443080081)
                ·
                  refine ⟨322670330431031582310061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430227107241375443080081 322670330431031582310061)
                  ·
                    refine ⟨121001373911636843366273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322670330431031582310061 121001373911636843366273)
                    ·
                      rfl

theorem cell22_353474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_353474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353474 prefixEnd_353474 := by exact prefixLift 353474
  have htrace : WordTrace (prefixWord ++ tailWord_353474) baseStart_353474 baseEnd_353474 := by
    simpa [prefixWord, tailWord_353474, baseEnd_353474] using wordTrace_append hprefix tailTrace_353474
  have hstable : (prefixWord ++ tailWord_353474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353474).length < 2 ^ (prefixWord ++ tailWord_353474).sum := by decide
  have hdescent : baseEnd_353474 < baseStart_353474 := by decide
  rcases family_descends (prefixWord ++ tailWord_353474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353539 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 4, 4]
def baseStart_353539 : Nat := 118140960795 + 353539 * 2 ^ 59
def prefixEnd_353539 : Nat := 4983230072969 + 3 ^ 40 * 353539 * 2
def baseEnd_353539 : Nat := 121023624739998340491073

theorem tailTrace_353539 : CollatzResearch.WordTrace tailWord_353539 prefixEnd_353539 121023624739998340491073 := by
  unfold tailWord_353539
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894626666196057499239671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8596417777464038332826447 12894626666196057499239671)
  ·
    refine ⟨19341939999294086248859507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12894626666196057499239671 19341939999294086248859507)
    ·
      refine ⟨29012909998941129373289261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19341939999294086248859507 29012909998941129373289261)
      ·
        refine ⟨10879841249602923514983473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29012909998941129373289261 10879841249602923514983473)
        ·
          refine ⟨8159880937202192636237605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10879841249602923514983473 8159880937202192636237605)
          ·
            refine ⟨1529977675725411119294551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8159880937202192636237605 1529977675725411119294551)
            ·
              refine ⟨2294966513588116678941827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529977675725411119294551 2294966513588116678941827)
              ·
                refine ⟨3442449770382175018412741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294966513588116678941827 3442449770382175018412741)
                ·
                  refine ⟨645459331946657815952389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3442449770382175018412741 645459331946657815952389)
                  ·
                    refine ⟨121023624739998340491073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 645459331946657815952389 121023624739998340491073)
                    ·
                      rfl

theorem cell22_353539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 4].length) (baseStart_353539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353539 prefixEnd_353539 := by exact prefixLift 353539
  have htrace : WordTrace (prefixWord ++ tailWord_353539) baseStart_353539 baseEnd_353539 := by
    simpa [prefixWord, tailWord_353539, baseEnd_353539] using wordTrace_append hprefix tailTrace_353539
  have hstable : (prefixWord ++ tailWord_353539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353539).length < 2 ^ (prefixWord ++ tailWord_353539).sum := by decide
  have hdescent : baseEnd_353539 < baseStart_353539 := by decide
  rcases family_descends (prefixWord ++ tailWord_353539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353541 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_353541 : Nat := 118140960795 + 353541 * 2 ^ 59
def prefixEnd_353541 : Nat := 4983230072969 + 3 ^ 40 * 353541 * 2
def baseEnd_353541 : Nat := 121024309380871001941067

theorem tailTrace_353541 : CollatzResearch.WordTrace tailWord_353541 prefixEnd_353541 121024309380871001941067 := by
  unfold tailWord_353541
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894699612188811840812477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8596466408125874560541651 12894699612188811840812477)
  ·
    refine ⟨4835512354570804440304679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12894699612188811840812477 4835512354570804440304679)
    ·
      refine ⟨7253268531856206660457019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835512354570804440304679 7253268531856206660457019)
      ·
        refine ⟨10879902797784309990685529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253268531856206660457019 10879902797784309990685529)
        ·
          refine ⟨8159927098338232493014147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10879902797784309990685529 8159927098338232493014147)
          ·
            refine ⟨12239890647507348739521221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159927098338232493014147 12239890647507348739521221)
            ·
              refine ⟨2294979496407627888660229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12239890647507348739521221 2294979496407627888660229)
              ·
                refine ⟨430308655576430229123793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2294979496407627888660229 430308655576430229123793)
                ·
                  refine ⟨322731491682322671842845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430308655576430229123793 322731491682322671842845)
                  ·
                    refine ⟨121024309380871001941067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322731491682322671842845 121024309380871001941067)
                    ·
                      rfl

theorem cell22_353541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_353541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353541 prefixEnd_353541 := by exact prefixLift 353541
  have htrace : WordTrace (prefixWord ++ tailWord_353541) baseStart_353541 baseEnd_353541 := by
    simpa [prefixWord, tailWord_353541, baseEnd_353541] using wordTrace_append hprefix tailTrace_353541
  have hstable : (prefixWord ++ tailWord_353541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353541).length < 2 ^ (prefixWord ++ tailWord_353541).sum := by decide
  have hdescent : baseEnd_353541 < baseStart_353541 := by decide
  rcases family_descends (prefixWord ++ tailWord_353541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353601 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_353601 : Nat := 118140960795 + 353601 * 2 ^ 59
def prefixEnd_353601 : Nat := 4983230072969 + 3 ^ 40 * 353601 * 2
def baseEnd_353601 : Nat := 121044848607050845440883

theorem tailTrace_353601 : CollatzResearch.WordTrace tailWord_353601 prefixEnd_353601 121044848607050845440883 := by
  unfold tailWord_353601
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896887991971442087996657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8597925327980961391997771 12896887991971442087996657)
  ·
    refine ⟨9672665993978581565997493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12896887991971442087996657 9672665993978581565997493)
    ·
      refine ⟨906812436935492021812265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9672665993978581565997493 906812436935492021812265)
      ·
        refine ⟨680109327701619016359199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 906812436935492021812265 680109327701619016359199)
        ·
          refine ⟨1020163991552428524538799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680109327701619016359199 1020163991552428524538799)
          ·
            refine ⟨1530245987328642786808199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020163991552428524538799 1530245987328642786808199)
            ·
              refine ⟨2295368980992964180212299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530245987328642786808199 2295368980992964180212299)
              ·
                refine ⟨3443053471489446270318449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295368980992964180212299 3443053471489446270318449)
                ·
                  refine ⟨2582290103617084702738837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3443053471489446270318449 2582290103617084702738837)
                  ·
                    refine ⟨121044848607050845440883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2582290103617084702738837 121044848607050845440883)
                    ·
                      rfl

theorem cell22_353601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_353601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353601 prefixEnd_353601 := by exact prefixLift 353601
  have htrace : WordTrace (prefixWord ++ tailWord_353601) baseStart_353601 baseEnd_353601 := by
    simpa [prefixWord, tailWord_353601, baseEnd_353601] using wordTrace_append hprefix tailTrace_353601
  have hstable : (prefixWord ++ tailWord_353601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353601).length < 2 ^ (prefixWord ++ tailWord_353601).sum := by decide
  have hdescent : baseEnd_353601 < baseStart_353601 := by decide
  rcases family_descends (prefixWord ++ tailWord_353601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353661 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 6]
def baseStart_353661 : Nat := 118140960795 + 353661 * 2 ^ 59
def prefixEnd_353661 : Nat := 4983230072969 + 3 ^ 40 * 353661 * 2
def baseEnd_353661 : Nat := 40355129277743562980233

theorem tailTrace_353661 : CollatzResearch.WordTrace tailWord_353661 prefixEnd_353661 40355129277743562980233 := by
  unfold tailWord_353661
  simp only [CollatzResearch.WordTrace]
  refine ⟨12899076371754072335180837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8599384247836048223453891 12899076371754072335180837)
  ·
    refine ⟨2418576819703888562846407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12899076371754072335180837 2418576819703888562846407)
    ·
      refine ⟨3627865229555832844269611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2418576819703888562846407 3627865229555832844269611)
      ·
        refine ⟨5441797844333749266404417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627865229555832844269611 5441797844333749266404417)
        ·
          refine ⟨4081348383250311949803313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5441797844333749266404417 4081348383250311949803313)
          ·
            refine ⟨3061011287437733962352485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4081348383250311949803313 3061011287437733962352485)
            ·
              refine ⟨573939616394575117941091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3061011287437733962352485 573939616394575117941091)
              ·
                refine ⟨860909424591862676911637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573939616394575117941091 860909424591862676911637)
                ·
                  refine ⟨40355129277743562980233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 860909424591862676911637 40355129277743562980233)
                  ·
                    rfl

theorem cell22_353661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_353661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353661 prefixEnd_353661 := by exact prefixLift 353661
  have htrace : WordTrace (prefixWord ++ tailWord_353661) baseStart_353661 baseEnd_353661 := by
    simpa [prefixWord, tailWord_353661, baseEnd_353661] using wordTrace_append hprefix tailTrace_353661
  have hstable : (prefixWord ++ tailWord_353661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353661).length < 2 ^ (prefixWord ++ tailWord_353661).sum := by decide
  have hdescent : baseEnd_353661 < baseStart_353661 := by decide
  rcases family_descends (prefixWord ++ tailWord_353661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353693 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_353693 : Nat := 118140960795 + 353693 * 2 ^ 59
def prefixEnd_353693 : Nat := 4983230072969 + 3 ^ 40 * 353693 * 2
def baseEnd_353693 : Nat := 121076342087193272140601

theorem tailTrace_353693 : CollatzResearch.WordTrace tailWord_353693 prefixEnd_353693 121076342087193272140601 := by
  unfold tailWord_353693
  simp only [CollatzResearch.WordTrace]
  refine ⟨12900243507638141800345733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8600162338425427866897155 12900243507638141800345733)
  ·
    refine ⟨2418795657682151587564825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12900243507638141800345733 2418795657682151587564825)
    ·
      refine ⟨1814096743261613690673619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2418795657682151587564825 1814096743261613690673619)
      ·
        refine ⟨2721145114892420536010429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814096743261613690673619 2721145114892420536010429)
        ·
          refine ⟨1020429418084657701003911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2721145114892420536010429 1020429418084657701003911)
          ·
            refine ⟨1530644127126986551505867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020429418084657701003911 1530644127126986551505867)
            ·
              refine ⟨2295966190690479827258801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530644127126986551505867 2295966190690479827258801)
              ·
                refine ⟨1721974643017859870444101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2295966190690479827258801 1721974643017859870444101)
                ·
                  refine ⟨322870245565848725708269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721974643017859870444101 322870245565848725708269)
                  ·
                    refine ⟨121076342087193272140601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322870245565848725708269 121076342087193272140601)
                    ·
                      rfl

theorem cell22_353693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_353693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353693 prefixEnd_353693 := by exact prefixLift 353693
  have htrace : WordTrace (prefixWord ++ tailWord_353693) baseStart_353693 baseEnd_353693 := by
    simpa [prefixWord, tailWord_353693, baseEnd_353693] using wordTrace_append hprefix tailTrace_353693
  have hstable : (prefixWord ++ tailWord_353693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353693).length < 2 ^ (prefixWord ++ tailWord_353693).sum := by decide
  have hdescent : baseEnd_353693 < baseStart_353693 := by decide
  rcases family_descends (prefixWord ++ tailWord_353693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353695 : List Nat := [1, 1, 2, 5, 1, 4, 1, 3, 4]
def baseStart_353695 : Nat := 118140960795 + 353695 * 2 ^ 59
def prefixEnd_353695 : Nat := 4983230072969 + 3 ^ 40 * 353695 * 2
def baseEnd_353695 : Nat := 40359008909355311196865

theorem tailTrace_353695 : CollatzResearch.WordTrace tailWord_353695 prefixEnd_353695 40359008909355311196865 := by
  unfold tailWord_353695
  simp only [CollatzResearch.WordTrace]
  refine ⟨12900316453630896141918539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8600210969087264094612359 12900316453630896141918539)
  ·
    refine ⟨19350474680446344212877809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12900316453630896141918539 19350474680446344212877809)
    ·
      refine ⟨14512856010334758159658357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19350474680446344212877809 14512856010334758159658357)
      ·
        refine ⟨1360580250968883577467971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14512856010334758159658357 1360580250968883577467971)
        ·
          refine ⟨2040870376453325366201957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360580250968883577467971 2040870376453325366201957)
          ·
            refine ⟨382663195584998506162867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2040870376453325366201957 382663195584998506162867)
            ·
              refine ⟨573994793377497759244301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382663195584998506162867 573994793377497759244301)
              ·
                refine ⟨215248047516561659716613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 573994793377497759244301 215248047516561659716613)
                ·
                  refine ⟨40359008909355311196865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215248047516561659716613 40359008909355311196865)
                  ·
                    rfl

theorem cell22_353695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 4].length) (baseStart_353695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353695 prefixEnd_353695 := by exact prefixLift 353695
  have htrace : WordTrace (prefixWord ++ tailWord_353695) baseStart_353695 baseEnd_353695 := by
    simpa [prefixWord, tailWord_353695, baseEnd_353695] using wordTrace_append hprefix tailTrace_353695
  have hstable : (prefixWord ++ tailWord_353695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353695).length < 2 ^ (prefixWord ++ tailWord_353695).sum := by decide
  have hdescent : baseEnd_353695 < baseStart_353695 := by decide
  rcases family_descends (prefixWord ++ tailWord_353695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353768 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 5]
def baseStart_353768 : Nat := 118140960795 + 353768 * 2 ^ 59
def prefixEnd_353768 : Nat := 4983230072969 + 3 ^ 40 * 353768 * 2
def baseEnd_353768 : Nat := 40367338706639358838457

theorem tailTrace_353768 : CollatzResearch.WordTrace tailWord_353768 prefixEnd_353768 40367338706639358838457 := by
  unfold tailWord_353768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451489491183214804662979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8601985988244286406217305 6451489491183214804662979)
  ·
    refine ⟨9677234236774822206994469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6451489491183214804662979 9677234236774822206994469)
    ·
      refine ⟨1814481419395279163811463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9677234236774822206994469 1814481419395279163811463)
      ·
        refine ⟨2721722129092918745717195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814481419395279163811463 2721722129092918745717195)
        ·
          refine ⟨4082583193639378118575793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2721722129092918745717195 4082583193639378118575793)
          ·
            refine ⟨3061937395229533588931845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4082583193639378118575793 3061937395229533588931845)
            ·
              refine ⟨574113261605537547924721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3061937395229533588931845 574113261605537547924721)
              ·
                refine ⟨430584946204153160943541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574113261605537547924721 430584946204153160943541)
                ·
                  refine ⟨40367338706639358838457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430584946204153160943541 40367338706639358838457)
                  ·
                    rfl

theorem cell22_353768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_353768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353768 prefixEnd_353768 := by exact prefixLift 353768
  have htrace : WordTrace (prefixWord ++ tailWord_353768) baseStart_353768 baseEnd_353768 := by
    simpa [prefixWord, tailWord_353768, baseEnd_353768] using wordTrace_append hprefix tailTrace_353768
  have hstable : (prefixWord ++ tailWord_353768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353768).length < 2 ^ (prefixWord ++ tailWord_353768).sum := by decide
  have hdescent : baseEnd_353768 < baseStart_353768 := by decide
  rcases family_descends (prefixWord ++ tailWord_353768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353841 : List Nat := [1, 2, 2, 3, 1, 1, 1, 11]
def baseStart_353841 : Nat := 118140960795 + 353841 * 2 ^ 59
def prefixEnd_353841 : Nat := 4983230072969 + 3 ^ 40 * 353841 * 2
def baseEnd_353841 : Nat := 13458556167974468826683

theorem tailTrace_353841 : CollatzResearch.WordTrace tailWord_353841 prefixEnd_353841 13458556167974468826683 := by
  unfold tailWord_353841
  simp only [CollatzResearch.WordTrace]
  refine ⟨12905641511101963076733377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8603761007401308717822251 12905641511101963076733377)
  ·
    refine ⟨9679231133326472307550033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12905641511101963076733377 9679231133326472307550033)
    ·
      refine ⟨7259423349994854230662525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9679231133326472307550033 7259423349994854230662525)
      ·
        refine ⟨2722283756248070336498447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7259423349994854230662525 2722283756248070336498447)
        ·
          refine ⟨4083425634372105504747671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722283756248070336498447 4083425634372105504747671)
          ·
            refine ⟨6125138451558158257121507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4083425634372105504747671 6125138451558158257121507)
            ·
              refine ⟨9187707677337237385682261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6125138451558158257121507 9187707677337237385682261)
              ·
                refine ⟨13458556167974468826683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 9187707677337237385682261 13458556167974468826683)
                ·
                  rfl

theorem cell22_353841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 11].length) (baseStart_353841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353841 prefixEnd_353841 := by exact prefixLift 353841
  have htrace : WordTrace (prefixWord ++ tailWord_353841) baseStart_353841 baseEnd_353841 := by
    simpa [prefixWord, tailWord_353841, baseEnd_353841] using wordTrace_append hprefix tailTrace_353841
  have hstable : (prefixWord ++ tailWord_353841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353841).length < 2 ^ (prefixWord ++ tailWord_353841).sum := by decide
  have hdescent : baseEnd_353841 < baseStart_353841 := by decide
  rcases family_descends (prefixWord ++ tailWord_353841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353845 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_353845 : Nat := 118140960795 + 353845 * 2 ^ 59
def prefixEnd_353845 : Nat := 4983230072969 + 3 ^ 40 * 353845 * 2
def baseEnd_353845 : Nat := 121128374793515542340135

theorem tailTrace_353845 : CollatzResearch.WordTrace tailWord_353845 prefixEnd_353845 121128374793515542340135 := by
  unfold tailWord_353845
  simp only [CollatzResearch.WordTrace]
  refine ⟨12905787403087471759878989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8603858268724981173252659 12905787403087471759878989)
  ·
    refine ⟨4839670276157801909954621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12905787403087471759878989 4839670276157801909954621)
    ·
      refine ⟨1814876353559175716232983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4839670276157801909954621 1814876353559175716232983)
      ·
        refine ⟨2722314530338763574349475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814876353559175716232983 2722314530338763574349475)
        ·
          refine ⟨4083471795508145361524213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722314530338763574349475 4083471795508145361524213)
          ·
            refine ⟨382825480828888627642895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4083471795508145361524213 382825480828888627642895)
            ·
              refine ⟨574238221243332941464343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382825480828888627642895 574238221243332941464343)
              ·
                refine ⟨861357331864999412196515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574238221243332941464343 861357331864999412196515)
                ·
                  refine ⟨1292035997797499118294773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861357331864999412196515 1292035997797499118294773)
                  ·
                    refine ⟨121128374793515542340135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1292035997797499118294773 121128374793515542340135)
                    ·
                      rfl

theorem cell22_353845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_353845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353845 prefixEnd_353845 := by exact prefixLift 353845
  have htrace : WordTrace (prefixWord ++ tailWord_353845) baseStart_353845 baseEnd_353845 := by
    simpa [prefixWord, tailWord_353845, baseEnd_353845] using wordTrace_append hprefix tailTrace_353845
  have hstable : (prefixWord ++ tailWord_353845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353845).length < 2 ^ (prefixWord ++ tailWord_353845).sum := by decide
  have hdescent : baseEnd_353845 < baseStart_353845 := by decide
  rcases family_descends (prefixWord ++ tailWord_353845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353856 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_353856 : Nat := 118140960795 + 353856 * 2 ^ 59
def prefixEnd_353856 : Nat := 4983230072969 + 3 ^ 40 * 353856 * 2
def baseEnd_353856 : Nat := 121132140318315180315101

theorem tailTrace_353856 : CollatzResearch.WordTrace tailWord_353856 prefixEnd_353856 121132140318315180315101 := by
  unfold tailWord_353856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453094303023810319264711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8604125737365080425686281 6453094303023810319264711)
  ·
    refine ⟨9679641454535715478897067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6453094303023810319264711 9679641454535715478897067)
    ·
      refine ⟨14519462181803573218345601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9679641454535715478897067 14519462181803573218345601)
      ·
        refine ⟨10889596636352679913759201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14519462181803573218345601 10889596636352679913759201)
        ·
          refine ⟨8167197477264509935319401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10889596636352679913759201 8167197477264509935319401)
          ·
            refine ⟨6125398107948382451489551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8167197477264509935319401 6125398107948382451489551)
            ·
              refine ⟨9188097161922573677234327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6125398107948382451489551 9188097161922573677234327)
              ·
                refine ⟨13782145742883860515851491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9188097161922573677234327 13782145742883860515851491)
                ·
                  refine ⟨20673218614325790773777237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13782145742883860515851491 20673218614325790773777237)
                  ·
                    refine ⟨121132140318315180315101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 20673218614325790773777237 121132140318315180315101)
                    ·
                      rfl

theorem cell22_353856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_353856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353856 prefixEnd_353856 := by exact prefixLift 353856
  have htrace : WordTrace (prefixWord ++ tailWord_353856) baseStart_353856 baseEnd_353856 := by
    simpa [prefixWord, tailWord_353856, baseEnd_353856] using wordTrace_append hprefix tailTrace_353856
  have hstable : (prefixWord ++ tailWord_353856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353856).length < 2 ^ (prefixWord ++ tailWord_353856).sum := by decide
  have hdescent : baseEnd_353856 < baseStart_353856 := by decide
  rcases family_descends (prefixWord ++ tailWord_353856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353871 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 1, 8]
def baseStart_353871 : Nat := 118140960795 + 353871 * 2 ^ 59
def prefixEnd_353871 : Nat := 4983230072969 + 3 ^ 40 * 353871 * 2
def baseEnd_353871 : Nat := 121137275124860141190055

theorem tailTrace_353871 : CollatzResearch.WordTrace tailWord_353871 prefixEnd_353871 121137275124860141190055 := by
  unfold tailWord_353871
  simp only [CollatzResearch.WordTrace]
  refine ⟨12906735700993278200325467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8604490467328852133550311 12906735700993278200325467)
  ·
    refine ⟨19360103551489917300488201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12906735700993278200325467 19360103551489917300488201)
    ·
      refine ⟨14520077663617437975366151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19360103551489917300488201 14520077663617437975366151)
      ·
        refine ⟨21780116495426156963049227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14520077663617437975366151 21780116495426156963049227)
        ·
          refine ⟨32670174743139235444573841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21780116495426156963049227 32670174743139235444573841)
          ·
            refine ⟨24502631057354426583430381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32670174743139235444573841 24502631057354426583430381)
            ·
              refine ⟨9188486646507909968786393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24502631057354426583430381 9188486646507909968786393)
              ·
                refine ⟨6891364984880932476589795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9188486646507909968786393 6891364984880932476589795)
                ·
                  refine ⟨10337047477321398714884693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6891364984880932476589795 10337047477321398714884693)
                  ·
                    refine ⟨121137275124860141190055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10337047477321398714884693 121137275124860141190055)
                    ·
                      rfl

theorem cell22_353871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_353871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353871 prefixEnd_353871 := by exact prefixLift 353871
  have htrace : WordTrace (prefixWord ++ tailWord_353871) baseStart_353871 baseEnd_353871 := by
    simpa [prefixWord, tailWord_353871, baseEnd_353871] using wordTrace_append hprefix tailTrace_353871
  have hstable : (prefixWord ++ tailWord_353871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353871).length < 2 ^ (prefixWord ++ tailWord_353871).sum := by decide
  have hdescent : baseEnd_353871 < baseStart_353871 := by decide
  rcases family_descends (prefixWord ++ tailWord_353871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353965 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 6]
def baseStart_353965 : Nat := 118140960795 + 353965 * 2 ^ 59
def prefixEnd_353965 : Nat := 4983230072969 + 3 ^ 40 * 353965 * 2
def baseEnd_353965 : Nat := 40389817748625076446589

theorem tailTrace_353965 : CollatzResearch.WordTrace tailWord_353965 prefixEnd_353965 40389817748625076446589 := by
  unfold tailWord_353965
  simp only [CollatzResearch.WordTrace]
  refine ⟨12910164162652732254247349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8606776108435154836164899 12910164162652732254247349)
  ·
    refine ⟨1210327890248693648835689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12910164162652732254247349 1210327890248693648835689)
    ·
      refine ⟨907745917686520236626767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1210327890248693648835689 907745917686520236626767)
      ·
        refine ⟨1361618876529780354940151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907745917686520236626767 1361618876529780354940151)
        ·
          refine ⟨2042428314794670532410227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361618876529780354940151 2042428314794670532410227)
          ·
            refine ⟨3063642472192005798615341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042428314794670532410227 3063642472192005798615341)
            ·
              refine ⟨1148865927072002174480753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3063642472192005798615341 1148865927072002174480753)
              ·
                refine ⟨861649445304001630860565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148865927072002174480753 861649445304001630860565)
                ·
                  refine ⟨40389817748625076446589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 861649445304001630860565 40389817748625076446589)
                  ·
                    rfl

theorem cell22_353965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_353965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353965 prefixEnd_353965 := by exact prefixLift 353965
  have htrace : WordTrace (prefixWord ++ tailWord_353965) baseStart_353965 baseEnd_353965 := by
    simpa [prefixWord, tailWord_353965, baseEnd_353965] using wordTrace_append hprefix tailTrace_353965
  have hstable : (prefixWord ++ tailWord_353965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353965).length < 2 ^ (prefixWord ++ tailWord_353965).sum := by decide
  have hdescent : baseEnd_353965 < baseStart_353965 := by decide
  rcases family_descends (prefixWord ++ tailWord_353965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353980 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_353980 : Nat := 118140960795 + 353980 * 2 ^ 59
def prefixEnd_353980 : Nat := 4983230072969 + 3 ^ 40 * 353980 * 2
def baseEnd_353980 : Nat := 121174588052420190214721

theorem tailTrace_353980 : CollatzResearch.WordTrace tailWord_353980 prefixEnd_353980 121174588052420190214721 := by
  unfold tailWord_353980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6455355628799194908021697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8607140838398926544028929 6455355628799194908021697)
  ·
    refine ⟨4841516721599396181016273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6455355628799194908021697 4841516721599396181016273)
    ·
      refine ⟨3631137541199547135762205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4841516721599396181016273 3631137541199547135762205)
      ·
        refine ⟨1361676577949830175910827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3631137541199547135762205 1361676577949830175910827)
        ·
          refine ⟨2042514866924745263866241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361676577949830175910827 2042514866924745263866241)
          ·
            refine ⟨1531886150193558947899681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2042514866924745263866241 1531886150193558947899681)
            ·
              refine ⟨1148914612645169210924761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531886150193558947899681 1148914612645169210924761)
              ·
                refine ⟨861685959483876908193571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148914612645169210924761 861685959483876908193571)
                ·
                  refine ⟨1292528939225815362290357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861685959483876908193571 1292528939225815362290357)
                  ·
                    refine ⟨121174588052420190214721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1292528939225815362290357 121174588052420190214721)
                    ·
                      rfl

theorem cell22_353980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_353980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353980 prefixEnd_353980 := by exact prefixLift 353980
  have htrace : WordTrace (prefixWord ++ tailWord_353980) baseStart_353980 baseEnd_353980 := by
    simpa [prefixWord, tailWord_353980, baseEnd_353980] using wordTrace_append hprefix tailTrace_353980
  have hstable : (prefixWord ++ tailWord_353980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353980).length < 2 ^ (prefixWord ++ tailWord_353980).sum := by decide
  have hdescent : baseEnd_353980 < baseStart_353980 := by decide
  rcases family_descends (prefixWord ++ tailWord_353980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353982 : List Nat := [4, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_353982 : Nat := 118140960795 + 353982 * 2 ^ 59
def prefixEnd_353982 : Nat := 4983230072969 + 3 ^ 40 * 353982 * 2
def baseEnd_353982 : Nat := 40391757564430950554905

theorem tailTrace_353982 : CollatzResearch.WordTrace tailWord_353982 prefixEnd_353982 40391757564430950554905 := by
  unfold tailWord_353982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613848025448893019702025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8607189469060762771744133 1613848025448893019702025)
  ·
    refine ⟨1210386019086669764776519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1613848025448893019702025 1210386019086669764776519)
    ·
      refine ⟨1815579028630004647164779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1210386019086669764776519 1815579028630004647164779)
      ·
        refine ⟨2723368542945006970747169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1815579028630004647164779 2723368542945006970747169)
        ·
          refine ⟨2042526407208755228060377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2723368542945006970747169 2042526407208755228060377)
          ·
            refine ⟨1531894805406566421045283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2042526407208755228060377 1531894805406566421045283)
            ·
              refine ⟨2297842208109849631567925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531894805406566421045283 2297842208109849631567925)
              ·
                refine ⟨215422707010298402959493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2297842208109849631567925 215422707010298402959493)
                ·
                  refine ⟨40391757564430950554905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215422707010298402959493 40391757564430950554905)
                  ·
                    rfl

theorem cell22_353982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_353982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_353982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_353982 prefixEnd_353982 := by exact prefixLift 353982
  have htrace : WordTrace (prefixWord ++ tailWord_353982) baseStart_353982 baseEnd_353982 := by
    simpa [prefixWord, tailWord_353982, baseEnd_353982] using wordTrace_append hprefix tailTrace_353982
  have hstable : (prefixWord ++ tailWord_353982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353982).length < 2 ^ (prefixWord ++ tailWord_353982).sum := by decide
  have hdescent : baseEnd_353982 < baseStart_353982 := by decide
  rcases family_descends (prefixWord ++ tailWord_353982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354072 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 5]
def baseStart_354072 : Nat := 118140960795 + 354072 * 2 ^ 59
def prefixEnd_354072 : Nat := 4983230072969 + 3 ^ 40 * 354072 * 2
def baseEnd_354072 : Nat := 40402027177520872304813

theorem tailTrace_354072 : CollatzResearch.WordTrace tailWord_354072 prefixEnd_354072 40402027177520872304813 := by
  unfold tailWord_354072
  simp only [CollatzResearch.WordTrace]
  refine ⟨6457033386632544764196235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8609377848843393018928313 6457033386632544764196235)
  ·
    refine ⟨9685550079948817146294353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6457033386632544764196235 9685550079948817146294353)
    ·
      refine ⟨7264162559961612859720765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9685550079948817146294353 7264162559961612859720765)
      ·
        refine ⟨2724060959985604822395287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7264162559961612859720765 2724060959985604822395287)
        ·
          refine ⟨4086091439978407233592931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724060959985604822395287 4086091439978407233592931)
          ·
            refine ⟨6129137159967610850389397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086091439978407233592931 6129137159967610850389397)
            ·
              refine ⟨287303304373481758612003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6129137159967610850389397 287303304373481758612003)
              ·
                refine ⟨430954956560222637918005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287303304373481758612003 430954956560222637918005)
                ·
                  refine ⟨40402027177520872304813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430954956560222637918005 40402027177520872304813)
                  ·
                    rfl

theorem cell22_354072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_354072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354072 prefixEnd_354072 := by exact prefixLift 354072
  have htrace : WordTrace (prefixWord ++ tailWord_354072) baseStart_354072 baseEnd_354072 := by
    simpa [prefixWord, tailWord_354072, baseEnd_354072] using wordTrace_append hprefix tailTrace_354072
  have hstable : (prefixWord ++ tailWord_354072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354072).length < 2 ^ (prefixWord ++ tailWord_354072).sum := by decide
  have hdescent : baseEnd_354072 < baseStart_354072 := by decide
  rcases family_descends (prefixWord ++ tailWord_354072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354117 : List Nat := [1, 3, 1, 1, 1, 2, 5, 4, 4]
def baseStart_354117 : Nat := 118140960795 + 354117 * 2 ^ 59
def prefixEnd_354117 : Nat := 4983230072969 + 3 ^ 40 * 354117 * 2
def baseEnd_354117 : Nat := 40407161984065833179767

theorem tailTrace_354117 : CollatzResearch.WordTrace tailWord_354117 prefixEnd_354117 40407161984065833179767 := by
  unfold tailWord_354117
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915708058102062213780605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8610472038734708142520403 12915708058102062213780605)
  ·
    refine ⟨4843390521788273330167727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12915708058102062213780605 4843390521788273330167727)
    ·
      refine ⟨7265085782682409995251591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4843390521788273330167727 7265085782682409995251591)
      ·
        refine ⟨10897628674023614992877387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7265085782682409995251591 10897628674023614992877387)
        ·
          refine ⟨16346443011035422489316081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10897628674023614992877387 16346443011035422489316081)
          ·
            refine ⟨12259832258276566866987061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16346443011035422489316081 12259832258276566866987061)
            ·
              refine ⟨1149359274213428143780037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12259832258276566866987061 1149359274213428143780037)
              ·
                refine ⟨215504863915017776958757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1149359274213428143780037 215504863915017776958757)
                ·
                  refine ⟨40407161984065833179767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215504863915017776958757 40407161984065833179767)
                  ·
                    rfl

theorem cell22_354117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_354117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354117 prefixEnd_354117 := by exact prefixLift 354117
  have htrace : WordTrace (prefixWord ++ tailWord_354117) baseStart_354117 baseEnd_354117 := by
    simpa [prefixWord, tailWord_354117, baseEnd_354117] using wordTrace_append hprefix tailTrace_354117
  have hstable : (prefixWord ++ tailWord_354117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354117).length < 2 ^ (prefixWord ++ tailWord_354117).sum := by decide
  have hdescent : baseEnd_354117 < baseStart_354117 := by decide
  rcases family_descends (prefixWord ++ tailWord_354117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354132 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_354132 : Nat := 118140960795 + 354132 * 2 ^ 59
def prefixEnd_354132 : Nat := 4983230072969 + 3 ^ 40 * 354132 * 2
def baseEnd_354132 : Nat := 121226620758742460414255

theorem tailTrace_354132 : CollatzResearch.WordTrace tailWord_354132 prefixEnd_354132 121226620758742460414255 := by
  unfold tailWord_354132
  simp only [CollatzResearch.WordTrace]
  refine ⟨6458127576523859887788325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8610836768698479850384433 6458127576523859887788325)
  ·
    refine ⟨1210898920598223728960311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6458127576523859887788325 1210898920598223728960311)
    ·
      refine ⟨1816348380897335593440467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1210898920598223728960311 1816348380897335593440467)
      ·
        refine ⟨2724522571346003390160701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1816348380897335593440467 2724522571346003390160701)
        ·
          refine ⟨1021695964254751271310263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2724522571346003390160701 1021695964254751271310263)
          ·
            refine ⟨1532543946382126906965395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021695964254751271310263 1532543946382126906965395)
            ·
              refine ⟨2298815919573190360448093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532543946382126906965395 2298815919573190360448093)
              ·
                refine ⟨862055969839946385168035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2298815919573190360448093 862055969839946385168035)
                ·
                  refine ⟨1293083954759919577752053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862055969839946385168035 1293083954759919577752053)
                  ·
                    refine ⟨121226620758742460414255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1293083954759919577752053 121226620758742460414255)
                    ·
                      rfl

theorem cell22_354132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_354132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354132 prefixEnd_354132 := by exact prefixLift 354132
  have htrace : WordTrace (prefixWord ++ tailWord_354132) baseStart_354132 baseEnd_354132 := by
    simpa [prefixWord, tailWord_354132, baseEnd_354132] using wordTrace_append hprefix tailTrace_354132
  have hstable : (prefixWord ++ tailWord_354132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354132).length < 2 ^ (prefixWord ++ tailWord_354132).sum := by decide
  have hdescent : baseEnd_354132 < baseStart_354132 := by decide
  rcases family_descends (prefixWord ++ tailWord_354132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354147 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 1, 6]
def baseStart_354147 : Nat := 118140960795 + 354147 * 2 ^ 59
def prefixEnd_354147 : Nat := 4983230072969 + 3 ^ 40 * 354147 * 2
def baseEnd_354147 : Nat := 121231755565287421289209

theorem tailTrace_354147 : CollatzResearch.WordTrace tailWord_354147 prefixEnd_354147 121231755565287421289209 := by
  unfold tailWord_354147
  simp only [CollatzResearch.WordTrace]
  refine ⟨12916802247993377337372695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8611201498662251558248463 12916802247993377337372695)
  ·
    refine ⟨19375203371990066006059043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12916802247993377337372695 19375203371990066006059043)
    ·
      refine ⟨29062805057985099009088565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19375203371990066006059043 29062805057985099009088565)
      ·
        refine ⟨2724637974186103032102053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29062805057985099009088565 2724637974186103032102053)
        ·
          refine ⟨510869620159894318519135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2724637974186103032102053 510869620159894318519135)
          ·
            refine ⟨766304430239841477778703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510869620159894318519135 766304430239841477778703)
            ·
              refine ⟨1149456645359762216668055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766304430239841477778703 1149456645359762216668055)
              ·
                refine ⟨1724184968039643325002083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149456645359762216668055 1724184968039643325002083)
                ·
                  refine ⟨2586277452059464987503125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724184968039643325002083 2586277452059464987503125)
                  ·
                    refine ⟨121231755565287421289209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2586277452059464987503125 121231755565287421289209)
                    ·
                      rfl

theorem cell22_354147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 6].length) (baseStart_354147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354147 prefixEnd_354147 := by exact prefixLift 354147
  have htrace : WordTrace (prefixWord ++ tailWord_354147) baseStart_354147 baseEnd_354147 := by
    simpa [prefixWord, tailWord_354147, baseEnd_354147] using wordTrace_append hprefix tailTrace_354147
  have hstable : (prefixWord ++ tailWord_354147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354147).length < 2 ^ (prefixWord ++ tailWord_354147).sum := by decide
  have hdescent : baseEnd_354147 < baseStart_354147 := by decide
  rcases family_descends (prefixWord ++ tailWord_354147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354166 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_354166 : Nat := 118140960795 + 354166 * 2 ^ 59
def prefixEnd_354166 : Nat := 4983230072969 + 3 ^ 40 * 354166 * 2
def baseEnd_354166 : Nat := 121238259653577705064151

theorem tailTrace_354166 : CollatzResearch.WordTrace tailWord_354166 prefixEnd_354166 121238259653577705064151 := by
  unfold tailWord_354166
  simp only [CollatzResearch.WordTrace]
  refine ⟨807343452182783973894647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8611663489949695721542901 807343452182783973894647)
  ·
    refine ⟨1211015178274175960841971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 807343452182783973894647 1211015178274175960841971)
    ·
      refine ⟨1816522767411263941262957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211015178274175960841971 1816522767411263941262957)
      ·
        refine ⟨681196037779223977973609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1816522767411263941262957 681196037779223977973609)
        ·
          refine ⟨510897028334417983480207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681196037779223977973609 510897028334417983480207)
          ·
            refine ⟨766345542501626975220311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510897028334417983480207 766345542501626975220311)
            ·
              refine ⟨1149518313752440462830467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766345542501626975220311 1149518313752440462830467)
              ·
                refine ⟨1724277470628660694245701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149518313752440462830467 1724277470628660694245701)
                ·
                  refine ⟨323302025742873880171069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1724277470628660694245701 323302025742873880171069)
                  ·
                    refine ⟨121238259653577705064151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323302025742873880171069 121238259653577705064151)
                    ·
                      rfl

theorem cell22_354166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_354166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354166 prefixEnd_354166 := by exact prefixLift 354166
  have htrace : WordTrace (prefixWord ++ tailWord_354166) baseStart_354166 baseEnd_354166 := by
    simpa [prefixWord, tailWord_354166, baseEnd_354166] using wordTrace_append hprefix tailTrace_354166
  have hstable : (prefixWord ++ tailWord_354166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354166).length < 2 ^ (prefixWord ++ tailWord_354166).sum := by decide
  have hdescent : baseEnd_354166 < baseStart_354166 := by decide
  rcases family_descends (prefixWord ++ tailWord_354166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354271 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 1, 4]
def baseStart_354271 : Nat := 118140960795 + 354271 * 2 ^ 59
def prefixEnd_354271 : Nat := 4983230072969 + 3 ^ 40 * 354271 * 2
def baseEnd_354271 : Nat := 121274203299392431188829

theorem tailTrace_354271 : CollatzResearch.WordTrace tailWord_354271 prefixEnd_354271 121274203299392431188829 := by
  unfold tailWord_354271
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921324899544146514886667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8614216599696097676591111 12921324899544146514886667)
  ·
    refine ⟨19381987349316219772330001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12921324899544146514886667 19381987349316219772330001)
    ·
      refine ⟨14536490511987164829247501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19381987349316219772330001 14536490511987164829247501)
      ·
        refine ⟨5451183941995186810967813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14536490511987164829247501 5451183941995186810967813)
        ·
          refine ⟨1022096989124097527056465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5451183941995186810967813 1022096989124097527056465)
          ·
            refine ⟨766572741843073145292349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022096989124097527056465 766572741843073145292349)
            ·
              refine ⟨287464778191152429484631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 766572741843073145292349 287464778191152429484631)
              ·
                refine ⟨431197167286728644226947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287464778191152429484631 431197167286728644226947)
                ·
                  refine ⟨646795750930092966340421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431197167286728644226947 646795750930092966340421)
                  ·
                    refine ⟨121274203299392431188829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 646795750930092966340421 121274203299392431188829)
                    ·
                      rfl

theorem cell22_354271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 4].length) (baseStart_354271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354271 prefixEnd_354271 := by exact prefixLift 354271
  have htrace : WordTrace (prefixWord ++ tailWord_354271) baseStart_354271 baseEnd_354271 := by
    simpa [prefixWord, tailWord_354271, baseEnd_354271] using wordTrace_append hprefix tailTrace_354271
  have hstable : (prefixWord ++ tailWord_354271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354271).length < 2 ^ (prefixWord ++ tailWord_354271).sum := by decide
  have hdescent : baseEnd_354271 < baseStart_354271 := by decide
  rcases family_descends (prefixWord ++ tailWord_354271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354286 : List Nat := [4, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_354286 : Nat := 118140960795 + 354286 * 2 ^ 59
def prefixEnd_354286 : Nat := 4983230072969 + 3 ^ 40 * 354286 * 2
def baseEnd_354286 : Nat := 40426446035312464021261

theorem tailTrace_354286 : CollatzResearch.WordTrace tailWord_354286 prefixEnd_354286 40426446035312464021261 := by
  unfold tailWord_354286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615233999311225509585339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8614581329659869384455141 1615233999311225509585339)
  ·
    refine ⟨2422850998966838264378009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1615233999311225509585339 2422850998966838264378009)
    ·
      refine ⟨1817138249225128698283507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2422850998966838264378009 1817138249225128698283507)
      ·
        refine ⟨2725707373837693047425261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817138249225128698283507 2725707373837693047425261)
        ·
          refine ⟨1022140265189134892784473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2725707373837693047425261 1022140265189134892784473)
          ·
            refine ⟨766605198891851169588355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022140265189134892784473 766605198891851169588355)
            ·
              refine ⟨1149907798337776754382533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766605198891851169588355 1149907798337776754382533)
              ·
                refine ⟨215607712188333141446725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1149907798337776754382533 215607712188333141446725)
                ·
                  refine ⟨40426446035312464021261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215607712188333141446725 40426446035312464021261)
                  ·
                    rfl

theorem cell22_354286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_354286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354286 prefixEnd_354286 := by exact prefixLift 354286
  have htrace : WordTrace (prefixWord ++ tailWord_354286) baseStart_354286 baseEnd_354286 := by
    simpa [prefixWord, tailWord_354286, baseEnd_354286] using wordTrace_append hprefix tailTrace_354286
  have hstable : (prefixWord ++ tailWord_354286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354286).length < 2 ^ (prefixWord ++ tailWord_354286).sum := by decide
  have hdescent : baseEnd_354286 < baseStart_354286 := by decide
  rcases family_descends (prefixWord ++ tailWord_354286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354297 : List Nat := [1, 2, 1, 3, 1, 4, 3, 7]
def baseStart_354297 : Nat := 118140960795 + 354297 * 2 ^ 59
def prefixEnd_354297 : Nat := 4983230072969 + 3 ^ 40 * 354297 * 2
def baseEnd_354297 : Nat := 13475900403415225559861

theorem tailTrace_354297 : CollatzResearch.WordTrace tailWord_354297 prefixEnd_354297 13475900403415225559861 := by
  unfold tailWord_354297
  simp only [CollatzResearch.WordTrace]
  refine ⟨12922273197449952955333145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8614848798299968636888763 12922273197449952955333145)
  ·
    refine ⟨9691704898087464716499859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12922273197449952955333145 9691704898087464716499859)
    ·
      refine ⟨14537557347131197074749789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9691704898087464716499859 14537557347131197074749789)
      ·
        refine ⟨5451584005174198903031171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14537557347131197074749789 5451584005174198903031171)
        ·
          refine ⟨8177376007761298354546757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451584005174198903031171 8177376007761298354546757)
          ·
            refine ⟨1533258001455243441477517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8177376007761298354546757 1533258001455243441477517)
            ·
              refine ⟨574971750545716290554069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1533258001455243441477517 574971750545716290554069)
              ·
                refine ⟨13475900403415225559861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 574971750545716290554069 13475900403415225559861)
                ·
                  rfl

theorem cell22_354297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 7].length) (baseStart_354297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354297 prefixEnd_354297 := by exact prefixLift 354297
  have htrace : WordTrace (prefixWord ++ tailWord_354297) baseStart_354297 baseEnd_354297 := by
    simpa [prefixWord, tailWord_354297, baseEnd_354297] using wordTrace_append hprefix tailTrace_354297
  have hstable : (prefixWord ++ tailWord_354297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354297).length < 2 ^ (prefixWord ++ tailWord_354297).sum := by decide
  have hdescent : baseEnd_354297 < baseStart_354297 := by decide
  rcases family_descends (prefixWord ++ tailWord_354297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354346 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_354346 : Nat := 118140960795 + 354346 * 2 ^ 59
def prefixEnd_354346 : Nat := 4983230072969 + 3 ^ 40 * 354346 * 2
def baseEnd_354346 : Nat := 121299877332117235563599

theorem tailTrace_354346 : CollatzResearch.WordTrace tailWord_354346 prefixEnd_354346 121299877332117235563599 := by
  unfold tailWord_354346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231015093568108580966723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8616040249514956215911261 3231015093568108580966723)
  ·
    refine ⟨4846522640352162871450085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3231015093568108580966723 4846522640352162871450085)
    ·
      refine ⟨908722995066030538396891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4846522640352162871450085 908722995066030538396891)
      ·
        refine ⟨1363084492599045807595337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908722995066030538396891 1363084492599045807595337)
        ·
          refine ⟨1022313369449284355696503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1363084492599045807595337 1022313369449284355696503)
          ·
            refine ⟨1533470054173926533544755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022313369449284355696503 1533470054173926533544755)
            ·
              refine ⟨2300205081260889800317133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533470054173926533544755 2300205081260889800317133)
              ·
                refine ⟨862576905472833675118925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2300205081260889800317133 862576905472833675118925)
                ·
                  refine ⟨323466339552312628169597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862576905472833675118925 323466339552312628169597)
                  ·
                    refine ⟨121299877332117235563599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323466339552312628169597 121299877332117235563599)
                    ·
                      rfl

theorem cell22_354346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_354346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354346 prefixEnd_354346 := by exact prefixLift 354346
  have htrace : WordTrace (prefixWord ++ tailWord_354346) baseStart_354346 baseEnd_354346 := by
    simpa [prefixWord, tailWord_354346, baseEnd_354346] using wordTrace_append hprefix tailTrace_354346
  have hstable : (prefixWord ++ tailWord_354346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354346).length < 2 ^ (prefixWord ++ tailWord_354346).sum := by decide
  have hdescent : baseEnd_354346 < baseStart_354346 := by decide
  rcases family_descends (prefixWord ++ tailWord_354346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354397 : List Nat := [1, 4, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_354397 : Nat := 118140960795 + 354397 * 2 ^ 59
def prefixEnd_354397 : Nat := 4983230072969 + 3 ^ 40 * 354397 * 2
def baseEnd_354397 : Nat := 121317335674370102538443

theorem tailTrace_354397 : CollatzResearch.WordTrace tailWord_354397 prefixEnd_354397 121317335674370102538443 := by
  unfold tailWord_354397
  simp only [CollatzResearch.WordTrace]
  refine ⟨12925920497087670033973445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8617280331391780022648963 12925920497087670033973445)
  ·
    refine ⟨2423610093203938131370021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12925920497087670033973445 2423610093203938131370021)
    ·
      refine ⟨454426892475738399631879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2423610093203938131370021 454426892475738399631879)
      ·
        refine ⟨681640338713607599447819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454426892475738399631879 681640338713607599447819)
        ·
          refine ⟨1022460508070411399171729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681640338713607599447819 1022460508070411399171729)
          ·
            refine ⟨766845381052808549378797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022460508070411399171729 766845381052808549378797)
            ·
              refine ⟨287567017894803206017049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 766845381052808549378797 287567017894803206017049)
              ·
                refine ⟨215675263421102404512787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287567017894803206017049 215675263421102404512787)
                ·
                  refine ⟨323512895131653606769181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215675263421102404512787 323512895131653606769181)
                  ·
                    refine ⟨121317335674370102538443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323512895131653606769181 121317335674370102538443)
                    ·
                      rfl

theorem cell22_354397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_354397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354397 prefixEnd_354397 := by exact prefixLift 354397
  have htrace : WordTrace (prefixWord ++ tailWord_354397) baseStart_354397 baseEnd_354397 := by
    simpa [prefixWord, tailWord_354397, baseEnd_354397] using wordTrace_append hprefix tailTrace_354397
  have hstable : (prefixWord ++ tailWord_354397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354397).length < 2 ^ (prefixWord ++ tailWord_354397).sum := by decide
  have hdescent : baseEnd_354397 < baseStart_354397 := by decide
  rcases family_descends (prefixWord ++ tailWord_354397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354404 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 6]
def baseStart_354404 : Nat := 118140960795 + 354404 * 2 ^ 59
def prefixEnd_354404 : Nat := 4983230072969 + 3 ^ 40 * 354404 * 2
def baseEnd_354404 : Nat := 40439910639141472537807

theorem tailTrace_354404 : CollatzResearch.WordTrace tailWord_354404 prefixEnd_354404 40439910639141472537807 := by
  unfold tailWord_354404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463087904031155114739133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8617450538708206819652177 6463087904031155114739133)
  ·
    refine ⟨2423657964011683168027175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6463087904031155114739133 2423657964011683168027175)
    ·
      refine ⟨3635486946017524752040763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2423657964011683168027175 3635486946017524752040763)
      ·
        refine ⟨5453230419026287128061145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635486946017524752040763 5453230419026287128061145)
        ·
          refine ⟨4089922814269715346045859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5453230419026287128061145 4089922814269715346045859)
          ·
            refine ⟨6134884221404573019068789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089922814269715346045859 6134884221404573019068789)
            ·
              refine ⟨575145395756678720537699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6134884221404573019068789 575145395756678720537699)
              ·
                refine ⟨862718093635018080806549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575145395756678720537699 862718093635018080806549)
                ·
                  refine ⟨40439910639141472537807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 862718093635018080806549 40439910639141472537807)
                  ·
                    rfl

theorem cell22_354404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_354404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354404 prefixEnd_354404 := by exact prefixLift 354404
  have htrace : WordTrace (prefixWord ++ tailWord_354404) baseStart_354404 baseEnd_354404 := by
    simpa [prefixWord, tailWord_354404, baseEnd_354404] using wordTrace_append hprefix tailTrace_354404
  have hstable : (prefixWord ++ tailWord_354404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354404).length < 2 ^ (prefixWord ++ tailWord_354404).sum := by decide
  have hdescent : baseEnd_354404 < baseStart_354404 := by decide
  rcases family_descends (prefixWord ++ tailWord_354404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354410 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_354410 : Nat := 118140960795 + 354410 * 2 ^ 59
def prefixEnd_354410 : Nat := 4983230072969 + 3 ^ 40 * 354410 * 2
def baseEnd_354410 : Nat := 40440595280014133987801

theorem tailTrace_354410 : CollatzResearch.WordTrace tailWord_354410 prefixEnd_354410 40440595280014133987801 := by
  unfold tailWord_354410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231598661510143313549171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8617596430693715502797789 3231598661510143313549171)
  ·
    refine ⟨4847397992265214970323757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3231598661510143313549171 4847397992265214970323757)
    ·
      refine ⟨1817774247099455613871409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4847397992265214970323757 1817774247099455613871409)
      ·
        refine ⟨1363330685324591710403557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1817774247099455613871409 1363330685324591710403557)
        ·
          refine ⟨255624503498360945700667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1363330685324591710403557 255624503498360945700667)
          ·
            refine ⟨383436755247541418551001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255624503498360945700667 383436755247541418551001)
            ·
              refine ⟨287577566435656063913251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383436755247541418551001 287577566435656063913251)
              ·
                refine ⟨431366349653484095869877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287577566435656063913251 431366349653484095869877)
                ·
                  refine ⟨40440595280014133987801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 431366349653484095869877 40440595280014133987801)
                  ·
                    rfl

theorem cell22_354410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_354410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354410 prefixEnd_354410 := by exact prefixLift 354410
  have htrace : WordTrace (prefixWord ++ tailWord_354410) baseStart_354410 baseEnd_354410 := by
    simpa [prefixWord, tailWord_354410, baseEnd_354410] using wordTrace_append hprefix tailTrace_354410
  have hstable : (prefixWord ++ tailWord_354410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354410).length < 2 ^ (prefixWord ++ tailWord_354410).sum := by decide
  have hdescent : baseEnd_354410 < baseStart_354410 := by decide
  rcases family_descends (prefixWord ++ tailWord_354410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354455 : List Nat := [1, 1, 3, 3, 4, 2, 2, 2, 4]
def baseStart_354455 : Nat := 118140960795 + 354455 * 2 ^ 59
def prefixEnd_354455 : Nat := 4983230072969 + 3 ^ 40 * 354455 * 2
def baseEnd_354455 : Nat := 40445730086559094862755

theorem tailTrace_354455 : CollatzResearch.WordTrace tailWord_354455 prefixEnd_354455 40445730086559094862755 := by
  unfold tailWord_354455
  simp only [CollatzResearch.WordTrace]
  refine ⟨12928035930877545939584819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8618690620585030626389879 12928035930877545939584819)
  ·
    refine ⟨19392053896316318909377229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12928035930877545939584819 19392053896316318909377229)
    ·
      refine ⟨7272020211118619591016461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19392053896316318909377229 7272020211118619591016461)
      ·
        refine ⟨2727007579169482346631173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7272020211118619591016461 2727007579169482346631173)
        ·
          refine ⟨511313921094277939993345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2727007579169482346631173 511313921094277939993345)
          ·
            refine ⟨383485440820708454995009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511313921094277939993345 383485440820708454995009)
            ·
              refine ⟨287614080615531341246257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383485440820708454995009 287614080615531341246257)
              ·
                refine ⟨215710560461648505934693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287614080615531341246257 215710560461648505934693)
                ·
                  refine ⟨40445730086559094862755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215710560461648505934693 40445730086559094862755)
                  ·
                    rfl

theorem cell22_354455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 4].length) (baseStart_354455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354455 prefixEnd_354455 := by exact prefixLift 354455
  have htrace : WordTrace (prefixWord ++ tailWord_354455) baseStart_354455 baseEnd_354455 := by
    simpa [prefixWord, tailWord_354455, baseEnd_354455] using wordTrace_append hprefix tailTrace_354455
  have hstable : (prefixWord ++ tailWord_354455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354455).length < 2 ^ (prefixWord ++ tailWord_354455).sum := by decide
  have hdescent : baseEnd_354455 < baseStart_354455 := by decide
  rcases family_descends (prefixWord ++ tailWord_354455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354466 : List Nat := [3, 3, 1, 3, 1, 1, 3, 7]
def baseStart_354466 : Nat := 118140960795 + 354466 * 2 ^ 59
def prefixEnd_354466 : Nat := 4983230072969 + 3 ^ 40 * 354466 * 2
def baseEnd_354466 : Nat := 13482328420497435840359

theorem tailTrace_354466 : CollatzResearch.WordTrace tailWord_354466 prefixEnd_354466 13482328420497435840359 := by
  unfold tailWord_354466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3232109283459423704558813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8618958089225129878823501 3232109283459423704558813)
  ·
    refine ⟨1212040981297283889209555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3232109283459423704558813 1212040981297283889209555)
    ·
      refine ⟨1818061471945925833814333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1212040981297283889209555 1818061471945925833814333)
      ·
        refine ⟨681773051979722187680375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1818061471945925833814333 681773051979722187680375)
        ·
          refine ⟨1022659577969583281520563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681773051979722187680375 1022659577969583281520563)
          ·
            refine ⟨1533989366954374922280845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022659577969583281520563 1533989366954374922280845)
            ·
              refine ⟨575246012607890595855317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1533989366954374922280845 575246012607890595855317)
              ·
                refine ⟨13482328420497435840359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 575246012607890595855317 13482328420497435840359)
                ·
                  rfl

theorem cell22_354466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_354466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354466 prefixEnd_354466 := by exact prefixLift 354466
  have htrace : WordTrace (prefixWord ++ tailWord_354466) baseStart_354466 baseEnd_354466 := by
    simpa [prefixWord, tailWord_354466, baseEnd_354466] using wordTrace_append hprefix tailTrace_354466
  have hstable : (prefixWord ++ tailWord_354466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354466).length < 2 ^ (prefixWord ++ tailWord_354466).sum := by decide
  have hdescent : baseEnd_354466 < baseStart_354466 := by decide
  rcases family_descends (prefixWord ++ tailWord_354466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354485 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_354485 : Nat := 118140960795 + 354485 * 2 ^ 59
def prefixEnd_354485 : Nat := 4983230072969 + 3 ^ 40 * 354485 * 2
def baseEnd_354485 : Nat := 121347459872767206338173

theorem tailTrace_354485 : CollatzResearch.WordTrace tailWord_354485 prefixEnd_354485 121347459872767206338173 := by
  unfold tailWord_354485
  simp only [CollatzResearch.WordTrace]
  refine ⟨12929130120768861063176909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8619420080512574042117939 12929130120768861063176909)
  ·
    refine ⟨4848423795288322898691341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12929130120768861063176909 4848423795288322898691341)
    ·
      refine ⟨1818158923233121087009253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4848423795288322898691341 1818158923233121087009253)
      ·
        refine ⟨340904798106210203814235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1818158923233121087009253 340904798106210203814235)
        ·
          refine ⟨511357197159315305721353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340904798106210203814235 511357197159315305721353)
          ·
            refine ⟨383517897869486479291015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511357197159315305721353 383517897869486479291015)
            ·
              refine ⟨575276846804229718936523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383517897869486479291015 575276846804229718936523)
              ·
                refine ⟨862915270206344578404785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575276846804229718936523 862915270206344578404785)
                ·
                  refine ⟨647186452654758433803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 862915270206344578404785 647186452654758433803589)
                  ·
                    refine ⟨121347459872767206338173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 647186452654758433803589 121347459872767206338173)
                    ·
                      rfl

theorem cell22_354485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_354485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354485 prefixEnd_354485 := by exact prefixLift 354485
  have htrace : WordTrace (prefixWord ++ tailWord_354485) baseStart_354485 baseEnd_354485 := by
    simpa [prefixWord, tailWord_354485, baseEnd_354485] using wordTrace_append hprefix tailTrace_354485
  have hstable : (prefixWord ++ tailWord_354485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354485).length < 2 ^ (prefixWord ++ tailWord_354485).sum := by decide
  have hdescent : baseEnd_354485 < baseStart_354485 := by decide
  rcases family_descends (prefixWord ++ tailWord_354485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354539 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 6]
def baseStart_354539 : Nat := 118140960795 + 354539 * 2 ^ 59
def prefixEnd_354539 : Nat := 4983230072969 + 3 ^ 40 * 354539 * 2
def baseEnd_354539 : Nat := 40455315058776355162669

theorem tailTrace_354539 : CollatzResearch.WordTrace tailWord_354539 prefixEnd_354539 40455315058776355162669 := by
  unfold tailWord_354539
  simp only [CollatzResearch.WordTrace]
  refine ⟨12931099662573228285642671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8620733108382152190428447 12931099662573228285642671)
  ·
    refine ⟨19396649493859842428464007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12931099662573228285642671 19396649493859842428464007)
    ·
      refine ⟨29094974240789763642696011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19396649493859842428464007 29094974240789763642696011)
      ·
        refine ⟨43642461361184645464044017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29094974240789763642696011 43642461361184645464044017)
        ·
          refine ⟨32731846020888484098033013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43642461361184645464044017 32731846020888484098033013)
          ·
            refine ⟨3068610564458295384190595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32731846020888484098033013 3068610564458295384190595)
            ·
              refine ⟨4602915846687443076285893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068610564458295384190595 4602915846687443076285893)
              ·
                refine ⟨863046721253895576803605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4602915846687443076285893 863046721253895576803605)
                ·
                  refine ⟨40455315058776355162669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 863046721253895576803605 40455315058776355162669)
                  ·
                    rfl

theorem cell22_354539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 6].length) (baseStart_354539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354539 prefixEnd_354539 := by exact prefixLift 354539
  have htrace : WordTrace (prefixWord ++ tailWord_354539) baseStart_354539 baseEnd_354539 := by
    simpa [prefixWord, tailWord_354539, baseEnd_354539] using wordTrace_append hprefix tailTrace_354539
  have hstable : (prefixWord ++ tailWord_354539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354539).length < 2 ^ (prefixWord ++ tailWord_354539).sum := by decide
  have hdescent : baseEnd_354539 < baseStart_354539 := by decide
  rcases family_descends (prefixWord ++ tailWord_354539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354558 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_354558 : Nat := 118140960795 + 354558 * 2 ^ 59
def prefixEnd_354558 : Nat := 4983230072969 + 3 ^ 40 * 354558 * 2
def baseEnd_354558 : Nat := 121372449264619349262949

theorem tailTrace_354558 : CollatzResearch.WordTrace tailWord_354558 prefixEnd_354558 121372449264619349262949 := by
  unfold tailWord_354558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616474081188049316323041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8621195099669596353722885 1616474081188049316323041)
  ·
    refine ⟨1212355560891036987242281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1616474081188049316323041 1212355560891036987242281)
    ·
      refine ⟨909266670668277740431711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1212355560891036987242281 909266670668277740431711)
      ·
        refine ⟨1363900006002416610647567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909266670668277740431711 1363900006002416610647567)
        ·
          refine ⟨2045850009003624915971351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363900006002416610647567 2045850009003624915971351)
          ·
            refine ⟨3068775013505437373957027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045850009003624915971351 3068775013505437373957027)
            ·
              refine ⟨4603162520258156060935541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068775013505437373957027 4603162520258156060935541)
              ·
                refine ⟨431546486274202130712707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4603162520258156060935541 431546486274202130712707)
                ·
                  refine ⟨647319729411303196069061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431546486274202130712707 647319729411303196069061)
                  ·
                    refine ⟨121372449264619349262949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 647319729411303196069061 121372449264619349262949)
                    ·
                      rfl

theorem cell22_354558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_354558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354558 prefixEnd_354558 := by exact prefixLift 354558
  have htrace : WordTrace (prefixWord ++ tailWord_354558) baseStart_354558 baseEnd_354558 := by
    simpa [prefixWord, tailWord_354558, baseEnd_354558] using wordTrace_append hprefix tailTrace_354558
  have hstable : (prefixWord ++ tailWord_354558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354558).length < 2 ^ (prefixWord ++ tailWord_354558).sum := by decide
  have hdescent : baseEnd_354558 < baseStart_354558 := by decide
  rcases family_descends (prefixWord ++ tailWord_354558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354571 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 4, 3]
def baseStart_354571 : Nat := 118140960795 + 354571 * 2 ^ 59
def prefixEnd_354571 : Nat := 4983230072969 + 3 ^ 40 * 354571 * 2
def baseEnd_354571 : Nat := 121376899430291648687909

theorem tailTrace_354571 : CollatzResearch.WordTrace tailWord_354571 prefixEnd_354571 121376899430291648687909 := by
  unfold tailWord_354571
  simp only [CollatzResearch.WordTrace]
  refine ⟨12932266798457297750807567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8621511198971531833871711 12932266798457297750807567)
  ·
    refine ⟨19398400197685946626211351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12932266798457297750807567 19398400197685946626211351)
    ·
      refine ⟨29097600296528919939317027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19398400197685946626211351 29097600296528919939317027)
      ·
        refine ⟨43646400444793379908975541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29097600296528919939317027 43646400444793379908975541)
        ·
          refine ⟨4091850041699379366466457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43646400444793379908975541 4091850041699379366466457)
          ·
            refine ⟨3068887531274534524849843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4091850041699379366466457 3068887531274534524849843)
            ·
              refine ⟨4603331296911801787274765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068887531274534524849843 4603331296911801787274765)
              ·
                refine ⟨1726249236341925670228037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4603331296911801787274765 1726249236341925670228037)
                ·
                  refine ⟨323671731814111063167757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726249236341925670228037 323671731814111063167757)
                  ·
                    refine ⟨121376899430291648687909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323671731814111063167757 121376899430291648687909)
                    ·
                      rfl

theorem cell22_354571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 3].length) (baseStart_354571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354571 prefixEnd_354571 := by exact prefixLift 354571
  have htrace : WordTrace (prefixWord ++ tailWord_354571) baseStart_354571 baseEnd_354571 := by
    simpa [prefixWord, tailWord_354571, baseEnd_354571] using wordTrace_append hprefix tailTrace_354571
  have hstable : (prefixWord ++ tailWord_354571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354571).length < 2 ^ (prefixWord ++ tailWord_354571).sum := by decide
  have hdescent : baseEnd_354571 < baseStart_354571 := by decide
  rcases family_descends (prefixWord ++ tailWord_354571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354605 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_354605 : Nat := 118140960795 + 354605 * 2 ^ 59
def prefixEnd_354605 : Nat := 4983230072969 + 3 ^ 40 * 354605 * 2
def baseEnd_354605 : Nat := 121388538325126893337805

theorem tailTrace_354605 : CollatzResearch.WordTrace tailWord_354605 prefixEnd_354605 121388538325126893337805 := by
  unfold tailWord_354605
  simp only [CollatzResearch.WordTrace]
  refine ⟨12933506880334121557545269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8622337920222747705030179 12933506880334121557545269)
  ·
    refine ⟨1212516270031323896019869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12933506880334121557545269 1212516270031323896019869)
    ·
      refine ⟨454693601261746461007451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1212516270031323896019869 454693601261746461007451)
      ·
        refine ⟨682040401892619691511177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454693601261746461007451 682040401892619691511177)
        ·
          refine ⟨511530301419464768633383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682040401892619691511177 511530301419464768633383)
          ·
            refine ⟨767295452129197152950075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511530301419464768633383 767295452129197152950075)
            ·
              refine ⟨1150943178193795729425113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767295452129197152950075 1150943178193795729425113)
              ·
                refine ⟨863207383645346797068835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150943178193795729425113 863207383645346797068835)
                ·
                  refine ⟨1294811075468020195603253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863207383645346797068835 1294811075468020195603253)
                  ·
                    refine ⟨121388538325126893337805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1294811075468020195603253 121388538325126893337805)
                    ·
                      rfl

theorem cell22_354605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_354605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354605 prefixEnd_354605 := by exact prefixLift 354605
  have htrace : WordTrace (prefixWord ++ tailWord_354605) baseStart_354605 baseEnd_354605 := by
    simpa [prefixWord, tailWord_354605, baseEnd_354605] using wordTrace_append hprefix tailTrace_354605
  have hstable : (prefixWord ++ tailWord_354605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354605).length < 2 ^ (prefixWord ++ tailWord_354605).sum := by decide
  have hdescent : baseEnd_354605 < baseStart_354605 := by decide
  rcases family_descends (prefixWord ++ tailWord_354605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354654 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_354654 : Nat := 118140960795 + 354654 * 2 ^ 59
def prefixEnd_354654 : Nat := 4983230072969 + 3 ^ 40 * 354654 * 2
def baseEnd_354654 : Nat := 121405312026507098862655

theorem tailTrace_354654 : CollatzResearch.WordTrace tailWord_354654 prefixEnd_354654 121405312026507098862655 := by
  unfold tailWord_354654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616911757144575365759877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8623529371437735284052677 1616911757144575365759877)
  ·
    refine ⟨303170954464607881079977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1616911757144575365759877 303170954464607881079977)
    ·
      refine ⟨227378215848455910809983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303170954464607881079977 227378215848455910809983)
      ·
        refine ⟨341067323772683866214975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227378215848455910809983 341067323772683866214975)
        ·
          refine ⟨511600985659025799322463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341067323772683866214975 511600985659025799322463)
          ·
            refine ⟨767401478488538698983695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511600985659025799322463 767401478488538698983695)
            ·
              refine ⟨1151102217732808048475543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767401478488538698983695 1151102217732808048475543)
              ·
                refine ⟨1726653326599212072713315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151102217732808048475543 1726653326599212072713315)
                ·
                  refine ⟨2589979989898818109069973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726653326599212072713315 2589979989898818109069973)
                  ·
                    refine ⟨121405312026507098862655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2589979989898818109069973 121405312026507098862655)
                    ·
                      rfl

theorem cell22_354654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_354654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354654 prefixEnd_354654 := by exact prefixLift 354654
  have htrace : WordTrace (prefixWord ++ tailWord_354654) baseStart_354654 baseEnd_354654 := by
    simpa [prefixWord, tailWord_354654, baseEnd_354654] using wordTrace_append hprefix tailTrace_354654
  have hstable : (prefixWord ++ tailWord_354654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354654).length < 2 ^ (prefixWord ++ tailWord_354654).sum := by decide
  have hdescent : baseEnd_354654 < baseStart_354654 := by decide
  rcases family_descends (prefixWord ++ tailWord_354654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354723 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 4, 3]
def baseStart_354723 : Nat := 118140960795 + 354723 * 2 ^ 59
def prefixEnd_354723 : Nat := 4983230072969 + 3 ^ 40 * 354723 * 2
def baseEnd_354723 : Nat := 121428932136613918887443

theorem tailTrace_354723 : CollatzResearch.WordTrace tailWord_354723 prefixEnd_354723 121428932136613918887443 := by
  unfold tailWord_354723
  simp only [CollatzResearch.WordTrace]
  refine ⟨12937810693906627710340823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8625207129271085140227215 12937810693906627710340823)
  ·
    refine ⟨19406716040859941565511235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12937810693906627710340823 19406716040859941565511235)
    ·
      refine ⟨29110074061289912348266853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19406716040859941565511235 29110074061289912348266853)
      ·
        refine ⟨5458138886491858565300035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29110074061289912348266853 5458138886491858565300035)
        ·
          refine ⟨8187208329737787847950053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458138886491858565300035 8187208329737787847950053)
          ·
            refine ⟨1535101561825835221490635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8187208329737787847950053 1535101561825835221490635)
            ·
              refine ⟨2302652342738752832235953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535101561825835221490635 2302652342738752832235953)
              ·
                refine ⟨1726989257054064624176965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2302652342738752832235953 1726989257054064624176965)
                ·
                  refine ⟨323810485697637117033181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726989257054064624176965 323810485697637117033181)
                  ·
                    refine ⟨121428932136613918887443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323810485697637117033181 121428932136613918887443)
                    ·
                      rfl

theorem cell22_354723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 3].length) (baseStart_354723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354723 prefixEnd_354723 := by exact prefixLift 354723
  have htrace : WordTrace (prefixWord ++ tailWord_354723) baseStart_354723 baseEnd_354723 := by
    simpa [prefixWord, tailWord_354723, baseEnd_354723] using wordTrace_append hprefix tailTrace_354723
  have hstable : (prefixWord ++ tailWord_354723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354723).length < 2 ^ (prefixWord ++ tailWord_354723).sum := by decide
  have hdescent : baseEnd_354723 < baseStart_354723 := by decide
  rcases family_descends (prefixWord ++ tailWord_354723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354738 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_354738 : Nat := 118140960795 + 354738 * 2 ^ 59
def prefixEnd_354738 : Nat := 4983230072969 + 3 ^ 40 * 354738 * 2
def baseEnd_354738 : Nat := 121434066943158879762397

theorem tailTrace_354738 : CollatzResearch.WordTrace tailWord_354738 prefixEnd_354738 121434066943158879762397 := by
  unfold tailWord_354738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234589447213071318034217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8625571859234856848091245 3234589447213071318034217)
  ·
    refine ⟨2425942085409803488525663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3234589447213071318034217 2425942085409803488525663)
    ·
      refine ⟨3638913128114705232788495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2425942085409803488525663 3638913128114705232788495)
      ·
        refine ⟨5458369692172057849182743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3638913128114705232788495 5458369692172057849182743)
        ·
          refine ⟨8187554538258086773774115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458369692172057849182743 8187554538258086773774115)
          ·
            refine ⟨12281331807387130160661173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187554538258086773774115 12281331807387130160661173)
            ·
              refine ⟨1151374856942543452561985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12281331807387130160661173 1151374856942543452561985)
              ·
                refine ⟨863531142706907589421489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151374856942543452561985 863531142706907589421489)
                ·
                  refine ⟨647648357030180692066117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 863531142706907589421489 647648357030180692066117)
                  ·
                    refine ⟨121434066943158879762397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 647648357030180692066117 121434066943158879762397)
                    ·
                      rfl

theorem cell22_354738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_354738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354738 prefixEnd_354738 := by exact prefixLift 354738
  have htrace : WordTrace (prefixWord ++ tailWord_354738) baseStart_354738 baseEnd_354738 := by
    simpa [prefixWord, tailWord_354738, baseEnd_354738] using wordTrace_append hprefix tailTrace_354738
  have hstable : (prefixWord ++ tailWord_354738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354738).length < 2 ^ (prefixWord ++ tailWord_354738).sum := by decide
  have hdescent : baseEnd_354738 < baseStart_354738 := by decide
  rcases family_descends (prefixWord ++ tailWord_354738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354811 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 10]
def baseStart_354811 : Nat := 118140960795 + 354811 * 2 ^ 59
def prefixEnd_354811 : Nat := 4983230072969 + 3 ^ 40 * 354811 * 2
def baseEnd_354811 : Nat := 121459056335011022687173

theorem tailTrace_354811 : CollatzResearch.WordTrace tailWord_354811 prefixEnd_354811 121459056335011022687173 := by
  unfold tailWord_354811
  simp only [CollatzResearch.WordTrace]
  refine ⟨12941020317587818739544287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8627346878391879159696191 12941020317587818739544287)
  ·
    refine ⟨19411530476381728109316431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12941020317587818739544287 19411530476381728109316431)
    ·
      refine ⟨29117295714572592163974647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19411530476381728109316431 29117295714572592163974647)
      ·
        refine ⟨43675943571858888245961971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29117295714572592163974647 43675943571858888245961971)
        ·
          refine ⟨65513915357788332368942957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43675943571858888245961971 65513915357788332368942957)
          ·
            refine ⟨24567718259170624638353609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65513915357788332368942957 24567718259170624638353609)
            ·
              refine ⟨18425788694377968478765207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24567718259170624638353609 18425788694377968478765207)
              ·
                refine ⟨27638683041566952718147811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18425788694377968478765207 27638683041566952718147811)
                ·
                  refine ⟨41458024562350429077221717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27638683041566952718147811 41458024562350429077221717)
                  ·
                    refine ⟨121459056335011022687173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 41458024562350429077221717 121459056335011022687173)
                    ·
                      rfl

theorem cell22_354811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_354811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354811 prefixEnd_354811 := by exact prefixLift 354811
  have htrace : WordTrace (prefixWord ++ tailWord_354811) baseStart_354811 baseEnd_354811 := by
    simpa [prefixWord, tailWord_354811, baseEnd_354811] using wordTrace_append hprefix tailTrace_354811
  have hstable : (prefixWord ++ tailWord_354811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354811).length < 2 ^ (prefixWord ++ tailWord_354811).sum := by decide
  have hdescent : baseEnd_354811 < baseStart_354811 := by decide
  rcases family_descends (prefixWord ++ tailWord_354811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354813 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_354813 : Nat := 118140960795 + 354813 * 2 ^ 59
def prefixEnd_354813 : Nat := 4983230072969 + 3 ^ 40 * 354813 * 2
def baseEnd_354813 : Nat := 121459740975883684137167

theorem tailTrace_354813 : CollatzResearch.WordTrace tailWord_354813 prefixEnd_354813 121459740975883684137167 := by
  unfold tailWord_354813
  simp only [CollatzResearch.WordTrace]
  refine ⟨12941093263580573081117093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8627395509053715387411395 12941093263580573081117093)
  ·
    refine ⟨2426454986921357452709455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12941093263580573081117093 2426454986921357452709455)
    ·
      refine ⟨3639682480382036179064183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2426454986921357452709455 3639682480382036179064183)
      ·
        refine ⟨5459523720573054268596275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639682480382036179064183 5459523720573054268596275)
        ·
          refine ⟨8189285580859581402894413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5459523720573054268596275 8189285580859581402894413)
          ·
            refine ⟨3070982092822343026085405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8189285580859581402894413 3070982092822343026085405)
            ·
              refine ⟨1151618284808378634782027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3070982092822343026085405 1151618284808378634782027)
              ·
                refine ⟨1727427427212567952173041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151618284808378634782027 1727427427212567952173041)
                ·
                  refine ⟨1295570570409425964129781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1727427427212567952173041 1295570570409425964129781)
                  ·
                    refine ⟨121459740975883684137167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1295570570409425964129781 121459740975883684137167)
                    ·
                      rfl

theorem cell22_354813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_354813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354813 prefixEnd_354813 := by exact prefixLift 354813
  have htrace : WordTrace (prefixWord ++ tailWord_354813) baseStart_354813 baseEnd_354813 := by
    simpa [prefixWord, tailWord_354813, baseEnd_354813] using wordTrace_append hprefix tailTrace_354813
  have hstable : (prefixWord ++ tailWord_354813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354813).length < 2 ^ (prefixWord ++ tailWord_354813).sum := by decide
  have hdescent : baseEnd_354813 < baseStart_354813 := by decide
  rcases family_descends (prefixWord ++ tailWord_354813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354836 : List Nat := [2, 4, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_354836 : Nat := 118140960795 + 354836 * 2 ^ 59
def prefixEnd_354836 : Nat := 4983230072969 + 3 ^ 40 * 354836 * 2
def baseEnd_354836 : Nat := 121467614345919290812097

theorem tailTrace_354836 : CollatzResearch.WordTrace tailWord_354836 prefixEnd_354836 121467614345919290812097 := by
  unfold tailWord_354836
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470966071248624004602181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8627954761664832006136241 6470966071248624004602181)
  ·
    refine ⟨1213306138359117000862909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6470966071248624004602181 1213306138359117000862909)
    ·
      refine ⟨454989801884668875323591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1213306138359117000862909 454989801884668875323591)
      ·
        refine ⟨682484702827003312985387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454989801884668875323591 682484702827003312985387)
        ·
          refine ⟨1023727054240504969478081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682484702827003312985387 1023727054240504969478081)
          ·
            refine ⟨767795290680378727108561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023727054240504969478081 767795290680378727108561)
            ·
              refine ⟨575846468010284045331421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767795290680378727108561 575846468010284045331421)
              ·
                refine ⟨215942425503856516999283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 575846468010284045331421 215942425503856516999283)
                ·
                  refine ⟨323913638255784775498925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215942425503856516999283 323913638255784775498925)
                  ·
                    refine ⟨121467614345919290812097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323913638255784775498925 121467614345919290812097)
                    ·
                      rfl

theorem cell22_354836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_354836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354836 prefixEnd_354836 := by exact prefixLift 354836
  have htrace : WordTrace (prefixWord ++ tailWord_354836) baseStart_354836 baseEnd_354836 := by
    simpa [prefixWord, tailWord_354836, baseEnd_354836] using wordTrace_append hprefix tailTrace_354836
  have hstable : (prefixWord ++ tailWord_354836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354836).length < 2 ^ (prefixWord ++ tailWord_354836).sum := by decide
  have hdescent : baseEnd_354836 < baseStart_354836 := by decide
  rcases family_descends (prefixWord ++ tailWord_354836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354873 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 3, 6]
def baseStart_354873 : Nat := 118140960795 + 354873 * 2 ^ 59
def prefixEnd_354873 : Nat := 4983230072969 + 3 ^ 40 * 354873 * 2
def baseEnd_354873 : Nat := 121480280202063527636983

theorem tailTrace_354873 : CollatzResearch.WordTrace tailWord_354873 prefixEnd_354873 121480280202063527636983 := by
  unfold tailWord_354873
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943281643363203328301273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8628854428908802218867515 12943281643363203328301273)
  ·
    refine ⟨9707461232522402496225955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12943281643363203328301273 9707461232522402496225955)
    ·
      refine ⟨14561191848783603744338933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9707461232522402496225955 14561191848783603744338933)
      ·
        refine ⟨1365111735823462851031775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14561191848783603744338933 1365111735823462851031775)
        ·
          refine ⟨2047667603735194276547663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365111735823462851031775 2047667603735194276547663)
          ·
            refine ⟨3071501405602791414821495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047667603735194276547663 3071501405602791414821495)
            ·
              refine ⟨4607252108404187122232243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071501405602791414821495 4607252108404187122232243)
              ·
                refine ⟨6910878162606280683348365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607252108404187122232243 6910878162606280683348365)
                ·
                  refine ⟨2591579310977355256255637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6910878162606280683348365 2591579310977355256255637)
                  ·
                    refine ⟨121480280202063527636983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2591579310977355256255637 121480280202063527636983)
                    ·
                      rfl

theorem cell22_354873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_354873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354873 prefixEnd_354873 := by exact prefixLift 354873
  have htrace : WordTrace (prefixWord ++ tailWord_354873) baseStart_354873 baseEnd_354873 := by
    simpa [prefixWord, tailWord_354873, baseEnd_354873] using wordTrace_append hprefix tailTrace_354873
  have hstable : (prefixWord ++ tailWord_354873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354873).length < 2 ^ (prefixWord ++ tailWord_354873).sum := by decide
  have hdescent : baseEnd_354873 < baseStart_354873 := by decide
  rcases family_descends (prefixWord ++ tailWord_354873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354926 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_354926 : Nat := 118140960795 + 354926 * 2 ^ 59
def prefixEnd_354926 : Nat := 4983230072969 + 3 ^ 40 * 354926 * 2
def baseEnd_354926 : Nat := 121498423185189056061821

theorem tailTrace_354926 : CollatzResearch.WordTrace tailWord_354926 prefixEnd_354926 121498423185189056061821 := by
  unfold tailWord_354926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1618151839021399172497579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8630143141447462253320421 1618151839021399172497579)
  ·
    refine ⟨2427227758532098758746369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1618151839021399172497579 2427227758532098758746369)
    ·
      refine ⟨1820420818899074069059777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2427227758532098758746369 1820420818899074069059777)
      ·
        refine ⟨1365315614174305551794833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1820420818899074069059777 1365315614174305551794833)
        ·
          refine ⟨1023986710630729163846125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1365315614174305551794833 1023986710630729163846125)
          ·
            refine ⟨383995016486523436442297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1023986710630729163846125 383995016486523436442297)
            ·
              refine ⟨287996262364892577331723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383995016486523436442297 287996262364892577331723)
              ·
                refine ⟨431994393547338865997585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287996262364892577331723 431994393547338865997585)
                ·
                  refine ⟨323995795160504149498189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431994393547338865997585 323995795160504149498189)
                  ·
                    refine ⟨121498423185189056061821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 323995795160504149498189 121498423185189056061821)
                    ·
                      rfl

theorem cell22_354926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_354926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354926 prefixEnd_354926 := by exact prefixLift 354926
  have htrace : WordTrace (prefixWord ++ tailWord_354926) baseStart_354926 baseEnd_354926 := by
    simpa [prefixWord, tailWord_354926, baseEnd_354926] using wordTrace_append hprefix tailTrace_354926
  have hstable : (prefixWord ++ tailWord_354926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354926).length < 2 ^ (prefixWord ++ tailWord_354926).sum := by decide
  have hdescent : baseEnd_354926 < baseStart_354926 := by decide
  rcases family_descends (prefixWord ++ tailWord_354926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354980 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_354980 : Nat := 118140960795 + 354980 * 2 ^ 59
def prefixEnd_354980 : Nat := 4983230072969 + 3 ^ 40 * 354980 * 2
def baseEnd_354980 : Nat := 121516908488750915211655

theorem tailTrace_354980 : CollatzResearch.WordTrace tailWord_354980 prefixEnd_354980 121516908488750915211655 := by
  unfold tailWord_354980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6473592126987780301223197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8631456169317040401630929 6473592126987780301223197)
  ·
    refine ⟨2427597047620417612958699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6473592126987780301223197 2427597047620417612958699)
    ·
      refine ⟨3641395571430626419438049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2427597047620417612958699 3641395571430626419438049)
      ·
        refine ⟨2731046678572969814578537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3641395571430626419438049 2731046678572969814578537)
        ·
          refine ⟨2048285008929727360933903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2731046678572969814578537 2048285008929727360933903)
          ·
            refine ⟨3072427513394591041400855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048285008929727360933903 3072427513394591041400855)
            ·
              refine ⟨4608641270091886562101283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072427513394591041400855 4608641270091886562101283)
              ·
                refine ⟨6912961905137829843151925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608641270091886562101283 6912961905137829843151925)
                ·
                  refine ⟨648090178606671547795493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6912961905137829843151925 648090178606671547795493)
                  ·
                    refine ⟨121516908488750915211655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 648090178606671547795493 121516908488750915211655)
                    ·
                      rfl

theorem cell22_354980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_354980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354980 prefixEnd_354980 := by exact prefixLift 354980
  have htrace : WordTrace (prefixWord ++ tailWord_354980) baseStart_354980 baseEnd_354980 := by
    simpa [prefixWord, tailWord_354980, baseEnd_354980] using wordTrace_append hprefix tailTrace_354980
  have hstable : (prefixWord ++ tailWord_354980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354980).length < 2 ^ (prefixWord ++ tailWord_354980).sum := by decide
  have hdescent : baseEnd_354980 < baseStart_354980 := by decide
  rcases family_descends (prefixWord ++ tailWord_354980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354995 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 6]
def baseStart_354995 : Nat := 118140960795 + 354995 * 2 ^ 59
def prefixEnd_354995 : Nat := 4983230072969 + 3 ^ 40 * 354995 * 2
def baseEnd_354995 : Nat := 40507347765098625362203

theorem tailTrace_354995 : CollatzResearch.WordTrace tailWord_354995 prefixEnd_354995 40507347765098625362203 := by
  unfold tailWord_354995
  simp only [CollatzResearch.WordTrace]
  refine ⟨12947731348921218164242439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8631820899280812109494959 12947731348921218164242439)
  ·
    refine ⟨19421597023381827246363659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12947731348921218164242439 19421597023381827246363659)
    ·
      refine ⟨29132395535072740869545489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19421597023381827246363659 29132395535072740869545489)
      ·
        refine ⟨21849296651304555652159117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29132395535072740869545489 21849296651304555652159117)
        ·
          refine ⟨8193486244239208369559669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21849296651304555652159117 8193486244239208369559669)
          ·
            refine ⟨768139335397425784646219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8193486244239208369559669 768139335397425784646219)
            ·
              refine ⟨1152209003096138676969329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768139335397425784646219 1152209003096138676969329)
              ·
                refine ⟨864156752322104007726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152209003096138676969329 864156752322104007726997)
                ·
                  refine ⟨40507347765098625362203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 864156752322104007726997 40507347765098625362203)
                  ·
                    rfl

theorem cell22_354995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 6].length) (baseStart_354995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354995 prefixEnd_354995 := by exact prefixLift 354995
  have htrace : WordTrace (prefixWord ++ tailWord_354995) baseStart_354995 baseEnd_354995 := by
    simpa [prefixWord, tailWord_354995, baseEnd_354995] using wordTrace_append hprefix tailTrace_354995
  have hstable : (prefixWord ++ tailWord_354995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354995).length < 2 ^ (prefixWord ++ tailWord_354995).sum := by decide
  have hdescent : baseEnd_354995 < baseStart_354995 := by decide
  rcases family_descends (prefixWord ++ tailWord_354995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354997 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_354997 : Nat := 118140960795 + 354997 * 2 ^ 59
def prefixEnd_354997 : Nat := 4983230072969 + 3 ^ 40 * 354997 * 2
def baseEnd_354997 : Nat := 121522727936168537536603

theorem tailTrace_354997 : CollatzResearch.WordTrace tailWord_354997 prefixEnd_354997 121522727936168537536603 := by
  unfold tailWord_354997
  simp only [CollatzResearch.WordTrace]
  refine ⟨12947804294913972505815245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8631869529942648337210163 12947804294913972505815245)
  ·
    refine ⟨4855426610592739689680717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12947804294913972505815245 4855426610592739689680717)
    ·
      refine ⟨1820784978972277383630269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4855426610592739689680717 1820784978972277383630269)
      ·
        refine ⟨682794367114604018861351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1820784978972277383630269 682794367114604018861351)
        ·
          refine ⟨1024191550671906028292027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682794367114604018861351 1024191550671906028292027)
          ·
            refine ⟨1536287326007859042438041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024191550671906028292027 1536287326007859042438041)
            ·
              refine ⟨1152215494505894281828531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536287326007859042438041 1152215494505894281828531)
              ·
                refine ⟨1728323241758841422742797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152215494505894281828531 1728323241758841422742797)
                ·
                  refine ⟨648121215659565533528549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1728323241758841422742797 648121215659565533528549)
                  ·
                    refine ⟨121522727936168537536603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 648121215659565533528549 121522727936168537536603)
                    ·
                      rfl

theorem cell22_354997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_354997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_354997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_354997 prefixEnd_354997 := by exact prefixLift 354997
  have htrace : WordTrace (prefixWord ++ tailWord_354997) baseStart_354997 baseEnd_354997 := by
    simpa [prefixWord, tailWord_354997, baseEnd_354997] using wordTrace_append hprefix tailTrace_354997
  have hstable : (prefixWord ++ tailWord_354997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354997).length < 2 ^ (prefixWord ++ tailWord_354997).sum := by decide
  have hdescent : baseEnd_354997 < baseStart_354997 := by decide
  rcases family_descends (prefixWord ++ tailWord_354997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355025 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 4, 4]
def baseStart_355025 : Nat := 118140960795 + 355025 * 2 ^ 59
def prefixEnd_355025 : Nat := 4983230072969 + 3 ^ 40 * 355025 * 2
def baseEnd_355025 : Nat := 121532312908385797836517

theorem tailTrace_355025 : CollatzResearch.WordTrace tailWord_355025 prefixEnd_355025 121532312908385797836517 := by
  unfold tailWord_355025
  simp only [CollatzResearch.WordTrace]
  refine ⟨12948825538812533287834529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8632550359208355525223019 12948825538812533287834529)
  ·
    refine ⟨9711619154109399965875897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12948825538812533287834529 9711619154109399965875897)
    ·
      refine ⟨7283714365582049974406923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9711619154109399965875897 7283714365582049974406923)
      ·
        refine ⟨10925571548373074961610385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7283714365582049974406923 10925571548373074961610385)
        ·
          refine ⟨8194178661279806221207789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10925571548373074961610385 8194178661279806221207789)
          ·
            refine ⟨3072816997979927332952921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8194178661279806221207789 3072816997979927332952921)
            ·
              refine ⟨2304612748484945499714691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3072816997979927332952921 2304612748484945499714691)
              ·
                refine ⟨3456919122727418249572037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304612748484945499714691 3456919122727418249572037)
                ·
                  refine ⟨648172335511390921794757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3456919122727418249572037 648172335511390921794757)
                  ·
                    refine ⟨121532312908385797836517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 648172335511390921794757 121532312908385797836517)
                    ·
                      rfl

theorem cell22_355025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_355025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355025 prefixEnd_355025 := by exact prefixLift 355025
  have htrace : WordTrace (prefixWord ++ tailWord_355025) baseStart_355025 baseEnd_355025 := by
    simpa [prefixWord, tailWord_355025, baseEnd_355025] using wordTrace_append hprefix tailTrace_355025
  have hstable : (prefixWord ++ tailWord_355025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355025).length < 2 ^ (prefixWord ++ tailWord_355025).sum := by decide
  have hdescent : baseEnd_355025 < baseStart_355025 := by decide
  rcases family_descends (prefixWord ++ tailWord_355025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355029 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 6]
def baseStart_355029 : Nat := 118140960795 + 355029 * 2 ^ 59
def prefixEnd_355029 : Nat := 4983230072969 + 3 ^ 40 * 355029 * 2
def baseEnd_355029 : Nat := 40511227396710373578835

theorem tailTrace_355029 : CollatzResearch.WordTrace tailWord_355029 prefixEnd_355029 40511227396710373578835 := by
  unfold tailWord_355029
  simp only [CollatzResearch.WordTrace]
  refine ⟨12948971430798041970980141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8632647620532027980653427 12948971430798041970980141)
  ·
    refine ⟨4855864286549265739117553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12948971430798041970980141 4855864286549265739117553)
    ·
      refine ⟨3641898214911949304338165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4855864286549265739117553 3641898214911949304338165)
      ·
        refine ⟨341427957647995247281703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3641898214911949304338165 341427957647995247281703)
        ·
          refine ⟨512141936471992870922555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341427957647995247281703 512141936471992870922555)
          ·
            refine ⟨768212904707989306383833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512141936471992870922555 768212904707989306383833)
            ·
              refine ⟨576159678530991979787875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768212904707989306383833 576159678530991979787875)
              ·
                refine ⟨864239517796487969681813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576159678530991979787875 864239517796487969681813)
                ·
                  refine ⟨40511227396710373578835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 864239517796487969681813 40511227396710373578835)
                  ·
                    rfl

theorem cell22_355029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_355029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355029 prefixEnd_355029 := by exact prefixLift 355029
  have htrace : WordTrace (prefixWord ++ tailWord_355029) baseStart_355029 baseEnd_355029 := by
    simpa [prefixWord, tailWord_355029, baseEnd_355029] using wordTrace_append hprefix tailTrace_355029
  have hstable : (prefixWord ++ tailWord_355029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355029).length < 2 ^ (prefixWord ++ tailWord_355029).sum := by decide
  have hdescent : baseEnd_355029 < baseStart_355029 := by decide
  rcases family_descends (prefixWord ++ tailWord_355029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355089 : List Nat := [1, 2, 2, 1, 1, 3, 2, 6, 1, 3]
def baseStart_355089 : Nat := 118140960795 + 355089 * 2 ^ 59
def prefixEnd_355089 : Nat := 4983230072969 + 3 ^ 40 * 355089 * 2
def baseEnd_355089 : Nat := 121554221416310964236321

theorem tailTrace_355089 : CollatzResearch.WordTrace tailWord_355089 prefixEnd_355089 121554221416310964236321 := by
  unfold tailWord_355089
  simp only [CollatzResearch.WordTrace]
  refine ⟨12951159810580672218164321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8634106540387114812109547 12951159810580672218164321)
  ·
    refine ⟨9713369857935504163623241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12951159810580672218164321 9713369857935504163623241)
    ·
      refine ⟨7285027393451628122717431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9713369857935504163623241 7285027393451628122717431)
      ·
        refine ⟨10927541090177442184076147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7285027393451628122717431 10927541090177442184076147)
        ·
          refine ⟨16391311635266163276114221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10927541090177442184076147 16391311635266163276114221)
          ·
            refine ⟨6146741863224811228542833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16391311635266163276114221 6146741863224811228542833)
            ·
              refine ⟨4610056397418608421407125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6146741863224811228542833 4610056397418608421407125)
              ·
                refine ⟨216096393628997269753459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4610056397418608421407125 216096393628997269753459)
                ·
                  refine ⟨324144590443495904630189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216096393628997269753459 324144590443495904630189)
                  ·
                    refine ⟨121554221416310964236321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324144590443495904630189 121554221416310964236321)
                    ·
                      rfl

theorem cell22_355089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_355089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355089 prefixEnd_355089 := by exact prefixLift 355089
  have htrace : WordTrace (prefixWord ++ tailWord_355089) baseStart_355089 baseEnd_355089 := by
    simpa [prefixWord, tailWord_355089, baseEnd_355089] using wordTrace_append hprefix tailTrace_355089
  have hstable : (prefixWord ++ tailWord_355089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355089).length < 2 ^ (prefixWord ++ tailWord_355089).sum := by decide
  have hdescent : baseEnd_355089 < baseStart_355089 := by decide
  rcases family_descends (prefixWord ++ tailWord_355089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355140 : List Nat := [2, 3, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_355140 : Nat := 118140960795 + 355140 * 2 ^ 59
def prefixEnd_355140 : Nat := 4983230072969 + 3 ^ 40 * 355140 * 2
def baseEnd_355140 : Nat := 121571679758563831211165

theorem tailTrace_355140 : CollatzResearch.WordTrace tailWord_355140 prefixEnd_355140 121571679758563831211165 := by
  unfold tailWord_355140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6476509966697953964135437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8635346622263938618847249 6476509966697953964135437)
  ·
    refine ⟨2428691237511732736550789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6476509966697953964135437 2428691237511732736550789)
    ·
      refine ⟨455379607033449888103273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2428691237511732736550789 455379607033449888103273)
      ·
        refine ⟨341534705275087416077455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455379607033449888103273 341534705275087416077455)
        ·
          refine ⟨512302057912631124116183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341534705275087416077455 512302057912631124116183)
          ·
            refine ⟨768453086868946686174275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512302057912631124116183 768453086868946686174275)
            ·
              refine ⟨1152679630303420029261413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768453086868946686174275 1152679630303420029261413)
              ·
                refine ⟨216127430681891255486515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1152679630303420029261413 216127430681891255486515)
                ·
                  refine ⟨324191146022836883229773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216127430681891255486515 324191146022836883229773)
                  ·
                    refine ⟨121571679758563831211165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324191146022836883229773 121571679758563831211165)
                    ·
                      rfl

theorem cell22_355140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_355140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355140 prefixEnd_355140 := by exact prefixLift 355140
  have htrace : WordTrace (prefixWord ++ tailWord_355140) baseStart_355140 baseEnd_355140 := by
    simpa [prefixWord, tailWord_355140, baseEnd_355140] using wordTrace_append hprefix tailTrace_355140
  have hstable : (prefixWord ++ tailWord_355140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355140).length < 2 ^ (prefixWord ++ tailWord_355140).sum := by decide
  have hdescent : baseEnd_355140 < baseStart_355140 := by decide
  rcases family_descends (prefixWord ++ tailWord_355140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355162 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_355162 : Nat := 118140960795 + 355162 * 2 ^ 59
def prefixEnd_355162 : Nat := 4983230072969 + 3 ^ 40 * 355162 * 2
def baseEnd_355162 : Nat := 121579210808163107161097

theorem tailTrace_355162 : CollatzResearch.WordTrace tailWord_355162 prefixEnd_355162 121579210808163107161097 := by
  unfold tailWord_355162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3238455584829051421392935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8635881559544137123714493 3238455584829051421392935)
  ·
    refine ⟨4857683377243577132089403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3238455584829051421392935 4857683377243577132089403)
    ·
      refine ⟨7286525065865365698134105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4857683377243577132089403 7286525065865365698134105)
      ·
        refine ⟨5464893799399024273600579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7286525065865365698134105 5464893799399024273600579)
        ·
          refine ⟨8197340699098536410400869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464893799399024273600579 8197340699098536410400869)
          ·
            refine ⟨1537001381080975576950163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8197340699098536410400869 1537001381080975576950163)
            ·
              refine ⟨2305502071621463365425245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537001381080975576950163 2305502071621463365425245)
              ·
                refine ⟨864563276858048762034467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2305502071621463365425245 864563276858048762034467)
                ·
                  refine ⟨1296844915287073143051701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864563276858048762034467 1296844915287073143051701)
                  ·
                    refine ⟨121579210808163107161097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1296844915287073143051701 121579210808163107161097)
                    ·
                      rfl

theorem cell22_355162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_355162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355162 prefixEnd_355162 := by exact prefixLift 355162
  have htrace : WordTrace (prefixWord ++ tailWord_355162) baseStart_355162 baseEnd_355162 := by
    simpa [prefixWord, tailWord_355162, baseEnd_355162] using wordTrace_append hprefix tailTrace_355162
  have hstable : (prefixWord ++ tailWord_355162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355162).length < 2 ^ (prefixWord ++ tailWord_355162).sum := by decide
  have hdescent : baseEnd_355162 < baseStart_355162 := by decide
  rcases family_descends (prefixWord ++ tailWord_355162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355164 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 6]
def baseStart_355164 : Nat := 118140960795 + 355164 * 2 ^ 59
def prefixEnd_355164 : Nat := 4983230072969 + 3 ^ 40 * 355164 * 2
def baseEnd_355164 : Nat := 40526631816345256203697

theorem tailTrace_355164 : CollatzResearch.WordTrace tailWord_355164 prefixEnd_355164 40526631816345256203697 := by
  unfold tailWord_355164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6476947642654480013572273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8635930190205973351429697 6476947642654480013572273)
  ·
    refine ⟨4857710731990860010179205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6476947642654480013572273 4857710731990860010179205)
    ·
      refine ⟨910820762248286251908601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4857710731990860010179205 910820762248286251908601)
      ·
        refine ⟨683115571686214688931451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 910820762248286251908601 683115571686214688931451)
        ·
          refine ⟨1024673357529322033397177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683115571686214688931451 1024673357529322033397177)
          ·
            refine ⟨768505018146991525047883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024673357529322033397177 768505018146991525047883)
            ·
              refine ⟨1152757527220487287571825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768505018146991525047883 1152757527220487287571825)
              ·
                refine ⟨864568145415365465678869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152757527220487287571825 864568145415365465678869)
                ·
                  refine ⟨40526631816345256203697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 864568145415365465678869 40526631816345256203697)
                  ·
                    rfl

theorem cell22_355164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_355164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355164 prefixEnd_355164 := by exact prefixLift 355164
  have htrace : WordTrace (prefixWord ++ tailWord_355164) baseStart_355164 baseEnd_355164 := by
    simpa [prefixWord, tailWord_355164, baseEnd_355164] using wordTrace_append hprefix tailTrace_355164
  have hstable : (prefixWord ++ tailWord_355164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355164).length < 2 ^ (prefixWord ++ tailWord_355164).sum := by decide
  have hdescent : baseEnd_355164 < baseStart_355164 := by decide
  rcases family_descends (prefixWord ++ tailWord_355164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355226 : List Nat := [3, 1, 1, 4, 3, 2, 2, 6]
def baseStart_355226 : Nat := 118140960795 + 355226 * 2 ^ 59
def prefixEnd_355226 : Nat := 4983230072969 + 3 ^ 40 * 355226 * 2
def baseEnd_355226 : Nat := 13511235479565363728989

theorem tailTrace_355226 : CollatzResearch.WordTrace tailWord_355226 prefixEnd_355226 13511235479565363728989 := by
  unfold tailWord_355226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239039152771086153975383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8637437740722896410601021 3239039152771086153975383)
  ·
    refine ⟨4858558729156629230963075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3239039152771086153975383 4858558729156629230963075)
    ·
      refine ⟨7287838093734943846444613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4858558729156629230963075 7287838093734943846444613)
      ·
        refine ⟨1366469642575301971208365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7287838093734943846444613 1366469642575301971208365)
        ·
          refine ⟨512426115965738239203137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1366469642575301971208365 512426115965738239203137)
          ·
            refine ⟨384319586974303679402353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512426115965738239203137 384319586974303679402353)
            ·
              refine ⟨288239690230727759551765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384319586974303679402353 288239690230727759551765)
              ·
                refine ⟨13511235479565363728989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 288239690230727759551765 13511235479565363728989)
                ·
                  rfl

theorem cell22_355226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_355226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355226 prefixEnd_355226 := by exact prefixLift 355226
  have htrace : WordTrace (prefixWord ++ tailWord_355226) baseStart_355226 baseEnd_355226 := by
    simpa [prefixWord, tailWord_355226, baseEnd_355226] using wordTrace_append hprefix tailTrace_355226
  have hstable : (prefixWord ++ tailWord_355226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355226).length < 2 ^ (prefixWord ++ tailWord_355226).sum := by decide
  have hdescent : baseEnd_355226 < baseStart_355226 := by decide
  rcases family_descends (prefixWord ++ tailWord_355226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355258 : List Nat := [3, 1, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_355258 : Nat := 118140960795 + 355258 * 2 ^ 59
def prefixEnd_355258 : Nat := 4983230072969 + 3 ^ 40 * 355258 * 2
def baseEnd_355258 : Nat := 121612073570050856760803

theorem tailTrace_355258 : CollatzResearch.WordTrace tailWord_355258 prefixEnd_355258 121612073570050856760803 := by
  unfold tailWord_355258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239330936742103520266607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8638215831312276054044285 3239330936742103520266607)
  ·
    refine ⟨4858996405113155280399911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3239330936742103520266607 4858996405113155280399911)
    ·
      refine ⟨7288494607669732920599867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4858996405113155280399911 7288494607669732920599867)
      ·
        refine ⟨10932741911504599380899801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7288494607669732920599867 10932741911504599380899801)
        ·
          refine ⟨8199556433628449535674851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10932741911504599380899801 8199556433628449535674851)
          ·
            refine ⟨12299334650442674303512277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8199556433628449535674851 12299334650442674303512277)
            ·
              refine ⟨288265655869750178988569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12299334650442674303512277 288265655869750178988569)
              ·
                refine ⟨216199241902312634241427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288265655869750178988569 216199241902312634241427)
                ·
                  refine ⟨324298862853468951362141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216199241902312634241427 324298862853468951362141)
                  ·
                    refine ⟨121612073570050856760803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324298862853468951362141 121612073570050856760803)
                    ·
                      rfl

theorem cell22_355258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_355258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355258 prefixEnd_355258 := by exact prefixLift 355258
  have htrace : WordTrace (prefixWord ++ tailWord_355258) baseStart_355258 baseEnd_355258 := by
    simpa [prefixWord, tailWord_355258, baseEnd_355258] using wordTrace_append hprefix tailTrace_355258
  have hstable : (prefixWord ++ tailWord_355258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355258).length < 2 ^ (prefixWord ++ tailWord_355258).sum := by decide
  have hdescent : baseEnd_355258 < baseStart_355258 := by decide
  rcases family_descends (prefixWord ++ tailWord_355258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355267 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 5, 4]
def baseStart_355267 : Nat := 118140960795 + 355267 * 2 ^ 59
def prefixEnd_355267 : Nat := 4983230072969 + 3 ^ 40 * 355267 * 2
def baseEnd_355267 : Nat := 121615154453977833285775

theorem tailTrace_355267 : CollatzResearch.WordTrace tailWord_355267 prefixEnd_355267 121615154453977833285775 := by
  unfold tailWord_355267
  simp only [CollatzResearch.WordTrace]
  refine ⟨12957652003935808618144055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8638434669290539078762703 12957652003935808618144055)
  ·
    refine ⟨19436478005903712927216083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12957652003935808618144055 19436478005903712927216083)
    ·
      refine ⟨29154717008855569390824125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19436478005903712927216083 29154717008855569390824125)
      ·
        refine ⟨10933018878320838521559047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29154717008855569390824125 10933018878320838521559047)
        ·
          refine ⟨16399528317481257782338571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10933018878320838521559047 16399528317481257782338571)
          ·
            refine ⟨24599292476221886673507857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16399528317481257782338571 24599292476221886673507857)
            ·
              refine ⟨18449469357166415005130893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24599292476221886673507857 18449469357166415005130893)
              ·
                refine ⟨6918551008937405626924085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18449469357166415005130893 6918551008937405626924085)
                ·
                  refine ⟨648614157087881777524133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6918551008937405626924085 648614157087881777524133)
                  ·
                    refine ⟨121615154453977833285775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 648614157087881777524133 121615154453977833285775)
                    ·
                      rfl

theorem cell22_355267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 4].length) (baseStart_355267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355267 prefixEnd_355267 := by exact prefixLift 355267
  have htrace : WordTrace (prefixWord ++ tailWord_355267) baseStart_355267 baseEnd_355267 := by
    simpa [prefixWord, tailWord_355267, baseEnd_355267] using wordTrace_append hprefix tailTrace_355267
  have hstable : (prefixWord ++ tailWord_355267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355267).length < 2 ^ (prefixWord ++ tailWord_355267).sum := by decide
  have hdescent : baseEnd_355267 < baseStart_355267 := by decide
  rcases family_descends (prefixWord ++ tailWord_355267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355312 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_355312 : Nat := 118140960795 + 355312 * 2 ^ 59
def prefixEnd_355312 : Nat := 4983230072969 + 3 ^ 40 * 355312 * 2
def baseEnd_355312 : Nat := 121630558873612715910637

theorem tailTrace_355312 : CollatzResearch.WordTrace tailWord_355312 prefixEnd_355312 121630558873612715910637 := by
  unfold tailWord_355312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479646644386390651766095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8639528859181854202354793 6479646644386390651766095)
  ·
    refine ⟨9719469966579585977649143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6479646644386390651766095 9719469966579585977649143)
    ·
      refine ⟨14579204949869378966473715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9719469966579585977649143 14579204949869378966473715)
      ·
        refine ⟨21868807424804068449710573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14579204949869378966473715 21868807424804068449710573)
        ·
          refine ⟨8200802784301525668641465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21868807424804068449710573 8200802784301525668641465)
          ·
            refine ⟨6150602088226144251481099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8200802784301525668641465 6150602088226144251481099)
            ·
              refine ⟨9225903132339216377221649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150602088226144251481099 9225903132339216377221649)
              ·
                refine ⟨6919427349254412282916237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9225903132339216377221649 6919427349254412282916237)
                ·
                  refine ⟨2594785255970404606093589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6919427349254412282916237 2594785255970404606093589)
                  ·
                    refine ⟨121630558873612715910637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2594785255970404606093589 121630558873612715910637)
                    ·
                      rfl

theorem cell22_355312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_355312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355312 prefixEnd_355312 := by exact prefixLift 355312
  have htrace : WordTrace (prefixWord ++ tailWord_355312) baseStart_355312 baseEnd_355312 := by
    simpa [prefixWord, tailWord_355312, baseEnd_355312] using wordTrace_append hprefix tailTrace_355312
  have hstable : (prefixWord ++ tailWord_355312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355312).length < 2 ^ (prefixWord ++ tailWord_355312).sum := by decide
  have hdescent : baseEnd_355312 < baseStart_355312 := by decide
  rcases family_descends (prefixWord ++ tailWord_355312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355376 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 3, 3]
def baseStart_355376 : Nat := 118140960795 + 355376 * 2 ^ 59
def prefixEnd_355376 : Nat := 4983230072969 + 3 ^ 40 * 355376 * 2
def baseEnd_355376 : Nat := 121652467381537882310441

theorem tailTrace_355376 : CollatzResearch.WordTrace tailWord_355376 prefixEnd_355376 121652467381537882310441 := by
  unfold tailWord_355376
  simp only [CollatzResearch.WordTrace]
  refine ⟨6480813780270460116930991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8641085040360613489241321 6480813780270460116930991)
  ·
    refine ⟨9721220670405690175396487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6480813780270460116930991 9721220670405690175396487)
    ·
      refine ⟨14581831005608535263094731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9721220670405690175396487 14581831005608535263094731)
      ·
        refine ⟨21872746508412802894642097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14581831005608535263094731 21872746508412802894642097)
        ·
          refine ⟨16404559881309602170981573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21872746508412802894642097 16404559881309602170981573)
          ·
            refine ⟨3075854977745550407059045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16404559881309602170981573 3075854977745550407059045)
            ·
              refine ⟨576722808327290701323571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3075854977745550407059045 576722808327290701323571)
              ·
                refine ⟨865084212490936051985357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576722808327290701323571 865084212490936051985357)
                ·
                  refine ⟨324406579684101019494509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865084212490936051985357 324406579684101019494509)
                  ·
                    refine ⟨121652467381537882310441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324406579684101019494509 121652467381537882310441)
                    ·
                      rfl

theorem cell22_355376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_355376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355376 prefixEnd_355376 := by exact prefixLift 355376
  have htrace : WordTrace (prefixWord ++ tailWord_355376) baseStart_355376 baseEnd_355376 := by
    simpa [prefixWord, tailWord_355376, baseEnd_355376] using wordTrace_append hprefix tailTrace_355376
  have hstable : (prefixWord ++ tailWord_355376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355376).length < 2 ^ (prefixWord ++ tailWord_355376).sum := by decide
  have hdescent : baseEnd_355376 < baseStart_355376 := by decide
  rcases family_descends (prefixWord ++ tailWord_355376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355410 : List Nat := [3, 2, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_355410 : Nat := 118140960795 + 355410 * 2 ^ 59
def prefixEnd_355410 : Nat := 4983230072969 + 3 ^ 40 * 355410 * 2
def baseEnd_355410 : Nat := 121664106276373126960337

theorem tailTrace_355410 : CollatzResearch.WordTrace tailWord_355410 prefixEnd_355410 121664106276373126960337 := by
  unfold tailWord_355410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3240716910604436010149921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8641911761611829360399789 3240716910604436010149921)
  ·
    refine ⟨2430537682953327007612441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3240716910604436010149921 2430537682953327007612441)
    ·
      refine ⟨1822903262214995255709331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2430537682953327007612441 1822903262214995255709331)
      ·
        refine ⟨2734354893322492883563997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822903262214995255709331 2734354893322492883563997)
        ·
          refine ⟨1025383084995934831336499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2734354893322492883563997 1025383084995934831336499)
          ·
            refine ⟨1538074627493902247004749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025383084995934831336499 1538074627493902247004749)
            ·
              refine ⟨576777985310213342626781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1538074627493902247004749 576777985310213342626781)
              ·
                refine ⟨216291744491330003485043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 576777985310213342626781 216291744491330003485043)
                ·
                  refine ⟨324437616736995005227565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216291744491330003485043 324437616736995005227565)
                  ·
                    refine ⟨121664106276373126960337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324437616736995005227565 121664106276373126960337)
                    ·
                      rfl

theorem cell22_355410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_355410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355410 prefixEnd_355410 := by exact prefixLift 355410
  have htrace : WordTrace (prefixWord ++ tailWord_355410) baseStart_355410 baseEnd_355410 := by
    simpa [prefixWord, tailWord_355410, baseEnd_355410] using wordTrace_append hprefix tailTrace_355410
  have hstable : (prefixWord ++ tailWord_355410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355410).length < 2 ^ (prefixWord ++ tailWord_355410).sum := by decide
  have hdescent : baseEnd_355410 < baseStart_355410 := by decide
  rcases family_descends (prefixWord ++ tailWord_355410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355466 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_355466 : Nat := 118140960795 + 355466 * 2 ^ 59
def prefixEnd_355466 : Nat := 4983230072969 + 3 ^ 40 * 355466 * 2
def baseEnd_355466 : Nat := 121683276220807647560165

theorem tailTrace_355466 : CollatzResearch.WordTrace tailWord_355466 prefixEnd_355466 121683276220807647560165 := by
  unfold tailWord_355466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3241227532553716401159563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8643273420143243736425501 3241227532553716401159563)
  ·
    refine ⟨4861841298830574601739345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3241227532553716401159563 4861841298830574601739345)
    ·
      refine ⟨3646380974122930951304509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4861841298830574601739345 3646380974122930951304509)
      ·
        refine ⟨1367392865296099106739191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3646380974122930951304509 1367392865296099106739191)
        ·
          refine ⟨2051089297944148660108787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367392865296099106739191 2051089297944148660108787)
          ·
            refine ⟨3076633946916222990163181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2051089297944148660108787 3076633946916222990163181)
            ·
              refine ⟨1153737730093583621311193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3076633946916222990163181 1153737730093583621311193)
              ·
                refine ⟨865303297570187715983395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153737730093583621311193 865303297570187715983395)
                ·
                  refine ⟨1297954946355281573975093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865303297570187715983395 1297954946355281573975093)
                  ·
                    refine ⟨121683276220807647560165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1297954946355281573975093 121683276220807647560165)
                    ·
                      rfl

theorem cell22_355466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_355466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355466 prefixEnd_355466 := by exact prefixLift 355466
  have htrace : WordTrace (prefixWord ++ tailWord_355466) baseStart_355466 baseEnd_355466 := by
    simpa [prefixWord, tailWord_355466, baseEnd_355466] using wordTrace_append hprefix tailTrace_355466
  have hstable : (prefixWord ++ tailWord_355466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355466).length < 2 ^ (prefixWord ++ tailWord_355466).sum := by decide
  have hdescent : baseEnd_355466 < baseStart_355466 := by decide
  rcases family_descends (prefixWord ++ tailWord_355466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355470 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_355470 : Nat := 118140960795 + 355470 * 2 ^ 59
def prefixEnd_355470 : Nat := 4983230072969 + 3 ^ 40 * 355470 * 2
def baseEnd_355470 : Nat := 121684645502552970460153

theorem tailTrace_355470 : CollatzResearch.WordTrace tailWord_355470 prefixEnd_355470 121684645502552970460153 := by
  unfold tailWord_355470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620632002775046785972983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8643370681466916191855909 1620632002775046785972983)
  ·
    refine ⟨2430948004162570178959475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1620632002775046785972983 2430948004162570178959475)
    ·
      refine ⟨3646422006243855268439213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2430948004162570178959475 3646422006243855268439213)
      ·
        refine ⟨1367408252341445725664705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3646422006243855268439213 1367408252341445725664705)
        ·
          refine ⟨1025556189256084294248529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1367408252341445725664705 1025556189256084294248529)
          ·
            refine ⟨769167141942063220686397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1025556189256084294248529 769167141942063220686397)
            ·
              refine ⟨288437678228273707757399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 769167141942063220686397 288437678228273707757399)
              ·
                refine ⟨432656517342410561636099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288437678228273707757399 432656517342410561636099)
                ·
                  refine ⟨648984776013615842454149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432656517342410561636099 648984776013615842454149)
                  ·
                    refine ⟨121684645502552970460153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 648984776013615842454149 121684645502552970460153)
                    ·
                      rfl

theorem cell22_355470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_355470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355470 prefixEnd_355470 := by exact prefixLift 355470
  have htrace : WordTrace (prefixWord ++ tailWord_355470) baseStart_355470 baseEnd_355470 := by
    simpa [prefixWord, tailWord_355470, baseEnd_355470] using wordTrace_append hprefix tailTrace_355470
  have hstable : (prefixWord ++ tailWord_355470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355470).length < 2 ^ (prefixWord ++ tailWord_355470).sum := by decide
  have hdescent : baseEnd_355470 < baseStart_355470 := by decide
  rcases family_descends (prefixWord ++ tailWord_355470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355479 : List Nat := [1, 1, 3, 3, 3, 11]
def baseStart_355479 : Nat := 118140960795 + 355479 * 2 ^ 59
def prefixEnd_355479 : Nat := 4983230072969 + 3 ^ 40 * 355479 * 2
def baseEnd_355479 : Nat := 1502317609709628975125

theorem tailTrace_355479 : CollatzResearch.WordTrace tailWord_355479 prefixEnd_355479 1502317609709628975125 := by
  unfold tailWord_355479
  simp only [CollatzResearch.WordTrace]
  refine ⟨12965384279167768824861491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8643589519445179216574327 12965384279167768824861491)
  ·
    refine ⟨19448076418751653237292237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12965384279167768824861491 19448076418751653237292237)
    ·
      refine ⟨7293028657031869963984589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19448076418751653237292237 7293028657031869963984589)
      ·
        refine ⟨2734885746386951236494221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7293028657031869963984589 2734885746386951236494221)
        ·
          refine ⟨1025582154895106713685333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2734885746386951236494221 1025582154895106713685333)
          ·
            refine ⟨1502317609709628975125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1025582154895106713685333 1502317609709628975125)
            ·
              rfl

theorem cell22_355479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 11].length) (baseStart_355479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355479 prefixEnd_355479 := by exact prefixLift 355479
  have htrace : WordTrace (prefixWord ++ tailWord_355479) baseStart_355479 baseEnd_355479 := by
    simpa [prefixWord, tailWord_355479, baseEnd_355479] using wordTrace_append hprefix tailTrace_355479
  have hstable : (prefixWord ++ tailWord_355479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355479).length < 2 ^ (prefixWord ++ tailWord_355479).sum := by decide
  have hdescent : baseEnd_355479 < baseStart_355479 := by decide
  rcases family_descends (prefixWord ++ tailWord_355479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 3, 7]
def baseStart_355539 : Nat := 118140960795 + 355539 * 2 ^ 59
def prefixEnd_355539 : Nat := 4983230072969 + 3 ^ 40 * 355539 * 2
def baseEnd_355539 : Nat := 121708265612659790484941

theorem tailTrace_355539 : CollatzResearch.WordTrace tailWord_355539 prefixEnd_355539 121708265612659790484941 := by
  unfold tailWord_355539
  simp only [CollatzResearch.WordTrace]
  refine ⟨12967572658950399072045671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8645048439300266048030447 12967572658950399072045671)
  ·
    refine ⟨19451358988425598608068507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12967572658950399072045671 19451358988425598608068507)
    ·
      refine ⟨29177038482638397912102761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19451358988425598608068507 29177038482638397912102761)
      ·
        refine ⟨21882778861978798434077071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29177038482638397912102761 21882778861978798434077071)
        ·
          refine ⟨32824168292968197651115607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21882778861978798434077071 32824168292968197651115607)
          ·
            refine ⟨49236252439452296476673411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32824168292968197651115607 49236252439452296476673411)
            ·
              refine ⟨73854378659178444715010117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49236252439452296476673411 73854378659178444715010117)
              ·
                refine ⟨13847695998595958384064397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73854378659178444715010117 13847695998595958384064397)
                ·
                  refine ⟨5192885999473484394024149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13847695998595958384064397 5192885999473484394024149)
                  ·
                    refine ⟨121708265612659790484941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5192885999473484394024149 121708265612659790484941)
                    ·
                      rfl

theorem cell22_355539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_355539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355539 prefixEnd_355539 := by exact prefixLift 355539
  have htrace : WordTrace (prefixWord ++ tailWord_355539) baseStart_355539 baseEnd_355539 := by
    simpa [prefixWord, tailWord_355539, baseEnd_355539] using wordTrace_append hprefix tailTrace_355539
  have hstable : (prefixWord ++ tailWord_355539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355539).length < 2 ^ (prefixWord ++ tailWord_355539).sum := by decide
  have hdescent : baseEnd_355539 < baseStart_355539 := by decide
  rcases family_descends (prefixWord ++ tailWord_355539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355556 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_355556 : Nat := 118140960795 + 355556 * 2 ^ 59
def prefixEnd_355556 : Nat := 4983230072969 + 3 ^ 40 * 355556 * 2
def baseEnd_355556 : Nat := 121714085060077412809889

theorem tailTrace_355556 : CollatzResearch.WordTrace tailWord_355556 prefixEnd_355556 121714085060077412809889 := by
  unfold tailWord_355556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484096349944405487707261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8645461799925873983609681 6484096349944405487707261)
  ·
    refine ⟨2431536131229152057890223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6484096349944405487707261 2431536131229152057890223)
    ·
      refine ⟨3647304196843728086835335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2431536131229152057890223 3647304196843728086835335)
      ·
        refine ⟨5470956295265592130253003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647304196843728086835335 5470956295265592130253003)
        ·
          refine ⟨8206434442898388195379505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5470956295265592130253003 8206434442898388195379505)
          ·
            refine ⟨6154825832173791146534629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8206434442898388195379505 6154825832173791146534629)
            ·
              refine ⟨1154029843532585839975243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6154825832173791146534629 1154029843532585839975243)
              ·
                refine ⟨1731044765298878759962865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154029843532585839975243 1731044765298878759962865)
                ·
                  refine ⟨1298283573974159069972149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1731044765298878759962865 1298283573974159069972149)
                  ·
                    refine ⟨121714085060077412809889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1298283573974159069972149 121714085060077412809889)
                    ·
                      rfl

theorem cell22_355556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_355556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355556 prefixEnd_355556 := by exact prefixLift 355556
  have htrace : WordTrace (prefixWord ++ tailWord_355556) baseStart_355556 baseEnd_355556 := by
    simpa [prefixWord, tailWord_355556, baseEnd_355556] using wordTrace_append hprefix tailTrace_355556
  have hstable : (prefixWord ++ tailWord_355556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355556).length < 2 ^ (prefixWord ++ tailWord_355556).sum := by decide
  have hdescent : baseEnd_355556 < baseStart_355556 := by decide
  rcases family_descends (prefixWord ++ tailWord_355556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355633 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_355633 : Nat := 118140960795 + 355633 * 2 ^ 59
def prefixEnd_355633 : Nat := 4983230072969 + 3 ^ 40 * 355633 * 2
def baseEnd_355633 : Nat := 121740443733674878634653

theorem tailTrace_355633 : CollatzResearch.WordTrace tailWord_355633 prefixEnd_355633 121740443733674878634653 := by
  unfold tailWord_355633
  simp only [CollatzResearch.WordTrace]
  refine ⟨12971001120609853125967553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8647334080406568750645035 12971001120609853125967553)
  ·
    refine ⟨9728250840457389844475665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12971001120609853125967553 9728250840457389844475665)
    ·
      refine ⟨7296188130343042383356749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9728250840457389844475665 7296188130343042383356749)
      ·
        refine ⟨2736070548878640893758781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7296188130343042383356749 2736070548878640893758781)
        ·
          refine ⟨1026026455829490335159543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2736070548878640893758781 1026026455829490335159543)
          ·
            refine ⟨1539039683744235502739315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026026455829490335159543 1539039683744235502739315)
            ·
              refine ⟨2308559525616353254108973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539039683744235502739315 2308559525616353254108973)
              ·
                refine ⟨865709822106132470290865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2308559525616353254108973 865709822106132470290865)
                ·
                  refine ⟨649282366579599352718149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 865709822106132470290865 649282366579599352718149)
                  ·
                    refine ⟨121740443733674878634653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 649282366579599352718149 121740443733674878634653)
                    ·
                      rfl

theorem cell22_355633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_355633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355633 prefixEnd_355633 := by exact prefixLift 355633
  have htrace : WordTrace (prefixWord ++ tailWord_355633) baseStart_355633 baseEnd_355633 := by
    simpa [prefixWord, tailWord_355633, baseEnd_355633] using wordTrace_append hprefix tailTrace_355633
  have hstable : (prefixWord ++ tailWord_355633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355633).length < 2 ^ (prefixWord ++ tailWord_355633).sum := by decide
  have hdescent : baseEnd_355633 < baseStart_355633 := by decide
  rcases family_descends (prefixWord ++ tailWord_355633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355652 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_355652 : Nat := 118140960795 + 355652 * 2 ^ 59
def prefixEnd_355652 : Nat := 4983230072969 + 3 ^ 40 * 355652 * 2
def baseEnd_355652 : Nat := 121746947821965162409595

theorem tailTrace_355652 : CollatzResearch.WordTrace tailWord_355652 prefixEnd_355652 121746947821965162409595 := by
  unfold tailWord_355652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6485847053770509685454605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8647796071694012913939473 6485847053770509685454605)
  ·
    refine ⟨2432192645163941132045477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6485847053770509685454605 2432192645163941132045477)
    ·
      refine ⟨456036120968238962258527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2432192645163941132045477 456036120968238962258527)
      ·
        refine ⟨684054181452358443387791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456036120968238962258527 684054181452358443387791)
        ·
          refine ⟨1026081272178537665081687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684054181452358443387791 1026081272178537665081687)
          ·
            refine ⟨1539121908267806497622531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026081272178537665081687 1539121908267806497622531)
            ·
              refine ⟨2308682862401709746433797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539121908267806497622531 2308682862401709746433797)
              ·
                refine ⟨432878036700320577456337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2308682862401709746433797 432878036700320577456337)
                ·
                  refine ⟨324658527525240433092253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432878036700320577456337 324658527525240433092253)
                  ·
                    refine ⟨121746947821965162409595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324658527525240433092253 121746947821965162409595)
                    ·
                      rfl

theorem cell22_355652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_355652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355652 prefixEnd_355652 := by exact prefixLift 355652
  have htrace : WordTrace (prefixWord ++ tailWord_355652) baseStart_355652 baseEnd_355652 := by
    simpa [prefixWord, tailWord_355652, baseEnd_355652] using wordTrace_append hprefix tailTrace_355652
  have hstable : (prefixWord ++ tailWord_355652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355652).length < 2 ^ (prefixWord ++ tailWord_355652).sum := by decide
  have hdescent : baseEnd_355652 < baseStart_355652 := by decide
  rcases family_descends (prefixWord ++ tailWord_355652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355680 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 3, 3]
def baseStart_355680 : Nat := 118140960795 + 355680 * 2 ^ 59
def prefixEnd_355680 : Nat := 4983230072969 + 3 ^ 40 * 355680 * 2
def baseEnd_355680 : Nat := 121756532794182422709509

theorem tailTrace_355680 : CollatzResearch.WordTrace tailWord_355680 prefixEnd_355680 121756532794182422709509 := by
  unfold tailWord_355680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486357675719790076464247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8648476900959720101952329 6486357675719790076464247)
  ·
    refine ⟨9729536513579685114696371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6486357675719790076464247 9729536513579685114696371)
    ·
      refine ⟨14594304770369527672044557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9729536513579685114696371 14594304770369527672044557)
      ·
        refine ⟨5472864288888572877016709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14594304770369527672044557 5472864288888572877016709)
        ·
          refine ⟨1026162054166607414440633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5472864288888572877016709 1026162054166607414440633)
          ·
            refine ⟨769621540624955560830475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1026162054166607414440633 769621540624955560830475)
            ·
              refine ⟨1154432310937433341245713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769621540624955560830475 1154432310937433341245713)
              ·
                refine ⟨865824233203075005934285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154432310937433341245713 865824233203075005934285)
                ·
                  refine ⟨324684087451153127225357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865824233203075005934285 324684087451153127225357)
                  ·
                    refine ⟨121756532794182422709509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324684087451153127225357 121756532794182422709509)
                    ·
                      rfl

theorem cell22_355680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_355680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355680 prefixEnd_355680 := by exact prefixLift 355680
  have htrace : WordTrace (prefixWord ++ tailWord_355680) baseStart_355680 baseEnd_355680 := by
    simpa [prefixWord, tailWord_355680, baseEnd_355680] using wordTrace_append hprefix tailTrace_355680
  have hstable : (prefixWord ++ tailWord_355680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355680).length < 2 ^ (prefixWord ++ tailWord_355680).sum := by decide
  have hdescent : baseEnd_355680 < baseStart_355680 := by decide
  rcases family_descends (prefixWord ++ tailWord_355680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355691 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 6, 5]
def baseStart_355691 : Nat := 118140960795 + 355691 * 2 ^ 59
def prefixEnd_355691 : Nat := 4983230072969 + 3 ^ 40 * 355691 * 2
def baseEnd_355691 : Nat := 121760298318982060684475

theorem tailTrace_355691 : CollatzResearch.WordTrace tailWord_355691 prefixEnd_355691 121760298318982060684475 := by
  unfold tailWord_355691
  simp only [CollatzResearch.WordTrace]
  refine ⟨12973116554399729031578927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8648744369599819354385951 12973116554399729031578927)
  ·
    refine ⟨19459674831599593547368391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12973116554399729031578927 19459674831599593547368391)
    ·
      refine ⟨29189512247399390321052587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19459674831599593547368391 29189512247399390321052587)
      ·
        refine ⟨43784268371099085481578881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29189512247399390321052587 43784268371099085481578881)
        ·
          refine ⟨32838201278324314111184161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43784268371099085481578881 32838201278324314111184161)
          ·
            refine ⟨24628650958743235583388121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32838201278324314111184161 24628650958743235583388121)
            ·
              refine ⟨18471488219057426687541091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24628650958743235583388121 18471488219057426687541091)
              ·
                refine ⟨27707232328586140031311637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18471488219057426687541091 27707232328586140031311637)
                ·
                  refine ⟨1298776515402475313967733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27707232328586140031311637 1298776515402475313967733)
                  ·
                    refine ⟨121760298318982060684475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1298776515402475313967733 121760298318982060684475)
                    ·
                      rfl

theorem cell22_355691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_355691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355691 prefixEnd_355691 := by exact prefixLift 355691
  have htrace : WordTrace (prefixWord ++ tailWord_355691) baseStart_355691 baseEnd_355691 := by
    simpa [prefixWord, tailWord_355691, baseEnd_355691] using wordTrace_append hprefix tailTrace_355691
  have hstable : (prefixWord ++ tailWord_355691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355691).length < 2 ^ (prefixWord ++ tailWord_355691).sum := by decide
  have hdescent : baseEnd_355691 < baseStart_355691 := by decide
  rcases family_descends (prefixWord ++ tailWord_355691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355714 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_355714 : Nat := 118140960795 + 355714 * 2 ^ 59
def prefixEnd_355714 : Nat := 4983230072969 + 3 ^ 40 * 355714 * 2
def baseEnd_355714 : Nat := 121768171689017667359405

theorem tailTrace_355714 : CollatzResearch.WordTrace tailWord_355714 prefixEnd_355714 121768171689017667359405 := by
  unfold tailWord_355714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243488858329100989916549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8649303622210935973110797 3243488858329100989916549)
  ·
    refine ⟨608154160936706435609353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3243488858329100989916549 608154160936706435609353)
    ·
      refine ⟨456115620702529826707015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 608154160936706435609353 456115620702529826707015)
      ·
        refine ⟨684173431053794740060523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456115620702529826707015 684173431053794740060523)
        ·
          refine ⟨1026260146580692110090785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684173431053794740060523 1026260146580692110090785)
          ·
            refine ⟨769695109935519082568089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1026260146580692110090785 769695109935519082568089)
            ·
              refine ⟨577271332451639311926067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769695109935519082568089 577271332451639311926067)
              ·
                refine ⟨865906998677458967889101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577271332451639311926067 865906998677458967889101)
                ·
                  refine ⟨324715124504047112958413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865906998677458967889101 324715124504047112958413)
                  ·
                    refine ⟨121768171689017667359405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324715124504047112958413 121768171689017667359405)
                    ·
                      rfl

theorem cell22_355714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_355714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355714 prefixEnd_355714 := by exact prefixLift 355714
  have htrace : WordTrace (prefixWord ++ tailWord_355714) baseStart_355714 baseEnd_355714 := by
    simpa [prefixWord, tailWord_355714, baseEnd_355714] using wordTrace_append hprefix tailTrace_355714
  have hstable : (prefixWord ++ tailWord_355714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355714).length < 2 ^ (prefixWord ++ tailWord_355714).sum := by decide
  have hdescent : baseEnd_355714 < baseStart_355714 := by decide
  rcases family_descends (prefixWord ++ tailWord_355714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355738 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 6]
def baseStart_355738 : Nat := 118140960795 + 355738 * 2 ^ 59
def prefixEnd_355738 : Nat := 4983230072969 + 3 ^ 40 * 355738 * 2
def baseEnd_355738 : Nat := 40592129126496534919777

theorem tailTrace_355738 : CollatzResearch.WordTrace tailWord_355738 prefixEnd_355738 40592129126496534919777 := by
  unfold tailWord_355738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243707696307364014634967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8649887190152970705693245 3243707696307364014634967)
  ·
    refine ⟨4865561544461046021952451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3243707696307364014634967 4865561544461046021952451)
    ·
      refine ⟨7298342316691569032928677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865561544461046021952451 7298342316691569032928677)
      ·
        refine ⟨1368439184379669193674127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7298342316691569032928677 1368439184379669193674127)
        ·
          refine ⟨2052658776569503790511191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368439184379669193674127 2052658776569503790511191)
          ·
            refine ⟨3078988164854255685766787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052658776569503790511191 3078988164854255685766787)
            ·
              refine ⟨4618482247281383528650181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078988164854255685766787 4618482247281383528650181)
              ·
                refine ⟨865965421365259411621909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4618482247281383528650181 865965421365259411621909)
                ·
                  refine ⟨40592129126496534919777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 865965421365259411621909 40592129126496534919777)
                  ·
                    rfl

theorem cell22_355738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_355738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355738 prefixEnd_355738 := by exact prefixLift 355738
  have htrace : WordTrace (prefixWord ++ tailWord_355738) baseStart_355738 baseEnd_355738 := by
    simpa [prefixWord, tailWord_355738, baseEnd_355738] using wordTrace_append hprefix tailTrace_355738
  have hstable : (prefixWord ++ tailWord_355738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355738).length < 2 ^ (prefixWord ++ tailWord_355738).sum := by decide
  have hdescent : baseEnd_355738 < baseStart_355738 := by decide
  rcases family_descends (prefixWord ++ tailWord_355738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355757 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_355757 : Nat := 118140960795 + 355757 * 2 ^ 59
def prefixEnd_355757 : Nat := 4983230072969 + 3 ^ 40 * 355757 * 2
def baseEnd_355757 : Nat := 121782891467779888534273

theorem tailTrace_355757 : CollatzResearch.WordTrace tailWord_355757 prefixEnd_355757 121782891467779888534273 := by
  unfold tailWord_355757
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975523772160622303481525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8650349181440414868987683 12975523772160622303481525)
  ·
    refine ⟨1216455353640058340951393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12975523772160622303481525 1216455353640058340951393)
    ·
      refine ⟨912341515230043755713545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1216455353640058340951393 912341515230043755713545)
      ·
        refine ⟨684256136422532816785159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912341515230043755713545 684256136422532816785159)
        ·
          refine ⟨1026384204633799225177739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684256136422532816785159 1026384204633799225177739)
          ·
            refine ⟨1539576306950698837766609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026384204633799225177739 1539576306950698837766609)
            ·
              refine ⟨1154682230213024128324957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539576306950698837766609 1154682230213024128324957)
              ·
                refine ⟨433005836329884048121859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1154682230213024128324957 433005836329884048121859)
                ·
                  refine ⟨649508754494826072182789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433005836329884048121859 649508754494826072182789)
                  ·
                    refine ⟨121782891467779888534273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 649508754494826072182789 121782891467779888534273)
                    ·
                      rfl

theorem cell22_355757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_355757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355757 prefixEnd_355757 := by exact prefixLift 355757
  have htrace : WordTrace (prefixWord ++ tailWord_355757) baseStart_355757 baseEnd_355757 := by
    simpa [prefixWord, tailWord_355757, baseEnd_355757] using wordTrace_append hprefix tailTrace_355757
  have hstable : (prefixWord ++ tailWord_355757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355757).length < 2 ^ (prefixWord ++ tailWord_355757).sum := by decide
  have hdescent : baseEnd_355757 < baseStart_355757 := by decide
  rcases family_descends (prefixWord ++ tailWord_355757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355768 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_355768 : Nat := 118140960795 + 355768 * 2 ^ 59
def prefixEnd_355768 : Nat := 4983230072969 + 3 ^ 40 * 355768 * 2
def baseEnd_355768 : Nat := 121786656992579526509239

theorem tailTrace_355768 : CollatzResearch.WordTrace tailWord_355768 prefixEnd_355768 121786656992579526509239 := by
  unfold tailWord_355768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6487962487560385591065979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8650616650080514121421305 6487962487560385591065979)
  ·
    refine ⟨9731943731340578386598969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6487962487560385591065979 9731943731340578386598969)
    ·
      refine ⟨7298957798505433789949227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9731943731340578386598969 7298957798505433789949227)
      ·
        refine ⟨10948436697758150684923841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7298957798505433789949227 10948436697758150684923841)
        ·
          refine ⟨8211327523318613013692881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10948436697758150684923841 8211327523318613013692881)
          ·
            refine ⟨6158495642488959760269661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8211327523318613013692881 6158495642488959760269661)
            ·
              refine ⟨2309435865933359910101123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6158495642488959760269661 2309435865933359910101123)
              ·
                refine ⟨3464153798900039865151685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2309435865933359910101123 3464153798900039865151685)
                ·
                  refine ⟨649528837293757474715941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3464153798900039865151685 649528837293757474715941)
                  ·
                    refine ⟨121786656992579526509239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 649528837293757474715941 121786656992579526509239)
                    ·
                      rfl

theorem cell22_355768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_355768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355768 prefixEnd_355768 := by exact prefixLift 355768
  have htrace : WordTrace (prefixWord ++ tailWord_355768) baseStart_355768 baseEnd_355768 := by
    simpa [prefixWord, tailWord_355768, baseEnd_355768] using wordTrace_append hprefix tailTrace_355768
  have hstable : (prefixWord ++ tailWord_355768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355768).length < 2 ^ (prefixWord ++ tailWord_355768).sum := by decide
  have hdescent : baseEnd_355768 < baseStart_355768 := by decide
  rcases family_descends (prefixWord ++ tailWord_355768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355772 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 6]
def baseStart_355772 : Nat := 118140960795 + 355772 * 2 ^ 59
def prefixEnd_355772 : Nat := 4983230072969 + 3 ^ 40 * 355772 * 2
def baseEnd_355772 : Nat := 40596008758108283136409

theorem tailTrace_355772 : CollatzResearch.WordTrace tailWord_355772 prefixEnd_355772 40596008758108283136409 := by
  unfold tailWord_355772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488035433553139932638785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8650713911404186576851713 6488035433553139932638785)
  ·
    refine ⟨4866026575164854949479089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6488035433553139932638785 4866026575164854949479089)
    ·
      refine ⟨3649519931373641212109317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4866026575164854949479089 3649519931373641212109317)
      ·
        refine ⟨684284987132557727270497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3649519931373641212109317 684284987132557727270497)
        ·
          refine ⟨513213740349418295452873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 684284987132557727270497 513213740349418295452873)
          ·
            refine ⟨384910305262063721589655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513213740349418295452873 384910305262063721589655)
            ·
              refine ⟨577365457893095582384483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384910305262063721589655 577365457893095582384483)
              ·
                refine ⟨866048186839643373576725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577365457893095582384483 866048186839643373576725)
                ·
                  refine ⟨40596008758108283136409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 866048186839643373576725 40596008758108283136409)
                  ·
                    rfl

theorem cell22_355772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_355772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355772 prefixEnd_355772 := by exact prefixLift 355772
  have htrace : WordTrace (prefixWord ++ tailWord_355772) baseStart_355772 baseEnd_355772 := by
    simpa [prefixWord, tailWord_355772, baseEnd_355772] using wordTrace_append hprefix tailTrace_355772
  have hstable : (prefixWord ++ tailWord_355772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355772).length < 2 ^ (prefixWord ++ tailWord_355772).sum := by decide
  have hdescent : baseEnd_355772 < baseStart_355772 := by decide
  rcases family_descends (prefixWord ++ tailWord_355772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355783 : List Nat := [1, 1, 4, 1, 1, 3, 4, 7]
def baseStart_355783 : Nat := 118140960795 + 355783 * 2 ^ 59
def prefixEnd_355783 : Nat := 4983230072969 + 3 ^ 40 * 355783 * 2
def baseEnd_355783 : Nat := 13532421311013831931577

theorem tailTrace_355783 : CollatzResearch.WordTrace tailWord_355783 prefixEnd_355783 13532421311013831931577 := by
  unfold tailWord_355783
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976472070066428743928003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8650981380044285829285335 12976472070066428743928003)
  ·
    refine ⟨19464708105099643115892005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12976472070066428743928003 19464708105099643115892005)
    ·
      refine ⟨3649632769706183084229751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19464708105099643115892005 3649632769706183084229751)
      ·
        refine ⟨5474449154559274626344627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3649632769706183084229751 5474449154559274626344627)
        ·
          refine ⟨8211673731838911939516941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5474449154559274626344627 8211673731838911939516941)
          ·
            refine ⟨3079377649439591977318853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8211673731838911939516941 3079377649439591977318853)
            ·
              refine ⟨577383309269923495747285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3079377649439591977318853 577383309269923495747285)
              ·
                refine ⟨13532421311013831931577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 577383309269923495747285 13532421311013831931577)
                ·
                  rfl

theorem cell22_355783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 7].length) (baseStart_355783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355783 prefixEnd_355783 := by exact prefixLift 355783
  have htrace : WordTrace (prefixWord ++ tailWord_355783) baseStart_355783 baseEnd_355783 := by
    simpa [prefixWord, tailWord_355783, baseEnd_355783] using wordTrace_append hprefix tailTrace_355783
  have hstable : (prefixWord ++ tailWord_355783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355783).length < 2 ^ (prefixWord ++ tailWord_355783).sum := by decide
  have hdescent : baseEnd_355783 < baseStart_355783 := by decide
  rcases family_descends (prefixWord ++ tailWord_355783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355787 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 2, 3]
def baseStart_355787 : Nat := 118140960795 + 355787 * 2 ^ 59
def prefixEnd_355787 : Nat := 4983230072969 + 3 ^ 40 * 355787 * 2
def baseEnd_355787 : Nat := 121793161080869810284181

theorem tailTrace_355787 : CollatzResearch.WordTrace tailWord_355787 prefixEnd_355787 121793161080869810284181 := by
  unfold tailWord_355787
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976617962051937427073615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8651078641367958284715743 12976617962051937427073615)
  ·
    refine ⟨19464926943077906140610423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12976617962051937427073615 19464926943077906140610423)
    ·
      refine ⟨29197390414616859210915635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19464926943077906140610423 29197390414616859210915635)
      ·
        refine ⟨43796085621925288816373453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29197390414616859210915635 43796085621925288816373453)
        ·
          refine ⟨16423532108221983306140045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43796085621925288816373453 16423532108221983306140045)
          ·
            refine ⟨6158824540583243739802517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16423532108221983306140045 6158824540583243739802517)
            ·
              refine ⟨288694900339839550303243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6158824540583243739802517 288694900339839550303243)
              ·
                refine ⟨433042350509759325454865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288694900339839550303243 433042350509759325454865)
                ·
                  refine ⟨324781762882319494091149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433042350509759325454865 324781762882319494091149)
                  ·
                    refine ⟨121793161080869810284181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324781762882319494091149 121793161080869810284181)
                    ·
                      rfl

theorem cell22_355787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 3].length) (baseStart_355787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355787 prefixEnd_355787 := by exact prefixLift 355787
  have htrace : WordTrace (prefixWord ++ tailWord_355787) baseStart_355787 baseEnd_355787 := by
    simpa [prefixWord, tailWord_355787, baseEnd_355787] using wordTrace_append hprefix tailTrace_355787
  have hstable : (prefixWord ++ tailWord_355787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355787).length < 2 ^ (prefixWord ++ tailWord_355787).sum := by decide
  have hdescent : baseEnd_355787 < baseStart_355787 := by decide
  rcases family_descends (prefixWord ++ tailWord_355787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355830 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_355830 : Nat := 118140960795 + 355830 * 2 ^ 59
def prefixEnd_355830 : Nat := 4983230072969 + 3 ^ 40 * 355830 * 2
def baseEnd_355830 : Nat := 121807880859632031459049

theorem tailTrace_355830 : CollatzResearch.WordTrace tailWord_355830 prefixEnd_355830 121807880859632031459049 := by
  unfold tailWord_355830
  simp only [CollatzResearch.WordTrace]
  refine ⟨811136643806009735680559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8652124200597437180592629 811136643806009735680559)
  ·
    refine ⟨1216704965709014603520839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 811136643806009735680559 1216704965709014603520839)
    ·
      refine ⟨1825057448563521905281259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216704965709014603520839 1825057448563521905281259)
      ·
        refine ⟨2737586172845282857921889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825057448563521905281259 2737586172845282857921889)
        ·
          refine ⟨2053189629633962143441417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2737586172845282857921889 2053189629633962143441417)
          ·
            refine ⟨1539892222225471607581063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053189629633962143441417 1539892222225471607581063)
            ·
              refine ⟨2309838333338207411371595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539892222225471607581063 2309838333338207411371595)
              ·
                refine ⟨3464757500007311117057393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2309838333338207411371595 3464757500007311117057393)
                ·
                  refine ⟨2598568125005483337793045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3464757500007311117057393 2598568125005483337793045)
                  ·
                    refine ⟨121807880859632031459049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2598568125005483337793045 121807880859632031459049)
                    ·
                      rfl

theorem cell22_355830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_355830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355830 prefixEnd_355830 := by exact prefixLift 355830
  have htrace : WordTrace (prefixWord ++ tailWord_355830) baseStart_355830 baseEnd_355830 := by
    simpa [prefixWord, tailWord_355830, baseEnd_355830] using wordTrace_append hprefix tailTrace_355830
  have hstable : (prefixWord ++ tailWord_355830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355830).length < 2 ^ (prefixWord ++ tailWord_355830).sum := by decide
  have hdescent : baseEnd_355830 < baseStart_355830 := by decide
  rcases family_descends (prefixWord ++ tailWord_355830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355853 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_355853 : Nat := 118140960795 + 355853 * 2 ^ 59
def prefixEnd_355853 : Nat := 4983230072969 + 3 ^ 40 * 355853 * 2
def baseEnd_355853 : Nat := 121815754229667638133979

theorem tailTrace_355853 : CollatzResearch.WordTrace tailWord_355853 prefixEnd_355853 121815754229667638133979 := by
  unfold tailWord_355853
  simp only [CollatzResearch.WordTrace]
  refine ⟨12979025179812830698976213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8652683453208553799317475 12979025179812830698976213)
  ·
    refine ⟨304195902651863219507255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12979025179812830698976213 304195902651863219507255)
    ·
      refine ⟨456293853977794829260883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304195902651863219507255 456293853977794829260883)
      ·
        refine ⟨684440780966692243891325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456293853977794829260883 684440780966692243891325)
        ·
          refine ⟨256665292862509591459247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 684440780966692243891325 256665292862509591459247)
          ·
            refine ⟨384997939293764387188871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256665292862509591459247 384997939293764387188871)
            ·
              refine ⟨577496908940646580783307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384997939293764387188871 577496908940646580783307)
              ·
                refine ⟨866245363410969871174961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577496908940646580783307 866245363410969871174961)
                ·
                  refine ⟨649684022558227403381221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 866245363410969871174961 649684022558227403381221)
                  ·
                    refine ⟨121815754229667638133979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 649684022558227403381221 121815754229667638133979)
                    ·
                      rfl

theorem cell22_355853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_355853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355853 prefixEnd_355853 := by exact prefixLift 355853
  have htrace : WordTrace (prefixWord ++ tailWord_355853) baseStart_355853 baseEnd_355853 := by
    simpa [prefixWord, tailWord_355853, baseEnd_355853] using wordTrace_append hprefix tailTrace_355853
  have hstable : (prefixWord ++ tailWord_355853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355853).length < 2 ^ (prefixWord ++ tailWord_355853).sum := by decide
  have hdescent : baseEnd_355853 < baseStart_355853 := by decide
  rcases family_descends (prefixWord ++ tailWord_355853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355920 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_355920 : Nat := 118140960795 + 355920 * 2 ^ 59
def prefixEnd_355920 : Nat := 4983230072969 + 3 ^ 40 * 355920 * 2
def baseEnd_355920 : Nat := 121838689698901796708773

theorem tailTrace_355920 : CollatzResearch.WordTrace tailWord_355920 prefixEnd_355920 121838689698901796708773 := by
  unfold tailWord_355920
  simp only [CollatzResearch.WordTrace]
  refine ⟨6490734435285050570832607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8654312580380067427776809 6490734435285050570832607)
  ·
    refine ⟨9736101652927575856248911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6490734435285050570832607 9736101652927575856248911)
    ·
      refine ⟨14604152479391363784373367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9736101652927575856248911 14604152479391363784373367)
      ·
        refine ⟨21906228719087045676560051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14604152479391363784373367 21906228719087045676560051)
        ·
          refine ⟨32859343078630568514840077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21906228719087045676560051 32859343078630568514840077)
          ·
            refine ⟨12322253654486463193065029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32859343078630568514840077 12322253654486463193065029)
            ·
              refine ⟨2310422560216211848699693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12322253654486463193065029 2310422560216211848699693)
              ·
                refine ⟨866408460081079443262385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2310422560216211848699693 866408460081079443262385)
                ·
                  refine ⟨649806345060809582446789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 866408460081079443262385 649806345060809582446789)
                  ·
                    refine ⟨121838689698901796708773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 649806345060809582446789 121838689698901796708773)
                    ·
                      rfl

theorem cell22_355920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_355920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355920 prefixEnd_355920 := by exact prefixLift 355920
  have htrace : WordTrace (prefixWord ++ tailWord_355920) baseStart_355920 baseEnd_355920 := by
    simpa [prefixWord, tailWord_355920, baseEnd_355920] using wordTrace_append hprefix tailTrace_355920
  have hstable : (prefixWord ++ tailWord_355920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355920).length < 2 ^ (prefixWord ++ tailWord_355920).sum := by decide
  have hdescent : baseEnd_355920 < baseStart_355920 := by decide
  rcases family_descends (prefixWord ++ tailWord_355920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355922 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_355922 : Nat := 118140960795 + 355922 * 2 ^ 59
def prefixEnd_355922 : Nat := 4983230072969 + 3 ^ 40 * 355922 * 2
def baseEnd_355922 : Nat := 121839374339774458158767

theorem tailTrace_355922 : CollatzResearch.WordTrace tailWord_355922 prefixEnd_355922 121839374339774458158767 := by
  unfold tailWord_355922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245385454140713870809505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8654361211041903655492013 3245385454140713870809505)
  ·
    refine ⟨2434039090605535403107129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3245385454140713870809505 2434039090605535403107129)
    ·
      refine ⟨1825529317954151552330347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2434039090605535403107129 1825529317954151552330347)
      ·
        refine ⟨2738293976931227328495521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825529317954151552330347 2738293976931227328495521)
        ·
          refine ⟨2053720482698420496371641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2738293976931227328495521 2053720482698420496371641)
          ·
            refine ⟨1540290362023815372278731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053720482698420496371641 1540290362023815372278731)
            ·
              refine ⟨2310435543035723058418097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540290362023815372278731 2310435543035723058418097)
              ·
                refine ⟨1732826657276792293813573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310435543035723058418097 1732826657276792293813573)
                ·
                  refine ⟨324904998239398555090045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732826657276792293813573 324904998239398555090045)
                  ·
                    refine ⟨121839374339774458158767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324904998239398555090045 121839374339774458158767)
                    ·
                      rfl

theorem cell22_355922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_355922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_355922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_355922 prefixEnd_355922 := by exact prefixLift 355922
  have htrace : WordTrace (prefixWord ++ tailWord_355922) baseStart_355922 baseEnd_355922 := by
    simpa [prefixWord, tailWord_355922, baseEnd_355922] using wordTrace_append hprefix tailTrace_355922
  have hstable : (prefixWord ++ tailWord_355922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355922).length < 2 ^ (prefixWord ++ tailWord_355922).sum := by decide
  have hdescent : baseEnd_355922 < baseStart_355922 := by decide
  rcases family_descends (prefixWord ++ tailWord_355922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356001 : List Nat := [1, 2, 3, 3, 2, 2, 1, 4, 1, 3]
def baseStart_356001 : Nat := 118140960795 + 356001 * 2 ^ 59
def prefixEnd_356001 : Nat := 4983230072969 + 3 ^ 40 * 356001 * 2
def baseEnd_356001 : Nat := 121866417654244585433525

theorem tailTrace_356001 : CollatzResearch.WordTrace tailWord_356001 prefixEnd_356001 121866417654244585433525 := by
  unfold tailWord_356001
  simp only [CollatzResearch.WordTrace]
  refine ⟨12984423183276651975363857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8656282122184434650242571 12984423183276651975363857)
  ·
    refine ⟨9738317387457488981522893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12984423183276651975363857 9738317387457488981522893)
    ·
      refine ⟨3651869020296558368071085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9738317387457488981522893 3651869020296558368071085)
      ·
        refine ⟨1369450882611209388026657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3651869020296558368071085 1369450882611209388026657)
        ·
          refine ⟨1027088161958407041019993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1369450882611209388026657 1027088161958407041019993)
          ·
            refine ⟨770316121468805280764995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027088161958407041019993 770316121468805280764995)
            ·
              refine ⟨1155474182203207921147493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770316121468805280764995 1155474182203207921147493)
              ·
                refine ⟨216651409163101485215155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1155474182203207921147493 216651409163101485215155)
                ·
                  refine ⟨324977113744652227822733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216651409163101485215155 324977113744652227822733)
                  ·
                    refine ⟨121866417654244585433525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324977113744652227822733 121866417654244585433525)
                    ·
                      rfl

theorem cell22_356001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_356001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356001 prefixEnd_356001 := by exact prefixLift 356001
  have htrace : WordTrace (prefixWord ++ tailWord_356001) baseStart_356001 baseEnd_356001 := by
    simpa [prefixWord, tailWord_356001, baseEnd_356001] using wordTrace_append hprefix tailTrace_356001
  have hstable : (prefixWord ++ tailWord_356001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356001).length < 2 ^ (prefixWord ++ tailWord_356001).sum := by decide
  have hdescent : baseEnd_356001 < baseStart_356001 := by decide
  rcases family_descends (prefixWord ++ tailWord_356001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356025 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 8]
def baseStart_356025 : Nat := 118140960795 + 356025 * 2 ^ 59
def prefixEnd_356025 : Nat := 4983230072969 + 3 ^ 40 * 356025 * 2
def baseEnd_356025 : Nat := 40624877781572174277817

theorem tailTrace_356025 : CollatzResearch.WordTrace tailWord_356025 prefixEnd_356025 40624877781572174277817 := by
  unfold tailWord_356025
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985298535189704074237529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8656865690126469382825019 12985298535189704074237529)
  ·
    refine ⟨9738973901392278055678147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12985298535189704074237529 9738973901392278055678147)
    ·
      refine ⟨14608460852088417083517221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9738973901392278055678147 14608460852088417083517221)
      ·
        refine ⟨2739086409766578203159479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14608460852088417083517221 2739086409766578203159479)
        ·
          refine ⟨4108629614649867304739219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739086409766578203159479 4108629614649867304739219)
          ·
            refine ⟨6162944421974800957108829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4108629614649867304739219 6162944421974800957108829)
            ·
              refine ⟨2311104158240550358915811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6162944421974800957108829 2311104158240550358915811)
              ·
                refine ⟨3466656237360825538373717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311104158240550358915811 3466656237360825538373717)
                ·
                  refine ⟨40624877781572174277817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3466656237360825538373717 40624877781572174277817)
                  ·
                    rfl

theorem cell22_356025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_356025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356025 prefixEnd_356025 := by exact prefixLift 356025
  have htrace : WordTrace (prefixWord ++ tailWord_356025) baseStart_356025 baseEnd_356025 := by
    simpa [prefixWord, tailWord_356025, baseEnd_356025] using wordTrace_append hprefix tailTrace_356025
  have hstable : (prefixWord ++ tailWord_356025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356025).length < 2 ^ (prefixWord ++ tailWord_356025).sum := by decide
  have hdescent : baseEnd_356025 < baseStart_356025 := by decide
  rcases family_descends (prefixWord ++ tailWord_356025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356072 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_356072 : Nat := 118140960795 + 356072 * 2 ^ 59
def prefixEnd_356072 : Nat := 4983230072969 + 3 ^ 40 * 356072 * 2
def baseEnd_356072 : Nat := 121890722405224066908307

theorem tailTrace_356072 : CollatzResearch.WordTrace tailWord_356072 prefixEnd_356072 121890722405224066908307 := by
  unfold tailWord_356072
  simp only [CollatzResearch.WordTrace]
  refine ⟨6493506383009715550599235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8658008510679620734132313 6493506383009715550599235)
  ·
    refine ⟨9740259574514573325898853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6493506383009715550599235 9740259574514573325898853)
    ·
      refine ⟨1826298670221482498606035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9740259574514573325898853 1826298670221482498606035)
      ·
        refine ⟨2739448005332223747909053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826298670221482498606035 2739448005332223747909053)
        ·
          refine ⟨1027293001999583905465895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2739448005332223747909053 1027293001999583905465895)
          ·
            refine ⟨1540939502999375858198843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027293001999583905465895 1540939502999375858198843)
            ·
              refine ⟨2311409254499063787298265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540939502999375858198843 2311409254499063787298265)
              ·
                refine ⟨1733556940874297840473699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2311409254499063787298265 1733556940874297840473699)
                ·
                  refine ⟨2600335411311446760710549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1733556940874297840473699 2600335411311446760710549)
                  ·
                    refine ⟨121890722405224066908307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2600335411311446760710549 121890722405224066908307)
                    ·
                      rfl

theorem cell22_356072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_356072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356072 prefixEnd_356072 := by exact prefixLift 356072
  have htrace : WordTrace (prefixWord ++ tailWord_356072) baseStart_356072 baseEnd_356072 := by
    simpa [prefixWord, tailWord_356072, baseEnd_356072] using wordTrace_append hprefix tailTrace_356072
  have hstable : (prefixWord ++ tailWord_356072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356072).length < 2 ^ (prefixWord ++ tailWord_356072).sum := by decide
  have hdescent : baseEnd_356072 < baseStart_356072 := by decide
  rcases family_descends (prefixWord ++ tailWord_356072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356074 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_356074 : Nat := 118140960795 + 356074 * 2 ^ 59
def prefixEnd_356074 : Nat := 4983230072969 + 3 ^ 40 * 356074 * 2
def baseEnd_356074 : Nat := 121891407046096728358301

theorem tailTrace_356074 : CollatzResearch.WordTrace tailWord_356074 prefixEnd_356074 121891407046096728358301 := by
  unfold tailWord_356074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3246771428003046360692819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8658057141341456961847517 3246771428003046360692819)
  ·
    refine ⟨4870157142004569541039229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3246771428003046360692819 4870157142004569541039229)
    ·
      refine ⟨1826308928251713577889711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4870157142004569541039229 1826308928251713577889711)
      ·
        refine ⟨2739463392377570366834567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826308928251713577889711 2739463392377570366834567)
        ·
          refine ⟨4109195088566355550251851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739463392377570366834567 4109195088566355550251851)
          ·
            refine ⟨6163792632849533325377777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109195088566355550251851 6163792632849533325377777)
            ·
              refine ⟨4622844474637149994033333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6163792632849533325377777 4622844474637149994033333)
              ·
                refine ⟨433391669497232811940625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4622844474637149994033333 433391669497232811940625)
                ·
                  refine ⟨325043752122924608955469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433391669497232811940625 325043752122924608955469)
                  ·
                    refine ⟨121891407046096728358301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 325043752122924608955469 121891407046096728358301)
                    ·
                      rfl

theorem cell22_356074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_356074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356074 prefixEnd_356074 := by exact prefixLift 356074
  have htrace : WordTrace (prefixWord ++ tailWord_356074) baseStart_356074 baseEnd_356074 := by
    simpa [prefixWord, tailWord_356074, baseEnd_356074] using wordTrace_append hprefix tailTrace_356074
  have hstable : (prefixWord ++ tailWord_356074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356074).length < 2 ^ (prefixWord ++ tailWord_356074).sum := by decide
  have hdescent : baseEnd_356074 < baseStart_356074 := by decide
  rcases family_descends (prefixWord ++ tailWord_356074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356087 : List Nat := [1, 1, 3, 1, 1, 1, 8, 6]
def baseStart_356087 : Nat := 118140960795 + 356087 * 2 ^ 59
def prefixEnd_356087 : Nat := 4983230072969 + 3 ^ 40 * 356087 * 2
def baseEnd_356087 : Nat := 13543984134641003087029

theorem tailTrace_356087 : CollatzResearch.WordTrace tailWord_356087 prefixEnd_356087 13543984134641003087029 := by
  unfold tailWord_356087
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987559860965088662994515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8658373240643392441996343 12987559860965088662994515)
  ·
    refine ⟨19481339791447632994491773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12987559860965088662994515 19481339791447632994491773)
    ·
      refine ⟨7305502421792862372934415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19481339791447632994491773 7305502421792862372934415)
      ·
        refine ⟨10958253632689293559401623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7305502421792862372934415 10958253632689293559401623)
        ·
          refine ⟨16437380449033940339102435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10958253632689293559401623 16437380449033940339102435)
          ·
            refine ⟨24656070673550910508653653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16437380449033940339102435 24656070673550910508653653)
            ·
              refine ⟨288938328205674732523285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 24656070673550910508653653 288938328205674732523285)
              ·
                refine ⟨13543984134641003087029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 288938328205674732523285 13543984134641003087029)
                ·
                  rfl

theorem cell22_356087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 6].length) (baseStart_356087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356087 prefixEnd_356087 := by exact prefixLift 356087
  have htrace : WordTrace (prefixWord ++ tailWord_356087) baseStart_356087 baseEnd_356087 := by
    simpa [prefixWord, tailWord_356087, baseEnd_356087] using wordTrace_append hprefix tailTrace_356087
  have hstable : (prefixWord ++ tailWord_356087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356087).length < 2 ^ (prefixWord ++ tailWord_356087).sum := by decide
  have hdescent : baseEnd_356087 < baseStart_356087 := by decide
  rcases family_descends (prefixWord ++ tailWord_356087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356194 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 8]
def baseStart_356194 : Nat := 118140960795 + 356194 * 2 ^ 59
def prefixEnd_356194 : Nat := 4983230072969 + 3 ^ 40 * 356194 * 2
def baseEnd_356194 : Nat := 40644161832818805119311

theorem tailTrace_356194 : CollatzResearch.WordTrace tailWord_356194 prefixEnd_356194 40644161832818805119311 := by
  unfold tailWord_356194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247865617894361484284909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8660974981051630624759757 3247865617894361484284909)
  ·
    refine ⟨1217949606710385556606841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3247865617894361484284909 1217949606710385556606841)
    ·
      refine ⟨913462205032789167455131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1217949606710385556606841 913462205032789167455131)
      ·
        refine ⟨1370193307549183751182697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913462205032789167455131 1370193307549183751182697)
        ·
          refine ⟨1027644980661887813387023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370193307549183751182697 1027644980661887813387023)
          ·
            refine ⟨1541467470992831720080535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027644980661887813387023 1541467470992831720080535)
            ·
              refine ⟨2312201206489247580120803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1541467470992831720080535 2312201206489247580120803)
              ·
                refine ⟨3468301809733871370181205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2312201206489247580120803 3468301809733871370181205)
                ·
                  refine ⟨40644161832818805119311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3468301809733871370181205 40644161832818805119311)
                  ·
                    rfl

theorem cell22_356194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_356194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356194 prefixEnd_356194 := by exact prefixLift 356194
  have htrace : WordTrace (prefixWord ++ tailWord_356194) baseStart_356194 baseEnd_356194 := by
    simpa [prefixWord, tailWord_356194, baseEnd_356194] using wordTrace_append hprefix tailTrace_356194
  have hstable : (prefixWord ++ tailWord_356194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356194).length < 2 ^ (prefixWord ++ tailWord_356194).sum := by decide
  have hdescent : baseEnd_356194 < baseStart_356194 := by decide
  rcases family_descends (prefixWord ++ tailWord_356194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356209 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 4, 3]
def baseStart_356209 : Nat := 118140960795 + 356209 * 2 ^ 59
def prefixEnd_356209 : Nat := 4983230072969 + 3 ^ 40 * 356209 * 2
def baseEnd_356209 : Nat := 121937620305001376232887

theorem tailTrace_356209 : CollatzResearch.WordTrace tailWord_356209 prefixEnd_356209 121937620305001376232887 := by
  unfold tailWord_356209
  simp only [CollatzResearch.WordTrace]
  refine ⟨12992009566523103498935681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8661339711015402332623787 12992009566523103498935681)
  ·
    refine ⟨9744007174892327624201761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12992009566523103498935681 9744007174892327624201761)
    ·
      refine ⟨7308005381169245718151321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9744007174892327624201761 7308005381169245718151321)
      ·
        refine ⟨5481004035876934288613491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7308005381169245718151321 5481004035876934288613491)
        ·
          refine ⟨8221506053815401432920237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481004035876934288613491 8221506053815401432920237)
          ·
            refine ⟨3083064770180775537345089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8221506053815401432920237 3083064770180775537345089)
            ·
              refine ⟨2312298577635581653008817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3083064770180775537345089 2312298577635581653008817)
              ·
                refine ⟨1734223933226686239756613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2312298577635581653008817 1734223933226686239756613)
                ·
                  refine ⟨325166987480003669954365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1734223933226686239756613 325166987480003669954365)
                  ·
                    refine ⟨121937620305001376232887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 325166987480003669954365 121937620305001376232887)
                    ·
                      rfl

theorem cell22_356209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_356209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356209 prefixEnd_356209 := by exact prefixLift 356209
  have htrace : WordTrace (prefixWord ++ tailWord_356209) baseStart_356209 baseEnd_356209 := by
    simpa [prefixWord, tailWord_356209, baseEnd_356209] using wordTrace_append hprefix tailTrace_356209
  have hstable : (prefixWord ++ tailWord_356209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356209).length < 2 ^ (prefixWord ++ tailWord_356209).sum := by decide
  have hdescent : baseEnd_356209 < baseStart_356209 := by decide
  rcases family_descends (prefixWord ++ tailWord_356209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356440 : List Nat := [2, 1, 2, 2, 1, 4, 3, 3, 1, 3]
def baseStart_356440 : Nat := 118140960795 + 356440 * 2 ^ 59
def prefixEnd_356440 : Nat := 4983230072969 + 3 ^ 40 * 356440 * 2
def baseEnd_356440 : Nat := 122016696325793773707179

theorem tailTrace_356440 : CollatzResearch.WordTrace tailWord_356440 prefixEnd_356440 122016696325793773707179 := by
  unfold tailWord_356440
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500217414343114975297387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8666956552457486633729849 6500217414343114975297387)
  ·
    refine ⟨9750326121514672462946081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6500217414343114975297387 9750326121514672462946081)
    ·
      refine ⟨7312744591136004347209561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9750326121514672462946081 7312744591136004347209561)
      ·
        refine ⟨5484558443352003260407171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7312744591136004347209561 5484558443352003260407171)
        ·
          refine ⟨8226837665028004890610757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5484558443352003260407171 8226837665028004890610757)
          ·
            refine ⟨1542532062192750916989517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8226837665028004890610757 1542532062192750916989517)
            ·
              refine ⟨578449523322281593871069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1542532062192750916989517 578449523322281593871069)
              ·
                refine ⟨216918571245855597701651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 578449523322281593871069 216918571245855597701651)
                ·
                  refine ⟨325377856868783396552477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216918571245855597701651 325377856868783396552477)
                  ·
                    refine ⟨122016696325793773707179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 325377856868783396552477 122016696325793773707179)
                    ·
                      rfl

theorem cell22_356440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_356440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356440 prefixEnd_356440 := by exact prefixLift 356440
  have htrace : WordTrace (prefixWord ++ tailWord_356440) baseStart_356440 baseEnd_356440 := by
    simpa [prefixWord, tailWord_356440, baseEnd_356440] using wordTrace_append hprefix tailTrace_356440
  have hstable : (prefixWord ++ tailWord_356440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356440).length < 2 ^ (prefixWord ++ tailWord_356440).sum := by decide
  have hdescent : baseEnd_356440 < baseStart_356440 := by decide
  rcases family_descends (prefixWord ++ tailWord_356440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356470 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_356470 : Nat := 118140960795 + 356470 * 2 ^ 59
def prefixEnd_356470 : Nat := 4983230072969 + 3 ^ 40 * 356470 * 2
def baseEnd_356470 : Nat := 40675655312961231819029

theorem tailTrace_356470 : CollatzResearch.WordTrace tailWord_356470 prefixEnd_356470 40675655312961231819029 := by
  unfold tailWord_356470
  simp only [CollatzResearch.WordTrace]
  refine ⟨812595563661096567136679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8667686012385030049457909 812595563661096567136679)
  ·
    refine ⟨1218893345491644850705019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 812595563661096567136679 1218893345491644850705019)
    ·
      refine ⟨1828340018237467276057529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218893345491644850705019 1828340018237467276057529)
      ·
        refine ⟨1371255013678100457043147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1828340018237467276057529 1371255013678100457043147)
        ·
          refine ⟨2056882520517150685564721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371255013678100457043147 2056882520517150685564721)
          ·
            refine ⟨1542661890387863014173541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2056882520517150685564721 1542661890387863014173541)
            ·
              refine ⟨289249104447724315157539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1542661890387863014173541 289249104447724315157539)
              ·
                refine ⟨433873656671586472736309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289249104447724315157539 433873656671586472736309)
                ·
                  refine ⟨40675655312961231819029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 433873656671586472736309 40675655312961231819029)
                  ·
                    rfl

theorem cell22_356470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_356470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356470 prefixEnd_356470 := by exact prefixLift 356470
  have htrace : WordTrace (prefixWord ++ tailWord_356470) baseStart_356470 baseEnd_356470 := by
    simpa [prefixWord, tailWord_356470, baseEnd_356470] using wordTrace_append hprefix tailTrace_356470
  have hstable : (prefixWord ++ tailWord_356470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356470).length < 2 ^ (prefixWord ++ tailWord_356470).sum := by decide
  have hdescent : baseEnd_356470 < baseStart_356470 := by decide
  rcases family_descends (prefixWord ++ tailWord_356470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356483 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 1, 4]
def baseStart_356483 : Nat := 118140960795 + 356483 * 2 ^ 59
def prefixEnd_356483 : Nat := 4983230072969 + 3 ^ 40 * 356483 * 2
def baseEnd_356483 : Nat := 122031416104555994882047

theorem tailTrace_356483 : CollatzResearch.WordTrace tailWord_356483 prefixEnd_356483 122031416104555994882047 := by
  unfold tailWord_356483
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002003167530448294410103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8668002111686965529606735 13002003167530448294410103)
  ·
    refine ⟨19503004751295672441615155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13002003167530448294410103 19503004751295672441615155)
    ·
      refine ⟨29254507126943508662422733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19503004751295672441615155 29254507126943508662422733)
      ·
        refine ⟨10970440172603815748408525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29254507126943508662422733 10970440172603815748408525)
        ·
          refine ⟨4113915064726430905653197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10970440172603815748408525 4113915064726430905653197)
          ·
            refine ⟨1542718149272411589619949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4113915064726430905653197 1542718149272411589619949)
            ·
              refine ⟨578519305977154346107481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1542718149272411589619949 578519305977154346107481)
              ·
                refine ⟨433889479482865759580611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578519305977154346107481 433889479482865759580611)
                ·
                  refine ⟨650834219224298639370917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433889479482865759580611 650834219224298639370917)
                  ·
                    refine ⟨122031416104555994882047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 650834219224298639370917 122031416104555994882047)
                    ·
                      rfl

theorem cell22_356483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 4].length) (baseStart_356483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356483 prefixEnd_356483 := by exact prefixLift 356483
  have htrace : WordTrace (prefixWord ++ tailWord_356483) baseStart_356483 baseEnd_356483 := by
    simpa [prefixWord, tailWord_356483, baseEnd_356483] using wordTrace_append hprefix tailTrace_356483
  have hstable : (prefixWord ++ tailWord_356483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356483).length < 2 ^ (prefixWord ++ tailWord_356483).sum := by decide
  have hdescent : baseEnd_356483 < baseStart_356483 := by decide
  rcases family_descends (prefixWord ++ tailWord_356483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356496 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_356496 : Nat := 118140960795 + 356496 * 2 ^ 59
def prefixEnd_356496 : Nat := 4983230072969 + 3 ^ 40 * 356496 * 2
def baseEnd_356496 : Nat := 122035866270228294307007

theorem tailTrace_356496 : CollatzResearch.WordTrace tailWord_356496 prefixEnd_356496 122035866270228294307007 := by
  unfold tailWord_356496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501238658241675757316671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8668318210988901009755561 6501238658241675757316671)
  ·
    refine ⟨9751857987362513635975007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6501238658241675757316671 9751857987362513635975007)
    ·
      refine ⟨14627786981043770453962511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9751857987362513635975007 14627786981043770453962511)
      ·
        refine ⟨21941680471565655680943767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627786981043770453962511 21941680471565655680943767)
        ·
          refine ⟨32912520707348483521415651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21941680471565655680943767 32912520707348483521415651)
          ·
            refine ⟨49368781061022725282123477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32912520707348483521415651 49368781061022725282123477)
            ·
              refine ⟨1157080806117720123799769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49368781061022725282123477 1157080806117720123799769)
              ·
                refine ⟨867810604588290092849827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157080806117720123799769 867810604588290092849827)
                ·
                  refine ⟨1301715906882435139274741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867810604588290092849827 1301715906882435139274741)
                  ·
                    refine ⟨122035866270228294307007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1301715906882435139274741 122035866270228294307007)
                    ·
                      rfl

theorem cell22_356496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_356496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356496 prefixEnd_356496 := by exact prefixLift 356496
  have htrace : WordTrace (prefixWord ++ tailWord_356496) baseStart_356496 baseEnd_356496 := by
    simpa [prefixWord, tailWord_356496, baseEnd_356496] using wordTrace_append hprefix tailTrace_356496
  have hstable : (prefixWord ++ tailWord_356496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356496).length < 2 ^ (prefixWord ++ tailWord_356496).sum := by decide
  have hdescent : baseEnd_356496 < baseStart_356496 := by decide
  rcases family_descends (prefixWord ++ tailWord_356496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356545 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_356545 : Nat := 118140960795 + 356545 * 2 ^ 59
def prefixEnd_356545 : Nat := 4983230072969 + 3 ^ 40 * 356545 * 2
def baseEnd_356545 : Nat := 122052639971608499831857

theorem tailTrace_356545 : CollatzResearch.WordTrace tailWord_356545 prefixEnd_356545 122052639971608499831857 := by
  unfold tailWord_356545
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004264493305832883167089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8669509662203888588778059 13004264493305832883167089)
  ·
    refine ⟨9753198369979374662375317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13004264493305832883167089 9753198369979374662375317)
    ·
      refine ⟨457181173592783187298843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9753198369979374662375317 457181173592783187298843)
      ·
        refine ⟨685771760389174780948265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457181173592783187298843 685771760389174780948265)
        ·
          refine ⟨514328820291881085711199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685771760389174780948265 514328820291881085711199)
          ·
            refine ⟨771493230437821628566799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514328820291881085711199 771493230437821628566799)
            ·
              refine ⟨1157239845656732442850199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771493230437821628566799 1157239845656732442850199)
              ·
                refine ⟨1735859768485098664275299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157239845656732442850199 1735859768485098664275299)
                ·
                  refine ⟨2603789652727647996412949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735859768485098664275299 2603789652727647996412949)
                  ·
                    refine ⟨122052639971608499831857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2603789652727647996412949 122052639971608499831857)
                    ·
                      rfl

theorem cell22_356545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_356545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356545 prefixEnd_356545 := by exact prefixLift 356545
  have htrace : WordTrace (prefixWord ++ tailWord_356545) baseStart_356545 baseEnd_356545 := by
    simpa [prefixWord, tailWord_356545, baseEnd_356545] using wordTrace_append hprefix tailTrace_356545
  have hstable : (prefixWord ++ tailWord_356545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356545).length < 2 ^ (prefixWord ++ tailWord_356545).sum := by decide
  have hdescent : baseEnd_356545 < baseStart_356545 := by decide
  rcases family_descends (prefixWord ++ tailWord_356545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356665 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_356665 : Nat := 118140960795 + 356665 * 2 ^ 59
def prefixEnd_356665 : Nat := 4983230072969 + 3 ^ 40 * 356665 * 2
def baseEnd_356665 : Nat := 122093718423968186831489

theorem tailTrace_356665 : CollatzResearch.WordTrace tailWord_356665 prefixEnd_356665 122093718423968186831489 := by
  unfold tailWord_356665
  simp only [CollatzResearch.WordTrace]
  refine ⟨13008641252871093377535449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8672427501914062251690299 13008641252871093377535449)
  ·
    refine ⟨9756480939653320033151587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13008641252871093377535449 9756480939653320033151587)
    ·
      refine ⟨14634721409479980049727381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9756480939653320033151587 14634721409479980049727381)
      ·
        refine ⟨686002566069374064830971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14634721409479980049727381 686002566069374064830971)
        ·
          refine ⟨1029003849104061097246457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686002566069374064830971 1029003849104061097246457)
          ·
            refine ⟨771752886828045822934843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1029003849104061097246457 771752886828045822934843)
            ·
              refine ⟨1157629330242068734402265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771752886828045822934843 1157629330242068734402265)
              ·
                refine ⟨868221997681551550801699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157629330242068734402265 868221997681551550801699)
                ·
                  refine ⟨1302332996522327326202549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868221997681551550801699 1302332996522327326202549)
                  ·
                    refine ⟨122093718423968186831489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1302332996522327326202549 122093718423968186831489)
                    ·
                      rfl

theorem cell22_356665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_356665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356665 prefixEnd_356665 := by exact prefixLift 356665
  have htrace : WordTrace (prefixWord ++ tailWord_356665) baseStart_356665 baseEnd_356665 := by
    simpa [prefixWord, tailWord_356665, baseEnd_356665] using wordTrace_append hprefix tailTrace_356665
  have hstable : (prefixWord ++ tailWord_356665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356665).length < 2 ^ (prefixWord ++ tailWord_356665).sum := by decide
  have hdescent : baseEnd_356665 < baseStart_356665 := by decide
  rcases family_descends (prefixWord ++ tailWord_356665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356708 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_356708 : Nat := 118140960795 + 356708 * 2 ^ 59
def prefixEnd_356708 : Nat := 4983230072969 + 3 ^ 40 * 356708 * 2
def baseEnd_356708 : Nat := 122108438202730408006357

theorem tailTrace_356708 : CollatzResearch.WordTrace tailWord_356708 prefixEnd_356708 122108438202730408006357 := by
  unfold tailWord_356708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6505104795857655860675389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8673473061143541147567185 6505104795857655860675389)
  ·
    refine ⟨2439414298446620947753271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6505104795857655860675389 2439414298446620947753271)
    ·
      refine ⟨3659121447669931421629907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2439414298446620947753271 3659121447669931421629907)
      ·
        refine ⟨5488682171504897132444861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659121447669931421629907 5488682171504897132444861)
        ·
          refine ⟨2058255814314336424666823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5488682171504897132444861 2058255814314336424666823)
          ·
            refine ⟨3087383721471504637000235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058255814314336424666823 3087383721471504637000235)
            ·
              refine ⟨4631075582207256955500353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087383721471504637000235 4631075582207256955500353)
              ·
                refine ⟨3473306686655442716625265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4631075582207256955500353 3473306686655442716625265)
                ·
                  refine ⟨2604980014991582037468949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3473306686655442716625265 2604980014991582037468949)
                  ·
                    refine ⟨122108438202730408006357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2604980014991582037468949 122108438202730408006357)
                    ·
                      rfl

theorem cell22_356708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_356708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356708 prefixEnd_356708 := by exact prefixLift 356708
  have htrace : WordTrace (prefixWord ++ tailWord_356708) baseStart_356708 baseEnd_356708 := by
    simpa [prefixWord, tailWord_356708, baseEnd_356708] using wordTrace_append hprefix tailTrace_356708
  have hstable : (prefixWord ++ tailWord_356708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356708).length < 2 ^ (prefixWord ++ tailWord_356708).sum := by decide
  have hdescent : baseEnd_356708 < baseStart_356708 := by decide
  rcases family_descends (prefixWord ++ tailWord_356708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356853 : List Nat := [1, 3, 5, 1, 2, 2, 2, 2, 4]
def baseStart_356853 : Nat := 118140960795 + 356853 * 2 ^ 59
def prefixEnd_356853 : Nat := 4983230072969 + 3 ^ 40 * 356853 * 2
def baseEnd_356853 : Nat := 40719358221999454376971

theorem tailTrace_356853 : CollatzResearch.WordTrace tailWord_356853 prefixEnd_356853 40719358221999454376971 := by
  unfold tailWord_356853
  simp only [CollatzResearch.WordTrace]
  refine ⟨13015498176190001485379213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8676998784126667656919475 13015498176190001485379213)
  ·
    refine ⟨4880811816071250557017205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13015498176190001485379213 4880811816071250557017205)
    ·
      refine ⟨457576107756679739720363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4880811816071250557017205 457576107756679739720363)
      ·
        refine ⟨686364161635019609580545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457576107756679739720363 686364161635019609580545)
        ·
          refine ⟨514773121226264707185409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686364161635019609580545 514773121226264707185409)
          ·
            refine ⟨386079840919698530389057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514773121226264707185409 386079840919698530389057)
            ·
              refine ⟨289559880689773897791793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386079840919698530389057 289559880689773897791793)
              ·
                refine ⟨217169910517330423343845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289559880689773897791793 217169910517330423343845)
                ·
                  refine ⟨40719358221999454376971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217169910517330423343845 40719358221999454376971)
                  ·
                    rfl

theorem cell22_356853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_356853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356853 prefixEnd_356853 := by exact prefixLift 356853
  have htrace : WordTrace (prefixWord ++ tailWord_356853) baseStart_356853 baseEnd_356853 := by
    simpa [prefixWord, tailWord_356853, baseEnd_356853] using wordTrace_append hprefix tailTrace_356853
  have hstable : (prefixWord ++ tailWord_356853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356853).length < 2 ^ (prefixWord ++ tailWord_356853).sum := by decide
  have hdescent : baseEnd_356853 < baseStart_356853 := by decide
  rcases family_descends (prefixWord ++ tailWord_356853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356952 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 4, 3]
def baseStart_356952 : Nat := 118140960795 + 356952 * 2 ^ 59
def prefixEnd_356952 : Nat := 4983230072969 + 3 ^ 40 * 356952 * 2
def baseEnd_356952 : Nat := 122191964389195104905609

theorem tailTrace_356952 : CollatzResearch.WordTrace tailWord_356952 prefixEnd_356952 122191964389195104905609 := by
  unfold tailWord_356952
  simp only [CollatzResearch.WordTrace]
  refine ⟨6509554501415670696616555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8679406001887560928822073 6509554501415670696616555)
  ·
    refine ⟨9764331752123506044924833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6509554501415670696616555 9764331752123506044924833)
    ·
      refine ⟨7323248814092629533693625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9764331752123506044924833 7323248814092629533693625)
      ·
        refine ⟨5492436610569472150270219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7323248814092629533693625 5492436610569472150270219)
        ·
          refine ⟨8238654915854208225405329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5492436610569472150270219 8238654915854208225405329)
          ·
            refine ⟨6178991186890656169053997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8238654915854208225405329 6178991186890656169053997)
            ·
              refine ⟨2317121695083996063395249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6178991186890656169053997 2317121695083996063395249)
              ·
                refine ⟨1737841271312997047546437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317121695083996063395249 1737841271312997047546437)
                ·
                  refine ⟨325845238371186946414957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1737841271312997047546437 325845238371186946414957)
                  ·
                    refine ⟨122191964389195104905609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 325845238371186946414957 122191964389195104905609)
                    ·
                      rfl

theorem cell22_356952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_356952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_356952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_356952 prefixEnd_356952 := by exact prefixLift 356952
  have htrace : WordTrace (prefixWord ++ tailWord_356952) baseStart_356952 baseEnd_356952 := by
    simpa [prefixWord, tailWord_356952, baseEnd_356952] using wordTrace_append hprefix tailTrace_356952
  have hstable : (prefixWord ++ tailWord_356952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356952).length < 2 ^ (prefixWord ++ tailWord_356952).sum := by decide
  have hdescent : baseEnd_356952 < baseStart_356952 := by decide
  rcases family_descends (prefixWord ++ tailWord_356952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357089 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 6]
def baseStart_357089 : Nat := 118140960795 + 357089 * 2 ^ 59
def prefixEnd_357089 : Nat := 4983230072969 + 3 ^ 40 * 357089 * 2
def baseEnd_357089 : Nat := 40746287429657471410063

theorem tailTrace_357089 : CollatzResearch.WordTrace tailWord_357089 prefixEnd_357089 40746287429657471410063 := by
  unfold tailWord_357089
  simp only [CollatzResearch.WordTrace]
  refine ⟨13024105803335013790970321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8682737202223342527313547 13024105803335013790970321)
  ·
    refine ⟨9768079352501260343227741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13024105803335013790970321 9768079352501260343227741)
    ·
      refine ⟨3663029757187972628710403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9768079352501260343227741 3663029757187972628710403)
      ·
        refine ⟨5494544635781958943065605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663029757187972628710403 5494544635781958943065605)
        ·
          refine ⟨1030227119209117301824801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5494544635781958943065605 1030227119209117301824801)
          ·
            refine ⟨772670339406837976368601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030227119209117301824801 772670339406837976368601)
            ·
              refine ⟨579502754555128482276451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772670339406837976368601 579502754555128482276451)
              ·
                refine ⟨869254131832692723414677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579502754555128482276451 869254131832692723414677)
                ·
                  refine ⟨40746287429657471410063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 869254131832692723414677 40746287429657471410063)
                  ·
                    rfl

theorem cell22_357089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_357089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357089 prefixEnd_357089 := by exact prefixLift 357089
  have htrace : WordTrace (prefixWord ++ tailWord_357089) baseStart_357089 baseEnd_357089 := by
    simpa [prefixWord, tailWord_357089, baseEnd_357089] using wordTrace_append hprefix tailTrace_357089
  have hstable : (prefixWord ++ tailWord_357089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357089).length < 2 ^ (prefixWord ++ tailWord_357089).sum := by decide
  have hdescent : baseEnd_357089 < baseStart_357089 := by decide
  rcases family_descends (prefixWord ++ tailWord_357089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357117 : List Nat := [1, 4, 1, 1, 1, 1, 5, 8]
def baseStart_357117 : Nat := 118140960795 + 357117 * 2 ^ 59
def prefixEnd_357117 : Nat := 4983230072969 + 3 ^ 40 * 357117 * 2
def baseEnd_357117 : Nat := 13583160806798852725567

theorem tailTrace_357117 : CollatzResearch.WordTrace tailWord_357117 prefixEnd_357117 13583160806798852725567 := by
  unfold tailWord_357117
  simp only [CollatzResearch.WordTrace]
  refine ⟨13025127047233574572989605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8683418031489049715326403 13025127047233574572989605)
  ·
    refine ⟨2442211321356295232435551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13025127047233574572989605 2442211321356295232435551)
    ·
      refine ⟨3663316982034442848653327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2442211321356295232435551 3663316982034442848653327)
      ·
        refine ⟨5494975473051664272979991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663316982034442848653327 5494975473051664272979991)
        ·
          refine ⟨8242463209577496409469987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5494975473051664272979991 8242463209577496409469987)
          ·
            refine ⟨12363694814366244614204981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8242463209577496409469987 12363694814366244614204981)
            ·
              refine ⟨1159096388846835432581717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12363694814366244614204981 1159096388846835432581717)
              ·
                refine ⟨13583160806798852725567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1159096388846835432581717 13583160806798852725567)
                ·
                  rfl

theorem cell22_357117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 8].length) (baseStart_357117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357117 prefixEnd_357117 := by exact prefixLift 357117
  have htrace : WordTrace (prefixWord ++ tailWord_357117) baseStart_357117 baseEnd_357117 := by
    simpa [prefixWord, tailWord_357117, baseEnd_357117] using wordTrace_append hprefix tailTrace_357117
  have hstable : (prefixWord ++ tailWord_357117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357117).length < 2 ^ (prefixWord ++ tailWord_357117).sum := by decide
  have hdescent : baseEnd_357117 < baseStart_357117 := by decide
  rcases family_descends (prefixWord ++ tailWord_357117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357196 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 5]
def baseStart_357196 : Nat := 118140960795 + 357196 * 2 ^ 59
def prefixEnd_357196 : Nat := 4983230072969 + 3 ^ 40 * 357196 * 2
def baseEnd_357196 : Nat := 40758496858553267268287

theorem tailTrace_357196 : CollatzResearch.WordTrace tailWord_357196 prefixEnd_357196 40758496858553267268287 := by
  unfold tailWord_357196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6514004206973685532557721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8685338942631580710076961 6514004206973685532557721)
  ·
    refine ⟨4885503155230264149418291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6514004206973685532557721 4885503155230264149418291)
    ·
      refine ⟨7328254732845396224127437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4885503155230264149418291 7328254732845396224127437)
      ·
        refine ⟨2748095524817023584047789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7328254732845396224127437 2748095524817023584047789)
        ·
          refine ⟨1030535821806383844017921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2748095524817023584047789 1030535821806383844017921)
          ·
            refine ⟨772901866354787883013441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030535821806383844017921 772901866354787883013441)
            ·
              refine ⟨579676399766090912260081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772901866354787883013441 579676399766090912260081)
              ·
                refine ⟨434757299824568184195061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579676399766090912260081 434757299824568184195061)
                ·
                  refine ⟨40758496858553267268287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 434757299824568184195061 40758496858553267268287)
                  ·
                    rfl

theorem cell22_357196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_357196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357196 prefixEnd_357196 := by exact prefixLift 357196
  have htrace : WordTrace (prefixWord ++ tailWord_357196) baseStart_357196 baseEnd_357196 := by
    simpa [prefixWord, tailWord_357196, baseEnd_357196] using wordTrace_append hprefix tailTrace_357196
  have hstable : (prefixWord ++ tailWord_357196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357196).length < 2 ^ (prefixWord ++ tailWord_357196).sum := by decide
  have hdescent : baseEnd_357196 < baseStart_357196 := by decide
  rcases family_descends (prefixWord ++ tailWord_357196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357209 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_357209 : Nat := 118140960795 + 357209 * 2 ^ 59
def prefixEnd_357209 : Nat := 4983230072969 + 3 ^ 40 * 357209 * 2
def baseEnd_357209 : Nat := 122279940741332101229821

theorem tailTrace_357209 : CollatzResearch.WordTrace tailWord_357209 prefixEnd_357209 122279940741332101229821 := by
  unfold tailWord_357209
  simp only [CollatzResearch.WordTrace]
  refine ⟨13028482562900274285338681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8685655041933516190225787 13028482562900274285338681)
  ·
    refine ⟨9771361922175205714004011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13028482562900274285338681 9771361922175205714004011)
    ·
      refine ⟨14657042883262808571006017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9771361922175205714004011 14657042883262808571006017)
      ·
        refine ⟨10992782162447106428254513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14657042883262808571006017 10992782162447106428254513)
        ·
          refine ⟨8244586621835329821190885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10992782162447106428254513 8244586621835329821190885)
          ·
            refine ⟨1545859991594124341473291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8244586621835329821190885 1545859991594124341473291)
            ·
              refine ⟨2318789987391186512209937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545859991594124341473291 2318789987391186512209937)
              ·
                refine ⟨1739092490543389884157453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2318789987391186512209937 1739092490543389884157453)
                ·
                  refine ⟨652159683953771206559045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1739092490543389884157453 652159683953771206559045)
                  ·
                    refine ⟨122279940741332101229821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 652159683953771206559045 122279940741332101229821)
                    ·
                      rfl

theorem cell22_357209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_357209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357209 prefixEnd_357209 := by exact prefixLift 357209
  have htrace : WordTrace (prefixWord ++ tailWord_357209) baseStart_357209 baseEnd_357209 := by
    simpa [prefixWord, tailWord_357209, baseEnd_357209] using wordTrace_append hprefix tailTrace_357209
  have hstable : (prefixWord ++ tailWord_357209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357209).length < 2 ^ (prefixWord ++ tailWord_357209).sum := by decide
  have hdescent : baseEnd_357209 < baseStart_357209 := by decide
  rcases family_descends (prefixWord ++ tailWord_357209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357224 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 8]
def baseStart_357224 : Nat := 118140960795 + 357224 * 2 ^ 59
def prefixEnd_357224 : Nat := 4983230072969 + 3 ^ 40 * 357224 * 2
def baseEnd_357224 : Nat := 40761691849292354034925

theorem tailTrace_357224 : CollatzResearch.WordTrace tailWord_357224 prefixEnd_357224 40761691849292354034925 := by
  unfold tailWord_357224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6514514828922965923567363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8686019771897287898089817 6514514828922965923567363)
  ·
    refine ⟨9771772243384448885351045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6514514828922965923567363 9771772243384448885351045)
    ·
      refine ⟨1832207295634584166003321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9771772243384448885351045 1832207295634584166003321)
      ·
        refine ⟨1374155471725938124502491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1832207295634584166003321 1374155471725938124502491)
        ·
          refine ⟨2061233207588907186753737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374155471725938124502491 2061233207588907186753737)
          ·
            refine ⟨1545924905691680390065303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2061233207588907186753737 1545924905691680390065303)
            ·
              refine ⟨2318887358537520585097955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545924905691680390065303 2318887358537520585097955)
              ·
                refine ⟨3478331037806280877646933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318887358537520585097955 3478331037806280877646933)
                ·
                  refine ⟨40761691849292354034925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3478331037806280877646933 40761691849292354034925)
                  ·
                    rfl

theorem cell22_357224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_357224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357224 prefixEnd_357224 := by exact prefixLift 357224
  have htrace : WordTrace (prefixWord ++ tailWord_357224) baseStart_357224 baseEnd_357224 := by
    simpa [prefixWord, tailWord_357224, baseEnd_357224] using wordTrace_append hprefix tailTrace_357224
  have hstable : (prefixWord ++ tailWord_357224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357224).length < 2 ^ (prefixWord ++ tailWord_357224).sum := by decide
  have hdescent : baseEnd_357224 < baseStart_357224 := by decide
  rcases family_descends (prefixWord ++ tailWord_357224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357241 : List Nat := [1, 2, 1, 3, 2, 3, 1, 5, 4]
def baseStart_357241 : Nat := 118140960795 + 357241 * 2 ^ 59
def prefixEnd_357241 : Nat := 4983230072969 + 3 ^ 40 * 357241 * 2
def baseEnd_357241 : Nat := 40763631665098228143241

theorem tailTrace_357241 : CollatzResearch.WordTrace tailWord_357241 prefixEnd_357241 40763631665098228143241 := by
  unfold tailWord_357241
  simp only [CollatzResearch.WordTrace]
  refine ⟨13029649698784343750503577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8686433132522895833669051 13029649698784343750503577)
  ·
    refine ⟨9772237274088257812877683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13029649698784343750503577 9772237274088257812877683)
    ·
      refine ⟨14658355911132386719316525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9772237274088257812877683 14658355911132386719316525)
      ·
        refine ⟨5496883466674645019743697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14658355911132386719316525 5496883466674645019743697)
        ·
          refine ⟨4122662600005983764807773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5496883466674645019743697 4122662600005983764807773)
          ·
            refine ⟨1545998475002243911802915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4122662600005983764807773 1545998475002243911802915)
            ·
              refine ⟨2318997712503365867704373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545998475002243911802915 2318997712503365867704373)
              ·
                refine ⟨217406035547190550097285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2318997712503365867704373 217406035547190550097285)
                ·
                  refine ⟨40763631665098228143241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217406035547190550097285 40763631665098228143241)
                  ·
                    rfl

theorem cell22_357241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 4].length) (baseStart_357241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357241 prefixEnd_357241 := by exact prefixLift 357241
  have htrace : WordTrace (prefixWord ++ tailWord_357241) baseStart_357241 baseEnd_357241 := by
    simpa [prefixWord, tailWord_357241, baseEnd_357241] using wordTrace_append hprefix tailTrace_357241
  have hstable : (prefixWord ++ tailWord_357241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357241).length < 2 ^ (prefixWord ++ tailWord_357241).sum := by decide
  have hdescent : baseEnd_357241 < baseStart_357241 := by decide
  rcases family_descends (prefixWord ++ tailWord_357241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357258 : List Nat := [3, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_357258 : Nat := 118140960795 + 357258 * 2 ^ 59
def prefixEnd_357258 : Nat := 4983230072969 + 3 ^ 40 * 357258 * 2
def baseEnd_357258 : Nat := 40765571480904102251557

theorem tailTrace_357258 : CollatzResearch.WordTrace tailWord_357258 prefixEnd_357258 40765571480904102251557 := by
  unfold tailWord_357258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257567434930688913468107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8686846493148503769248285 3257567434930688913468107)
  ·
    refine ⟨4886351152396033370202161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3257567434930688913468107 4886351152396033370202161)
    ·
      refine ⟨3664763364297025027651621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4886351152396033370202161 3664763364297025027651621)
      ·
        refine ⟨687143130805692192684679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3664763364297025027651621 687143130805692192684679)
        ·
          refine ⟨1030714696208538289027019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687143130805692192684679 1030714696208538289027019)
          ·
            refine ⟨1546072044312807433540529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030714696208538289027019 1546072044312807433540529)
            ·
              refine ⟨1159554033234605575155397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1546072044312807433540529 1159554033234605575155397)
              ·
                refine ⟨217416381231488545341637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1159554033234605575155397 217416381231488545341637)
                ·
                  refine ⟨40765571480904102251557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217416381231488545341637 40765571480904102251557)
                  ·
                    rfl

theorem cell22_357258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_357258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357258 prefixEnd_357258 := by exact prefixLift 357258
  have htrace : WordTrace (prefixWord ++ tailWord_357258) baseStart_357258 baseEnd_357258 := by
    simpa [prefixWord, tailWord_357258, baseEnd_357258] using wordTrace_append hprefix tailTrace_357258
  have hstable : (prefixWord ++ tailWord_357258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357258).length < 2 ^ (prefixWord ++ tailWord_357258).sum := by decide
  have hdescent : baseEnd_357258 < baseStart_357258 := by decide
  rcases family_descends (prefixWord ++ tailWord_357258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357284 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_357284 : Nat := 118140960795 + 357284 * 2 ^ 59
def prefixEnd_357284 : Nat := 4983230072969 + 3 ^ 40 * 357284 * 2
def baseEnd_357284 : Nat := 122305614774056905604591

theorem tailTrace_357284 : CollatzResearch.WordTrace tailWord_357284 prefixEnd_357284 122305614774056905604591 := by
  unfold tailWord_357284
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515609018814281047159453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8687478691752374729545937 6515609018814281047159453)
  ·
    refine ⟨2443353382055355392684795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6515609018814281047159453 2443353382055355392684795)
    ·
      refine ⟨3665030073083033089027193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443353382055355392684795 3665030073083033089027193)
      ·
        refine ⟨2748772554812274816770395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3665030073083033089027193 2748772554812274816770395)
        ·
          refine ⟨4123158832218412225155593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2748772554812274816770395 4123158832218412225155593)
          ·
            refine ⟨3092369124163809168866695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4123158832218412225155593 3092369124163809168866695)
            ·
              refine ⟨4638553686245713753300043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092369124163809168866695 4638553686245713753300043)
              ·
                refine ⟨6957830529368570629950065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4638553686245713753300043 6957830529368570629950065)
                ·
                  refine ⟨5218372897026427972462549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6957830529368570629950065 5218372897026427972462549)
                  ·
                    refine ⟨122305614774056905604591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5218372897026427972462549 122305614774056905604591)
                    ·
                      rfl

theorem cell22_357284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_357284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357284 prefixEnd_357284 := by exact prefixLift 357284
  have htrace : WordTrace (prefixWord ++ tailWord_357284) baseStart_357284 baseEnd_357284 := by
    simpa [prefixWord, tailWord_357284, baseEnd_357284] using wordTrace_append hprefix tailTrace_357284
  have hstable : (prefixWord ++ tailWord_357284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357284).length < 2 ^ (prefixWord ++ tailWord_357284).sum := by decide
  have hdescent : baseEnd_357284 < baseStart_357284 := by decide
  rcases family_descends (prefixWord ++ tailWord_357284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357329 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_357329 : Nat := 118140960795 + 357329 * 2 ^ 59
def prefixEnd_357329 : Nat := 4983230072969 + 3 ^ 40 * 357329 * 2
def baseEnd_357329 : Nat := 122321019193691788229453

theorem tailTrace_357329 : CollatzResearch.WordTrace tailWord_357329 prefixEnd_357329 122321019193691788229453 := by
  unfold tailWord_357329
  simp only [CollatzResearch.WordTrace]
  refine ⟨13032859322465534779707041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8688572881643689853138027 13032859322465534779707041)
  ·
    refine ⟨9774644491849151084780281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13032859322465534779707041 9774644491849151084780281)
    ·
      refine ⟨7330983368886863313585211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9774644491849151084780281 7330983368886863313585211)
      ·
        refine ⟨10996475053330294970377817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330983368886863313585211 10996475053330294970377817)
        ·
          refine ⟨8247356289997721227783363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10996475053330294970377817 8247356289997721227783363)
          ·
            refine ⟨12371034434996581841675045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8247356289997721227783363 12371034434996581841675045)
            ·
              refine ⟨2319568956561859095314071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12371034434996581841675045 2319568956561859095314071)
              ·
                refine ⟨3479353434842788642971107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2319568956561859095314071 3479353434842788642971107)
                ·
                  refine ⟨5219030152264182964456661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3479353434842788642971107 5219030152264182964456661)
                  ·
                    refine ⟨122321019193691788229453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5219030152264182964456661 122321019193691788229453)
                    ·
                      rfl

theorem cell22_357329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_357329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357329 prefixEnd_357329 := by exact prefixLift 357329
  have htrace : WordTrace (prefixWord ++ tailWord_357329) baseStart_357329 baseEnd_357329 := by
    simpa [prefixWord, tailWord_357329, baseEnd_357329] using wordTrace_append hprefix tailTrace_357329
  have hstable : (prefixWord ++ tailWord_357329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357329).length < 2 ^ (prefixWord ++ tailWord_357329).sum := by decide
  have hdescent : baseEnd_357329 < baseStart_357329 := by decide
  rcases family_descends (prefixWord ++ tailWord_357329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357410 : List Nat := [3, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_357410 : Nat := 118140960795 + 357410 * 2 ^ 59
def prefixEnd_357410 : Nat := 4983230072969 + 3 ^ 40 * 357410 * 2
def baseEnd_357410 : Nat := 40782915716344858984735

theorem tailTrace_357410 : CollatzResearch.WordTrace tailWord_357410 prefixEnd_357410 40782915716344858984735 := by
  unfold tailWord_357410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3258953408793021403351421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8690542423448057075603789 3258953408793021403351421)
  ·
    refine ⟨1222107528297383026256783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3258953408793021403351421 1222107528297383026256783)
    ·
      refine ⟨1833161292446074539385175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1222107528297383026256783 1833161292446074539385175)
      ·
        refine ⟨2749741938669111809077763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833161292446074539385175 2749741938669111809077763)
        ·
          refine ⟨4124612908003667713616645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749741938669111809077763 4124612908003667713616645)
          ·
            refine ⟨773364920250687696303121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4124612908003667713616645 773364920250687696303121)
            ·
              refine ⟨580023690188015772227341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773364920250687696303121 580023690188015772227341)
              ·
                refine ⟨217508883820505914585253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580023690188015772227341 217508883820505914585253)
                ·
                  refine ⟨40782915716344858984735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217508883820505914585253 40782915716344858984735)
                  ·
                    rfl

theorem cell22_357410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_357410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357410 prefixEnd_357410 := by exact prefixLift 357410
  have htrace : WordTrace (prefixWord ++ tailWord_357410) baseStart_357410 baseEnd_357410 := by
    simpa [prefixWord, tailWord_357410, baseEnd_357410] using wordTrace_append hprefix tailTrace_357410
  have hstable : (prefixWord ++ tailWord_357410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357410).length < 2 ^ (prefixWord ++ tailWord_357410).sum := by decide
  have hdescent : baseEnd_357410 < baseStart_357410 := by decide
  rcases family_descends (prefixWord ++ tailWord_357410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357412 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_357412 : Nat := 118140960795 + 357412 * 2 ^ 59
def prefixEnd_357412 : Nat := 4983230072969 + 3 ^ 40 * 357412 * 2
def baseEnd_357412 : Nat := 122349431789907238404199

theorem tailTrace_357412 : CollatzResearch.WordTrace tailWord_357412 prefixEnd_357412 122349431789907238404199 := by
  unfold tailWord_357412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517943290582419977489245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8690591054109893303318993 6517943290582419977489245)
  ·
    refine ⟨2444228733968407491558467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6517943290582419977489245 2444228733968407491558467)
    ·
      refine ⟨3666343100952611237337701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2444228733968407491558467 3666343100952611237337701)
      ·
        refine ⟨687439331428614607000819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3666343100952611237337701 687439331428614607000819)
        ·
          refine ⟨1031158997142921910501229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687439331428614607000819 1031158997142921910501229)
          ·
            refine ⟨386684623928595716437961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1031158997142921910501229 386684623928595716437961)
            ·
              refine ⟨290013467946446787328471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386684623928595716437961 290013467946446787328471)
              ·
                refine ⟨435020201919670180992707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290013467946446787328471 435020201919670180992707)
                ·
                  refine ⟨652530302879505271489061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435020201919670180992707 652530302879505271489061)
                  ·
                    refine ⟨122349431789907238404199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 652530302879505271489061 122349431789907238404199)
                    ·
                      rfl

theorem cell22_357412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_357412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357412 prefixEnd_357412 := by exact prefixLift 357412
  have htrace : WordTrace (prefixWord ++ tailWord_357412) baseStart_357412 baseEnd_357412 := by
    simpa [prefixWord, tailWord_357412, baseEnd_357412] using wordTrace_append hprefix tailTrace_357412
  have hstable : (prefixWord ++ tailWord_357412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357412).length < 2 ^ (prefixWord ++ tailWord_357412).sum := by decide
  have hdescent : baseEnd_357412 < baseStart_357412 := by decide
  rcases family_descends (prefixWord ++ tailWord_357412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357487 : List Nat := [1, 1, 2, 1, 3, 3, 5, 2, 1, 3]
def baseStart_357487 : Nat := 118140960795 + 357487 * 2 ^ 59
def prefixEnd_357487 : Nat := 4983230072969 + 3 ^ 40 * 357487 * 2
def baseEnd_357487 : Nat := 122375105822632042778969

theorem tailTrace_357487 : CollatzResearch.WordTrace tailWord_357487 prefixEnd_357487 122375105822632042778969 := by
  unfold tailWord_357487
  simp only [CollatzResearch.WordTrace]
  refine ⟨13038622055893127763958715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8692414703928751842639143 13038622055893127763958715)
  ·
    refine ⟨19557933083839691645938073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13038622055893127763958715 19557933083839691645938073)
    ·
      refine ⟨14668449812879768734453555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19557933083839691645938073 14668449812879768734453555)
      ·
        refine ⟨22002674719319653101680333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14668449812879768734453555 22002674719319653101680333)
        ·
          refine ⟨8251003019744869913130125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22002674719319653101680333 8251003019744869913130125)
          ·
            refine ⟨3094126132404326217423797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8251003019744869913130125 3094126132404326217423797)
            ·
              refine ⟨290074324912905582883481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3094126132404326217423797 290074324912905582883481)
              ·
                refine ⟨217555743684679187162611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290074324912905582883481 217555743684679187162611)
                ·
                  refine ⟨326333615527018780743917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217555743684679187162611 326333615527018780743917)
                  ·
                    refine ⟨122375105822632042778969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326333615527018780743917 122375105822632042778969)
                    ·
                      rfl

theorem cell22_357487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 3].length) (baseStart_357487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357487 prefixEnd_357487 := by exact prefixLift 357487
  have htrace : WordTrace (prefixWord ++ tailWord_357487) baseStart_357487 baseEnd_357487 := by
    simpa [prefixWord, tailWord_357487, baseEnd_357487] using wordTrace_append hprefix tailTrace_357487
  have hstable : (prefixWord ++ tailWord_357487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357487).length < 2 ^ (prefixWord ++ tailWord_357487).sum := by decide
  have hdescent : baseEnd_357487 < baseStart_357487 := by decide
  rcases family_descends (prefixWord ++ tailWord_357487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357511 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 8]
def baseStart_357511 : Nat := 118140960795 + 357511 * 2 ^ 59
def prefixEnd_357511 : Nat := 4983230072969 + 3 ^ 40 * 357511 * 2
def baseEnd_357511 : Nat := 40794440504367993392965

theorem tailTrace_357511 : CollatzResearch.WordTrace tailWord_357511 prefixEnd_357511 40794440504367993392965 := by
  unfold tailWord_357511
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039497407806179862832387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8692998271870786575221591 13039497407806179862832387)
  ·
    refine ⟨19559246111709269794248581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13039497407806179862832387 19559246111709269794248581)
    ·
      refine ⟨3667358645945488086421609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19559246111709269794248581 3667358645945488086421609)
      ·
        refine ⟨2750518984459116064816207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3667358645945488086421609 2750518984459116064816207)
        ·
          refine ⟨4125778476688674097224311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750518984459116064816207 4125778476688674097224311)
          ·
            refine ⟨6188667715033011145836467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4125778476688674097224311 6188667715033011145836467)
            ·
              refine ⟨9283001572549516718754701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6188667715033011145836467 9283001572549516718754701)
              ·
                refine ⟨3481125589706068769533013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9283001572549516718754701 3481125589706068769533013)
                ·
                  refine ⟨40794440504367993392965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3481125589706068769533013 40794440504367993392965)
                  ·
                    rfl

theorem cell22_357511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 8].length) (baseStart_357511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357511 prefixEnd_357511 := by exact prefixLift 357511
  have htrace : WordTrace (prefixWord ++ tailWord_357511) baseStart_357511 baseEnd_357511 := by
    simpa [prefixWord, tailWord_357511, baseEnd_357511] using wordTrace_append hprefix tailTrace_357511
  have hstable : (prefixWord ++ tailWord_357511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357511).length < 2 ^ (prefixWord ++ tailWord_357511).sum := by decide
  have hdescent : baseEnd_357511 < baseStart_357511 := by decide
  rcases family_descends (prefixWord ++ tailWord_357511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357513 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_357513 : Nat := 118140960795 + 357513 * 2 ^ 59
def prefixEnd_357513 : Nat := 4983230072969 + 3 ^ 40 * 357513 * 2
def baseEnd_357513 : Nat := 122384006153976641628889

theorem tailTrace_357513 : CollatzResearch.WordTrace tailWord_357513 prefixEnd_357513 122384006153976641628889 := by
  unfold tailWord_357513
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039570353798934204405193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8693046902532622802936795 13039570353798934204405193)
  ·
    refine ⟨9779677765349200653303895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13039570353798934204405193 9779677765349200653303895)
    ·
      refine ⟨14669516648023800979955843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9779677765349200653303895 14669516648023800979955843)
      ·
        refine ⟨22004274972035701469933765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14669516648023800979955843 22004274972035701469933765)
        ·
          refine ⟨4125801557256694025612581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22004274972035701469933765 4125801557256694025612581)
          ·
            refine ⟨773587791985630129802359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4125801557256694025612581 773587791985630129802359)
            ·
              refine ⟨1160381687978445194703539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773587791985630129802359 1160381687978445194703539)
              ·
                refine ⟨1740572531967667792055309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160381687978445194703539 1740572531967667792055309)
                ·
                  refine ⟨652714699487875422020741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1740572531967667792055309 652714699487875422020741)
                  ·
                    refine ⟨122384006153976641628889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 652714699487875422020741 122384006153976641628889)
                    ·
                      rfl

theorem cell22_357513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_357513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357513 prefixEnd_357513 := by exact prefixLift 357513
  have htrace : WordTrace (prefixWord ++ tailWord_357513) baseStart_357513 baseEnd_357513 := by
    simpa [prefixWord, tailWord_357513, baseEnd_357513] using wordTrace_append hprefix tailTrace_357513
  have hstable : (prefixWord ++ tailWord_357513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357513).length < 2 ^ (prefixWord ++ tailWord_357513).sum := by decide
  have hdescent : baseEnd_357513 < baseStart_357513 := by decide
  rcases family_descends (prefixWord ++ tailWord_357513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357538 : List Nat := [3, 3, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_357538 : Nat := 118140960795 + 357538 * 2 ^ 59
def prefixEnd_357538 : Nat := 4983230072969 + 3 ^ 40 * 357538 * 2
def baseEnd_357538 : Nat := 122392564164884909753813

theorem tailTrace_357538 : CollatzResearch.WordTrace tailWord_357538 prefixEnd_357538 122392564164884909753813 := by
  unfold tailWord_357538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260120544677090868516317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8693654785805575649376845 3260120544677090868516317)
  ·
    refine ⟨1222545204253909075693619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3260120544677090868516317 1222545204253909075693619)
    ·
      refine ⟨1833817806380863613540429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1222545204253909075693619 1833817806380863613540429)
      ·
        refine ⟨687681677392823855077661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1833817806380863613540429 687681677392823855077661)
        ·
          refine ⟨257880629022308945654123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 687681677392823855077661 257880629022308945654123)
          ·
            refine ⟨386820943533463418481185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257880629022308945654123 386820943533463418481185)
            ·
              refine ⟨290115707650097563860889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386820943533463418481185 290115707650097563860889)
              ·
                refine ⟨217586780737573172895667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 290115707650097563860889 217586780737573172895667)
                ·
                  refine ⟨326380171106359759343501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217586780737573172895667 326380171106359759343501)
                  ·
                    refine ⟨122392564164884909753813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326380171106359759343501 122392564164884909753813)
                    ·
                      rfl

theorem cell22_357538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_357538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357538 prefixEnd_357538 := by exact prefixLift 357538
  have htrace : WordTrace (prefixWord ++ tailWord_357538) baseStart_357538 baseEnd_357538 := by
    simpa [prefixWord, tailWord_357538, baseEnd_357538] using wordTrace_append hprefix tailTrace_357538
  have hstable : (prefixWord ++ tailWord_357538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357538).length < 2 ^ (prefixWord ++ tailWord_357538).sum := by decide
  have hdescent : baseEnd_357538 < baseStart_357538 := by decide
  rcases family_descends (prefixWord ++ tailWord_357538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357571 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 9]
def baseStart_357571 : Nat := 118140960795 + 357571 * 2 ^ 59
def prefixEnd_357571 : Nat := 4983230072969 + 3 ^ 40 * 357571 * 2
def baseEnd_357571 : Nat := 122403860739283823678711

theorem tailTrace_357571 : CollatzResearch.WordTrace tailWord_357571 prefixEnd_357571 122403860739283823678711 := by
  unfold tailWord_357571
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041685787588810110016567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8694457191725873406677711 13041685787588810110016567)
  ·
    refine ⟨19562528681383215165024851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13041685787588810110016567 19562528681383215165024851)
    ·
      refine ⟨29343793022074822747537277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19562528681383215165024851 29343793022074822747537277)
      ·
        refine ⟨11003922383278058530326479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29343793022074822747537277 11003922383278058530326479)
        ·
          refine ⟨16505883574917087795489719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11003922383278058530326479 16505883574917087795489719)
          ·
            refine ⟨24758825362375631693234579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16505883574917087795489719 24758825362375631693234579)
            ·
              refine ⟨37138238043563447539851869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24758825362375631693234579 37138238043563447539851869)
              ·
                refine ⟨13926839266336292827444451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37138238043563447539851869 13926839266336292827444451)
                ·
                  refine ⟨20890258899504439241166677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13926839266336292827444451 20890258899504439241166677)
                  ·
                    refine ⟨122403860739283823678711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 20890258899504439241166677 122403860739283823678711)
                    ·
                      rfl

theorem cell22_357571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_357571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357571 prefixEnd_357571 := by exact prefixLift 357571
  have htrace : WordTrace (prefixWord ++ tailWord_357571) baseStart_357571 baseEnd_357571 := by
    simpa [prefixWord, tailWord_357571, baseEnd_357571] using wordTrace_append hprefix tailTrace_357571
  have hstable : (prefixWord ++ tailWord_357571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357571).length < 2 ^ (prefixWord ++ tailWord_357571).sum := by decide
  have hdescent : baseEnd_357571 < baseStart_357571 := by decide
  rcases family_descends (prefixWord ++ tailWord_357571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357682 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_357682 : Nat := 118140960795 + 357682 * 2 ^ 59
def prefixEnd_357682 : Nat := 4983230072969 + 3 ^ 40 * 357682 * 2
def baseEnd_357682 : Nat := 122441858307716534153371

theorem tailTrace_357682 : CollatzResearch.WordTrace tailWord_357682 prefixEnd_357682 122441858307716534153371 := by
  unfold tailWord_357682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3261433572546669016826825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8697156193457784044871533 3261433572546669016826825)
  ·
    refine ⟨2446075179410001762620119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3261433572546669016826825 2446075179410001762620119)
    ·
      refine ⟨3669112769115002643930179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2446075179410001762620119 3669112769115002643930179)
      ·
        refine ⟨5503669153672503965895269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3669112769115002643930179 5503669153672503965895269)
        ·
          refine ⟨1031937966313594493605363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5503669153672503965895269 1031937966313594493605363)
          ·
            refine ⟨1547906949470391740408045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031937966313594493605363 1547906949470391740408045)
            ·
              refine ⟨580465106051396902653017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1547906949470391740408045 580465106051396902653017)
              ·
                refine ⟨435348829538547676989763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580465106051396902653017 435348829538547676989763)
                ·
                  refine ⟨653023244307821515484645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435348829538547676989763 653023244307821515484645)
                  ·
                    refine ⟨122441858307716534153371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 653023244307821515484645 122441858307716534153371)
                    ·
                      rfl

theorem cell22_357682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_357682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357682 prefixEnd_357682 := by exact prefixLift 357682
  have htrace : WordTrace (prefixWord ++ tailWord_357682) baseStart_357682 baseEnd_357682 := by
    simpa [prefixWord, tailWord_357682, baseEnd_357682] using wordTrace_append hprefix tailTrace_357682
  have hstable : (prefixWord ++ tailWord_357682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357682).length < 2 ^ (prefixWord ++ tailWord_357682).sum := by decide
  have hdescent : baseEnd_357682 < baseStart_357682 := by decide
  rcases family_descends (prefixWord ++ tailWord_357682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357695 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 1, 5]
def baseStart_357695 : Nat := 118140960795 + 357695 * 2 ^ 59
def prefixEnd_357695 : Nat := 4983230072969 + 3 ^ 40 * 357695 * 2
def baseEnd_357695 : Nat := 122446308473388833578331

theorem tailTrace_357695 : CollatzResearch.WordTrace tailWord_357695 prefixEnd_357695 122446308473388833578331 := by
  unfold tailWord_357695
  simp only [CollatzResearch.WordTrace]
  refine ⟨13046208439139579287530539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8697472292759719525020359 13046208439139579287530539)
  ·
    refine ⟨19569312658709368931295809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13046208439139579287530539 19569312658709368931295809)
    ·
      refine ⟨14676984494032026698471857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19569312658709368931295809 14676984494032026698471857)
      ·
        refine ⟨11007738370524020023853893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14676984494032026698471857 11007738370524020023853893)
        ·
          refine ⟨2063950944473253754472605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11007738370524020023853893 2063950944473253754472605)
          ·
            refine ⟨773981604177470157927227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2063950944473253754472605 773981604177470157927227)
            ·
              refine ⟨1160972406266205236890841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773981604177470157927227 1160972406266205236890841)
              ·
                refine ⟨870729304699653927668131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1160972406266205236890841 870729304699653927668131)
                ·
                  refine ⟨1306093957049480891502197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870729304699653927668131 1306093957049480891502197)
                  ·
                    refine ⟨122446308473388833578331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1306093957049480891502197 122446308473388833578331)
                    ·
                      rfl

theorem cell22_357695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_357695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357695 prefixEnd_357695 := by exact prefixLift 357695
  have htrace : WordTrace (prefixWord ++ tailWord_357695) baseStart_357695 baseEnd_357695 := by
    simpa [prefixWord, tailWord_357695, baseEnd_357695] using wordTrace_append hprefix tailTrace_357695
  have hstable : (prefixWord ++ tailWord_357695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357695).length < 2 ^ (prefixWord ++ tailWord_357695).sum := by decide
  have hdescent : baseEnd_357695 < baseStart_357695 := by decide
  rcases family_descends (prefixWord ++ tailWord_357695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357708 : List Nat := [2, 2, 1, 3, 2, 12]
def baseStart_357708 : Nat := 118140960795 + 357708 * 2 ^ 59
def prefixEnd_357708 : Nat := 4983230072969 + 3 ^ 40 * 357708 * 2
def baseEnd_357708 : Nat := 1511737760976063370411

theorem tailTrace_357708 : CollatzResearch.WordTrace tailWord_357708 prefixEnd_357708 1511737760976063370411 := by
  unfold tailWord_357708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6523341294046241253876889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8697788392061655005169185 6523341294046241253876889)
  ·
    refine ⟨4892505970534680940407667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6523341294046241253876889 4892505970534680940407667)
    ·
      refine ⟨7338758955802021410611501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4892505970534680940407667 7338758955802021410611501)
      ·
        refine ⟨2752034608425758028979313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7338758955802021410611501 2752034608425758028979313)
        ·
          refine ⟨2064025956319318521734485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2752034608425758028979313 2064025956319318521734485)
          ·
            refine ⟨1511737760976063370411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2064025956319318521734485 1511737760976063370411)
            ·
              rfl

theorem cell22_357708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 12].length) (baseStart_357708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357708 prefixEnd_357708 := by exact prefixLift 357708
  have htrace : WordTrace (prefixWord ++ tailWord_357708) baseStart_357708 baseEnd_357708 := by
    simpa [prefixWord, tailWord_357708, baseEnd_357708] using wordTrace_append hprefix tailTrace_357708
  have hstable : (prefixWord ++ tailWord_357708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357708).length < 2 ^ (prefixWord ++ tailWord_357708).sum := by decide
  have hdescent : baseEnd_357708 < baseStart_357708 := by decide
  rcases family_descends (prefixWord ++ tailWord_357708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357710 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_357710 : Nat := 118140960795 + 357710 * 2 ^ 59
def prefixEnd_357710 : Nat := 4983230072969 + 3 ^ 40 * 357710 * 2
def baseEnd_357710 : Nat := 122451443279933794453285

theorem tailTrace_357710 : CollatzResearch.WordTrace tailWord_357710 prefixEnd_357710 122451443279933794453285 := by
  unfold tailWord_357710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630844441760654606165823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8697837022723491232884389 1630844441760654606165823)
  ·
    refine ⟨2446266662640981909248735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1630844441760654606165823 2446266662640981909248735)
    ·
      refine ⟨3669399993961472863873103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2446266662640981909248735 3669399993961472863873103)
      ·
        refine ⟨5504099990942209295809655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3669399993961472863873103 5504099990942209295809655)
        ·
          refine ⟨8256149986413313943714483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5504099990942209295809655 8256149986413313943714483)
          ·
            refine ⟨12384224979619970915571725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8256149986413313943714483 12384224979619970915571725)
            ·
              refine ⟨4644084367357489093339397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12384224979619970915571725 4644084367357489093339397)
              ·
                refine ⟨870765818879529205001137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4644084367357489093339397 870765818879529205001137)
                ·
                  refine ⟨653074364159646903750853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 870765818879529205001137 653074364159646903750853)
                  ·
                    refine ⟨122451443279933794453285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 653074364159646903750853 122451443279933794453285)
                    ·
                      rfl

theorem cell22_357710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_357710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357710 prefixEnd_357710 := by exact prefixLift 357710
  have htrace : WordTrace (prefixWord ++ tailWord_357710) baseStart_357710 baseEnd_357710 := by
    simpa [prefixWord, tailWord_357710, baseEnd_357710] using wordTrace_append hprefix tailTrace_357710
  have hstable : (prefixWord ++ tailWord_357710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357710).length < 2 ^ (prefixWord ++ tailWord_357710).sum := by decide
  have hdescent : baseEnd_357710 < baseStart_357710 := by decide
  rcases family_descends (prefixWord ++ tailWord_357710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357712 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 2, 3]
def baseStart_357712 : Nat := 118140960795 + 357712 * 2 ^ 59
def prefixEnd_357712 : Nat := 4983230072969 + 3 ^ 40 * 357712 * 2
def baseEnd_357712 : Nat := 122452127920806455903279

theorem tailTrace_357712 : CollatzResearch.WordTrace tailWord_357712 prefixEnd_357712 122452127920806455903279 := by
  unfold tailWord_357712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6523414240038995595449695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8697885653385327460599593 6523414240038995595449695)
  ·
    refine ⟨9785121360058493393174543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6523414240038995595449695 9785121360058493393174543)
    ·
      refine ⟨14677682040087740089761815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9785121360058493393174543 14677682040087740089761815)
      ·
        refine ⟨22016523060131610134642723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14677682040087740089761815 22016523060131610134642723)
        ·
          refine ⟨33024784590197415201964085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22016523060131610134642723 33024784590197415201964085)
          ·
            refine ⟨3096073555331007675184133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33024784590197415201964085 3096073555331007675184133)
            ·
              refine ⟨580513791624563939097025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3096073555331007675184133 580513791624563939097025)
              ·
                refine ⟨435385343718422954322769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580513791624563939097025 435385343718422954322769)
                ·
                  refine ⟨326539007788817215742077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435385343718422954322769 326539007788817215742077)
                  ·
                    refine ⟨122452127920806455903279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326539007788817215742077 122452127920806455903279)
                    ·
                      rfl

theorem cell22_357712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_357712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357712 prefixEnd_357712 := by exact prefixLift 357712
  have htrace : WordTrace (prefixWord ++ tailWord_357712) baseStart_357712 baseEnd_357712 := by
    simpa [prefixWord, tailWord_357712, baseEnd_357712] using wordTrace_append hprefix tailTrace_357712
  have hstable : (prefixWord ++ tailWord_357712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357712).length < 2 ^ (prefixWord ++ tailWord_357712).sum := by decide
  have hdescent : baseEnd_357712 < baseStart_357712 := by decide
  rcases family_descends (prefixWord ++ tailWord_357712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357785 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_357785 : Nat := 118140960795 + 357785 * 2 ^ 59
def prefixEnd_357785 : Nat := 4983230072969 + 3 ^ 40 * 357785 * 2
def baseEnd_357785 : Nat := 122477117312658598828055

theorem tailTrace_357785 : CollatzResearch.WordTrace tailWord_357785 prefixEnd_357785 122477117312658598828055 := by
  unfold tailWord_357785
  simp only [CollatzResearch.WordTrace]
  refine ⟨13049491008813524658306809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8699660672542349772204539 13049491008813524658306809)
  ·
    refine ⟨9787118256610143493730107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13049491008813524658306809 9787118256610143493730107)
    ·
      refine ⟨14680677384915215240595161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9787118256610143493730107 14680677384915215240595161)
      ·
        refine ⟨11010508038686411430446371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14680677384915215240595161 11010508038686411430446371)
        ·
          refine ⟨16515762058029617145669557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11010508038686411430446371 16515762058029617145669557)
          ·
            refine ⟨1548352692940276607406521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16515762058029617145669557 1548352692940276607406521)
            ·
              refine ⟨1161264519705207455554891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548352692940276607406521 1161264519705207455554891)
              ·
                refine ⟨1741896779557811183332337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161264519705207455554891 1741896779557811183332337)
                ·
                  refine ⟨1306422584668358387499253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1741896779557811183332337 1306422584668358387499253)
                  ·
                    refine ⟨122477117312658598828055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1306422584668358387499253 122477117312658598828055)
                    ·
                      rfl

theorem cell22_357785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_357785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357785 prefixEnd_357785 := by exact prefixLift 357785
  have htrace : WordTrace (prefixWord ++ tailWord_357785) baseStart_357785 baseEnd_357785 := by
    simpa [prefixWord, tailWord_357785, baseEnd_357785] using wordTrace_append hprefix tailTrace_357785
  have hstable : (prefixWord ++ tailWord_357785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357785).length < 2 ^ (prefixWord ++ tailWord_357785).sum := by decide
  have hdescent : baseEnd_357785 < baseStart_357785 := by decide
  rcases family_descends (prefixWord ++ tailWord_357785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357877 : List Nat := [1, 3, 5, 1, 1, 11]
def baseStart_357877 : Nat := 118140960795 + 357877 * 2 ^ 59
def prefixEnd_357877 : Nat := 4983230072969 + 3 ^ 40 * 357877 * 2
def baseEnd_357877 : Nat := 1512451985096308957133

theorem tailTrace_357877 : CollatzResearch.WordTrace tailWord_357877 prefixEnd_357877 1512451985096308957133 := by
  unfold tailWord_357877
  simp only [CollatzResearch.WordTrace]
  refine ⟨13052846524480224370655885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8701897682986816247103923 13052846524480224370655885)
  ·
    refine ⟨4894817446680084138995957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13052846524480224370655885 4894817446680084138995957)
    ·
      refine ⟨458889135626257888030871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4894817446680084138995957 458889135626257888030871)
      ·
        refine ⟨688333703439386832046307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458889135626257888030871 688333703439386832046307)
        ·
          refine ⟨1032500555159080248069461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688333703439386832046307 1032500555159080248069461)
          ·
            refine ⟨1512451985096308957133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1032500555159080248069461 1512451985096308957133)
            ·
              rfl

theorem cell22_357877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 11].length) (baseStart_357877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357877 prefixEnd_357877 := by exact prefixLift 357877
  have htrace : WordTrace (prefixWord ++ tailWord_357877) baseStart_357877 baseEnd_357877 := by
    simpa [prefixWord, tailWord_357877, baseEnd_357877] using wordTrace_append hprefix tailTrace_357877
  have hstable : (prefixWord ++ tailWord_357877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357877).length < 2 ^ (prefixWord ++ tailWord_357877).sum := by decide
  have hdescent : baseEnd_357877 < baseStart_357877 := by decide
  rcases family_descends (prefixWord ++ tailWord_357877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357909 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_357909 : Nat := 118140960795 + 357909 * 2 ^ 59
def prefixEnd_357909 : Nat := 4983230072969 + 3 ^ 40 * 357909 * 2
def baseEnd_357909 : Nat := 122519565046763608727675

theorem tailTrace_357909 : CollatzResearch.WordTrace tailWord_357909 prefixEnd_357909 122519565046763608727675 := by
  unfold tailWord_357909
  simp only [CollatzResearch.WordTrace]
  refine ⟨13054013660364293835820781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8702675773576195890547187 13054013660364293835820781)
  ·
    refine ⟨4895255122636610188432793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13054013660364293835820781 4895255122636610188432793)
    ·
      refine ⟨3671441341977457641324595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4895255122636610188432793 3671441341977457641324595)
      ·
        refine ⟨5507162012966186461986893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3671441341977457641324595 5507162012966186461986893)
        ·
          refine ⟨2065185754862319923245085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5507162012966186461986893 2065185754862319923245085)
          ·
            refine ⟨774444658073369971216907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2065185754862319923245085 774444658073369971216907)
            ·
              refine ⟨1161666987110054956825361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774444658073369971216907 1161666987110054956825361)
              ·
                refine ⟨871250240332541217619021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161666987110054956825361 871250240332541217619021)
                ·
                  refine ⟨326718840124702956607133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871250240332541217619021 326718840124702956607133)
                  ·
                    refine ⟨122519565046763608727675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326718840124702956607133 122519565046763608727675)
                    ·
                      rfl

theorem cell22_357909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_357909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357909 prefixEnd_357909 := by exact prefixLift 357909
  have htrace : WordTrace (prefixWord ++ tailWord_357909) baseStart_357909 baseEnd_357909 := by
    simpa [prefixWord, tailWord_357909, baseEnd_357909] using wordTrace_append hprefix tailTrace_357909
  have hstable : (prefixWord ++ tailWord_357909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357909).length < 2 ^ (prefixWord ++ tailWord_357909).sum := by decide
  have hdescent : baseEnd_357909 < baseStart_357909 := by decide
  rcases family_descends (prefixWord ++ tailWord_357909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357939 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 5]
def baseStart_357939 : Nat := 118140960795 + 357939 * 2 ^ 59
def prefixEnd_357939 : Nat := 4983230072969 + 3 ^ 40 * 357939 * 2
def baseEnd_357939 : Nat := 40843278219951176825861

theorem tailTrace_357939 : CollatzResearch.WordTrace tailWord_357939 prefixEnd_357939 40843278219951176825861 := by
  unfold tailWord_357939
  simp only [CollatzResearch.WordTrace]
  refine ⟨13055107850255608959412871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8703405233503739306275247 13055107850255608959412871)
  ·
    refine ⟨19582661775383413439119307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13055107850255608959412871 19582661775383413439119307)
    ·
      refine ⟨29373992663075120158678961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19582661775383413439119307 29373992663075120158678961)
      ·
        refine ⟨22030494497306340119009221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29373992663075120158678961 22030494497306340119009221)
        ·
          refine ⟨4130717718244938772314229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22030494497306340119009221 4130717718244938772314229)
          ·
            refine ⟨387254786085463009904459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4130717718244938772314229 387254786085463009904459)
            ·
              refine ⟨580882179128194514856689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387254786085463009904459 580882179128194514856689)
              ·
                refine ⟨435661634346145886142517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580882179128194514856689 435661634346145886142517)
                ·
                  refine ⟨40843278219951176825861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 435661634346145886142517 40843278219951176825861)
                  ·
                    rfl

theorem cell22_357939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 5].length) (baseStart_357939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357939 prefixEnd_357939 := by exact prefixLift 357939
  have htrace : WordTrace (prefixWord ++ tailWord_357939) baseStart_357939 baseEnd_357939 := by
    simpa [prefixWord, tailWord_357939, baseEnd_357939] using wordTrace_append hprefix tailTrace_357939
  have hstable : (prefixWord ++ tailWord_357939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357939).length < 2 ^ (prefixWord ++ tailWord_357939).sum := by decide
  have hdescent : baseEnd_357939 < baseStart_357939 := by decide
  rcases family_descends (prefixWord ++ tailWord_357939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357969 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_357969 : Nat := 118140960795 + 357969 * 2 ^ 59
def prefixEnd_357969 : Nat := 4983230072969 + 3 ^ 40 * 357969 * 2
def baseEnd_357969 : Nat := 122540104272943452227491

theorem tailTrace_357969 : CollatzResearch.WordTrace tailWord_357969 prefixEnd_357969 122540104272943452227491 := by
  unfold tailWord_357969
  simp only [CollatzResearch.WordTrace]
  refine ⟨13056202040146924083004961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8704134693431282722003307 13056202040146924083004961)
  ·
    refine ⟨9792151530110193062253721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13056202040146924083004961 9792151530110193062253721)
    ·
      refine ⟨7344113647582644796690291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9792151530110193062253721 7344113647582644796690291)
      ·
        refine ⟨11016170471373967195035437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7344113647582644796690291 11016170471373967195035437)
        ·
          refine ⟨4131063926765237698138289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11016170471373967195035437 4131063926765237698138289)
          ·
            refine ⟨3098297945073928273603717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4131063926765237698138289 3098297945073928273603717)
            ·
              refine ⟨580930864701361551300697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3098297945073928273603717 580930864701361551300697)
              ·
                refine ⟨435698148526021163475523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580930864701361551300697 435698148526021163475523)
                ·
                  refine ⟨653547222789031745213285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435698148526021163475523 653547222789031745213285)
                  ·
                    refine ⟨122540104272943452227491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 653547222789031745213285 122540104272943452227491)
                    ·
                      rfl

theorem cell22_357969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_357969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357969 prefixEnd_357969 := by exact prefixLift 357969
  have htrace : WordTrace (prefixWord ++ tailWord_357969) baseStart_357969 baseEnd_357969 := by
    simpa [prefixWord, tailWord_357969, baseEnd_357969] using wordTrace_append hprefix tailTrace_357969
  have hstable : (prefixWord ++ tailWord_357969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357969).length < 2 ^ (prefixWord ++ tailWord_357969).sum := by decide
  have hdescent : baseEnd_357969 < baseStart_357969 := by decide
  rcases family_descends (prefixWord ++ tailWord_357969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357999 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 2, 3]
def baseStart_357999 : Nat := 118140960795 + 357999 * 2 ^ 59
def prefixEnd_357999 : Nat := 4983230072969 + 3 ^ 40 * 357999 * 2
def baseEnd_357999 : Nat := 122550373886033373977399

theorem tailTrace_357999 : CollatzResearch.WordTrace tailWord_357999 prefixEnd_357999 122550373886033373977399 := by
  unfold tailWord_357999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13057296230038239206597051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8704864153358826137731367 13057296230038239206597051)
  ·
    refine ⟨19585944345057358809895577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13057296230038239206597051 19585944345057358809895577)
    ·
      refine ⟨14689458258793019107421683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19585944345057358809895577 14689458258793019107421683)
      ·
        refine ⟨22034187388189528661132525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14689458258793019107421683 22034187388189528661132525)
        ·
          refine ⟨8262820270571073247924697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22034187388189528661132525 8262820270571073247924697)
          ·
            refine ⟨6197115202928304935943523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8262820270571073247924697 6197115202928304935943523)
            ·
              refine ⟨9295672804392457403915285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6197115202928304935943523 9295672804392457403915285)
              ·
                refine ⟨435734662705896440808529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9295672804392457403915285 435734662705896440808529)
                ·
                  refine ⟨326800997029422330606397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435734662705896440808529 326800997029422330606397)
                  ·
                    refine ⟨122550373886033373977399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326800997029422330606397 122550373886033373977399)
                    ·
                      rfl

theorem cell22_357999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_357999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_357999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_357999 prefixEnd_357999 := by exact prefixLift 357999
  have htrace : WordTrace (prefixWord ++ tailWord_357999) baseStart_357999 baseEnd_357999 := by
    simpa [prefixWord, tailWord_357999, baseEnd_357999] using wordTrace_append hprefix tailTrace_357999
  have hstable : (prefixWord ++ tailWord_357999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357999).length < 2 ^ (prefixWord ++ tailWord_357999).sum := by decide
  have hdescent : baseEnd_357999 < baseStart_357999 := by decide
  rcases family_descends (prefixWord ++ tailWord_357999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358050 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_358050 : Nat := 118140960795 + 358050 * 2 ^ 59
def prefixEnd_358050 : Nat := 4983230072969 + 3 ^ 40 * 358050 * 2
def baseEnd_358050 : Nat := 122567832228286240952243

theorem tailTrace_358050 : CollatzResearch.WordTrace tailWord_358050 prefixEnd_358050 122567832228286240952243 := by
  unfold tailWord_358050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3264789088213368729175901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8706104235235649944469069 3264789088213368729175901)
  ·
    refine ⟨1224295908080013273440963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3264789088213368729175901 1224295908080013273440963)
    ·
      refine ⟨1836443862120019910161445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1224295908080013273440963 1836443862120019910161445)
      ·
        refine ⟨344333224147503733155271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1836443862120019910161445 344333224147503733155271)
        ·
          refine ⟨516499836221255599732907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344333224147503733155271 516499836221255599732907)
          ·
            refine ⟨774749754331883399599361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516499836221255599732907 774749754331883399599361)
            ·
              refine ⟨581062315748912549699521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774749754331883399599361 581062315748912549699521)
              ·
                refine ⟨435796736811684412274641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581062315748912549699521 435796736811684412274641)
                ·
                  refine ⟨326847552608763309205981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435796736811684412274641 326847552608763309205981)
                  ·
                    refine ⟨122567832228286240952243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326847552608763309205981 122567832228286240952243)
                    ·
                      rfl

theorem cell22_358050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_358050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358050 prefixEnd_358050 := by exact prefixLift 358050
  have htrace : WordTrace (prefixWord ++ tailWord_358050) baseStart_358050 baseEnd_358050 := by
    simpa [prefixWord, tailWord_358050, baseEnd_358050] using wordTrace_append hprefix tailTrace_358050
  have hstable : (prefixWord ++ tailWord_358050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358050).length < 2 ^ (prefixWord ++ tailWord_358050).sum := by decide
  have hdescent : baseEnd_358050 < baseStart_358050 := by decide
  rcases family_descends (prefixWord ++ tailWord_358050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358061 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_358061 : Nat := 118140960795 + 358061 * 2 ^ 59
def prefixEnd_358061 : Nat := 4983230072969 + 3 ^ 40 * 358061 * 2
def baseEnd_358061 : Nat := 122571597753085878927209

theorem tailTrace_358061 : CollatzResearch.WordTrace tailWord_358061 prefixEnd_358061 122571597753085878927209 := by
  unfold tailWord_358061
  simp only [CollatzResearch.WordTrace]
  refine ⟨13059557555813623795354037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8706371703875749196902691 13059557555813623795354037)
  ·
    refine ⟨1224333520857527230814441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13059557555813623795354037 1224333520857527230814441)
    ·
      refine ⟨918250140643145423110831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1224333520857527230814441 918250140643145423110831)
      ·
        refine ⟨1377375210964718134666247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918250140643145423110831 1377375210964718134666247)
        ·
          refine ⟨2066062816447077201999371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377375210964718134666247 2066062816447077201999371)
          ·
            refine ⟨3099094224670615802999057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066062816447077201999371 3099094224670615802999057)
            ·
              refine ⟨2324320668502961852249293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3099094224670615802999057 2324320668502961852249293)
              ·
                refine ⟨871620250688610694593485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2324320668502961852249293 871620250688610694593485)
                ·
                  refine ⟨326857594008229010472557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 871620250688610694593485 326857594008229010472557)
                  ·
                    refine ⟨122571597753085878927209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326857594008229010472557 122571597753085878927209)
                    ·
                      rfl

theorem cell22_358061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_358061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358061 prefixEnd_358061 := by exact prefixLift 358061
  have htrace : WordTrace (prefixWord ++ tailWord_358061) baseStart_358061 baseEnd_358061 := by
    simpa [prefixWord, tailWord_358061, baseEnd_358061] using wordTrace_append hprefix tailTrace_358061
  have hstable : (prefixWord ++ tailWord_358061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358061).length < 2 ^ (prefixWord ++ tailWord_358061).sum := by decide
  have hdescent : baseEnd_358061 < baseStart_358061 := by decide
  rcases family_descends (prefixWord ++ tailWord_358061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358074 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_358074 : Nat := 118140960795 + 358074 * 2 ^ 59
def prefixEnd_358074 : Nat := 4983230072969 + 3 ^ 40 * 358074 * 2
def baseEnd_358074 : Nat := 40858682639586059450723

theorem tailTrace_358074 : CollatzResearch.WordTrace tailWord_358074 prefixEnd_358074 40858682639586059450723 := by
  unfold tailWord_358074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3265007926191631753894319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8706687803177684677051517 3265007926191631753894319)
  ·
    refine ⟨4897511889287447630841479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3265007926191631753894319 4897511889287447630841479)
    ·
      refine ⟨7346267833931171446262219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4897511889287447630841479 7346267833931171446262219)
      ·
        refine ⟨11019401750896757169393329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7346267833931171446262219 11019401750896757169393329)
        ·
          refine ⟨8264551313172567877044997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11019401750896757169393329 8264551313172567877044997)
          ·
            refine ⟨1549603371219856476945937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8264551313172567877044997 1549603371219856476945937)
            ·
              refine ⟨1162202528414892357709453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549603371219856476945937 1162202528414892357709453)
              ·
                refine ⟨435825948155584634141045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1162202528414892357709453 435825948155584634141045)
                ·
                  refine ⟨40858682639586059450723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 435825948155584634141045 40858682639586059450723)
                  ·
                    rfl

theorem cell22_358074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_358074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358074 prefixEnd_358074 := by exact prefixLift 358074
  have htrace : WordTrace (prefixWord ++ tailWord_358074) baseStart_358074 baseEnd_358074 := by
    simpa [prefixWord, tailWord_358074, baseEnd_358074] using wordTrace_append hprefix tailTrace_358074
  have hstable : (prefixWord ++ tailWord_358074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358074).length < 2 ^ (prefixWord ++ tailWord_358074).sum := by decide
  have hdescent : baseEnd_358074 < baseStart_358074 := by decide
  rcases family_descends (prefixWord ++ tailWord_358074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358082 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_358082 : Nat := 118140960795 + 358082 * 2 ^ 59
def prefixEnd_358082 : Nat := 4983230072969 + 3 ^ 40 * 358082 * 2
def baseEnd_358082 : Nat := 122578786482248824152145

theorem tailTrace_358082 : CollatzResearch.WordTrace tailWord_358082 prefixEnd_358082 122578786482248824152145 := by
  unfold tailWord_358082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3265080872184386095467125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8706882325825029587912333 3265080872184386095467125)
  ·
    refine ⟨306101331767286196450043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3265080872184386095467125 306101331767286196450043)
    ·
      refine ⟨459151997650929294675065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306101331767286196450043 459151997650929294675065)
      ·
        refine ⟨344363998238196971006299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459151997650929294675065 344363998238196971006299)
        ·
          refine ⟨516545997357295456509449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344363998238196971006299 516545997357295456509449)
          ·
            refine ⟨387409498017971592382087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516545997357295456509449 387409498017971592382087)
            ·
              refine ⟨581114247026957388573131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387409498017971592382087 581114247026957388573131)
              ·
                refine ⟨871671370540436082859697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581114247026957388573131 871671370540436082859697)
                ·
                  refine ⟨653753527905327062144773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 871671370540436082859697 653753527905327062144773)
                  ·
                    refine ⟨122578786482248824152145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 653753527905327062144773 122578786482248824152145)
                    ·
                      rfl

theorem cell22_358082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_358082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358082 prefixEnd_358082 := by exact prefixLift 358082
  have htrace : WordTrace (prefixWord ++ tailWord_358082) baseStart_358082 baseEnd_358082 := by
    simpa [prefixWord, tailWord_358082, baseEnd_358082] using wordTrace_append hprefix tailTrace_358082
  have hstable : (prefixWord ++ tailWord_358082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358082).length < 2 ^ (prefixWord ++ tailWord_358082).sum := by decide
  have hdescent : baseEnd_358082 < baseStart_358082 := by decide
  rcases family_descends (prefixWord ++ tailWord_358082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358213 : List Nat := [1, 3, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_358213 : Nat := 118140960795 + 358213 * 2 ^ 59
def prefixEnd_358213 : Nat := 4983230072969 + 3 ^ 40 * 358213 * 2
def baseEnd_358213 : Nat := 122623630459408149126743

theorem tailTrace_358213 : CollatzResearch.WordTrace tailWord_358213 prefixEnd_358213 122623630459408149126743 := by
  unfold tailWord_358213
  simp only [CollatzResearch.WordTrace]
  refine ⟨13065101451262953754887293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8710067634175302503258195 13065101451262953754887293)
  ·
    refine ⟨4899413044223607658082735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13065101451262953754887293 4899413044223607658082735)
    ·
      refine ⟨7349119566335411487124103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899413044223607658082735 7349119566335411487124103)
      ·
        refine ⟨11023679349503117230686155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7349119566335411487124103 11023679349503117230686155)
        ·
          refine ⟨16535519024254675846029233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11023679349503117230686155 16535519024254675846029233)
          ·
            refine ⟨12401639268191006884521925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16535519024254675846029233 12401639268191006884521925)
            ·
              refine ⟨2325307362785813790847861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12401639268191006884521925 2325307362785813790847861)
              ·
                refine ⟨217997565261170042891987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2325307362785813790847861 217997565261170042891987)
                ·
                  refine ⟨326996347891755064337981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217997565261170042891987 326996347891755064337981)
                  ·
                    refine ⟨122623630459408149126743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 326996347891755064337981 122623630459408149126743)
                    ·
                      rfl

theorem cell22_358213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_358213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358213 prefixEnd_358213 := by exact prefixLift 358213
  have htrace : WordTrace (prefixWord ++ tailWord_358213) baseStart_358213 baseEnd_358213 := by
    simpa [prefixWord, tailWord_358213, baseEnd_358213] using wordTrace_append hprefix tailTrace_358213
  have hstable : (prefixWord ++ tailWord_358213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358213).length < 2 ^ (prefixWord ++ tailWord_358213).sum := by decide
  have hdescent : baseEnd_358213 < baseStart_358213 := by decide
  rcases family_descends (prefixWord ++ tailWord_358213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
